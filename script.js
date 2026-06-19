const $ = id => document.getElementById(id);
const playBeep = (freq, type) => { try { const ctx=new(window.AudioContext||window.webkitAudioContext)({ latencyHint: 'interactive' }),osc=ctx.createOscillator(),g=ctx.createGain();osc.type=type;osc.frequency.value=freq;g.gain.setValueAtTime(0.05,ctx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+0.3);osc.connect(g);g.connect(ctx.destination);osc.start();osc.stop(ctx.currentTime+0.3); } catch(e){} };
const playJoinSound = () => playBeep(880, 'sine'), playLeaveSound = () => playBeep(440, 'triangle'); 

function mungeSDP(sdp) {
    const match = sdp.match(/a=rtpmap:(\d+) opus\/48000\/2/i);
    if (match) {
        const pt = match[1];
        const fmtpRegex = new RegExp(`(a=fmtp:${pt} .*)`);
        if (fmtpRegex.test(sdp)) {
            return sdp.replace(fmtpRegex, `$1;useinbandfec=1;usedtx=1`);
        } else {
            return sdp.replace(new RegExp(`(a=rtpmap:${pt} opus\\/48000\\/2\\r\\n)`, 'i'), `$1a=fmtp:${pt} useinbandfec=1;usedtx=1\r\n`);
        }
    }
    return sdp;
}

const fileWorkerCode = `
    self.onmessage = async (e) => {
        try {
            const chunk = e.data.file.slice(e.data.offset, e.data.offset + e.data.chunkSize);
            const buffer = await chunk.arrayBuffer();
            self.postMessage({ buffer: buffer, txId: e.data.txId, index: e.data.index }, [buffer]);
        } catch (err) {
            self.postMessage({ error: err.message, txId: e.data.txId, index: e.data.index });
        }
    };
`;
const fileWorker = new Worker(URL.createObjectURL(new Blob([fileWorkerCode], { type: 'application/javascript' })));
const _wcbs = {};
fileWorker.onmessage = (e) => {
    const key = e.data.txId + '-' + e.data.index;
    const cb = _wcbs[key];
    if (cb) { delete _wcbs[key]; cb(e.data); }
};
const readChunkViaWorker = (file, offset, chunkSize, txId, index) => {
    return new Promise((resolve, reject) => {
        _wcbs[txId + '-' + index] = (data) => {
            if (data.error) reject(new Error(data.error));
            else resolve(data.buffer);
        };
        fileWorker.postMessage({ file, offset, chunkSize, txId, index });
    });
};

const CHUNK_SIZE = 65536;
const WINDOW_SIZE = 10;
const RETRY_TIMEOUT = 3000;
const MAX_RETRIES = 15;
const ACK_FLUSH_INTERVAL = 200;
const GAP_CHECK_INTERVAL = 2000;
const STALL_TIMEOUT = 15000;
const MAX_FILE_SIZE = 524288000;

async function computeHash(buffer) {
    const h = await crypto.subtle.digest('SHA-256', buffer);
    return Array.from(new Uint8Array(h)).map(b => b.toString(16).padStart(2, '0')).join('');
}

class BitSet {
    constructor(size) { this._s = size; this._w = new Uint32Array(Math.ceil(size / 32)); this._c = 0; }
    add(i) { const w = i >>> 5, b = 1 << (i & 31); if (!(this._w[w] & b)) { this._w[w] |= b; this._c++; } }
    has(i) { return !!((this._w[i >>> 5] >>> (i & 31)) & 1); }
    count() { return this._c; }
    toArray() { const r = []; for (let i = 0; i < this._s; i++) if (this.has(i)) r.push(i); return r; }
    getGaps(upTo) { const r = []; for (let i = 0; i <= Math.min(upTo, this._s - 1); i++) if (!this.has(i)) r.push(i); return r; }
}

let myName = "", myId = "", isHost = false, peer, ROOM_ID = "superconf-mesh-secretpassword", localStream = null, isMuted = false;
let screenStream = null, screenCalls = {}, camStream = null, camCalls = {};

const connections = {}, fileConns = {}, peerNames = {}, fileTransfers = {}, pendingConnections = new Set(), lastSeen = {}, activeSounds = {}, lastRealPing = {};
const peerConfig = { config: { iceServers: [{ urls: 'stun:stun.l.google.com:19302' }, { urls: 'stun:stun1.l.google.com:19302' }] } };

const dlIcon = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>';

const soundboard = {};
let waitingForKeyBind = null;
let amITyping = false;
let typingTimeout = null;
const typingUsers = new Set();
let tempPeer = null;

const senderTransfers = {};

function cleanupSenderTx(txId) {
    const tx = senderTransfers[txId];
    if (!tx) return;
    if (tx._timers) tx._timers.forEach(t => clearTimeout(t));
    delete senderTransfers[txId];
}

window.toggleTx = (txId) => {
    const tx = senderTransfers[txId];
    if (tx && !tx.completed) {
        tx.paused = !tx.paused;
        const btn = $(`pause-${txId}`);
        if (btn) btn.innerHTML = tx.paused ? "▶️ Resume" : "⏸️ Pause";
        bcast({ type: 'file-control', txId, action: tx.paused ? 'pause' : 'resume' });
        if (tx._waker) { tx._waker(); tx._waker = null; }
    }
};

window.cancelTx = (txId) => {
    const tx = senderTransfers[txId];
    if (tx) {
        tx.canceled = true;
        bcast({ type: 'file-control', txId, action: 'cancel' });
        const msgNode = $(`msg-${txId}`);
        if (msgNode) msgNode.innerHTML = `<div class="msg-info">You</div><div style="color: #da373c;">❌ Upload Canceled</div>`;
        if (tx._waker) { tx._waker(); tx._waker = null; }
        setTimeout(() => cleanupSenderTx(txId), 100);
    }
};

window.toggleRx = (txId, sid) => {
    const tr = fileTransfers[txId];
    const conn = fileConns[sid];
    if (tr && conn && conn.open) {
        tr.paused = !tr.paused;
        const btn = $(`pause-rx-${txId}`);
        if (btn) btn.innerHTML = tr.paused ? "▶️ Resume" : "⏸️ Pause";
        conn.send({ type: 'file-control-rx', txId, action: tr.paused ? 'pause' : 'resume' });
    }
};

window.cancelRx = (txId, sid) => {
    const tr = fileTransfers[txId];
    if (tr) {
        if (tr._ackTimer) clearInterval(tr._ackTimer);
        if (tr._gapTimer) clearInterval(tr._gapTimer);
        delete fileTransfers[txId];
    }
    const msgNode = $(`msg-rx-${txId}`);
    if (msgNode) msgNode.innerHTML = `<div class="msg-info">${peerNames[sid] || 'Someone'}</div><div style="color: #da373c;">❌ Download Canceled</div>`;
};

let currentFx = 0; 
const fxIcons = ['✨', '🧚', '👻', '🌈'];
const fxNames = ['None', 'Fairy Dust', 'Ghost', 'Rainbow'];
let fxHue = 0;
let lastFxTime = 0;

$('cursor-btn').onclick = () => {
    currentFx = (currentFx + 1) % 4;
    $('cursor-btn').innerText = fxIcons[currentFx];
    $('cursor-btn').classList.toggle('active', currentFx > 0);
    addSystemMsg(`Cursor effect: <b>${fxNames[currentFx]}</b>`);
};

document.addEventListener('mousemove', e => {
    if (currentFx === 0 || $('login-screen').style.display !== 'none') return;
    const now = Date.now();
    if (now - lastFxTime < 30) return; 
    lastFxTime = now;

    const p = document.createElement('div');
    p.className = 'fx-part';
    p.style.left = (e.clientX - 10) + 'px';
    p.style.top = (e.clientY - 10) + 'px';

    if (currentFx === 1) { 
        p.innerText = '✨';
        p.style.fontSize = (Math.random() * 12 + 8) + 'px';
        p.style.animation = 'fxFall 0.8s forwards';
    } else if (currentFx === 2) { 
        p.innerText = '👻';
        p.style.fontSize = '20px';
        p.style.animation = 'fxFloat 0.8s forwards';
    } else if (currentFx === 3) { 
        p.style.width = '14px';
        p.style.height = '14px';
        p.style.borderRadius = '50%';
        p.style.background = `hsl(${fxHue}, 100%, 50%)`;
        p.style.boxShadow = `0 0 10px hsl(${fxHue}, 100%, 50%)`;
        p.style.animation = 'fxFade 0.6s forwards';
        fxHue = (fxHue + 15) % 360;
    }

    $('cursor-fx').appendChild(p);
    setTimeout(() => p.remove(), 1000);
});

window.addEventListener('DOMContentLoaded', () => {
    tempPeer = new Peer(peerConfig);
    
    const doCheck = () => {
        if(!tempPeer || tempPeer.destroyed || tempPeer.disconnected) return;
        const pConn = tempPeer.connect(ROOM_ID, { metadata: { isPing: true }, reliable: true });
        let gotResp = false;
        
        pConn.on('open', () => { pConn.send({ type: 'get-count' }); });
        pConn.on('data', d => {
            if (d.type === 'count-resp') {
                gotResp = true;
                const count = d.count;
                $('online-users').innerText = `🟢 ${count} User${count !== 1 ? 's' : ''} Online`;
                setTimeout(() => pConn.close(), 100);
            }
        });
        pConn.on('error', () => {
            if(!gotResp) $('online-users').innerText = "🟢 0 Users Online";
        });
        setTimeout(() => { 
            if(!gotResp) {
                $('online-users').innerText = "🟢 0 Users Online"; 
                if (pConn) pConn.close();
            }
        }, 2000);
    };

    tempPeer.on('open', () => {
        doCheck();
        window.loginPingInterval = setInterval(doCheck, 3000);
    });
    tempPeer.on('error', () => {
        $('online-users').innerText = "🟢 0 Users Online";
    });
    
    $('messages').addEventListener('click', (e) => {
        if (e.target.tagName === 'IMG') {
            if (e.target.requestFullscreen) {
                e.target.requestFullscreen();
            } else if (e.target.webkitRequestFullscreen) {
                e.target.webkitRequestFullscreen();
            }
        }
    });
});

const trig = e => { if (e.key === 'Enter') $('join-btn').click(); };
$('username').addEventListener('keypress', trig); $('room-pass').addEventListener('keypress', trig);
const escapeHTML = s => s.replace(/[&<>'"]/g, t => ({'&':'&amp;','<':'&lt;','>':'&gt;',"'":'&#39;','"':'&quot;'}[t]));
const linkify = s => s.replace(/(https?:\/\/[^\s]+)/g, url => `<a href="${url}" target="_blank">${url}</a>`);

$('join-btn').onclick = async () => {
    if (window.loginPingInterval) clearInterval(window.loginPingInterval);
    if (tempPeer && !tempPeer.destroyed) { tempPeer.destroy(); }
    
    myName = $('username').value.trim() || "Anon";
    if ($('room-pass').value.trim() !== "secretpassword") return alert("Incorrect password! Access denied.");
    
    if ("Notification" in window && Notification.permission !== "granted" && Notification.permission !== "denied") {
        Notification.requestPermission();
    }

    try { 
        localStream = await navigator.mediaDevices.getUserMedia({ 
            audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false, latency: 0 } 
        }); 
    } 
    catch(err) { }

    $('login-screen').style.display = 'none'; $('conn-status').innerText = "Initializing...";
    
    $('room-clock').style.display = 'inline-block';
    const tickClock = () => { 
        const now = new Date();
        const days = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
        const dateStr = `${days[now.getDay()]} ${now.getDate()}, ${now.getFullYear()}`;
        const timeStr = now.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
        $('room-clock').innerHTML = `${dateStr}<br>${timeStr}`; 
    };
    tickClock();
    setInterval(tickClock, 1000);

    initPeerJS();
};

function notifyUser(title, body) {
    if ("Notification" in window && Notification.permission === "granted" && document.hidden) {
        new Notification(title, { body: body });
    }
}

function initPeerJS() {
    $('searching-container').style.display = 'flex';
    peer = new Peer(ROOM_ID, peerConfig);
    peer.on('connection', handleNewConnection); peer.on('call', handleNewCall);
    peer.on('open', id => {
        myId = id; isHost = true; $('conn-status').innerText = "Host Ready"; $('conn-status').style.color = "#23a559";
        const safeMyName = escapeHTML(myName);
        addSystemMsg(`You created the room as <b>${safeMyName}</b>`); addUserToSidebar(safeMyName, "me"); enableChat();
    });
    peer.on('error', err => {
        if (err.type === 'unavailable-id') {
            peer = new Peer(peerConfig);
            peer.on('connection', handleNewConnection); peer.on('call', handleNewCall);
            peer.on('open', id => {
                myId = id; isHost = false; $('conn-status').innerText = "Connected"; $('conn-status').style.color = "#23a559";
                const safeMyName = escapeHTML(myName);
                addSystemMsg(`You joined as <b>${safeMyName}</b>`); addUserToSidebar(safeMyName, "me"); connectToPeer(ROOM_ID); enableChat();
            });
        }
    });
}

function connectToPeer(targetId) {
    if (connections[targetId] || pendingConnections.has(targetId) || targetId === myId) return;
    pendingConnections.add(targetId); setTimeout(() => pendingConnections.delete(targetId), 4000);
    
    const connChat = peer.connect(targetId, { reliable: false, label: 'chat' }); 
    handleNewConnection(connChat);

    const connFile = peer.connect(targetId, { reliable: true, label: 'file' }); 
    handleNewConnection(connFile);
    
    if (localStream) handleNewCall(peer.call(targetId, localStream, { metadata: { type: 'audio' }, sdpTransform: mungeSDP }));
}

function handleNewConnection(conn) {
    if (conn.metadata?.isPing) {
        conn.on('data', data => {
            if (data.type === 'get-count') conn.send({ type: 'count-resp', count: Object.keys(connections).length + 1 });
        });
        return;
    }

    if (conn.label === 'file') {
        const setupFile = () => { fileConns[conn.peer] = conn; };
        conn.open ? setupFile() : conn.on('open', setupFile);

        const sendUnicast = (peerId, msg) => { const c = fileConns[peerId]; if (c && c.open) c.send(msg); };

        conn.on('data', data => {
            const sid = conn.peer; lastSeen[sid] = Date.now();

            // --- CONTROL MESSAGES ---
            if (data.type === 'file-control') {
                const tr = fileTransfers[data.txId];
                if (!tr && data.action !== 'cancel') return;
                if (data.action === 'pause') {
                    const btn = $(`pause-rx-${data.txId}`);
                    if (btn) { btn.innerHTML = "▶️ Resume"; tr.paused = true; }
                } else if (data.action === 'resume') {
                    const btn = $(`pause-rx-${data.txId}`);
                    if (btn) { btn.innerHTML = "⏸️ Pause"; tr.paused = false; }
                } else if (data.action === 'cancel') {
                    const tr2 = fileTransfers[data.txId];
                    if (tr2) {
                        if (tr2._ackTimer) clearInterval(tr2._ackTimer);
                        if (tr2._gapTimer) clearInterval(tr2._gapTimer);
                        delete fileTransfers[data.txId];
                    }
                    const msgNode = $(`msg-rx-${data.txId}`);
                    if (msgNode) msgNode.innerHTML = `<div class="msg-info">${peerNames[sid] || 'Someone'}</div><div style="color: #da373c;">❌ Sender Canceled Transfer</div>`;
                }
                return;
            }
            if (data.type === 'file-control-rx') {
                const tx = senderTransfers[data.txId];
                if (tx) {
                    if (data.action === 'pause' && !tx.paused) window.toggleTx(data.txId);
                    else if (data.action === 'resume' && tx.paused) window.toggleTx(data.txId);
                }
                return;
            }

            // --- SENDER-SIDE: responses from receivers ---
            if (data.type === 'file-ack' || data.type === 'file-bulk-ack') {
                const tx = senderTransfers[data.txId];
                if (!tx || tx.completed) return;
                const indices = data.type === 'file-ack' ? [data.index] : data.indices;
                if (!tx.peerAcks[sid]) tx.peerAcks[sid] = new BitSet(tx.totalChunks);
                for (const idx of indices) tx.peerAcks[sid].add(idx);
                tx.lastAckTime = Date.now();
                if (tx._waker) { tx._waker(); tx._waker = null; }
                return;
            }
            if (data.type === 'file-nak') {
                const tx = senderTransfers[data.txId];
                if (!tx || tx.completed) return;
                tx._retxQ.add(data.index);
                if (tx._waker) { tx._waker(); tx._waker = null; }
                return;
            }
            if (data.type === 'file-status') {
                const tx = senderTransfers[data.txId];
                if (!tx || tx.completed) return;
                if (data.received) {
                    if (!tx.peerAcks[sid]) tx.peerAcks[sid] = new BitSet(tx.totalChunks);
                    for (const idx of data.received) tx.peerAcks[sid].add(idx);
                }
                if (data.gaps) for (const idx of data.gaps) tx._retxQ.add(idx);
                tx.lastAckTime = Date.now();
                if (tx._waker) { tx._waker(); tx._waker = null; }
                return;
            }
            if (data.type === 'file-status-req') {
                const tr = fileTransfers[data.txId];
                if (!tr) return;
                const recv = tr._received.toArray();
                const gaps = tr._received.getGaps(tr._receivedCount > 0 ? tr.totalChunks - 1 : -1);
                sendUnicast(sid, { type: 'file-status', txId: data.txId, received: recv, gaps });
                return;
            }
            if (data.type === 'file-complete') {
                const tx = senderTransfers[data.txId];
                if (!tx) return;
                if (data.verified) {
                    tx.completedPeers.add(sid);
                    sendUnicast(sid, { type: 'file-complete-ack', txId: data.txId });
                    if (tx._waker) { tx._waker(); tx._waker = null; }
                } else {
                    tx.canceled = true;
                    const msgNode = $(`msg-${data.txId}`);
                    if (msgNode) msgNode.innerHTML = `<div class="msg-info">You</div><div style="color: #da373c;">❌ Upload Failed: Receiver integrity check failed</div>`;
                    cleanupSenderTx(data.txId);
                }
                return;
            }
            if (data.type === 'file-complete-ack') {
                const tr = fileTransfers[data.txId];
                if (!tr) return;
                tr._senderDone = true;
                setTimeout(() => {
                    if (tr._ackTimer) clearInterval(tr._ackTimer);
                    if (tr._gapTimer) clearInterval(tr._gapTimer);
                    delete fileTransfers[data.txId];
                }, 1000);
                return;
            }

            // --- RECEIVER-SIDE: file meta + chunks ---
            if (data.type === 'file-meta') {
                const txId = data.txId;
                const tc = data.totalChunks;
                const tr = {
                    meta: data, chunks: new Array(tc), totalChunks: tc,
                    _received: new BitSet(tc), _receivedCount: 0, _receivedBytes: 0,
                    senderId: sid, paused: false, completed: false, _senderDone: false,
                    _ackBatch: [], _nakBatch: [], _ackTimer: null, _gapTimer: null
                };
                fileTransfers[txId] = tr;

                tr._ackTimer = setInterval(() => {
                    if (tr.completed || !fileTransfers[txId]) { clearInterval(tr._ackTimer); tr._ackTimer = null; return; }
                    if (tr._ackBatch.length) sendUnicast(sid, { type: 'file-bulk-ack', txId, indices: tr._ackBatch.splice(0) });
                    if (tr._nakBatch.length) {
                        const batch = tr._nakBatch.splice(0);
                        for (const idx of batch) sendUnicast(sid, { type: 'file-nak', txId, index: idx });
                    }
                }, ACK_FLUSH_INTERVAL);

                tr._gapTimer = setInterval(() => {
                    if (tr.completed || !fileTransfers[txId]) { clearInterval(tr._gapTimer); tr._gapTimer = null; return; }
                    let highest = -1;
                    for (let i = tr.totalChunks - 1; i >= 0; i--) { if (tr._received.has(i)) { highest = i; break; } }
                    if (highest > 0) {
                        const gaps = tr._received.getGaps(highest);
                        if (gaps.length) sendUnicast(sid, { type: 'file-status', txId, received: tr._received.toArray(), gaps });
                    }
                }, GAP_CHECK_INTERVAL);

                const progHtml = `
                <div>📥 Downloading <b>${data.name}</b>...</div>
                <div class="progress-container"><div class="progress-bar" id="bar-rx-${txId}"></div></div>
                <div style="margin-top: 8px; display: flex; gap: 8px;">
                    <button class="tx-btn" id="pause-rx-${txId}" onclick="window.toggleRx('${txId}', '${sid}')">⏸️ Pause</button>
                    <button class="tx-btn tx-btn-danger" onclick="window.cancelRx('${txId}', '${sid}')">❌ Cancel</button>
                </div>`;
                addMessage(progHtml, peerNames[sid] || "Someone", 'theirs', `msg-rx-${txId}`);
                return;
            }

            if (data.type === 'file-chunk') {
                const tr = fileTransfers[data.txId];
                if (!tr || tr.completed || tr.paused) return;
                const idx = data.index;
                if (tr._received.has(idx)) return;

                (async () => {
                    try {
                        const ch = await computeHash(data.data);
                        if (ch !== tr.meta.chunkHashes[idx]) { tr._nakBatch.push(idx); return; }
                        tr.chunks[idx] = data.data;
                        tr._received.add(idx);
                        tr._receivedCount++;
                        tr._receivedBytes += data.data.byteLength;
                        tr._ackBatch.push(idx);

                        const bar = $(`bar-rx-${data.txId}`);
                        if (bar) bar.style.width = `${Math.min((tr._receivedBytes / tr.meta.size) * 100, 100)}%`;

                        if (tr._receivedCount >= tr.totalChunks && !tr.completed) {
                            tr.completed = true;
                            if (tr._ackTimer) { clearInterval(tr._ackTimer); tr._ackTimer = null; }
                            if (tr._gapTimer) { clearInterval(tr._gapTimer); tr._gapTimer = null; }
                            const blob = new Blob(tr.chunks, { type: tr.meta.fileType });
                            const buf = await blob.arrayBuffer();
                            const ok = await computeHash(buf) === tr.meta.fileHash;

                            if (ok) {
                                const msgNode = $(`msg-rx-${data.txId}`);
                                if (msgNode) msgNode.remove();
                                const url = URL.createObjectURL(blob);
                                const sn = peerNames[sid] || "Someone";
                                const ct = tr.meta.fileType;
                                if (ct.startsWith('image/')) addMessage(`<img src="${url}"><a href="${url}" download="${tr.meta.name}" class="chat-media-link">${dlIcon} Download Image</a>`, sn, 'theirs');
                                else if (ct.startsWith('video/')) addMessage(`<video src="${url}" controls preload="metadata"></video><a href="${url}" download="${tr.meta.name}" class="chat-media-link">${dlIcon} Download Video</a>`, sn, 'theirs');
                                else if (ct.startsWith('audio/')) addMessage(`<audio src="${url}" controls></audio><a href="${url}" download="${tr.meta.name}" class="chat-media-link">${dlIcon} Download Audio</a>`, sn, 'theirs');
                                else addMessage(`<div>📂 ${tr.meta.name}</div><a href="${url}" download="${tr.meta.name}" class="chat-media-link">${dlIcon} Download File</a>`, sn, 'theirs');
                                playJoinSound();
                                notifyUser(`Incoming file from ${sn}`, tr.meta.name);
                                sendUnicast(sid, { type: 'file-complete', txId: data.txId, verified: true });
                                setTimeout(() => { if (!tr._senderDone && fileTransfers[data.txId]) { if (tr._ackTimer) clearInterval(tr._ackTimer); if (tr._gapTimer) clearInterval(tr._gapTimer); delete fileTransfers[data.txId]; } }, 10000);
                            } else {
                                sendUnicast(sid, { type: 'file-complete', txId: data.txId, verified: false });
                                $(`msg-rx-${data.txId}`).innerHTML = `<div class="msg-info">${peerNames[sid] || "Someone"}</div><div style="color: #da373c;">❌ Download Failed: File integrity check failed</div>`;
                                delete fileTransfers[data.txId];
                            }
                        }
                    } catch (_) { tr._nakBatch.push(idx); }
                })();
                return;
            }
        });
        conn.on('close', () => { delete fileConns[conn.peer]; });
        conn.on('error', () => { delete fileConns[conn.peer]; });
        return;
    }

    const setup = () => {
        pendingConnections.delete(conn.peer); lastSeen[conn.peer] = Date.now();
        $('searching-container').style.display = 'none'; connections[conn.peer] = conn;
        if (!isHost && conn.peer === ROOM_ID) { $('conn-status').innerText = "Connected"; $('conn-status').style.color = "#23a559"; }
        conn.send({ type: 'name', value: myName });
        if (isHost) { const peers = Object.keys(connections).filter(id => id !== conn.peer); if(peers.length) conn.send({ type: 'peer-list', peers }); }
        
        if (screenStream) {
            screenCalls[conn.peer] = peer.call(conn.peer, screenStream, { metadata: { type: 'screenshare' }, sdpTransform: mungeSDP });
            applyBitrateLimit(screenCalls[conn.peer], 1000000);
        }
        if (camStream) {
            camCalls[conn.peer] = peer.call(conn.peer, camStream, { metadata: { type: 'webcam' }, sdpTransform: mungeSDP });
            applyBitrateLimit(camCalls[conn.peer], 500000);
        }
    };
    
    conn.open ? setup() : conn.on('open', setup);
    conn.on('data', data => {
        const sid = conn.peer; lastSeen[sid] = Date.now();
        if (data.type === 'name') {
            const safeName = escapeHTML(data.value);
            peerNames[sid] = safeName;
            addUserToSidebar(safeName, sid);
            addSystemMsg(`<b>${safeName}</b> joined.`);
            playJoinSound();
        }
        else if (data.type === 'peer-list' || data.type === 'mesh-sync') data.peers.forEach(pid => { if(pid !== myId && !connections[pid]) connectToPeer(pid); });
        else if (data.type === 'text') {
            const senderName = peerNames[sid] || "Unknown";
            addMessage(linkify(escapeHTML(data.value)), senderName, 'theirs');
            playJoinSound();
            notifyUser(`New message from ${senderName}`, data.value);
        }
        else if (data.type === 'typing') { 
            const uname = peerNames[sid] || "Someone"; 
            data.state ? typingUsers.add(uname) : typingUsers.delete(uname); 
            updateTypingUI(); 
        }
        else if (data.type === 'ping') conn.send({ type: 'pong', time: data.time });
        else if (data.type === 'pong') {
            const lat = Date.now() - data.time;
            lastRealPing[sid] = lat;
            updatePingUI(sid, lat);
        }
        else if (data.type === 'play-sound') { 
            playCustomSound(data.buffer, data.mime, sid); 
            addSystemMsg(`🎵 <b>${peerNames[sid] || "Someone"}</b> played a sound.`);
            const url = URL.createObjectURL(new Blob([data.buffer], { type: data.mime }));
            addMessage(`<audio src="${url}" controls></audio><a href="${url}" download="${data.name || 'sound'}" class="chat-media-link">${dlIcon} Download Audio</a>`, peerNames[sid] || "Someone", 'theirs');
        }
    });
    conn.on('close', () => removePeer(conn.peer)); conn.on('error', () => removePeer(conn.peer));
}

function handleNewCall(call) {
    const type = call.metadata?.type;
    if (type === 'screenshare' || type === 'webcam') {
        call.answer(undefined, { sdpTransform: mungeSDP });
        call.on('stream', st => addVideoElement(call.peer + (type==='webcam'?'-cam':''), st, false));
        call.on('close', () => $(`video-${call.peer}${type==='webcam'?'-cam':''}`)?.remove());
        return;
    }
    localStream ? call.answer(localStream, { sdpTransform: mungeSDP }) : call.answer(undefined, { sdpTransform: mungeSDP });
    call.on('stream', st => {
        if (!$(`audio-${call.peer}`)) {
            const a = new Audio(); a.id = `audio-${call.peer}`; a.srcObject = st; a.autoplay = true;
            document.body.appendChild(a);
            
            const vs = $(`vol-${call.peer}`); if(vs) a.volume = vs.value;
            const muteIcon = $(`mute-icon-${call.peer}`);
            if(muteIcon && muteIcon.innerText === "🔇") a.muted = true;
        }
    });
}

function applyBitrateLimit(call, maxBitrate) {
    call.on('open', () => {
        if (!call.peerConnection) return;
        const senders = call.peerConnection.getSenders();
        const videoSender = senders.find(s => s.track && s.track.kind === 'video');
        if (videoSender) {
            const params = videoSender.getParameters();
            if (!params.encodings) params.encodings = [{}];
            params.encodings[0].maxBitrate = maxBitrate;
            videoSender.setParameters(params).catch(e => console.warn("Failed to set bitrate limit", e));
        }
    });
}

function removePeer(id) {
    if (!connections[id]) return;
    const uname = peerNames[id] || "Someone";
    addSystemMsg(`<b>${uname}</b> left.`); playLeaveSound();
    
    if (typingUsers.has(uname)) { typingUsers.delete(uname); updateTypingUI(); }

    for (let tid in fileTransfers) {
        if (fileTransfers[tid].senderId === id) {
            const tr = fileTransfers[tid];
            if (tr._ackTimer) clearInterval(tr._ackTimer);
            if (tr._gapTimer) clearInterval(tr._gapTimer);
            const msgNode = $(`msg-rx-${tid}`);
            if (msgNode) msgNode.innerHTML = `<div class="msg-info">${uname}</div><div style="color: #da373c;">❌ Download Failed: User disconnected</div>`;
            delete fileTransfers[tid];
        }
    }
    for (let tid in senderTransfers) {
        const tx = senderTransfers[tid];
        if (tx && tx.peerAcks) {
            delete tx.peerAcks[id];
            if (tx._waker) { tx._waker(); tx._waker = null; }
        }
    }

    ['', '-cam'].forEach(ext => { $(`video-${id}${ext}`)?.remove(); });
    if (screenCalls[id]) { screenCalls[id].close(); delete screenCalls[id]; }
    if (camCalls[id]) { camCalls[id].close(); delete camCalls[id]; }
    $(`sidebar-${id}`)?.remove(); $(`audio-${id}`)?.remove();
    
    delete connections[id]; delete fileConns[id]; delete peerNames[id]; delete lastSeen[id]; delete lastRealPing[id]; pendingConnections.delete(id);
    
    if (id === ROOM_ID && !isHost) { $('searching-container').style.display = 'flex'; $('conn-status').innerText = "Searching..."; $('conn-status').style.color = "#f0b232"; }
    if (!Object.keys(connections).length) $('searching-container').style.display = 'flex';
}

$('cam-btn').onclick = async () => {
    if (camStream) {
        camStream.getTracks().forEach(t => t.stop()); Object.values(camCalls).forEach(c => c.close());
        camCalls = {}; camStream = null; $('cam-btn').classList.remove('active'); $('video-me-cam')?.remove(); return;
    }
    try {
        camStream = await navigator.mediaDevices.getUserMedia({ 
            video: { width: { ideal: 640 }, height: { ideal: 480 }, frameRate: { ideal: 30 } } 
        });
        const camTrack = camStream.getVideoTracks()[0];
        if (camTrack) camTrack.contentHint = 'fluid';
        
        $('cam-btn').classList.add('active'); addVideoElement('me-cam', camStream, true);
        Object.keys(connections).forEach(id => {
            camCalls[id] = peer.call(id, camStream, { metadata: { type: 'webcam' }, sdpTransform: mungeSDP });
            applyBitrateLimit(camCalls[id], 500000);
        });
    } catch (err) { console.error(err); }
};

$('screen-btn').onclick = async () => {
    if (screenStream) {
        screenStream.getTracks().forEach(t => t.stop()); Object.values(screenCalls).forEach(c => c.close());
        screenCalls = {}; screenStream = null; $('screen-btn').classList.remove('active'); $('video-me')?.remove(); return;
    }
    try {
        screenStream = await navigator.mediaDevices.getDisplayMedia({ 
            video: { frameRate: { ideal: 15, max: 30 } }, 
            audio: true 
        });
        const screenTrack = screenStream.getVideoTracks()[0];
        if (screenTrack) screenTrack.contentHint = 'detail';
        
        $('screen-btn').classList.add('active'); addVideoElement('me', screenStream, true);
        screenStream.getVideoTracks()[0].onended = $('screen-btn').onclick;
        Object.keys(connections).forEach(id => {
            screenCalls[id] = peer.call(id, screenStream, { metadata: { type: 'screenshare' }, sdpTransform: mungeSDP });
            applyBitrateLimit(screenCalls[id], 1000000);
        });
    } catch (err) {}
};

function addVideoElement(id, stream, isLocal) {
    if ($(`video-${id}`)) return;
    const v = document.createElement('video');
    v.id = `video-${id}`; 
    v.className = 'screen-video'; 
    v.srcObject = stream; 
    v.autoplay = true; 
    v.playsInline = true;
    v.title = "Click to fullscreen";
    if (isLocal) v.muted = true;
    v.onclick = () => v.requestFullscreen?.();
    v.onpause = () => v.play();
    $('video-grid').appendChild(v);
}

const bcast = d => {
    if (d.type && d.type.startsWith('file-')) {
        Object.values(fileConns).forEach(c => c.open && c.send(d));
    } else {
        Object.values(connections).forEach(c => c.open && c.send(d));
    }
};

$('send-btn').onclick = () => { 
    const t = $('msg-input').value; 
    if(!t||!Object.keys(connections).length) return; 
    
    if (amITyping) { amITyping = false; clearTimeout(typingTimeout); bcast({ type: 'typing', state: false }); }
    
    bcast({type:'text',value:t}); 
    addMessage(linkify(escapeHTML(t)), "You", 'mine'); 
    $('msg-input').value = ""; 
};
$('msg-input').addEventListener('keypress', e => { if (e.key === 'Enter') $('send-btn').click(); });

$('msg-input').addEventListener('input', () => {
    if (!amITyping && $('msg-input').value.trim() !== "") {
        amITyping = true;
        bcast({ type: 'typing', state: true });
    }
    clearTimeout(typingTimeout);
    typingTimeout = setTimeout(() => {
        if (amITyping) {
            amITyping = false;
            bcast({ type: 'typing', state: false });
        }
    }, 500); 
});

function updateTypingUI() {
    const ind = $('typing-indicator');
    if (typingUsers.size === 0) {
        ind.classList.remove('active');
        ind.innerText = "";
    } else {
        ind.classList.add('active');
        const arr = Array.from(typingUsers);
        if (arr.length === 1) ind.innerText = `${arr[0]} is typing...`;
        else if (arr.length === 2) ind.innerText = `${arr[0]} and ${arr[1]} are typing...`;
        else ind.innerText = `Several people are typing...`;
    }
}

let dragCounter = 0;
const dropOverlay = $('drop-overlay');

document.addEventListener('dragenter', e => {
    if ($('login-screen').style.display !== 'none') return;
    e.preventDefault();
    dragCounter++;
    dropOverlay.style.display = 'flex';
});

document.addEventListener('dragover', e => {
    if ($('login-screen').style.display !== 'none') return;
    e.preventDefault();
});

document.addEventListener('dragleave', () => {
    if ($('login-screen').style.display !== 'none') return;
    dragCounter--;
    if (dragCounter === 0) dropOverlay.style.display = 'none';
});

document.addEventListener('drop', async e => {
    if ($('login-screen').style.display !== 'none') return;
    e.preventDefault();
    dragCounter = 0;
    dropOverlay.style.display = 'none';

    if (e.dataTransfer.files && e.dataTransfer.files.length > 0) {
        const file = e.dataTransfer.files[0];
        
        if (file.type.startsWith('audio/')) {
            if (Object.keys(connections).length === 0) {
                return addSystemMsg("❌ No one is in the room to hear sounds!");
            }
            addSystemMsg(`Playing <b>${file.name}</b> to the room...`);
            const buffer = await file.arrayBuffer();
            playCustomSound(buffer, file.type, null);
            const url = URL.createObjectURL(new Blob([buffer], { type: file.type }));
            addMessage(`<audio src="${url}" controls></audio><a href="${url}" download="${file.name}" class="chat-media-link">${dlIcon} Download Audio</a>`, "You", 'mine');
            bcast({ type: 'play-sound', buffer: buffer, mime: file.type, name: file.name });
        } else {
            sendFile(file);
        }
    }
});

async function sendFile(file) {
    if (!file) return;
    if (Object.keys(connections).length === 0) {
        return addSystemMsg("❌ No one is in the room to receive files!");
    }
    if (file.size > MAX_FILE_SIZE) {
        return addSystemMsg(`❌ File too large (max ${Math.round(MAX_FILE_SIZE/1024/1024)}MB)`);
    }
    const filename = file.name || `Pasted Media - ${new Date().toLocaleTimeString()}`;
    const txId = 'tx-' + Date.now() + '-' + Math.floor(Math.random() * 1000000);
    const totalChunks = Math.ceil(file.size / CHUNK_SIZE);
    const activePeerIds = Object.keys(fileConns).filter(pid => fileConns[pid] && fileConns[pid].open);
    if (activePeerIds.length === 0) {
        return addSystemMsg("❌ No file connections available!");
    }

    const progHtml = `
    <div>📤 Preparing <b>${filename}</b> (${(file.size / 1024 / 1024).toFixed(1)} MB)...</div>
    <div class="progress-container"><div class="progress-bar" id="bar-${txId}"></div></div>
    <div style="margin-top: 8px; display: flex; gap: 8px;">
        <button class="tx-btn" id="pause-${txId}" onclick="window.toggleTx('${txId}')">⏸️ Pause</button>
        <button class="tx-btn tx-btn-danger" onclick="window.cancelTx('${txId}')">❌ Cancel</button>
    </div>`;
    addMessage(progHtml, "You", 'mine', `msg-${txId}`);
    const bar = $(`bar-${txId}`);

    const tx = {
        txId, filename, totalChunks, fileSize: file.size,
        file, _buf: null,
        chunkHashes: new Array(totalChunks),
        fileHash: null,
        peerAcks: {},
        _inFlight: new Set(),
        _retry: new Uint8Array(totalChunks),
        _sentTime: new Array(totalChunks),
        _retxQ: new Set(),
        _timers: new Map(),
        completedPeers: new Set(),
        paused: false, canceled: false, completed: false,
        _waker: null, lastAckTime: Date.now()
    };
    for (const pid of activePeerIds) tx.peerAcks[pid] = new BitSet(totalChunks);
    senderTransfers[txId] = tx;

    // Read file + pre-compute hashes
    let fileBuffer;
    try { fileBuffer = await file.arrayBuffer(); } catch (e) { cleanupSenderTx(txId); return; }
    tx._buf = fileBuffer;

    const hashBatchSz = 20;
    for (let s = 0; s < totalChunks; s += hashBatchSz) {
        const e = Math.min(s + hashBatchSz, totalChunks);
        const ps = [];
        for (let i = s; i < e; i++) {
            const off = i * CHUNK_SIZE;
            ps.push(computeHash(fileBuffer.slice(off, off + CHUNK_SIZE)).then(h => { tx.chunkHashes[i] = h; }));
        }
        await Promise.all(ps);
        if (tx.canceled) { cleanupSenderTx(txId); return; }
    }
    tx.fileHash = await computeHash(fileBuffer);
    if (tx.canceled) { cleanupSenderTx(txId); return; }

    bcast({ type: 'file-meta', txId, name: filename, fileType: file.type, size: file.size, totalChunks, chunkHashes: tx.chunkHashes, fileHash: tx.fileHash });

    let nextIdx = 0;

    const allAcked = () => {
        const pids = Object.keys(tx.peerAcks);
        if (!pids.length) return false;
        for (let i = 0; i < totalChunks; i++) {
            for (const pid of pids) { if (!tx.peerAcks[pid].has(i)) return false; }
        }
        return true;
    };

    const sendOne = (idx) => {
        const start = idx * CHUNK_SIZE;
        const end = Math.min(start + CHUNK_SIZE, fileBuffer.byteLength);
        bcast({ type: 'file-chunk', txId, index: idx, data: fileBuffer.slice(start, end), hash: tx.chunkHashes[idx] });
        tx._inFlight.add(idx);
        tx._sentTime[idx] = Date.now();
        // If already has a timer, clear it
        if (tx._timers.has(idx)) { clearTimeout(tx._timers.get(idx)); }
        const t = setTimeout(() => {
            if (tx.canceled || tx.completed) return;
            if (!tx._inFlight.has(idx)) return;
            // Check if ALL peers have ACKed this chunk
            let allDone = true;
            for (const pid of Object.keys(tx.peerAcks)) { if (!tx.peerAcks[pid].has(idx)) { allDone = false; break; } }
            if (!allDone) {
                tx._retxQ.add(idx);
                if (tx._waker) { tx._waker(); tx._waker = null; }
            }
        }, RETRY_TIMEOUT);
        tx._timers.set(idx, t);
    };

    while (!tx.canceled && !tx.completed) {
        // Process retransmit queue
        if (tx._retxQ.size > 0) {
            const batch = Array.from(tx._retxQ);
            tx._retxQ.clear();
            for (const idx of batch) {
                tx._retry[idx]++;
                if (tx._retry[idx] > MAX_RETRIES) {
                    tx.canceled = true;
                    const mn = $(`msg-${txId}`);
                    if (mn) mn.innerHTML = `<div class="msg-info">You</div><div style="color: #da373c;">❌ Upload Failed: Max retries for chunk ${idx}</div>`;
                    cleanupSenderTx(txId); return;
                }
                sendOne(idx);
            }
        }

        // Fill send window
        while (tx._inFlight.size < WINDOW_SIZE && nextIdx < totalChunks && !tx.paused && !tx.canceled) {
            sendOne(nextIdx);
            nextIdx++;
        }

        // Update progress bar (based on chunks ACKed by ALL peers)
        if (bar) {
            let totalAcked = 0;
            const pids = Object.keys(tx.peerAcks);
            if (pids.length > 0) {
                for (let i = 0; i < totalChunks; i++) {
                    let allAcked = true;
                    for (const pid of pids) { if (!tx.peerAcks[pid].has(i)) { allAcked = false; break; } }
                    if (allAcked) totalAcked++;
                }
            }
            bar.style.width = `${totalChunks > 0 ? Math.min((totalAcked / totalChunks) * 100, 100) : 0}%`;
        }

        // Stall detection
        if (nextIdx >= totalChunks && tx._inFlight.size === 0 && !allAcked()) {
            if (Date.now() - tx.lastAckTime > STALL_TIMEOUT) {
                for (const pid of Object.keys(tx.peerAcks)) {
                    if (tx.peerAcks[pid].count() < totalChunks && fileConns[pid] && fileConns[pid].open) {
                        fileConns[pid].send({ type: 'file-status-req', txId });
                    }
                }
                tx.lastAckTime = Date.now();
            }
        }

        if (tx.completed || allAcked()) { tx.completed = true; break; }

        // Wait for waker or poll
        if (tx._inFlight.size > 0 || tx._retxQ.size > 0) {
            await new Promise(r => { tx._waker = r; });
        } else if (nextIdx >= totalChunks) {
            await new Promise(r => setTimeout(r, 100));
        } else {
            await new Promise(r => setTimeout(r, 50));
        }
    }

    if (tx.canceled) { cleanupSenderTx(txId); return; }

    // Clean up timers
    tx._timers.forEach(t => clearTimeout(t));
    tx._timers.clear();

    // Show completion UI immediately
    const msgNode = $(`msg-${txId}`);
    if (msgNode) msgNode.remove();

    const url = URL.createObjectURL(file);
    if (file.type.startsWith('image/')) {
        addMessage(`<img src="${url}"><a href="${url}" download="${filename}" class="chat-media-link">${dlIcon} Download Image</a>`, "You", 'mine');
    } else if (file.type.startsWith('video/')) {
        addMessage(`<video src="${url}" controls preload="metadata"></video><a href="${url}" download="${filename}" class="chat-media-link">${dlIcon} Download Video</a>`, "You", 'mine');
    } else if (file.type.startsWith('audio/')) {
        addMessage(`<audio src="${url}" controls></audio><a href="${url}" download="${filename}" class="chat-media-link">${dlIcon} Download Audio</a>`, "You", 'mine');
    } else {
        addMessage(`<div>📂 Shared: ${filename}</div><a href="${url}" download="${filename}" class="chat-media-link">${dlIcon} Download File</a>`, "You", 'mine');
    }

    setTimeout(() => cleanupSenderTx(txId), 5000);
}

$('file-input').onchange = () => {
    sendFile($('file-input').files[0]);
    $('file-input').value = "";
};

document.addEventListener('paste', (e) => {
    if (e.clipboardData && e.clipboardData.files.length > 0) {
        const file = e.clipboardData.files[0];
        if (file.type.startsWith('image/') || file.type.startsWith('video/')) {
            const ext = file.type.split('/')[1] || 'bin';
            const pastedFile = new File([file], `Pasted Media - ${new Date().toLocaleTimeString()}.${ext}`, { type: file.type });
            sendFile(pastedFile);
        }
    }
});

$('soundboard-input').onchange = async (e) => {
    const file = e.target.files[0];
    if (!file) return;
    
    waitingForKeyBind = { buffer: await file.arrayBuffer(), mime: file.type, name: file.name };
    addSystemMsg(`Press a <b>Numpad key (0-9)</b> to bind the sound <b>${file.name}</b>...`);
    e.target.value = "";
};

document.addEventListener('keydown', (e) => {
    if ($('login-screen').style.display !== 'none') return;
    
    if ((e.key === '*' && e.target.tagName !== 'INPUT') || e.code === 'NumpadMultiply') {
        for (let k in soundboard) delete soundboard[k];
        waitingForKeyBind = null;
        addSystemMsg("🧹 Cleared all Numpad sound bindings.");
        return;
    }

    const match = e.code.match(/^Numpad(\d)$/);
    if (!match) return;
    const num = match[1];

    if (waitingForKeyBind) {
        soundboard[num] = waitingForKeyBind;
        addSystemMsg(`🎵 Bound <b>${waitingForKeyBind.name}</b> to Numpad <b>${num}</b>.`);
        waitingForKeyBind = null;
        return;
    }

    if (soundboard[num]) {
        if (Object.keys(connections).length === 0) {
            return addSystemMsg("❌ No one is in the room to hear that!");
        }
        playCustomSound(soundboard[num].buffer, soundboard[num].mime, null);
        const url = URL.createObjectURL(new Blob([soundboard[num].buffer], { type: soundboard[num].mime }));
        addMessage(`<audio src="${url}" controls></audio><a href="${url}" download="${soundboard[num].name}" class="chat-media-link">${dlIcon} Download Audio</a>`, "You", 'mine');
        bcast({ type: 'play-sound', buffer: soundboard[num].buffer, mime: soundboard[num].mime, name: soundboard[num].name });
    }
});

function playCustomSound(buffer, mime, senderId) {
    try {
        const blob = new Blob([buffer], { type: mime });
        const url = URL.createObjectURL(blob);
        const audio = new Audio(url);
        
        if (senderId) {
            const volSlider = $(`vol-${senderId}`);
            if (volSlider) {
                audio.volume = parseFloat(volSlider.value);
            }
            
            const muteIcon = $(`mute-icon-${senderId}`);
            if (muteIcon && muteIcon.innerText === "🔇") {
                audio.muted = true;
            }

            if (!activeSounds[senderId]) activeSounds[senderId] = [];
            activeSounds[senderId].push(audio);
        }

        audio.play().catch(err => console.log("Sound play prevented:", err));
        audio.onended = () => {
            URL.revokeObjectURL(url); 
            if (senderId && activeSounds[senderId]) {
                activeSounds[senderId] = activeSounds[senderId].filter(a => a !== audio);
            }
        };
    } catch (err) {}
}


setInterval(() => {
    if (isHost) { const peers = Object.keys(connections); if(peers.length) bcast({ type: 'mesh-sync', peers }); }
    else if (!connections[ROOM_ID]) connectToPeer(ROOM_ID);
}, 3000);

setInterval(() => {
    bcast({ type: 'ping', time: Date.now() });
}, 1000);

setInterval(() => {
    const now = Date.now();
    Object.keys(connections).forEach(id => {
        const elapsed = now - (lastSeen[id] || now);
        
        if (elapsed > 10000) {
            removePeer(id);
        } else if (elapsed > 1000) {
            const basePing = lastRealPing[id] || 0;
            const simulatedPing = Math.floor(basePing + (elapsed - 1000));
            updatePingUI(id, simulatedPing);
        }
    });
}, 100);

function updatePingUI(id, lat) { 
    const p = $(`ping-${id}`); 
    const dot = $(`status-dot-${id}`);
    
    if(p){ 
        p.innerText = `${lat}ms`; 
        p.className = `ping-display ${lat<100?'ping-good':lat<300?'ping-med':'ping-bad'}`; 
    }
    if(dot && id !== 'me'){ 
        dot.className = `status-dot ${lat<100?'dot-good':lat<300?'dot-med':'dot-bad'}`;
    }
}

function enableChat() { $('msg-input').disabled = $('send-btn').disabled = false; }
$('logout-btn').onclick = () => { if(peer) peer.destroy(); location.reload(); };

function addMessage(html, user, type, msgId = null) { 
    const d = document.createElement('div'); 
    d.className = `msg ${type}`; 
    if (msgId) d.id = msgId;
    d.innerHTML = `<div class="msg-info">${user}</div><div>${html}</div>`; 
    $('messages').appendChild(d); 
    
    const scrollToBottom = () => $('messages').scrollTop = $('messages').scrollHeight;
    scrollToBottom(); 

    const medias = d.querySelectorAll('img, video, audio');
    medias.forEach(m => {
        m.onload = m.onloadedmetadata = scrollToBottom; 
    });
}

function addSystemMsg(txt) { 
    const d = document.createElement('div'); 
    d.style.cssText = "text-align:center;font-size:12px;font-weight:500;color:#949ba4;margin:10px 0"; 
    d.innerHTML = txt; 
    $('messages').appendChild(d);
    $('messages').scrollTop = $('messages').scrollHeight;
}

function addUserToSidebar(name, id) {
    if ($(`sidebar-${id}`)) { $(`name-${id}`).innerText = name; return; }
    const d = document.createElement('div'); d.className = 'user-item'; d.id = `sidebar-${id}`;
    
    let right = "";
    if (id === "me") {
        right = `<div style="display:flex;align-items:center;gap:5px;margin-right:8px"><span id="my-mic-toggle" style="font-size:14px;cursor:pointer;user-select:none;transition:0.2s;" title="Toggle Mic">🎤</span></div>`;
    } else {
        right = `<div style="display:flex;align-items:center;gap:5px;margin-right:8px"><span id="mute-icon-${id}" style="font-size:14px;opacity:0.8;cursor:pointer;user-select:none;transition:0.2s;" title="Mute/Unmute">🔊</span><input type="range" class="vol-slider" id="vol-${id}" min="0" max="1" step="0.05" value="1"></div><span id="ping-${id}" class="ping-display ping-med">-- ms</span>`;
    }

    d.innerHTML = `<div class="user-left"><div id="status-dot-${id}" class="status-dot dot-good"></div><span id="name-${id}" title="${name}${id==="me"?" (You)":""}">${name}${id==="me"?" (You)":""}</span></div><div style="display:flex;gap:8px;align-items:center;">${right}</div>`;
    $('user-list').appendChild(d);
    
    if (id === "me") {
        const myMicToggle = $('my-mic-toggle');
        if (!localStream) {
            myMicToggle.style.display = 'none'; 
        } else {
            myMicToggle.onclick = () => {
                isMuted = !isMuted;
                localStream.getAudioTracks()[0].enabled = !isMuted;
                myMicToggle.innerText = isMuted ? "🔇" : "🎤";
                myMicToggle.style.opacity = isMuted ? "0.5" : "1";
            };
        }
    } else {
        const muteIcon = $(`mute-icon-${id}`);
        const volSlider = $(`vol-${id}`);
        let isUserMuted = false;
        let previousVolume = 1;

        muteIcon.onclick = () => {
            isUserMuted = !isUserMuted;
            muteIcon.innerText = isUserMuted ? "🔇" : "🔊";
            muteIcon.style.opacity = isUserMuted ? "0.5" : "0.8";
            
            const a = $(`audio-${id}`);

            if (isUserMuted) {
                previousVolume = parseFloat(volSlider.value) > 0 ? parseFloat(volSlider.value) : 1;
                volSlider.value = 0;
                if (a) { a.muted = true; a.volume = 0; }
                if (activeSounds[id]) activeSounds[id].forEach(snd => { snd.muted = true; snd.volume = 0; });
            } else {
                volSlider.value = previousVolume;
                if (a) { a.muted = false; a.volume = previousVolume; }
                if (activeSounds[id]) activeSounds[id].forEach(snd => { snd.muted = false; snd.volume = previousVolume; });
            }
        };

        volSlider.addEventListener('input', e => { 
            const vol = parseFloat(e.target.value);
            const a = $(`audio-${id}`); 
            if(a) a.volume = vol; 
            
            if (activeSounds[id]) {
                activeSounds[id].forEach(snd => snd.volume = vol);
            }

            if (vol === 0 && !isUserMuted) {
                isUserMuted = true;
                muteIcon.innerText = "🔇";
                muteIcon.style.opacity = "0.5";
                if (a) a.muted = true;
                if (activeSounds[id]) activeSounds[id].forEach(snd => snd.muted = true);
            } 
            else if (isUserMuted && vol > 0) {
                isUserMuted = false;
                muteIcon.innerText = "🔊";
                muteIcon.style.opacity = "0.8";
                if (a) a.muted = false;
                if (activeSounds[id]) activeSounds[id].forEach(snd => snd.muted = false);
            }
        });
    }
}
