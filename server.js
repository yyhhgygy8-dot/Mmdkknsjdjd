'use strict';
/*
 * WG Panel - پنل مدیریت وایرگارد
 * Zero-dependency Node.js backend (only optional dependency: "qrcode" for QR images)
 */
const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { execFile } = require('child_process');

let QRCode = null;
try { QRCode = require('qrcode'); } catch (e) { /* optional */ }

const VERSION = '1.0.0';
const ROOT = __dirname;
const PUBLIC_DIR = path.join(ROOT, 'public');
const PORT = parseInt(process.env.PORT || '3000', 10);
const HOST = process.env.HOST || '0.0.0.0';
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(ROOT, 'data'));
const WG_DIR = process.env.WG_DIR || '/etc/wireguard';
const TRUST_PROXY = process.env.TRUST_PROXY === '1';
const DB_FILE = path.join(DATA_DIR, 'db.json');
const STARTED_AT = Date.now();

fs.mkdirSync(DATA_DIR, { recursive: true, mode: 0o700 });

/* ------------------------------------------------------------------ utils */
class ApiError extends Error {
  constructor(status, msg) { super(msg); this.status = status; }
}

function run(cmd, args, opts) {
  return new Promise((resolve) => {
    execFile(cmd, args, Object.assign({ timeout: 25000 }, opts || {}), (err, stdout, stderr) => {
      resolve({ ok: !err, stdout: String(stdout || ''), stderr: String(stderr || ''), err });
    });
  });
}

function genKeyPair() {
  const { publicKey, privateKey } = crypto.generateKeyPairSync('x25519');
  const priv = privateKey.export({ format: 'der', type: 'pkcs8' }).subarray(-32);
  const pub = publicKey.export({ format: 'der', type: 'spki' }).subarray(-32);
  return { privateKey: priv.toString('base64'), publicKey: pub.toString('base64') };
}
function genPsk() { return crypto.randomBytes(32).toString('base64'); }

function ip2int(ip) {
  const p = ip.split('.').map(Number);
  return (((p[0] << 24) >>> 0) + (p[1] << 16) + (p[2] << 8) + p[3]) >>> 0;
}
function int2ip(n) { return [n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255].join('.'); }
function parseCidr(c) {
  const m = /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})\/(\d{1,2})$/.exec(String(c || '').trim());
  if (!m) return null;
  const oct = m.slice(1, 5).map(Number);
  if (oct.some((o) => o > 255)) return null;
  const bits = +m[5];
  if (bits < 16 || bits > 29) return null;
  const mask = (0xFFFFFFFF << (32 - bits)) >>> 0;
  const base = (ip2int(oct.join('.')) & mask) >>> 0;
  return { base, bits, mask, size: Math.pow(2, 32 - bits) };
}

function fmtEndpoint(h) { return h.includes(':') && !h.startsWith('[') ? '[' + h + ']' : h; }
function esc(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}
function fmtBytes(n) {
  n = Number(n) || 0;
  const u = ['B', 'KB', 'MB', 'GB', 'TB'];
  let i = 0;
  while (n >= 1024 && i < u.length - 1) { n /= 1024; i++; }
  return (i === 0 ? n.toFixed(0) : n.toFixed(2)) + ' ' + u[i];
}
function fmtDate(ts) {
  try { return new Date(ts).toLocaleDateString('fa-IR', { timeZone: 'Asia/Tehran' }); } catch (e) { return new Date(ts).toISOString().slice(0, 10); }
}

/* --------------------------------------------------------------- database */
const NAT_KEYS = ['listenPort', 'subnet', 'interface', 'extIface', 'mtu'];

function defaultSettings() {
  return {
    panelUrl: process.env.PANEL_URL || 'https://cloud.stackdome.com',
    endpoint: process.env.ENDPOINT || '',
    listenPort: 51820,
    interface: 'wg0',
    subnet: '10.66.66.0/24',
    dns: '1.1.1.1, 8.8.8.8',
    mtu: 1420,
    keepalive: 25,
    allowedIps: '0.0.0.0/0, ::/0',
    usePsk: true,
    extIface: '',
    defaultQuotaGB: 0,
    defaultExpiryDays: 0,
    monthlyReset: false,
  };
}

let db = null;
function loadDb() {
  let raw = null;
  for (const f of [DB_FILE, DB_FILE + '.bak']) {
    if (fs.existsSync(f)) {
      try { raw = JSON.parse(fs.readFileSync(f, 'utf8')); break; } catch (e) {
        console.error('[db] cannot parse ' + f + ': ' + e.message);
      }
    }
  }
  if (!raw && fs.existsSync(DB_FILE)) {
    console.error('[db] database is corrupted and no valid backup found. Refusing to start to avoid data loss.');
    process.exit(1);
  }
  db = raw || {};
  db.settings = Object.assign(defaultSettings(), db.settings || {});
  db.clients = Array.isArray(db.clients) ? db.clients : [];
  db.logs = Array.isArray(db.logs) ? db.logs : [];
  db.runtime = db.runtime || {};
  if (!db.secret) db.secret = crypto.randomBytes(32).toString('hex');
  if (!db.server) db.server = genKeyPair();
  if (!db.admin) {
    const pass = process.env.ADMIN_PASSWORD || crypto.randomBytes(9).toString('base64url');
    db.admin = makeAdmin(process.env.ADMIN_USER || 'admin', pass);
    try {
      fs.writeFileSync(path.join(DATA_DIR, 'initial-admin.txt'),
        'username: ' + db.admin.username + '\npassword: ' + pass + '\n', { mode: 0o600 });
    } catch (e) { /* ignore */ }
    console.log('[panel] Admin created -> username: ' + db.admin.username + '  password: ' + pass);
  }
  saveNow();
}
function makeAdmin(username, password) {
  const salt = crypto.randomBytes(16).toString('hex');
  const hash = crypto.scryptSync(password, salt, 64).toString('hex');
  return { username, salt, hash, pv: Date.now() };
}
function checkPassword(password) {
  const h = crypto.scryptSync(String(password), db.admin.salt, 64);
  const e = Buffer.from(db.admin.hash, 'hex');
  return h.length === e.length && crypto.timingSafeEqual(h, e);
}

let saveTimer = null;
let lastBackup = 0;
function saveNow() {
  if (saveTimer) { clearTimeout(saveTimer); saveTimer = null; }
  const tmp = DB_FILE + '.tmp';
  try {
    if (fs.existsSync(DB_FILE) && Date.now() - lastBackup > 10 * 60 * 1000) {
      fs.copyFileSync(DB_FILE, DB_FILE + '.bak');
      lastBackup = Date.now();
    }
    fs.writeFileSync(tmp, JSON.stringify(db), { mode: 0o600 });
    fs.renameSync(tmp, DB_FILE);
  } catch (e) { console.error('[db] save failed: ' + e.message); }
}
function save() { if (!saveTimer) saveTimer = setTimeout(saveNow, 400); }

function log(msg) {
  console.log('[panel] ' + msg);
  db.logs.unshift({ t: Date.now(), m: msg });
  if (db.logs.length > 300) db.logs.length = 300;
  save();
}

/* ------------------------------------------------------------- wireguard */
let HAS_WG = false;
const state = { wgUp: false, publicIpTried: false, lastError: '' };

async function detectSystem() {
  if (process.env.DRY_RUN === '1') { HAS_WG = false; return; }
  const r = await run('bash', ['-c', 'command -v wg && command -v wg-quick']);
  const root = typeof process.getuid === 'function' ? process.getuid() === 0 : false;
  HAS_WG = r.ok && root;
  if (!HAS_WG) console.warn('[panel] WireGuard tools not available or not root -> DRY-RUN mode (no system changes).');
}

async function detectExtIface() {
  if (!HAS_WG) return '';
  const r = await run('ip', ['-o', '-4', 'route', 'show', 'to', 'default']);
  const m = /dev\s+(\S+)/.exec(r.stdout);
  return m ? m[1] : '';
}

function fetchPublicIp() {
  return new Promise((resolve) => {
    const req = https.get('https://api.ipify.org', { timeout: 6000 }, (res) => {
      let d = '';
      res.on('data', (c) => { d += c; if (d.length > 100) req.destroy(); });
      res.on('end', () => resolve(/^[0-9.]{7,15}$/.test(d.trim()) ? d.trim() : ''));
    });
    req.on('timeout', () => { req.destroy(); resolve(''); });
    req.on('error', () => resolve(''));
  });
}

function confPath() { return path.join(WG_DIR, db.settings.interface + '.conf'); }

function buildServerConf() {
  const s = db.settings;
  const net = parseCidr(s.subnet);
  const lines = [
    '# Generated by WG Panel - do not edit by hand',
    '[Interface]',
    'Address = ' + int2ip(net.base + 1) + '/' + net.bits,
    'ListenPort = ' + s.listenPort,
    'PrivateKey = ' + db.server.privateKey,
  ];
  if (s.mtu) lines.push('MTU = ' + s.mtu);
  const ext = s.extIface || db.runtime.detectedExt || '';
  if (ext && /^[a-zA-Z0-9_.:-]{1,15}$/.test(ext)) {
    lines.push('PostUp = iptables -A FORWARD -i %i -j ACCEPT; iptables -A FORWARD -o %i -j ACCEPT; iptables -t nat -A POSTROUTING -o ' + ext + ' -j MASQUERADE');
    lines.push('PostDown = iptables -D FORWARD -i %i -j ACCEPT; iptables -D FORWARD -o %i -j ACCEPT; iptables -t nat -D POSTROUTING -o ' + ext + ' -j MASQUERADE');
  }
  for (const c of db.clients) {
    if (!c.enabled) continue;
    lines.push('', '# ' + String(c.name).replace(/[\r\n]/g, ' '), '[Peer]', 'PublicKey = ' + c.publicKey);
    if (c.presharedKey) lines.push('PresharedKey = ' + c.presharedKey);
    lines.push('AllowedIPs = ' + c.address + '/32');
  }
  return lines.join('\n') + '\n';
}

function writeServerConf() {
  if (!HAS_WG) return;
  fs.mkdirSync(WG_DIR, { recursive: true, mode: 0o700 });
  fs.writeFileSync(confPath(), buildServerConf(), { mode: 0o600 });
}

let applyQueue = Promise.resolve();
function applyConfig(full) {
  applyQueue = applyQueue.then(() => doApply(full)).catch((e) => {
    state.lastError = e.message;
    log('خطا در اعمال تنظیمات وایرگارد: ' + e.message);
  });
  return applyQueue;
}
async function doApply(full) {
  if (!HAS_WG) return;
  const ifc = db.settings.interface;
  const prev = db.runtime.appliedIface;
  const up = (await run('wg', ['show', ifc])).ok;
  if (full && up) await tick(true);               // capture counters before restart
  writeServerConf();
  if (full || !up) {
    if (prev && prev !== ifc) await run('wg-quick', ['down', prev]);
    if (up) await run('wg-quick', ['down', confPath()]);
    const r = await run('wg-quick', ['up', confPath()]);
    if (!r.ok) throw new Error((r.stderr || 'wg-quick up failed').trim().slice(0, 500));
    state.lastError = '';
    log('اینترفیس ' + ifc + ' بالا آمد');
  } else {
    const r = await run('bash', ['-c', 'wg syncconf "$0" <(wg-quick strip "$1")', ifc, confPath()]);
    if (!r.ok) throw new Error((r.stderr || 'wg syncconf failed').trim().slice(0, 500));
    state.lastError = '';
  }
  db.runtime.appliedIface = ifc;
  save();
}

/* --------------------------------------------------------------- clients */
function allocIp() {
  const net = parseCidr(db.settings.subnet);
  const used = new Set(db.clients.map((c) => c.address));
  for (let i = 2; i < net.size - 1; i++) {
    const ip = int2ip(net.base + i);
    if (!used.has(ip)) return ip;
  }
  return null;
}

function limitReason(c) {
  if (c.quotaBytes > 0 && c.usedRx + c.usedTx >= c.quotaBytes) return 'quota';
  if (c.expiresAt && Date.now() >= c.expiresAt) return 'expired';
  return null;
}

function makeClient(name, quotaGB, expiryDays, note) {
  const address = allocIp();
  if (!address) throw new ApiError(400, 'ظرفیت آدرس‌های شبکه پر شده است. زیرشبکه را بزرگ‌تر کنید.');
  const kp = genKeyPair();
  return {
    id: crypto.randomUUID(),
    name, note: note || '',
    privateKey: kp.privateKey, publicKey: kp.publicKey,
    presharedKey: db.settings.usePsk ? genPsk() : '',
    address, enabled: true, disabledReason: null,
    quotaBytes: Math.round(quotaGB * 1024 * 1024 * 1024),
    usedRx: 0, usedTx: 0, lastRx: 0, lastTx: 0,
    expiresAt: expiryDays > 0 ? Date.now() + expiryDays * 86400000 : null,
    createdAt: Date.now(), lastHandshake: 0, lastEndpoint: '',
    token: crypto.randomBytes(18).toString('base64url'),
  };
}

function clientConfig(c) {
  const s = db.settings;
  let ep = s.endpoint;
  if (!ep) { try { ep = new URL(s.panelUrl).hostname; } catch (e) { ep = ''; } }
  if (!ep) throw new ApiError(400, 'آدرس سرور (Endpoint) در تنظیمات مشخص نشده است.');
  const l = ['[Interface]', 'PrivateKey = ' + c.privateKey, 'Address = ' + c.address + '/32'];
  if (s.dns) l.push('DNS = ' + s.dns);
  if (s.mtu) l.push('MTU = ' + s.mtu);
  l.push('', '[Peer]', 'PublicKey = ' + db.server.publicKey);
  if (c.presharedKey) l.push('PresharedKey = ' + c.presharedKey);
  l.push('Endpoint = ' + fmtEndpoint(ep) + ':' + s.listenPort, 'AllowedIPs = ' + s.allowedIps);
  if (s.keepalive) l.push('PersistentKeepalive = ' + s.keepalive);
  return l.join('\n') + '\n';
}

function fileSlug(c) {
  let s = String(c.name).replace(/[^A-Za-z0-9_-]/g, '').slice(0, 15);
  if (!s) s = 'wg-' + c.address.split('.').pop();
  return s;
}

function isOnline(c) { return c.lastHandshake && Date.now() - c.lastHandshake < 180000; }

function clientView(c) {
  const used = c.usedRx + c.usedTx;
  return {
    id: c.id, name: c.name, note: c.note, address: c.address,
    enabled: c.enabled, disabledReason: c.disabledReason,
    quotaBytes: c.quotaBytes, usedRx: c.usedRx, usedTx: c.usedTx, used,
    expiresAt: c.expiresAt, createdAt: c.createdAt,
    lastHandshake: c.lastHandshake, lastEndpoint: c.lastEndpoint,
    online: !!isOnline(c), token: c.token,
  };
}

async function tick(noApply) {
  const now = Date.now();
  let changed = false;

  // monthly reset
  if (db.settings.monthlyReset) {
    const d = new Date();
    const key = d.getUTCFullYear() * 100 + d.getUTCMonth() + 1;
    if (db.runtime.lastResetMonth && db.runtime.lastResetMonth !== key) {
      for (const c of db.clients) {
        c.usedRx = 0; c.usedTx = 0;
        if (!c.enabled && c.disabledReason === 'quota' && !limitReason(c)) { c.enabled = true; c.disabledReason = null; }
      }
      log('ریست ماهانهٔ مصرف حجم انجام شد');
      changed = true;
    }
    if (db.runtime.lastResetMonth !== key) { db.runtime.lastResetMonth = key; changed = true; }
  }

  if (HAS_WG) {
    const r = await run('wg', ['show', db.settings.interface, 'dump']);
    state.wgUp = r.ok;
    if (r.ok) {
      const seen = new Set();
      const lines = r.stdout.trim().split('\n').slice(1);
      const byPub = new Map(db.clients.map((c) => [c.publicKey, c]));
      for (const ln of lines) {
        const f = ln.split('\t');
        if (f.length < 8) continue;
        const c = byPub.get(f[0]);
        if (!c) continue;
        seen.add(c.id);
        const rx = Number(f[5]) || 0, tx = Number(f[6]) || 0;
        c.usedRx += rx >= c.lastRx ? rx - c.lastRx : rx;
        c.usedTx += tx >= c.lastTx ? tx - c.lastTx : tx;
        c.lastRx = rx; c.lastTx = tx;
        const hs = (Number(f[4]) || 0) * 1000;
        if (hs) c.lastHandshake = hs;
        if (f[2] && f[2] !== '(none)') c.lastEndpoint = f[2];
      }
      for (const c of db.clients) if (!seen.has(c.id)) { c.lastRx = 0; c.lastTx = 0; }
      changed = true;
    }
  }

  // enforce limits
  let needApply = false;
  for (const c of db.clients) {
    if (!c.enabled) continue;
    const why = limitReason(c);
    if (why) {
      c.enabled = false; c.disabledReason = why; needApply = true; changed = true;
      log('کاربر «' + c.name + '» غیرفعال شد (' + (why === 'quota' ? 'اتمام حجم' : 'پایان اعتبار') + ')');
    }
  }
  if (changed) save();
  if (needApply && !noApply) await applyConfig(false);
  return now;
}

/* ------------------------------------------------------------------ auth */
function signToken(p) {
  const b = Buffer.from(JSON.stringify(p)).toString('base64url');
  const s = crypto.createHmac('sha256', db.secret).update(b).digest('base64url');
  return b + '.' + s;
}
function verifyToken(t) {
  if (!t || typeof t !== 'string') return null;
  const [b, s] = t.split('.');
  if (!b || !s) return null;
  const e = crypto.createHmac('sha256', db.secret).update(b).digest('base64url');
  const x = Buffer.from(s), y = Buffer.from(e);
  if (x.length !== y.length || !crypto.timingSafeEqual(x, y)) return null;
  try {
    const p = JSON.parse(Buffer.from(b, 'base64url').toString());
    if (!p.exp || p.exp < Date.now() || p.pv !== db.admin.pv) return null;
    return p;
  } catch (e2) { return null; }
}
function getCookie(req, name) {
  const h = req.headers.cookie || '';
  for (const part of h.split(';')) {
    const i = part.indexOf('=');
    if (i > 0 && part.slice(0, i).trim() === name) return decodeURIComponent(part.slice(i + 1).trim());
  }
  return '';
}
function clientIp(req) {
  if (TRUST_PROXY && req.headers['x-forwarded-for']) return String(req.headers['x-forwarded-for']).split(',')[0].trim();
  return req.socket.remoteAddress || '';
}
const attempts = new Map();
function checkRate(ip) {
  const a = attempts.get(ip);
  if (a && a.until > Date.now()) throw new ApiError(429, 'تلاش‌های ناموفق زیاد بود. چند دقیقه بعد دوباره امتحان کنید.');
}
function failAttempt(ip) {
  const a = attempts.get(ip) || { n: 0, until: 0 };
  a.n++;
  if (a.n >= 8) { a.until = Date.now() + 10 * 60 * 1000; a.n = 0; }
  attempts.set(ip, a);
}

/* --------------------------------------------------------------- routing */
const routes = [];
function route(method, pattern, handler, opts) {
  routes.push({ method, re: new RegExp('^' + pattern + '$'), handler, auth: !(opts && opts.auth === false) });
}

function findClient(id) {
  const c = db.clients.find((x) => x.id === id);
  if (!c) throw new ApiError(404, 'کاربر پیدا نشد.');
  return c;
}

function num(v, def, min, max, label) {
  if (v === undefined || v === null || v === '') return def;
  const n = Number(v);
  if (!isFinite(n) || n < min || n > max) throw new ApiError(400, 'مقدار نامعتبر: ' + label);
  return n;
}
function cleanName(v) {
  const s = String(v || '').replace(/[\r\n\t]/g, ' ').trim();
  if (!s || s.length > 40) throw new ApiError(400, 'نام باید بین ۱ تا ۴۰ نویسه باشد.');
  return s;
}

route('POST', '/api/login', async (ctx) => {
  checkRate(ctx.ip);
  const { username, password } = ctx.body || {};
  const okUser = typeof username === 'string' && username === db.admin.username;
  const okPass = typeof password === 'string' && checkPassword(password);
  if (!okUser || !okPass) { failAttempt(ctx.ip); throw new ApiError(401, 'نام کاربری یا رمز عبور اشتباه است.'); }
  attempts.delete(ctx.ip);
  const maxAge = 7 * 24 * 3600;
  const tok = signToken({ u: db.admin.username, pv: db.admin.pv, exp: Date.now() + maxAge * 1000 });
  const secure = ctx.req.headers['x-forwarded-proto'] === 'https' || ctx.req.socket.encrypted ? '; Secure' : '';
  ctx.res.setHeader('Set-Cookie', 'session=' + encodeURIComponent(tok) + '; HttpOnly; SameSite=Strict; Path=/; Max-Age=' + maxAge + secure);
  return { ok: true };
}, { auth: false });

route('POST', '/api/logout', async (ctx) => {
  ctx.res.setHeader('Set-Cookie', 'session=; HttpOnly; SameSite=Strict; Path=/; Max-Age=0');
  return { ok: true };
}, { auth: false });

route('GET', '/api/me', async (ctx) => ({ username: db.admin.username, version: VERSION }));

route('POST', '/api/account', async (ctx) => {
  const { oldPassword, newPassword, newUsername } = ctx.body || {};
  if (!checkPassword(oldPassword || '')) throw new ApiError(400, 'رمز فعلی اشتباه است.');
  const uname = String(newUsername || db.admin.username).trim();
  if (!/^[A-Za-z0-9_.-]{3,32}$/.test(uname)) throw new ApiError(400, 'نام کاربری فقط حروف انگلیسی/عدد و ۳ تا ۳۲ نویسه باشد.');
  const pass = newPassword ? String(newPassword) : String(oldPassword);
  if (newPassword && pass.length < 8) throw new ApiError(400, 'رمز جدید حداقل ۸ نویسه باشد.');
  db.admin = makeAdmin(uname, pass);
  try { fs.unlinkSync(path.join(DATA_DIR, 'initial-admin.txt')); } catch (e) { /* ignore */ }
  log('اطلاعات ورود مدیر تغییر کرد');
  saveNow();
  ctx.res.setHeader('Set-Cookie', 'session=; HttpOnly; SameSite=Strict; Path=/; Max-Age=0');
  return { ok: true };
});

route('GET', '/api/dashboard', async () => {
  const total = db.clients.length;
  const active = db.clients.filter((c) => c.enabled).length;
  const online = db.clients.filter(isOnline).length;
  const traffic = db.clients.reduce((a, c) => a + c.usedRx + c.usedTx, 0);
  return {
    total, active, disabled: total - active, online, traffic,
    hasWg: HAS_WG, wgUp: state.wgUp, lastError: state.lastError, hasQr: !!QRCode,
    serverPublicKey: db.server.publicKey, endpoint: db.settings.endpoint,
    port: db.settings.listenPort, iface: db.settings.interface,
    uptime: Math.floor((Date.now() - STARTED_AT) / 1000), version: VERSION,
    panelUrl: db.settings.panelUrl,
  };
});

route('GET', '/api/clients', async () => db.clients.map(clientView));

route('POST', '/api/clients', async (ctx) => {
  const b = ctx.body || {};
  const s = db.settings;
  const count = Math.floor(num(b.count, 1, 1, 100, 'تعداد'));
  const quotaGB = num(b.quotaGB, s.defaultQuotaGB, 0, 100000, 'حجم');
  const days = Math.floor(num(b.expiryDays, s.defaultExpiryDays, 0, 3650, 'مدت اعتبار'));
  const note = String(b.note || '').slice(0, 200);
  const base = cleanName(b.name);
  const created = [];
  for (let i = 0; i < count; i++) {
    const name = count > 1 ? base + '-' + (i + 1) : base;
    const c = makeClient(name, quotaGB, days, note);
    db.clients.push(c);
    created.push(c);
  }
  log(created.length + ' کاربر جدید ساخته شد: ' + base);
  saveNow();
  await applyConfig(false);
  return created.map(clientView);
});

route('PATCH', '/api/clients/([0-9a-f-]{36})', async (ctx) => {
  const c = findClient(ctx.params[0]);
  const b = ctx.body || {};
  if (b.name !== undefined) c.name = cleanName(b.name);
  if (b.note !== undefined) c.note = String(b.note).slice(0, 200);
  if (b.quotaGB !== undefined) c.quotaBytes = Math.round(num(b.quotaGB, 0, 0, 100000, 'حجم') * 1024 * 1024 * 1024);
  if (b.expiresAt !== undefined) {
    if (b.expiresAt === null || b.expiresAt === '') c.expiresAt = null;
    else {
      const t = Number(b.expiresAt);
      if (!isFinite(t) || t < 0) throw new ApiError(400, 'تاریخ نامعتبر است.');
      c.expiresAt = t;
    }
  }
  if (b.enabled !== undefined) {
    if (b.enabled) {
      const why = limitReason(c);
      if (why) throw new ApiError(400, why === 'quota' ? 'حجم این کاربر تمام شده؛ ابتدا حجم را افزایش دهید یا مصرف را ریست کنید.' : 'اعتبار این کاربر تمام شده؛ ابتدا تاریخ انقضا را تمدید کنید.');
      c.enabled = true; c.disabledReason = null;
    } else { c.enabled = false; c.disabledReason = 'manual'; }
  } else if (!c.enabled && (c.disabledReason === 'quota' || c.disabledReason === 'expired') && !limitReason(c)) {
    c.enabled = true; c.disabledReason = null;   // limit raised -> auto re-enable
  }
  saveNow();
  await applyConfig(false);
  return clientView(c);
});

route('POST', '/api/clients/([0-9a-f-]{36})/reset', async (ctx) => {
  const c = findClient(ctx.params[0]);
  c.usedRx = 0; c.usedTx = 0;
  if (!c.enabled && c.disabledReason === 'quota' && !limitReason(c)) { c.enabled = true; c.disabledReason = null; }
  log('مصرف «' + c.name + '» ریست شد');
  saveNow();
  await applyConfig(false);
  return clientView(c);
});

route('POST', '/api/clients/([0-9a-f-]{36})/regenerate', async (ctx) => {
  const c = findClient(ctx.params[0]);
  const kp = genKeyPair();
  c.privateKey = kp.privateKey; c.publicKey = kp.publicKey;
  c.presharedKey = db.settings.usePsk ? genPsk() : '';
  c.lastRx = 0; c.lastTx = 0; c.lastHandshake = 0;
  c.token = crypto.randomBytes(18).toString('base64url');
  log('کلیدهای «' + c.name + '» دوباره ساخته شد');
  saveNow();
  await applyConfig(false);
  return clientView(c);
});

route('DELETE', '/api/clients/([0-9a-f-]{36})', async (ctx) => {
  const c = findClient(ctx.params[0]);
  db.clients = db.clients.filter((x) => x !== c);
  log('کاربر «' + c.name + '» حذف شد');
  saveNow();
  await applyConfig(false);
  return { ok: true };
});

route('GET', '/api/clients/([0-9a-f-]{36})/config', async (ctx) => {
  const c = findClient(ctx.params[0]);
  sendConfig(ctx.res, c);
});
route('GET', '/api/clients/([0-9a-f-]{36})/text', async (ctx) => ({ config: clientConfig(findClient(ctx.params[0])) }));
route('GET', '/api/clients/([0-9a-f-]{36})/qr', async (ctx) => {
  const c = findClient(ctx.params[0]);
  const svg = await qrSvg(clientConfig(c));
  if (!svg) throw new ApiError(404, 'ماژول QR نصب نیست.');
  ctx.res.writeHead(200, { 'Content-Type': 'image/svg+xml', 'Cache-Control': 'no-store' });
  ctx.res.end(svg);
});

async function qrSvg(text) {
  if (!QRCode) return null;
  try { return await QRCode.toString(text, { type: 'svg', margin: 2, errorCorrectionLevel: 'L' }); } catch (e) { return null; }
}
function sendConfig(res, c) {
  const conf = clientConfig(c);
  res.writeHead(200, {
    'Content-Type': 'text/plain; charset=utf-8',
    'Content-Disposition': 'attachment; filename="' + fileSlug(c) + '.conf"',
    'Cache-Control': 'no-store',
  });
  res.end(conf);
}

/* settings */
route('GET', '/api/settings', async () => Object.assign({}, db.settings, { detectedExt: db.runtime.detectedExt || '' }));

route('PUT', '/api/settings', async (ctx) => {
  const b = ctx.body || {};
  const cur = db.settings;
  const n = Object.assign({}, cur);

  if (b.panelUrl !== undefined) {
    const u = String(b.panelUrl).trim().replace(/\/+$/, '');
    if (u && !/^https?:\/\/[A-Za-z0-9.\-:\[\]]+(\/[^\s]*)?$/.test(u)) throw new ApiError(400, 'آدرس پنل نامعتبر است (مثال: https://cloud.stackdome.com).');
    n.panelUrl = u;
  }
  if (b.endpoint !== undefined) {
    const e = String(b.endpoint).trim();
    if (e && !/^[A-Za-z0-9.\-:\[\]]{1,255}$/.test(e)) throw new ApiError(400, 'آدرس سرور (Endpoint) نامعتبر است.');
    n.endpoint = e;
  }
  if (b.listenPort !== undefined) n.listenPort = Math.floor(num(b.listenPort, cur.listenPort, 1, 65535, 'پورت'));
  if (b.interface !== undefined) {
    if (!/^[A-Za-z0-9_-]{1,15}$/.test(String(b.interface))) throw new ApiError(400, 'نام اینترفیس نامعتبر است.');
    n.interface = String(b.interface);
  }
  if (b.subnet !== undefined) {
    if (!parseCidr(b.subnet)) throw new ApiError(400, 'زیرشبکه نامعتبر است (مثال: 10.66.66.0/24، پیشوند بین ۱۶ تا ۲۹).');
    n.subnet = String(b.subnet).trim();
  }
  if (b.dns !== undefined) {
    const d = String(b.dns).trim();
    if (d && !/^[0-9a-fA-F:., ]{1,100}$/.test(d)) throw new ApiError(400, 'DNS نامعتبر است.');
    n.dns = d;
  }
  if (b.mtu !== undefined) n.mtu = Math.floor(num(b.mtu, cur.mtu, 576, 1500, 'MTU'));
  if (b.keepalive !== undefined) n.keepalive = Math.floor(num(b.keepalive, cur.keepalive, 0, 600, 'Keepalive'));
  if (b.allowedIps !== undefined) {
    const a = String(b.allowedIps).trim();
    if (!/^[0-9a-fA-F:./, ]{1,300}$/.test(a) || !a) throw new ApiError(400, 'AllowedIPs نامعتبر است.');
    n.allowedIps = a;
  }
  if (b.extIface !== undefined) {
    const x = String(b.extIface).trim();
    if (x && !/^[a-zA-Z0-9_.:-]{1,15}$/.test(x)) throw new ApiError(400, 'نام کارت شبکهٔ خروجی نامعتبر است.');
    n.extIface = x;
  }
  if (b.usePsk !== undefined) n.usePsk = !!b.usePsk;
  if (b.defaultQuotaGB !== undefined) n.defaultQuotaGB = num(b.defaultQuotaGB, 0, 0, 100000, 'حجم پیش‌فرض');
  if (b.defaultExpiryDays !== undefined) n.defaultExpiryDays = Math.floor(num(b.defaultExpiryDays, 0, 0, 3650, 'اعتبار پیش‌فرض'));
  if (b.monthlyReset !== undefined) n.monthlyReset = !!b.monthlyReset;

  let reassigned = false;
  if (n.subnet !== cur.subnet) {
    const net = parseCidr(n.subnet);
    if (db.clients.length > net.size - 3) throw new ApiError(400, 'زیرشبکهٔ جدید برای تعداد کاربران فعلی کوچک است.');
    db.settings = n;
    db.clients.forEach((c, i) => { c.address = int2ip(net.base + 2 + i); });
    reassigned = true;
  }
  const needsRestart = NAT_KEYS.some((k) => n[k] !== cur[k]);
  db.settings = n;
  log('تنظیمات ذخیره شد' + (reassigned ? ' (آدرس‌های کاربران بازتخصیص شد؛ کانفیگ‌ها را دوباره بگیرید)' : ''));
  saveNow();
  await applyConfig(needsRestart);
  return { ok: true, needsRestart, reassigned };
});

route('POST', '/api/server/restart', async () => {
  await applyConfig(true);
  if (state.lastError) throw new ApiError(500, state.lastError);
  return { ok: true };
});

route('POST', '/api/server/detect-ip', async () => {
  const ip = await fetchPublicIp();
  if (!ip) throw new ApiError(502, 'تشخیص IP عمومی ممکن نشد.');
  return { ip };
});

/* logs + backup */
route('GET', '/api/logs', async () => db.logs);
route('DELETE', '/api/logs', async () => { db.logs = []; save(); return { ok: true }; });

route('GET', '/api/backup', async (ctx) => {
  ctx.res.writeHead(200, {
    'Content-Type': 'application/json',
    'Content-Disposition': 'attachment; filename="wg-panel-backup-' + new Date().toISOString().slice(0, 10) + '.json"',
    'Cache-Control': 'no-store',
  });
  ctx.res.end(JSON.stringify({ format: 'wg-panel-backup', version: 1, settings: db.settings, server: db.server, clients: db.clients }, null, 2));
});

route('POST', '/api/restore', async (ctx) => {
  const b = ctx.body || {};
  if (b.format !== 'wg-panel-backup' || !b.server || !b.server.privateKey || !b.server.publicKey || !Array.isArray(b.clients)) {
    throw new ApiError(400, 'فایل پشتیبان معتبر نیست.');
  }
  const settings = Object.assign(defaultSettings(), b.settings || {});
  if (!parseCidr(settings.subnet)) throw new ApiError(400, 'زیرشبکهٔ فایل پشتیبان نامعتبر است.');
  for (const c of b.clients) {
    if (!c || typeof c.publicKey !== 'string' || typeof c.privateKey !== 'string' || !/^\d+\.\d+\.\d+\.\d+$/.test(c.address || '')) {
      throw new ApiError(400, 'اطلاعات کاربران در فایل پشتیبان معتبر نیست.');
    }
  }
  db.settings = settings;
  db.server = { privateKey: b.server.privateKey, publicKey: b.server.publicKey };
  db.clients = b.clients.map((c) => Object.assign({
    id: crypto.randomUUID(), name: 'client', note: '', presharedKey: '', enabled: true, disabledReason: null,
    quotaBytes: 0, usedRx: 0, usedTx: 0, lastRx: 0, lastTx: 0, expiresAt: null, createdAt: Date.now(),
    lastHandshake: 0, lastEndpoint: '', token: crypto.randomBytes(18).toString('base64url'),
  }, c, { lastRx: 0, lastTx: 0 }));
  log('پشتیبان بازیابی شد (' + db.clients.length + ' کاربر)');
  saveNow();
  await applyConfig(true);
  return { ok: true, count: db.clients.length };
});

/* public user page */
function findByToken(t) { return db.clients.find((c) => c.token === t); }

route('GET', '/c/([A-Za-z0-9_-]{20,40})', async (ctx) => {
  const c = findByToken(ctx.params[0]);
  if (!c) throw new ApiError(404, 'لینک نامعتبر است.');
  let conf = '';
  try { conf = clientConfig(c); } catch (e) { conf = ''; }
  const svg = conf ? await qrSvg(conf) : null;
  const used = c.usedRx + c.usedTx;
  const pct = c.quotaBytes > 0 ? Math.min(100, Math.round((used / c.quotaBytes) * 100)) : 0;
  let status = 'فعال', cls = 'ok';
  if (!c.enabled) { status = c.disabledReason === 'quota' ? 'اتمام حجم' : c.disabledReason === 'expired' ? 'منقضی شده' : 'غیرفعال'; cls = 'bad'; }
  const html = '<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">' +
    '<meta name="viewport" content="width=device-width,initial-scale=1"><meta name="robots" content="noindex">' +
    '<title>' + esc(c.name) + '</title><link rel="stylesheet" href="/style.css"></head><body class="userpage">' +
    '<main class="ucard"><h1>' + esc(c.name) + '</h1>' +
    '<p><span class="badge ' + cls + '">' + status + '</span></p>' +
    '<div class="bar"><i style="width:' + pct + '%"></i></div>' +
    '<p class="muted">مصرف: <b>' + fmtBytes(used) + '</b> از <b>' + (c.quotaBytes > 0 ? fmtBytes(c.quotaBytes) : 'نامحدود') + '</b></p>' +
    '<p class="muted">انقضا: <b>' + (c.expiresAt ? fmtDate(c.expiresAt) : 'نامحدود') + '</b></p>' +
    (svg ? '<div class="qr">' + svg + '</div>' : '') +
    (conf ? '<p><a class="btn primary" href="/c/' + esc(c.token) + '/config">دانلود فایل کانفیگ</a> ' +
      '<button class="btn" id="copybtn" type="button">کپی کانفیگ</button></p>' +
      '<pre id="conf" class="conf">' + esc(conf) + '</pre><script src="/user.js"></script>' : '<p class="muted">کانفیگ در دسترس نیست.</p>') +
    '</main></body></html>';
  ctx.res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
  ctx.res.end(html);
}, { auth: false });

route('GET', '/c/([A-Za-z0-9_-]{20,40})/config', async (ctx) => {
  const c = findByToken(ctx.params[0]);
  if (!c) throw new ApiError(404, 'لینک نامعتبر است.');
  sendConfig(ctx.res, c);
}, { auth: false });

/* ----------------------------------------------------------- http server */
const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'application/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.ico': 'image/x-icon',
};

function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', (c) => {
      size += c.length;
      if (size > 5 * 1024 * 1024) { reject(new ApiError(413, 'حجم درخواست زیاد است.')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => {
      if (!chunks.length) return resolve({});
      try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8'))); } catch (e) { reject(new ApiError(400, 'JSON نامعتبر است.')); }
    });
    req.on('error', reject);
  });
}

function sendJson(res, status, obj) {
  if (res.headersSent || res.writableEnded) return;
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}

function serveStatic(req, res, pathname) {
  let p = pathname === '/' ? '/index.html' : pathname;
  const full = path.normalize(path.join(PUBLIC_DIR, p));
  if (!full.startsWith(PUBLIC_DIR + path.sep) && full !== PUBLIC_DIR) return false;
  if (!fs.existsSync(full) || !fs.statSync(full).isFile()) return false;
  const ext = path.extname(full).toLowerCase();
  res.writeHead(200, { 'Content-Type': MIME[ext] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
  fs.createReadStream(full).pipe(res);
  return true;
}

const server = http.createServer(async (req, res) => {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('Referrer-Policy', 'no-referrer');
  res.setHeader('Content-Security-Policy', "default-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; script-src 'self'; frame-ancestors 'none'");
  try {
    const url = new URL(req.url, 'http://localhost');
    const pathname = decodeURIComponent(url.pathname);
    const method = req.method;

    if (method === 'GET' || method === 'HEAD') {
      const isApi = pathname.startsWith('/api/') || pathname.startsWith('/c/');
      if (!isApi && serveStatic(req, res, pathname)) return;
    }

    let matched = null, params = [];
    for (const r of routes) {
      if (r.method !== method) continue;
      const m = r.re.exec(pathname);
      if (m) { matched = r; params = m.slice(1); break; }
    }
    if (!matched) {
      if (pathname.startsWith('/api/')) throw new ApiError(404, 'مسیر پیدا نشد.');
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('Not found');
    }

    if (method !== 'GET' && req.headers['x-requested-with'] !== 'panel') throw new ApiError(403, 'درخواست نامعتبر.');
    let user = null;
    if (matched.auth) {
      user = verifyToken(getCookie(req, 'session'));
      if (!user) throw new ApiError(401, 'نیاز به ورود دارید.');
    }
    const body = method === 'GET' || method === 'HEAD' ? {} : await readBody(req);
    const ctx = { req, res, url, params, body, ip: clientIp(req), user };
    const result = await matched.handler(ctx);
    if (!res.headersSent && !res.writableEnded) sendJson(res, 200, result === undefined ? { ok: true } : result);
  } catch (e) {
    const status = e instanceof ApiError ? e.status : 500;
    if (!(e instanceof ApiError)) console.error('[error]', e);
    const wantsHtml = /^\/c\//.test(req.url) && req.method === 'GET';
    if (wantsHtml && !res.headersSent) {
      res.writeHead(status, { 'Content-Type': 'text/html; charset=utf-8' });
      return res.end('<!doctype html><meta charset="utf-8"><body style="font-family:sans-serif;text-align:center;padding:3rem" dir="rtl">' + esc(e.message) + '</body>');
    }
    sendJson(res, status, { error: e instanceof ApiError ? e.message : 'خطای داخلی سرور' });
  }
});

/* ------------------------------------------------------------------ boot */
async function main() {
  loadDb();
  await detectSystem();
  if (HAS_WG) db.runtime.detectedExt = await detectExtIface();
  if (!db.settings.endpoint) {
    const ip = await fetchPublicIp();
    if (ip) { db.settings.endpoint = ip; log('آدرس سرور به‌صورت خودکار تنظیم شد: ' + ip); }
  }
  saveNow();
  await applyConfig(false);
  await tick();
  setInterval(() => { tick().catch((e) => console.error('[tick]', e.message)); }, 10000);

  server.listen(PORT, HOST, () => console.log('[panel] WG Panel v' + VERSION + ' listening on http://' + HOST + ':' + PORT + (HAS_WG ? '' : '  (DRY-RUN)')));
  const stop = () => { saveNow(); server.close(); process.exit(0); };
  process.on('SIGTERM', stop);
  process.on('SIGINT', stop);
}

process.on('unhandledRejection', (e) => console.error('[unhandled]', e));
main().catch((e) => { console.error(e); process.exit(1); });
