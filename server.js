'use strict';
const express = require('express');
const crypto = require('crypto');
const path = require('path');
const fs = require('fs');
const Database = require('better-sqlite3');
const rateLimit = require('express-rate-limit');

/* ------------------------------------------------------------------ */
/* Config                                                              */
/* ------------------------------------------------------------------ */
const PORT = process.env.PORT || 3000;
const APP_SECRET = process.env.APP_SECRET;
const DB_PATH = process.env.DB_PATH || path.join(__dirname, 'data.db');
const BASE_URL = (process.env.BASE_URL || '').replace(/\/+$/, '');
const BLOCK_BROWSERS = process.env.BLOCK_BROWSERS !== 'false';

if (!APP_SECRET || APP_SECRET.length < 24) {
  console.error('FATAL: set APP_SECRET (random string, min 24 characters).');
  process.exit(1);
}

class HttpError extends Error {
  constructor(status, message) { super(message); this.status = status; }
}

/* ------------------------------------------------------------------ */
/* Crypto helpers                                                      */
/* ------------------------------------------------------------------ */
const encKey = crypto.createHash('sha256').update('enc:' + APP_SECRET).digest();

function encrypt(text) {
  const iv = crypto.randomBytes(12);
  const c = crypto.createCipheriv('aes-256-gcm', encKey, iv);
  const ct = Buffer.concat([c.update(text, 'utf8'), c.final()]);
  return Buffer.concat([iv, c.getAuthTag(), ct]).toString('base64');
}
function decrypt(b64) {
  const buf = Buffer.from(b64, 'base64');
  const d = crypto.createDecipheriv('aes-256-gcm', encKey, buf.subarray(0, 12));
  d.setAuthTag(buf.subarray(12, 28));
  return Buffer.concat([d.update(buf.subarray(28)), d.final()]).toString('utf8');
}
const sha = (s) => crypto.createHash('sha256').update(String(s)).digest();
const safeEq = (a, b) => a.length === b.length && crypto.timingSafeEqual(a, b);

const KEY_ALPHABET = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // 32 chars, no lookalikes
function genKey() {
  const b = crypto.randomBytes(16);
  let s = '';
  for (let i = 0; i < 16; i++) {
    s += KEY_ALPHABET[b[i] % 32];
    if (i % 4 === 3 && i < 15) s += '-';
  }
  return s;
}
const genSlug = () => crypto.randomBytes(12).toString('base64url');
const genOwnerToken = () => crypto.randomBytes(24).toString('base64url');

/* ------------------------------------------------------------------ */
/* Database                                                            */
/* ------------------------------------------------------------------ */
fs.mkdirSync(path.dirname(path.resolve(DB_PATH)), { recursive: true });
const db = new Database(DB_PATH);
db.pragma('journal_mode = WAL');
db.pragma('foreign_keys = ON');

db.exec(`
CREATE TABLE IF NOT EXISTS scripts (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  slug TEXT UNIQUE NOT NULL,
  owner_hash TEXT NOT NULL,
  name TEXT NOT NULL,
  mode TEXT NOT NULL CHECK (mode IN ('keyed','nonkeyed')),
  code_enc TEXT NOT NULL,
  uses INTEGER NOT NULL DEFAULT 0,
  created_at INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS keys (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  script_id INTEGER NOT NULL REFERENCES scripts(id) ON DELETE CASCADE,
  key TEXT UNIQUE NOT NULL,
  note TEXT,
  duration INTEGER,
  max_hwids INTEGER NOT NULL DEFAULT 1,
  created_at INTEGER NOT NULL,
  activated_at INTEGER,
  expires_at INTEGER,
  uses INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS key_hwids (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  key_id INTEGER NOT NULL REFERENCES keys(id) ON DELETE CASCADE,
  hwid TEXT NOT NULL,
  ip TEXT,
  first_used INTEGER NOT NULL,
  last_used INTEGER NOT NULL,
  UNIQUE (key_id, hwid)
);
CREATE TABLE IF NOT EXISTS logs (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  script_id INTEGER,
  key_id INTEGER,
  key TEXT,
  hwid TEXT,
  ip TEXT,
  result TEXT NOT NULL,
  ts INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_keys_script ON keys(script_id);
CREATE INDEX IF NOT EXISTS idx_logs_script ON logs(script_id, id DESC);
`);

function pruneLogs() {
  db.prepare('DELETE FROM logs WHERE id < (SELECT COALESCE(MAX(id),0) - 100000 FROM logs)').run();
}
pruneLogs();
setInterval(pruneLogs, 3600 * 1000).unref();

const logStmt = db.prepare('INSERT INTO logs (script_id,key_id,key,hwid,ip,result,ts) VALUES (?,?,?,?,?,?,?)');
function logEvent(scriptId, keyId, key, hwid, ip, result) {
  logStmt.run(scriptId, keyId, key, hwid ? String(hwid).slice(0, 256) : null, ip || null, result, Date.now());
}

function keyStatus(k, hwidCount) {
  if (k.expires_at && k.expires_at <= Date.now()) return 'expired';
  if (hwidCount > 0) return 'used';
  return 'active';
}

function parseKeyOpts(o) {
  o = o || {};
  let duration = null;
  if (o.duration !== null && o.duration !== undefined && o.duration !== 'lifetime') {
    duration = Math.floor(Number(o.duration));
    if (!Number.isFinite(duration) || duration < 60 || duration > 315360000) {
      throw new HttpError(400, 'Invalid duration');
    }
  }
  const clamp = (v, lo, hi, d) => {
    const n = Math.floor(Number(v));
    return Number.isFinite(n) ? Math.min(hi, Math.max(lo, n)) : d;
  };
  return {
    duration,
    maxHwids: clamp(o.maxHwids, 1, 100, 1),
    count: clamp(o.count, 1, 100, 1),
    note: typeof o.note === 'string' ? o.note.slice(0, 100) : null,
  };
}

function createKeys(scriptId, opts) {
  const ins = db.prepare(
    'INSERT INTO keys (script_id,key,note,duration,max_hwids,created_at) VALUES (?,?,?,?,?,?)'
  );
  const out = [];
  for (let i = 0; i < opts.count; i++) {
    for (let attempt = 0; attempt < 5; attempt++) {
      const key = genKey();
      try {
        const info = ins.run(scriptId, key, opts.note, opts.duration, opts.maxHwids, Date.now());
        out.push({ id: Number(info.lastInsertRowid), key });
        break;
      } catch (e) {
        if (attempt === 4 || !String(e.message).includes('UNIQUE')) throw e;
      }
    }
  }
  return out;
}

function listKeys(scriptId) {
  const rows = db.prepare('SELECT * FROM keys WHERE script_id=? ORDER BY id DESC').all(scriptId);
  const hw = db.prepare('SELECT hwid,ip,first_used,last_used FROM key_hwids WHERE key_id=? ORDER BY id');
  return rows.map((k) => {
    const h = hw.all(k.id);
    return { ...k, hwids: h, status: keyStatus(k, h.length) };
  });
}

/* ------------------------------------------------------------------ */
/* App + middleware                                                    */
/* ------------------------------------------------------------------ */
const app = express();
app.set('trust proxy', 1);
app.disable('x-powered-by');
app.use((req, res, next) => {
  res.set({
    'X-Content-Type-Options': 'nosniff',
    'X-Frame-Options': 'DENY',
    'Referrer-Policy': 'no-referrer',
  });
  next();
});
app.use(express.json({ limit: '1mb' }));

const originOf = (req) => BASE_URL || `${req.protocol}://${req.get('host')}`;
const looksLikeBrowser = (req) => {
  const ua = req.get('user-agent') || '';
  return /mozilla/i.test(ua) && !/roblox/i.test(ua);
};
const luaWarn = (msg) => `warn(${JSON.stringify('[Loader] ' + msg)})`;

app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'index.html')));
app.get('/healthz', (req, res) => res.send('ok'));

/* ------------------------------------------------------------------ */
/* Public: raw loader + auth                                           */
/* ------------------------------------------------------------------ */
function buildStub(origin, slug) {
  return `-- Loadstring loader
local SLUG = ${JSON.stringify(slug)}
local AUTH_URL = ${JSON.stringify(origin + '/api/auth')}

local genv = (type(getgenv) == "function" and getgenv()) or _G
local key = genv.script_key or script_key
if type(key) ~= "string" or key == "" then
	warn('[Loader] No key set. Put script_key="YOUR_KEY"; before the loadstring.')
	return
end

local function fetchHwid()
	local ok, id = pcall(function()
		return game:GetService("RbxAnalyticsService"):GetClientId()
	end)
	if ok and type(id) == "string" and #id > 0 then return id end
	if type(gethwid) == "function" then
		local ok2, id2 = pcall(gethwid)
		if ok2 and id2 then return tostring(id2) end
	end
	return nil
end

local hwid = fetchHwid()
if not hwid then
	warn("[Loader] Could not read your HWID.")
	return
end

local req = (syn and syn.request) or (http and http.request) or http_request or request
if not req then
	warn("[Loader] Your executor does not support HTTP requests.")
	return
end

local HttpService = game:GetService("HttpService")
local ok, res = pcall(req, {
	Url = AUTH_URL,
	Method = "POST",
	Headers = { ["Content-Type"] = "application/json" },
	Body = HttpService:JSONEncode({ slug = SLUG, key = key, hwid = hwid }),
})
if not ok or not res then
	warn("[Loader] Request failed.")
	return
end
if res.StatusCode ~= 200 then
	warn("[Loader] " .. tostring(res.Body))
	return
end

local fn, err = loadstring(res.Body)
if not fn then
	warn("[Loader] " .. tostring(err))
	return
end
return fn()
`;
}

app.get('/raw/:slug', (req, res) => {
  res.set({ 'Cache-Control': 'no-store', 'Content-Type': 'text/plain; charset=utf-8' });
  const s = db.prepare('SELECT * FROM scripts WHERE slug=?').get(req.params.slug);
  if (!s) return res.status(404).send(luaWarn('Script not found.'));
  if (BLOCK_BROWSERS && looksLikeBrowser(req)) return res.status(403).send(luaWarn('Forbidden.'));

  if (s.mode === 'nonkeyed') {
    db.prepare('UPDATE scripts SET uses=uses+1 WHERE id=?').run(s.id);
    logEvent(s.id, null, null, null, req.ip, 'ok');
    return res.send(decrypt(s.code_enc));
  }
  res.send(buildStub(originOf(req), s.slug));
});

const authLimiter = rateLimit({ windowMs: 60 * 1000, limit: 60, standardHeaders: true, legacyHeaders: false });

app.post('/api/auth', authLimiter, (req, res) => {
  res.set('Cache-Control', 'no-store').type('text/plain');
  const { slug, key, hwid } = req.body || {};
  if (typeof slug !== 'string') return res.status(400).send('Bad request');
  const s = db.prepare('SELECT * FROM scripts WHERE slug=?').get(slug);
  if (!s) return res.status(404).send('Script not found');

  if (s.mode === 'nonkeyed') {
    db.prepare('UPDATE scripts SET uses=uses+1 WHERE id=?').run(s.id);
    logEvent(s.id, null, null, null, req.ip, 'ok');
    return res.send(decrypt(s.code_enc));
  }

  if (typeof key !== 'string' || !key.trim()) {
    logEvent(s.id, null, null, typeof hwid === 'string' ? hwid : null, req.ip, 'missing_key');
    return res.status(403).send('Missing key');
  }
  if (typeof hwid !== 'string' || hwid.length < 8 || hwid.length > 256) {
    logEvent(s.id, null, key.slice(0, 40), null, req.ip, 'bad_hwid');
    return res.status(400).send('Invalid HWID');
  }
  const keyStr = key.trim().toUpperCase().slice(0, 40);
  const k = db.prepare('SELECT * FROM keys WHERE key=? AND script_id=?').get(keyStr, s.id);
  if (!k) {
    logEvent(s.id, null, keyStr, hwid, req.ip, 'invalid_key');
    return res.status(403).send('Invalid key');
  }
  const now = Date.now();
  if (k.expires_at && k.expires_at <= now) {
    logEvent(s.id, k.id, k.key, hwid, req.ip, 'expired');
    return res.status(403).send('Key expired');
  }

  const result = db.transaction(() => {
    const bound = db.prepare('SELECT * FROM key_hwids WHERE key_id=?').all(k.id);
    const mine = bound.find((b) => b.hwid === hwid);
    if (mine) {
      db.prepare('UPDATE key_hwids SET last_used=?, ip=? WHERE id=?').run(now, req.ip, mine.id);
    } else if (bound.length < k.max_hwids) {
      db.prepare('INSERT INTO key_hwids (key_id,hwid,ip,first_used,last_used) VALUES (?,?,?,?,?)')
        .run(k.id, hwid, req.ip, now, now);
      if (!k.activated_at) {
        const exp = k.duration ? now + k.duration * 1000 : null;
        db.prepare('UPDATE keys SET activated_at=?, expires_at=? WHERE id=?').run(now, exp, k.id);
      }
    } else {
      return 'hwid_mismatch';
    }
    db.prepare('UPDATE keys SET uses=uses+1 WHERE id=?').run(k.id);
    db.prepare('UPDATE scripts SET uses=uses+1 WHERE id=?').run(s.id);
    return 'ok';
  })();

  logEvent(s.id, k.id, k.key, hwid, req.ip, result);
  if (result !== 'ok') return res.status(403).send('Key is locked to another device');
  res.send(decrypt(s.code_enc));
});

/* ------------------------------------------------------------------ */
/* Public: create a script (returns a private owner token)             */
/* ------------------------------------------------------------------ */
const createLimiter = rateLimit({
  windowMs: 60 * 60 * 1000, limit: 30, standardHeaders: true, legacyHeaders: false,
  message: { error: 'Too many scripts created from this network, try again later' },
});

const cleanName = (v) => {
  if (typeof v !== 'string' || !v.trim() || v.length > 100) throw new HttpError(400, 'Name must be 1-100 characters');
  return v.trim();
};
const cleanCode = (v) => {
  if (typeof v !== 'string' || !v.trim() || v.length > 800000) throw new HttpError(400, 'Script is empty or too large');
  return v;
};

app.post('/api/scripts', createLimiter, (req, res) => {
  const b = req.body || {};
  const name = cleanName(b.name);
  const code = cleanCode(b.code);
  if (b.mode !== 'keyed' && b.mode !== 'nonkeyed') throw new HttpError(400, 'Invalid mode');
  const opts = b.mode === 'keyed' ? parseKeyOpts(b.key) : null;
  const token = genOwnerToken();

  const out = db.transaction(() => {
    const slug = genSlug();
    const info = db.prepare('INSERT INTO scripts (slug,owner_hash,name,mode,code_enc,created_at) VALUES (?,?,?,?,?,?)')
      .run(slug, sha(token).toString('hex'), name, b.mode, encrypt(code), Date.now());
    const id = Number(info.lastInsertRowid);
    return { script: { id, slug, name, mode: b.mode }, keys: opts ? createKeys(id, opts) : [] };
  })();
  res.json({ ...out, token });
});

/* ------------------------------------------------------------------ */
/* Owner API: /api/s/:slug/*  (requires X-Owner-Token header)          */
/* ------------------------------------------------------------------ */
const ownerLimiter = rateLimit({ windowMs: 15 * 60 * 1000, limit: 600, standardHeaders: true, legacyHeaders: false });
const badTokenLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, limit: 20, standardHeaders: true, legacyHeaders: false,
  skipSuccessfulRequests: true, message: { error: 'Too many failed attempts, try again later' },
});

app.use('/api/s/:slug', ownerLimiter, badTokenLimiter, (req, res, next) => {
  const s = db.prepare('SELECT * FROM scripts WHERE slug=?').get(req.params.slug);
  const tok = req.get('x-owner-token');
  if (!s || typeof tok !== 'string' || !safeEq(sha(tok), Buffer.from(s.owner_hash, 'hex'))) {
    return res.status(401).json({ error: 'Invalid manage link' });
  }
  req.script = s;
  next();
});

const idParam = (v) => {
  const n = parseInt(v, 10);
  if (!Number.isInteger(n) || n < 1) throw new HttpError(400, 'Bad id');
  return n;
};
const getOwnKey = (req) => {
  const k = db.prepare('SELECT * FROM keys WHERE id=? AND script_id=?').get(idParam(req.params.kid), req.script.id);
  if (!k) throw new HttpError(404, 'Key not found');
  return k;
};

app.get('/api/s/:slug', (req, res) => {
  const s = req.script;
  res.json({
    id: s.id, slug: s.slug, name: s.name, mode: s.mode, uses: s.uses,
    created_at: s.created_at, code: decrypt(s.code_enc),
  });
});

app.put('/api/s/:slug', (req, res) => {
  const s = req.script;
  const b = req.body || {};
  const name = b.name !== undefined ? cleanName(b.name) : s.name;
  const code_enc = b.code !== undefined ? encrypt(cleanCode(b.code)) : s.code_enc;
  let mode = s.mode;
  if (b.mode !== undefined) {
    if (b.mode !== 'keyed' && b.mode !== 'nonkeyed') throw new HttpError(400, 'Invalid mode');
    mode = b.mode;
  }
  db.prepare('UPDATE scripts SET name=?, code_enc=?, mode=? WHERE id=?').run(name, code_enc, mode, s.id);
  res.json({ ok: true });
});

app.delete('/api/s/:slug', (req, res) => {
  db.prepare('DELETE FROM scripts WHERE id=?').run(req.script.id);
  res.json({ ok: true });
});

app.get('/api/s/:slug/keys', (req, res) => res.json(listKeys(req.script.id)));

app.post('/api/s/:slug/keys', (req, res) => {
  if (req.script.mode !== 'keyed') throw new HttpError(400, 'Script is not keyed');
  const opts = parseKeyOpts(req.body);
  const keys = db.transaction(() => createKeys(req.script.id, opts))();
  const s = req.script;
  res.json({ script: { id: s.id, slug: s.slug, name: s.name, mode: s.mode }, keys });
});

app.delete('/api/s/:slug/keys/:kid', (req, res) => {
  const k = getOwnKey(req);
  db.prepare('DELETE FROM keys WHERE id=?').run(k.id);
  res.json({ ok: true });
});

// Clears all HWIDs bound to the key. The expiry clock (if started) is NOT reset.
app.post('/api/s/:slug/keys/:kid/reset-hwid', (req, res) => {
  const k = getOwnKey(req);
  db.prepare('DELETE FROM key_hwids WHERE key_id=?').run(k.id);
  res.json({ ok: true });
});

// Replaces the key string with a fresh one and fully resets it (HWIDs, activation, expiry).
app.post('/api/s/:slug/keys/:kid/regenerate', (req, res) => {
  const k = getOwnKey(req);
  let newKey;
  db.transaction(() => {
    for (let attempt = 0; attempt < 5; attempt++) {
      newKey = genKey();
      try {
        db.prepare('UPDATE keys SET key=?, activated_at=NULL, expires_at=NULL, uses=0 WHERE id=?').run(newKey, k.id);
        break;
      } catch (e) {
        if (attempt === 4 || !String(e.message).includes('UNIQUE')) throw e;
      }
    }
    db.prepare('DELETE FROM key_hwids WHERE key_id=?').run(k.id);
  })();
  res.json({ key: newKey });
});

app.get('/api/s/:slug/logs', (req, res) => {
  const limit = Math.min(500, Math.max(1, parseInt(req.query.limit, 10) || 100));
  res.json(db.prepare('SELECT * FROM logs WHERE script_id=? ORDER BY id DESC LIMIT ?').all(req.script.id, limit));
});

/* ------------------------------------------------------------------ */
/* Errors                                                              */
/* ------------------------------------------------------------------ */
app.use((req, res) => res.status(404).json({ error: 'Not found' }));
app.use((err, req, res, next) => { // eslint-disable-line no-unused-vars
  if (err instanceof HttpError) return res.status(err.status).json({ error: err.message });
  if (err.type === 'entity.parse.failed') return res.status(400).json({ error: 'Bad JSON' });
  if (err.type === 'entity.too.large') return res.status(413).json({ error: 'Payload too large' });
  console.error(err);
  res.status(500).json({ error: 'Server error' });
});

app.listen(PORT, () => console.log(`Loadstring maker listening on :${PORT}`));
