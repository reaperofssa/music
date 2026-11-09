require('dotenv').config();
const { Telegraf, Markup } = require('telegraf');
const { MongoClient } = require('mongodb');
const crypto = require('crypto');
const path = require('path');
const fs = require('fs'), fsp = fs.promises;
const express = require('express');
const cors = require('cors');

const { BOT_TOKEN, MONGO_URI, HF_TOKEN, HF_USERNAME, HF_BACKUP_ACCOUNTS = '' } = process.env;
const APP_URL = (process.env.APP_URL || 'https://music-production-5aeb.up.railway.app').replace(/\/+$/, ''); // public url of this service (mini app, short links)
const SHORT_URL_BASE = (process.env.SHORT_URL_BASE ?? APP_URL).replace(/\/+$/, '') + '/'; // short-link prefix stored in mongo (song audio, covers, posters, profile images)
const UPLOADER_DB = process.env.UPLOADER_DB || 'xcatbox_clone'; // same db the python uploader / short-url service uses
const MAX_DATASET_SIZE = 12 * 1024 ** 3;   // 12GB per dataset
const MAX_ACCOUNT_STORAGE = 150 * 1024 ** 3; // 150GB per account
const DEST_DIR = 'uploads';
// files are staged on Railway first (serve from there), then pushed to Hugging Face BATCH_SIZE at a time as ONE commit.
// STAGE_DIR must be a Railway volume mount (e.g. /data/stage) or staged files are lost on redeploy.
const BATCH_SIZE = Number(process.env.BATCH_SIZE || 10);
const BATCH_MAX_AGE_MS = Number(process.env.BATCH_MAX_AGE_MIN || 10) * 60000;   // flush a partial batch after this long so nothing waits forever
let STAGE_DIR = path.resolve(process.env.STAGE_DIR || '/data/stage');
try { fs.mkdirSync(STAGE_DIR, { recursive: true }); } catch (e) { STAGE_DIR = path.resolve('stage'); fs.mkdirSync(STAGE_DIR, { recursive: true }); console.warn('[stage] could not use STAGE_DIR, falling back to', STAGE_DIR); }
const log = (...a) => console.log(`[${new Date().toISOString()}] [audio]`, ...a);
const who = u => u ? `${u.id}${u.username ? ' @' + u.username : ''}` : '?';
const mb = n => n ? (n / 1048576).toFixed(2) + 'MB' : '?';
const bot = new Telegraf(BOT_TOKEN);
let users, songs, queues, capsules, capSongs, jobs, imports, importItems, mm, hub, hfFiles, hfSettings, stagedFiles, nowp, lhours;
const HOUR = 3600 * 1000;
const DEFAULT_BOT_USERNAME = 'playIistsbot';   // used for Mini App links until the bot reports its own username

// ---------- poster (Deezer) ----------
const L = '\\p{L}\\p{M}\\p{N}';
const norm = s => (s || '').toLowerCase()
  .normalize('NFKD').replace(/[\u0300-\u036f]/g, '')
  .replace(/\(.*?\)|\[.*?\]/g, ' ')            // drop (feat. x), [Remastered]
  .replace(/\b(feat|ft|featuring)\b\.?/g, ' ')
  .replace(new RegExp(`[^${L}]+`, 'gu'), ' ')
  .trim();

const has = (hay, tok) => new RegExp(`(?<![${L}])${tok}(?![${L}])`, 'u').test(hay);
const toks = s => norm(s).split(' ').filter(Boolean);

// versions we don't want unless the song itself is one (tested on the raw title, brackets included)
const BAD = /\b(cover|remix|slowed|reverb|sped up|speed up|nightcore|8d|karaoke|instrumental|mashup|bass boosted|live)\b/;

// pure function: picks the best matching Deezer track or null
function pickMatch(tracks, { title, artist, duration }) {
  const tTok = toks(title);
  const aTok = toks(String(artist || '').split(/,|&|;|\/|\bfeat\b|\bft\b|\bx\b/i)[0]); // primary artist only
  if (!tTok.length) return null;
  const wantBad = BAD.test(String(title).toLowerCase());

  const picks = [];
  tracks.slice(0, 10).forEach((v, rank) => {
    const full = `${v.title || ''} ${v.title_version || ''}`;
    const vt = norm(full);
    const va = norm(v.artist?.name);
    const hay = `${vt} ${va}`;

    if (tTok.filter(k => has(hay, k)).length < Math.ceil(tTok.length * 0.8)) return;   // title words
    if (aTok.length && !aTok.every(k => has(hay, k))) return;                          // artist words
    if (BAD.test(full.toLowerCase()) && !wantBad) return;                              // wrong version
    if (!aTok.length && !(duration && v.duration)) return;                             // no artist -> need duration
    const diff = duration && v.duration ? Math.abs(v.duration - duration) : 0;
    if (diff > Math.max(10, duration * 0.05)) return;                                  // duration check

    picks.push({ v, rank, diff });
  });

  picks.sort((a, b) => a.diff - b.diff || a.rank - b.rank); // closest duration, then Deezer rank
  return picks[0]?.v || null;
}

async function fetchCover(album) {
  for (const u of [album?.cover_xl, album?.cover_big]) { // 1000x1000, then 500x500
    if (!u || u.includes('/cover//')) continue;          // Deezer's empty-cover placeholder
    try {
      const r = await ft(u);
      if (!r.ok) continue;
      const buf = Buffer.from(await r.arrayBuffer());
      if (buf.length > 3000) return buf;
    } catch {}
  }
  return null;
}

const sleep = ms => new Promise(r => setTimeout(r, ms));
const ft = (u, ms = 30000) => fetch(u, { signal: AbortSignal.timeout(ms) });   // fetch that gives up instead of hanging forever

// genres / release date / label live on the album endpoint (search results don't carry them)
async function fetchAlbumMeta(albumId) {
  if (!albumId) return {};
  try {
    const r = await ft(`https://api.deezer.com/album/${albumId}`);
    if (!r.ok) return {};
    const a = await r.json();
    if (a.error) return a.error.code === 4 ? { rateLimited: true } : {};
    return {
      genres: (a.genres?.data || []).map(g => g.name).filter(Boolean),
      releaseDate: a.release_date && a.release_date !== '0000-00-00' ? a.release_date : null,
      label: a.label || null,
    };
  } catch { return {}; }
}

// returns { buf (may be null), deezerId, album, explicit, genres, releaseDate, label } or null
async function findPoster({ title, artist, duration }) {
  if (!title) return null;
  const stripBr = x => String(x || '').replace(/\(.*?\)|\[.*?\]/g, ' ').replace(/\s+/g, ' ').trim();
  const q = encodeURIComponent(`${stripBr(title)} ${artist || ''}`.trim());
  const r = await ft(`https://api.deezer.com/search?q=${q}&limit=10`);
  if (!r.ok) return null;
  const { data = [] } = await r.json();
  const v = pickMatch(data, { title, artist, duration });
  if (!v) return null;
  const [buf, meta] = await Promise.all([fetchCover(v.album), fetchAlbumMeta(v.album?.id)]);
  return { buf, deezerId: v.id, album: v.album?.title || null, explicit: v.explicit_lyrics ?? null, ...meta };
}

// YouTube-style uploads put the channel in "artist" and "Artist - Title (Official Video)" in the title,
// so try: parsed from title -> as tagged -> title only (duration must then match)
async function findPosterSmart({ title, artist, duration }) {
  let fallback = null;
  const m = String(title || '').match(/^(.+?)\s+[-–—]\s+(.+)$/);
  const attempts = [];
  if (m) attempts.push({ title: m[2], artist: m[1], why: 'parsed "Artist - Title"' });
  attempts.push({ title, artist, why: 'as tagged' });
  attempts.push({ title: m ? m[2] : title, artist: null, why: 'title + duration only' });
  for (const t of attempts) {
    const p = await findPoster({ title: t.title, artist: t.artist, duration });
    log(`poster attempt (${t.why}) title="${t.title}" artist="${t.artist || ''}" -> ${p ? 'match deezer=' + p.deezerId + (p.buf ? '' : ' (no cover)') : 'no match'}`);
    if (p?.buf) return p;
    if (p && !fallback) fallback = p; // matched but no cover: keep the metadata, keep trying for a cover
  }
  return fallback;
}

// copies Deezer metadata onto a song object without overwriting what the file's own tags already gave us
function applyDeezerMeta(song, p) {
  song.deezer_id = p.deezerId;
  if (!song.album) song.album = p.album;
  const hasGenre = Array.isArray(song.genre) ? song.genre.length : song.genre;
  if (!hasGenre && p.genres?.length) song.genre = p.genres;
  if (p.releaseDate) {
    song.release_date = p.releaseDate;
    if (!song.year) song.year = Number(p.releaseDate.slice(0, 4)) || null;
  }
  if (p.label) song.label = p.label;
  if (p.explicit != null) song.explicit = !!p.explicit;
  song.deezer_meta = !p.rateLimited;
}

// one-off: fill genre / release date / label for songs saved before this existed (run with BACKFILL_DEEZER=1)
async function backfillDeezer() {
  const cur = songs.find({ deezer_id: { $ne: null }, deezer_meta: { $ne: true } }).project({ deezer_id: 1, album: 1, genre: 1, year: 1 });
  let done = 0, miss = 0;
  for await (const s of cur) {
    for (let attempt = 0; attempt < 3; attempt++) {
      let meta = {}, explicit = null;
      try {
        const r = await ft(`https://api.deezer.com/track/${s.deezer_id}`);
        const t = r.ok ? await r.json() : {};
        if (t.error?.code === 4) { await sleep(6000); continue; }   // Deezer quota: ~50 req / 5s
        explicit = t.explicit_lyrics ?? null;
        meta = await fetchAlbumMeta(t.album?.id);
      } catch {}
      if (meta.rateLimited) { await sleep(6000); continue; }
      const song = { album: s.album, genre: s.genre, year: s.year };
      applyDeezerMeta(song, { deezerId: s.deezer_id, album: null, explicit, ...meta });
      const { deezer_id, ...set } = song;
      await songs.updateOne({ _id: s._id }, { $set: set });
      meta.releaseDate || meta.genres?.length ? done++ : miss++;
      break;
    }
    await sleep(200);
  }
  log(`deezer backfill finished: ${done} updated, ${miss} had no data`);
}

// ---------- auth: Telegram Mini App initData -> HS256 JWT in an HttpOnly cookie (only sent to /me/*) ----------
const JWT_SECRET = process.env.JWT_SECRET || crypto.createHash('sha256').update('pl-jwt:' + BOT_TOKEN).digest('hex');
if (!process.env.JWT_SECRET) console.warn('[auth] JWT_SECRET not set - deriving one from BOT_TOKEN (set JWT_SECRET to rotate sessions independently)');
const SESSION_COOKIE = 'pl_session';
const SESSION_TTL = 7 * 24 * 3600;     // seconds
const INITDATA_MAX_AGE = 24 * 3600;    // seconds
const COOKIE_OPTS = req => ({ httpOnly: true, secure: !!req.secure, sameSite: 'lax', path: '/me' });
const b64u = x => Buffer.from(x).toString('base64url');
const hmac = (key, data) => crypto.createHmac('sha256', key).update(data).digest();
const same = (a, b) => a.length === b.length && crypto.timingSafeEqual(a, b);

const signJwt = payload => {
  const h = b64u(JSON.stringify({ alg: 'HS256', typ: 'JWT' })), b = b64u(JSON.stringify(payload));
  return `${h}.${b}.${hmac(JWT_SECRET, `${h}.${b}`).toString('base64url')}`;
};
const verifyJwt = tok => {
  const [h, b, sig] = String(tok || '').split('.');
  if (!h || !b || !sig || !same(Buffer.from(sig, 'base64url'), hmac(JWT_SECRET, `${h}.${b}`))) return null;
  try { const p = JSON.parse(Buffer.from(b, 'base64url').toString()); return p.exp > Date.now() / 1000 ? p : null; } catch { return null; }
};
// https://core.telegram.org/bots/webapps#validating-data-received-via-the-mini-app
function verifyInitData(raw, maxAge = INITDATA_MAX_AGE) {
  const params = new URLSearchParams(String(raw || ''));
  const hash = params.get('hash');
  if (!hash) return null;
  params.delete('hash');
  const check = [...params.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).map(([k, v]) => `${k}=${v}`).join('\n');
  if (!same(Buffer.from(hash, 'hex'), hmac(hmac('WebAppData', BOT_TOKEN), check))) return null;
  if (Date.now() / 1000 - Number(params.get('auth_date')) > maxAge) return null;
  try { const u = JSON.parse(params.get('user')); return Number.isInteger(u?.id) ? u : null; } catch { return null; }
}
const cookieOf = (req, name) => (req.headers.cookie || '').split(';').map(c => c.trim().split(/=(.*)/s)).find(([k]) => k === name)?.[1];

// ---------- api ----------
const BASE = APP_URL;
const PER_PAGE = 80;
const HOT_LIMIT = 60;
const MAX_CAPSULES = 50, MAX_CAPSULE_SONGS = 2000, GAP = 1024;
// _id last = stable order across pages when the sort key ties
const SORTS = {
  def: { pos: 1, created_at: -1, _id: -1 },   // pos = the owner's custom order (null = not placed yet = newest, on top)
  title: { title: 1, _id: 1 },
  artist: { artist: 1, title: 1, _id: 1 },
  plays: { listens: -1, created_at: -1, _id: -1 },
  released: { release_date: -1, created_at: -1, _id: -1 },
};
const LISTEN_WINDOW = 30 * 60 * 1000; // same IP counts once per song per 30 min
const BOT_UA = /bot|crawler|spider|preview|telegram|facebookexternalhit|whatsapp/i;

const shapeSong = s => {
  const { _id, ...r } = s;
  return {
    ...r,
    listens: s.listens || 0,
    listen_url: `${BASE}/listen/${s.song_id}`,
    info_url: `${BASE}/info/${s.song_id}`,
  };
};

const shapeUser = u => u && ({
  user_id: u._id,
  first_name: u.first_name,
  last_name: u.last_name,
  username: u.username,
  song_count: u.song_count || 0,
});

// ---------- genre capsules + appearance (pure helpers) ----------
const escRx = s => String(s).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const exactRx = s => new RegExp('^\\s*' + escRx(String(s).trim()) + '\\s*$', 'i');   // case-insensitive exact (arrays match per element)
// a genre capsule has no stored membership: it is every song of the user tagged with that genre,
// plus songs the owner pinned in (include), minus songs the owner removed (excluded)
const capFilter = (uid, c) => ({
  user_id: uid,
  $or: [{ genre: exactRx(c.genre) }, { song_id: { $in: c.include || [] } }],
  song_id: { $nin: c.excluded || [] },
});

// the owner's capsule order (users.cap_order = ids, "all" included); anything not listed yet (new capsules) goes last in creation order
const orderCaps = (u, list) => {
  const o = u.cap_order || [], at = new Map(o.map((id, i) => [id, i]));
  return list.map((c, i) => ({ c, k: at.has(c._id) ? at.get(c._id) : o.length + i })).sort((a, b) => a.k - b.k).map(x => x.c);
};

const HEX = /^#[0-9a-f]{6}$/i;
const THEME_ENUM = {
  mode: ['auto', 'light', 'dark'],
  font: ['system', 'serif', 'mono', 'rounded', 'display', 'condensed', 'handwritten', 'elegant', 'tech'],
  radius: ['sharp', 'soft', 'round', 'pill'],
  card: ['solid', 'glass', 'outline', 'neon', 'gradient', 'lifted'],
  effect: ['none', 'petals', 'snow', 'stars', 'hearts', 'fireflies', 'rain', 'bubbles', 'leaves', 'embers', 'confetti', 'sparkles', 'notes', 'meteors'],
  effectDensity: ['low', 'med', 'high'],
  avatarShape: ['round', 'squircle', 'square'],
  hero: ['auto', 'center', 'left'],
  heroCover: ['art', 'avatar'],
  coverShape: ['square', 'soft', 'round'],
  density: ['comfy', 'compact'],
  player: ['solid', 'glass', 'floating', 'accent'],
  gradType: ['linear', 'radial', 'conic'],
  bgAnim: ['none', 'aurora', 'drift', 'pulse'],
  bgPattern: ['none', 'dots', 'grid', 'lines', 'grain'],
  titleFx: ['none', 'gradient', 'glow', 'shine'],
  rowHover: ['tint', 'lift', 'glow', 'slide'],
  coverFx: ['none', 'shadow', 'glow', 'spin'],
  enter: ['rise', 'fade', 'zoom', 'slide', 'none'],
  clickFx: ['none', 'ripple', 'sparkle', 'hearts', 'notes'],
};
const THEME_NUM = { gradAngle: [0, 360], effectSpeed: [0.3, 2.5], bgBlur: [0, 24], bgDim: [0, 85], patternOpacity: [0, 60], effectSize: [0.5, 2], effectOpacity: [20, 100], fontScale: [85, 125], glowAmt: [0, 100] };
const THEME_BOOL = ['artColor', 'heroGlow', 'showPlays', 'showStats', 'rowStripes', 'fxPlayOnly'];
const THEME_HEX = ['bg', 'accent', 'bg2', 'bg3', 'accent2', 'textColor', 'effectColor'];
// whitelist everything: the page puts these straight into CSS variables / attributes
function cleanTheme(i, prev = {}) {
  const o = {};
  i = i && typeof i === 'object' ? i : {};
  for (const k of THEME_HEX) if (typeof i[k] === 'string' && HEX.test(i[k])) o[k] = i[k].toLowerCase();
  for (const [k, list] of Object.entries(THEME_ENUM)) if (list.includes(i[k])) o[k] = i[k];
  for (const [k, [lo, hi]] of Object.entries(THEME_NUM)) { const n = Number(i[k]); if (Number.isFinite(n)) o[k] = Math.min(hi, Math.max(lo, n)); }
  for (const k of THEME_BOOL) if (typeof i[k] === 'boolean') o[k] = i[k];
  if (typeof i.bio === 'string') { const b = i.bio.replace(/[\u0000-\u001f\u007f]+/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 140); if (b) o.bio = b; }
  if (prev.avatar) o.avatar = prev.avatar;          // images are only ever changed through the upload endpoints
  if (prev.bgImage) o.bgImage = prev.bgImage;
  return o;
}
function sniffImage(b) {
  if (b.length < 12) return null;
  if (b[0] === 0x89 && b[1] === 0x50 && b[2] === 0x4e && b[3] === 0x47) return { mime: 'image/png', ext: '.png' };
  if (b[0] === 0xff && b[1] === 0xd8 && b[2] === 0xff) return { mime: 'image/jpeg', ext: '.jpg' };
  if (b.toString('ascii', 0, 4) === 'RIFF' && b.toString('ascii', 8, 12) === 'WEBP') return { mime: 'image/webp', ext: '.webp' };
  if (b.toString('ascii', 0, 4) === 'GIF8') return { mime: 'image/gif', ext: '.gif' };
  return null;
}
const imgUploads = new Map();   // uid -> upload timestamps (simple hourly cap)

// queue helpers (pure)
const shuffleArr = a => {
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
};

// shuffle everything after the current song, remember the original order
const shuffleUpcoming = q => {
  q.original = q.items.slice();
  q.items = [...q.items.slice(0, q.index + 1), ...shuffleArr(q.items.slice(q.index + 1))];
  q.shuffle = true;
};

// restore the original order, keep the current song current
const unshuffle = q => {
  const cur = q.items[q.index];
  const orig = new Set(q.original || []);
  const inQ = new Set(q.items);
  const added = q.items.filter(i => !orig.has(i)); // queued while shuffled
  q.items = [...(q.original || []).filter(i => inQ.has(i)), ...added];
  q.index = Math.max(0, q.items.indexOf(cur));
  q.original = null;
  q.shuffle = false;
};
// end queue helpers

function startApi({ songs, users, queues }) {
  const app = express();
  app.set('trust proxy', true);
  app.use(cors());

  const seen = new Map();
  const pingSeen = new Map();   // ip:song -> time of the last listening-time ping
  setInterval(() => {
    const cut = Date.now() - LISTEN_WINDOW;
    for (const [k, t] of seen) if (t < cut) seen.delete(k);
    for (const [k, t] of pingSeen) if (t < Date.now() - 15 * 60 * 1000) pingSeen.delete(k);
  }, 10 * 60 * 1000).unref();

  const wrap = fn => (req, res) => fn(req, res).catch(e => {
    console.error(e);
    res.status(500).json({ error: 'internal error' });
  });

  const countListen = async (req, id) => {
    const key = `${req.ip}:${id}`;
    const now = Date.now();
    if (BOT_UA.test(req.get('user-agent') || '') || now - (seen.get(key) || 0) < LISTEN_WINDOW) return false;
    seen.set(key, now);
    await songs.updateOne({ song_id: id }, { $inc: { listens: 1 }, $set: { last_listened_at: new Date() } });
    // hourly bucket, so /top can rank by 24h / 7d / 30d and compare against the previous window (trends)
    const h = Math.floor(now / HOUR);
    lhours.updateOne({ _id: `${id}:${h}` }, { $inc: { n: 1 }, $setOnInsert: { song_id: id, h, expire_at: new Date(now + 75 * DAY) } }, { upsert: true })
      .catch(e => console.error('[top] hour bucket failed:', e.message));
    return true;
  };

  // count a listen and redirect to the audio file
  app.get('/listen/:songid', wrap(async (req, res) => {
    const id = req.params.songid;
    const s = await songs.findOne({ song_id: id }, { projection: { upload_url: 1, uploaded: 1 } });
    if (!s || !s.uploaded) return res.status(404).json({ error: 'song not found' });
    if (req.method === 'GET') await countListen(req, id);
    res.redirect(302, s.upload_url);
  }));

  // count a listen without redirecting - call when a preloaded track actually starts playing
  app.post('/listen/:songid', wrap(async (req, res) => {
    const id = req.params.songid;
    if (!(await songs.findOne({ song_id: id, uploaded: true }, { projection: { _id: 1 } })))
      return res.status(404).json({ error: 'song not found' });
    res.json({ counted: await countListen(req, id) });
  }));

  // listening-time ping: the player reports the seconds it actually played (every ~15s and when playback stops)
  app.post('/listen/:songid/ping', express.json(), wrap(async (req, res) => {
    if (BOT_UA.test(req.get('user-agent') || '')) return res.json({ ok: true });
    const id = req.params.songid;
    let sec = Math.floor(Number(req.body?.seconds));
    if (!Number.isFinite(sec) || sec < 1) return res.status(400).json({ error: 'seconds required' });
    const key = `${req.ip}:${id}`, now = Date.now(), prev = pingSeen.get(key);
    // never credit more than the wall-clock time since the last ping (plus slack), so a script can't inflate it
    const cap = prev && now - prev < 10 * 60 * 1000 ? (now - prev) / 1000 + 5 : 40;
    sec = Math.min(sec, 60, Math.floor(cap));
    pingSeen.set(key, now);
    const r = await songs.updateOne({ song_id: id, uploaded: true }, { $inc: { listen_seconds: sec } });
    if (!r.matchedCount) return res.status(404).json({ error: 'song not found' });
    res.json({ ok: true, credited: sec });
  }));

  app.get('/info/:songid', wrap(async (req, res) => {
    const s = await songs.findOne({ song_id: req.params.songid });
    if (!s) return res.status(404).json({ error: 'song not found' });
    const u = await users.findOne({ _id: s.user_id });
    res.json({ song: shapeSong(s), listens: s.listens || 0, added_by: shapeUser(u) });
  }));

  // Mini App direct link (t.me/<bot>/<app>?startapp=<user id>), app URL = <BASE>/playlists: the page reads the id from the start param
  app.get(['/playlist', '/playlists'], (req, res) => res.sendFile(path.join(__dirname, 'playlist.html')));

  // browsers get the playlist page, API clients (or ?format=json) get JSON
  app.get('/playlist/:userid', wrap(async (req, res) => {
    if (req.query.format !== 'json' && req.accepts(['json', 'html']) === 'html')
      return res.sendFile(path.join(__dirname, 'playlist.html'));

    const uid = Number(req.params.userid);
    if (!Number.isInteger(uid)) return res.status(400).json({ error: 'invalid user id' });
    const page = Math.max(1, parseInt(req.query.page, 10) || 1);
    const limit = Math.min(PER_PAGE, Math.max(1, parseInt(req.query.limit, 10) || PER_PAGE));
    const q = String(req.query.q || '').trim().slice(0, 100);
    const sortKey = Object.hasOwn(SORTS, req.query.sort) ? req.query.sort : 'def';

    const u = await users.findOne({ _id: uid });
    if (!u) return res.status(404).json({ error: 'user not found' });

    // scope: all songs, or one capsule (its order lives in capsule_songs)
    const scope = String(req.query.capsule || 'all');
    let cap = { id: 'all', name: 'All' }, ids = null, gcap = null;
    if (scope !== 'all') {
      const c = await capsules.findOne({ _id: scope, user_id: uid });
      if (!c) return res.status(404).json({ error: 'capsule not found' });
      cap = { id: c._id, name: c.name, genre: c.genre || null };
      if (c.genre) gcap = c;
      else ids = (await capSongs.find({ capsule_id: c._id }).sort({ pos: 1 }).project({ song_id: 1 }).toArray()).map(x => x.song_id);
    }
    const base = gcap ? capFilter(uid, gcap) : ids ? { user_id: uid, song_id: { $in: ids } } : { user_id: uid };
    const conds = [base];
    if (q) {
      const rx = new RegExp(escRx(q), 'i');
      conds.push({ $or: ['title', 'artist', 'album', 'album_artist', 'genre', 'label'].map(f => ({ [f]: rx })) }); // arrays (genre) match per element
    }
    const fArtist = String(req.query.artist || '').trim().slice(0, 200), fGenre = String(req.query.genre || '').trim().slice(0, 100);
    if (fArtist) conds.push({ artist: exactRx(fArtist) });
    if (fGenre) conds.push({ genre: exactRx(fGenre) });
    const filter = conds.length > 1 ? { $and: conds } : base;
    const skip = (page - 1) * limit;

    let total, items;
    if (ids && sortKey === 'def') {          // capsule order: filter, then page through the ordered ids
      let list = ids;
      if (q) { const hit = new Set((await songs.find(filter).project({ song_id: 1 }).toArray()).map(x => x.song_id)); list = ids.filter(i => hit.has(i)); }
      total = list.length;
      const slice = list.slice(skip, skip + limit);
      const byId = new Map((await songs.find({ user_id: uid, song_id: { $in: slice } }).toArray()).map(x => [x.song_id, x]));
      items = slice.map(i => byId.get(i)).filter(Boolean);
    } else {
      [total, items] = await Promise.all([
        songs.countDocuments(filter),
        songs.find(filter).collation({ locale: 'en', strength: 2 }).sort(SORTS[sortKey]).skip(skip).limit(limit).toArray(),
      ]);
    }
    const agg = page === 1 ? await songs.aggregate([{ $match: base },
      { $group: { _id: null, listens: { $sum: '$listens' }, duration: { $sum: '$duration' }, songs: { $sum: 1 } } }]).toArray() : [];
    res.json({
      user: shapeUser(u),
      capsule: cap,
      page,
      per_page: limit,
      total,                                  // matches for this q (== all songs in the scope when q is empty)
      pages: Math.ceil(total / limit),
      q, sort: sortKey,
      ...(page === 1 && { stats: { songs: agg[0]?.songs || 0, listens: agg[0]?.listens || 0, duration: agg[0]?.duration || 0 } }),
      songs: items.map(shapeSong),
    });
  }));

  app.get('/hot', wrap(async (req, res) => {
    const items = await songs.find({ uploaded: true }).sort({ listens: -1, created_at: -1 }).limit(HOT_LIMIT).toArray();
    const ids = [...new Set(items.map(s => s.user_id))];
    const us = await users.find({ _id: { $in: ids } }).toArray();
    const byId = new Map(us.map(u => [u._id, shapeUser(u)]));
    res.json({
      count: items.length,
      songs: items.map(s => ({ ...shapeSong(s), added_by: byId.get(s.user_id) || null })),
    });
  }));

  // ===== /top: most played songs, live, with trends =====
  // Ranked by plays inside a window (24h / 7d / 30d) or all time. Trend = rank now vs rank in the previous window of the same length
  // (all time: vs rank 24h ago, rebuilt as listens minus the last 24h of plays). Responses are cached a few seconds and shared.
  const TOP_HOURS = { '24h': 24, '7d': 168, '30d': 720 };
  const TOP_SHOW = 100, TOP_POOL = 300, TOP_TTL = 5000;
  const topCache = new Map();   // period -> { t, p }

  async function buildTop(period) {
    const now = Date.now(), hNow = Math.floor(now / HOUR);
    let cur, prevRank = new Map(), hasPrev = false;
    if (period === 'all') {
      const pool = await songs.find({ uploaded: true, listens: { $gt: 0 } }).sort({ listens: -1, created_at: -1, _id: -1 }).limit(TOP_POOL).toArray();
      const rec = new Map((await lhours.aggregate([{ $match: { h: { $gt: hNow - 24 } } }, { $group: { _id: '$song_id', n: { $sum: '$n' } } }]).toArray()).map(x => [x._id, x.n]));
      hasPrev = rec.size > 0;
      pool.map(s => ({ s, v: (s.listens || 0) - (rec.get(s.song_id) || 0) })).filter(x => x.v > 0)
        .sort((a, b) => b.v - a.v || b.s.created_at - a.s.created_at || (a.s._id < b.s._id ? 1 : -1))
        .forEach((x, i) => prevRank.set(x.s.song_id, i + 1));
      cur = pool.slice(0, TOP_SHOW).map(s => ({ s, plays: s.listens || 0, extra: rec.get(s.song_id) || 0 }));
    } else {
      const W = TOP_HOURS[period];
      const agg = (lo, hi, lim) => lhours.aggregate([{ $match: { h: { $gt: lo, $lte: hi } } }, { $group: { _id: '$song_id', n: { $sum: '$n' } } }, { $sort: { n: -1, _id: 1 } }, { $limit: lim }]).toArray();
      const [now_, prev] = await Promise.all([agg(hNow - W, hNow, TOP_SHOW + 50), agg(hNow - 2 * W, hNow - W, 1000)]);
      hasPrev = prev.length > 0;
      prev.forEach((x, i) => prevRank.set(x._id, i + 1));
      const docs = new Map((await songs.find({ song_id: { $in: now_.map(x => x._id) }, uploaded: true }).toArray()).map(s => [s.song_id, s]));
      cur = now_.filter(x => docs.has(x._id)).slice(0, TOP_SHOW).map(x => ({ s: docs.get(x._id), plays: x.n, extra: docs.get(x._id).listens || 0 }));
    }
    const owners = new Map((await users.find({ _id: { $in: [...new Set(cur.map(x => x.s.user_id))] } }).toArray()).map(u => [u._id, shapeUser(u)]));
    const live = await nowp.aggregate([{ $match: { playing: true, expire_at: { $gt: new Date() } } }, { $group: { _id: '$song_id', n: { $sum: 1 } } }]).toArray();
    const liveBy = new Map(live.map(x => [x._id, x.n]));
    return {
      period, updated_at: new Date(now), has_trend: hasPrev,
      live: live.reduce((a, x) => a + x.n, 0),
      songs: cur.map((x, i) => {
        const rank = i + 1, pr = prevRank.get(x.s.song_id);
        const trend = !hasPrev ? 'none' : pr == null ? 'new' : pr > rank ? 'up' : pr < rank ? 'down' : 'same';
        return { ...shapeSong(x.s), rank, prev_rank: pr ?? null, trend, delta: pr ? Math.abs(pr - rank) : 0, plays: x.plays, extra: x.extra,
          listeners: liveBy.get(x.s.song_id) || 0, added_by: owners.get(x.s.user_id) || null };
      }),
    };
  }
  const topCached = period => {
    const c = topCache.get(period);
    if (c && Date.now() - c.t < TOP_TTL) return c.p;
    const p = buildTop(period).catch(e => { topCache.delete(period); throw e; });
    topCache.set(period, { t: Date.now(), p });
    return p;
  };

  app.get('/top', (req, res) => res.sendFile(path.join(__dirname, 'top.html')));
  app.get('/top/data', wrap(async (req, res) => {
    const period = req.query.period === 'all' || TOP_HOURS[req.query.period] ? req.query.period : 'all';
    res.set('Cache-Control', 'no-store');
    res.json(await topCached(period));
  }));

  // ---------- queue / player ----------
  app.use(express.json());

  // owner editor page (Telegram Mini App); it signs in itself via /auth/tg
  app.get('/manage', (req, res) => res.sendFile(path.join(__dirname, 'manage.html')));

  // ===== sign-in: Telegram Mini App initData -> JWT cookie (HttpOnly, Path=/me, so only the /me/* APIs ever receive it) =====
  const needHeader = (req, res) => req.get('x-requested-with') === 'playlist' || (res.status(403).json({ error: 'missing X-Requested-With: playlist header' }), false);
  app.post('/auth/tg', wrap(async (req, res) => {
    if (!needHeader(req, res)) return;
    const u = verifyInitData(req.body?.initData);
    if (!u) return res.status(401).json({ error: 'invalid or expired Telegram data' });
    const now = Math.floor(Date.now() / 1000);
    res.cookie(SESSION_COOKIE, signJwt({ sub: u.id, iat: now, exp: now + SESSION_TTL }), { ...COOKIE_OPTS(req), maxAge: SESSION_TTL * 1000 });
    res.json({ user_id: u.id });
  }));
  app.get('/me', (req, res) => {
    const p = verifyJwt(cookieOf(req, SESSION_COOKIE));
    p ? res.json({ user_id: p.sub }) : res.status(401).json({ error: 'not signed in' });
  });
  app.post('/me/logout', (req, res) => { res.clearCookie(SESSION_COOKIE, COOKIE_OPTS(req)); res.json({ ok: true }); });

  // ===== now playing (powers /status). The player sends a heartbeat with Telegram initData, so it identifies the listener
  // whether the Mini App was opened from a group or from the bot's DM. No cookie involved, so no CSRF concern. =====
  const NOWP_TTL = 60 * 1000;
  app.post('/nowplaying', wrap(async (req, res) => {
    const u = verifyInitData(req.body?.initData, 7 * 24 * 3600);   // a player left open for days keeps its launch-time initData
    if (!u) return res.status(401).json({ error: 'invalid Telegram data' });
    const now = Date.now();
    const at = Math.min(Number(req.body?.at) || now, now + 60000);   // client clock, only used to ignore out-of-order requests
    const cur = await nowp.findOne({ _id: u.id }, { projection: { at: 1 } });
    if (cur && at < cur.at) return res.json({ ok: true, stale: true });
    if (req.body?.state !== 'playing') {
      await nowp.updateOne({ _id: u.id }, { $set: { playing: false, at, expire_at: new Date(now + NOWP_TTL) } }, { upsert: true });
      return res.json({ ok: true });
    }
    const id = String(req.body?.song_id || '');
    const s = await songs.findOne({ song_id: id, uploaded: true }, { projection: { title: 1, artist: 1, file_name: 1 } });
    if (!s) return res.status(404).json({ error: 'song not found' });
    await nowp.updateOne({ _id: u.id }, { $set: {
      playing: true, song_id: id, at, updated_at: new Date(now), expire_at: new Date(now + NOWP_TTL),
      title: s.title || (s.file_name || '').replace(/\.[^.]+$/, '') || 'Unknown', artist: s.artist || null,
    } }, { upsert: true });
    res.json({ ok: true });
  }));

  const auth = (req, res, next) => {
    const p = verifyJwt(cookieOf(req, SESSION_COOKIE));
    if (!p) return res.status(401).json({ error: 'not signed in' });
    if (req.method !== 'GET' && !needHeader(req, res)) return;   // CSRF: a custom header forces a CORS preflight, which cross-site pages can't pass with cookies
    req.uid = p.sub;
    next();
  };

  // ===== capsules (sub-playlists). "all" is virtual = every song of the user =====
  const cleanName = n => String(n ?? '').replace(/\s+/g, ' ').trim().slice(0, 40);
  const imgOf = s => s.image_url || s.poster_url || s.cover_url || null;
  const dupKey = e => e?.code === 11000;

  async function coversOf(uid, c) {
    const P = { image_url: 1, poster_url: 1, cover_url: 1 };
    let docs;
    if (c._id === 'all') docs = await songs.find({ user_id: uid }).sort(SORTS.def).limit(40).project(P).toArray();
    else if (c.genre) docs = await songs.find(capFilter(uid, c)).sort(SORTS.def).limit(40).project(P).toArray();
    else {
      const ids = (await capSongs.find({ capsule_id: c._id }).sort({ pos: 1 }).limit(24).project({ song_id: 1 }).toArray()).map(x => x.song_id);
      const m = new Map((await songs.find({ song_id: { $in: ids } }).project({ song_id: 1, ...P }).toArray()).map(x => [x.song_id, x]));
      docs = ids.map(i => m.get(i)).filter(Boolean);
    }
    return docs.map(imgOf).filter(Boolean).slice(0, 4);
  }

  // Mini App deep link base, t.me/<bot>/<app>. The page appends ?startapp=<user id> or ?startapp=<user id>_<capsule id>
  // (start params allow A-Z a-z 0-9 _ -, and capsule ids are hex, so "_" is a safe separator). null until the bot username is known.
  const shareBase = () => { const b = bot.botInfo?.username || process.env.BOT_USERNAME || DEFAULT_BOT_USERNAME; return b ? `https://t.me/${b}/${MINIAPP_NAME}` : null; };

  // public: [] when the user has no capsules, else [All, ...capsules] with counts and cover art
  app.get('/playlist/:userid/capsules', wrap(async (req, res) => {
    const uid = Number(req.params.userid);
    if (!Number.isInteger(uid)) return res.status(400).json({ error: 'invalid user id' });
    const u = await users.findOne({ _id: uid });
    if (!u) return res.status(404).json({ error: 'user not found' });
    const caps = await capsules.find({ user_id: uid }).sort({ created_at: 1 }).toArray();
    if (!caps.length) return res.json({ user: shapeUser(u), count: 0, capsules: [], share: shareBase() });
    const [total, counts] = await Promise.all([
      songs.countDocuments({ user_id: uid }),
      capSongs.aggregate([{ $match: { user_id: uid } }, { $group: { _id: '$capsule_id', n: { $sum: 1 } } }]).toArray(),
    ]);
    const n = new Map(counts.map(c => [c._id, c.n]));
    const gCount = new Map(await Promise.all(caps.filter(c => c.genre).map(async c => [c._id, await songs.countDocuments(capFilter(uid, c))])));
    const out = await Promise.all(orderCaps(u, [{ _id: 'all', name: 'All', count: total }, ...caps.map(c => ({ _id: c._id, name: c.name, genre: c.genre || null, include: c.include, excluded: c.excluded, count: c.genre ? gCount.get(c._id) : n.get(c._id) || 0 }))])
      .map(async c => ({ id: c._id, name: c.name, genre: c.genre || null, count: c.count, covers: await coversOf(uid, c) })));
    res.json({ user: shapeUser(u), count: caps.length, capsules: out, share: shareBase() });
  }));

  // body: { order: [capsule ids, "all" included] } - the first one is shown first on the playlist page
  app.put('/me/capsules/order', auth, wrap(async (req, res) => {
    const mine = new Set((await capsules.find({ user_id: req.uid }).project({ _id: 1 }).toArray()).map(c => c._id));
    mine.add('all');
    const want = Array.isArray(req.body?.order) ? req.body.order.map(String) : [];
    const order = [...new Set(want.filter(id => mine.has(id)))];
    await users.updateOne({ _id: req.uid }, { $set: { cap_order: order } });
    res.json({ ok: true, order });
  }));

  app.post('/me/capsules', auth, wrap(async (req, res) => {
    const name = cleanName(req.body?.name);
    if (!name) return res.status(400).json({ error: 'name required' });
    if (await capsules.countDocuments({ user_id: req.uid }) >= MAX_CAPSULES) return res.status(400).json({ error: `max ${MAX_CAPSULES} capsules` });
    const c = { _id: crypto.randomBytes(5).toString('hex'), user_id: req.uid, name, name_key: name.toLowerCase(), created_at: new Date() };
    try { await capsules.insertOne(c); } catch (e) { if (dupKey(e)) return res.status(409).json({ error: 'you already have a capsule with that name' }); throw e; }
    res.status(201).json({ id: c._id, name: c.name, count: 0 });
  }));

  // ===== import from Spotify: playlist link -> new capsule + durable per-track items (see "Spotify import" below). The page polls GET /me/imports/:id =====
  app.post('/me/imports/spotify', auth, wrap(async (req, res) => {
    const pid = spPlaylistId(req.body?.url);
    if (!pid) return res.status(400).json({ error: 'Paste a Spotify playlist link (open.spotify.com/playlist/…)' });
    const running = await imports.findOne({ user_id: req.uid, status: 'running' }, { projection: { _id: 1 } });
    if (running) return res.status(409).json({ error: 'You already have an import running', import_id: running._id });
    if (await capsules.countDocuments({ user_id: req.uid }) >= MAX_CAPSULES) return res.status(400).json({ error: `max ${MAX_CAPSULES} capsules` });
    let pl;
    try { pl = await spFetchPlaylist(pid); }
    catch (e) { log(`spotify playlist ${pid} failed: ${e.message}`); return res.status(502).json({ error: 'Could not read that playlist. Make sure it is public, then try again.' }); }

    const base = cleanName(req.body?.name) || cleanName(pl.name) || 'Spotify import';
    let cap = null;
    for (let n = 1; n <= 20 && !cap; n++) {   // same name already taken -> "Name (2)", "Name (3)"…
      const nm = n === 1 ? base : `${base.slice(0, 40 - String(n).length - 3)} (${n})`;
      const c = { _id: crypto.randomBytes(5).toString('hex'), user_id: req.uid, name: nm, name_key: nm.toLowerCase(), created_at: new Date() };
      try { await capsules.insertOne(c); cap = c; } catch (e) { if (!dupKey(e)) throw e; }
    }
    if (!cap) return res.status(409).json({ error: 'you already have capsules with that name. Rename one first' });

    const now = Date.now();
    const im = { _id: crypto.randomBytes(6).toString('hex'), user_id: req.uid, capsule_id: cap._id, capsule_name: cap.name, playlist_id: pid, playlist_name: pl.name || null, playlist_total: pl.total, status: 'running', created_at: new Date(now) };
    try {
      await imports.insertOne(im);
      await importItems.insertMany(pl.tracks.map((t, i) => ({
        _id: `${im._id}:${i}`, import_id: im._id, user_id: req.uid, capsule_id: cap._id, idx: i,
        track_id: t.id, spotify_url: `https://open.spotify.com/track/${t.id}`, title: t.title, artist: t.artist, image: t.image,
        status: 'pending', attempts: 0, error: null, order: now * 1000 + i, created_at: new Date(now), retry_at: new Date(now),
      })));
    } catch (e) {   // nothing queued -> don't leave an empty capsule behind
      await Promise.all([imports.deleteOne({ _id: im._id }), capsules.deleteOne({ _id: cap._id }), importItems.deleteMany({ import_id: im._id })]).catch(() => {});
      throw e;
    }
    log(`import ${im._id} queued: ${pl.tracks.length}/${pl.total} tracks of "${pl.name}" for user ${req.uid} -> capsule ${cap._id}`);
    pumpImports();
    res.status(201).json(await importView(im));
  }));

  app.get('/me/imports', auth, wrap(async (req, res) => {
    const list = await imports.find({ user_id: req.uid }).sort({ created_at: -1 }).limit(10).toArray();
    res.json({ imports: await Promise.all(list.map(im => importView(im, false))) });
  }));

  app.get('/me/imports/:id', auth, wrap(async (req, res) => {
    const im = await imports.findOne({ _id: String(req.params.id), user_id: req.uid });
    if (!im) return res.status(404).json({ error: 'import not found' });
    res.json(await importView(im));
  }));

  // failed songs go back in line with a fresh set of attempts
  app.post('/me/imports/:id/retry', auth, wrap(async (req, res) => {
    const im = await imports.findOne({ _id: String(req.params.id), user_id: req.uid });
    if (!im) return res.status(404).json({ error: 'import not found' });
    const r = await importItems.updateMany({ import_id: im._id, status: 'failed' }, { $set: { status: 'pending', attempts: 0, error: null, retry_at: new Date() }, $unset: { expire_at: '' } });
    if (r.modifiedCount) {
      await imports.updateOne({ _id: im._id }, { $set: { status: 'running' }, $unset: { expire_at: '', finished_at: '' } });
      await importItems.updateMany({ import_id: im._id }, { $unset: { expire_at: '' } });
      pumpImports();
    }
    res.json(await importView(im));
  }));

  // ===== facets, genre capsules, appearance =====
  const cleanQ = req => ({ q: String(req.query.q || '').trim().slice(0, 100), artist: String(req.query.artist || '').trim().slice(0, 200), genre: String(req.query.genre || '').trim().slice(0, 100) });
  const songFilter = (uid, { q, artist, genre }) => {
    const conds = [{ user_id: uid }];
    if (q) { const rx = new RegExp(escRx(q), 'i'); conds.push({ $or: ['title', 'artist', 'album', 'album_artist', 'genre', 'label'].map(f => ({ [f]: rx })) }); }
    if (artist) conds.push({ artist: exactRx(artist) });
    if (genre) conds.push({ genre: exactRx(genre) });
    return conds.length > 1 ? { $and: conds } : conds[0];
  };

  // artists + genres in the owner's library (for filters and the "turn genre into capsule" picker)
  app.get('/me/facets', auth, wrap(async (req, res) => {
    const [artists, genres, caps] = await Promise.all([
      songs.aggregate([{ $match: { user_id: req.uid, artist: { $type: 'string', $ne: '' } } },
        { $group: { _id: { $toLower: { $trim: { input: '$artist' } } }, name: { $first: '$artist' }, n: { $sum: 1 } } },
        { $sort: { n: -1, _id: 1 } }, { $limit: 500 }]).toArray(),
      songs.aggregate([{ $match: { user_id: req.uid } },
        { $project: { g: { $cond: [{ $isArray: '$genre' }, '$genre', { $cond: [{ $ifNull: ['$genre', false] }, ['$genre'], []] }] } } },
        { $unwind: '$g' }, { $match: { g: { $type: 'string', $ne: '' } } },
        { $group: { _id: { $toLower: { $trim: { input: '$g' } } }, name: { $first: { $trim: { input: '$g' } } }, n: { $sum: 1 } } },
        { $sort: { n: -1, _id: 1 } }, { $limit: 300 }]).toArray(),
      capsules.find({ user_id: req.uid, genre: { $ne: null } }).project({ genre: 1 }).toArray(),
    ]);
    const used = new Map(caps.map(c => [String(c.genre).toLowerCase().trim(), c._id]));
    res.json({
      artists: artists.map(x => ({ name: x.name, count: x.n })),
      genres: genres.map(x => ({ name: x.name, count: x.n, capsule_id: used.get(x._id) || null })),
    });
  }));

  // every song id matching the filters (for "select all N matching"), max 2000
  app.get('/me/songs/ids', auth, wrap(async (req, res) => {
    const ids = (await songs.find(songFilter(req.uid, cleanQ(req))).sort(SORTS.artist).limit(MAX_CAPSULE_SONGS).project({ song_id: 1 }).toArray()).map(x => x.song_id);
    res.json({ ids });
  }));

  // ids already inside a capsule (the song picker greys them out)
  app.get('/me/capsules/:cid/ids', auth, wrap(async (req, res) => {
    const scope = await scopeOf(req, res); if (!scope) return;
    if (scope === 'all') return res.json({ ids: [] });
    const c = req.capDoc;
    const ids = c.genre
      ? (await songs.find(capFilter(req.uid, c)).limit(5000).project({ song_id: 1 }).toArray()).map(x => x.song_id)
      : (await capSongs.find({ capsule_id: scope }).project({ song_id: 1 }).toArray()).map(x => x.song_id);
    res.json({ ids });
  }));

  // "Turn genre into capsule": a capsule that follows a genre. New songs of that genre show up on their own.
  app.post('/me/capsules/genre', auth, wrap(async (req, res) => {
    const genre = cleanName(req.body?.genre);
    if (!genre) return res.status(400).json({ error: 'genre required' });
    if (await capsules.countDocuments({ user_id: req.uid }) >= MAX_CAPSULES) return res.status(400).json({ error: `max ${MAX_CAPSULES} capsules` });
    if (await capsules.findOne({ user_id: req.uid, genre_key: genre.toLowerCase() }, { projection: { _id: 1 } })) return res.status(409).json({ error: 'you already have a capsule for that genre' });
    const c = { _id: crypto.randomBytes(5).toString('hex'), user_id: req.uid, name: genre, name_key: genre.toLowerCase(), genre, genre_key: genre.toLowerCase(), include: [], excluded: [], created_at: new Date() };
    try { await capsules.insertOne(c); } catch (e) { if (dupKey(e)) return res.status(409).json({ error: 'you already have a capsule with that name. Rename it first' }); throw e; }
    res.status(201).json({ id: c._id, name: c.name, genre: c.genre, count: await songs.countDocuments(capFilter(req.uid, c)) });
  }));

  // ----- playlist page appearance -----
  app.get('/playlist/:userid/theme', wrap(async (req, res) => {
    const uid = Number(req.params.userid);
    if (!Number.isInteger(uid)) return res.status(400).json({ error: 'invalid user id' });
    const u = await users.findOne({ _id: uid }, { projection: { theme: 1 } });
    if (!u) return res.status(404).json({ error: 'user not found' });
    res.set('Cache-Control', 'no-cache');
    res.json({ theme: u.theme || {} });
  }));

  app.put('/me/theme', auth, wrap(async (req, res) => {
    const u = await users.findOne({ _id: req.uid }, { projection: { theme: 1 } });
    if (!u) return res.status(404).json({ error: 'user not found' });
    const theme = cleanTheme(req.body?.theme, u.theme || {});
    await users.updateOne({ _id: req.uid }, { $set: { theme } });
    res.json({ theme });
  }));

  app.delete('/me/theme', auth, wrap(async (req, res) => {
    await users.updateOne({ _id: req.uid }, { $unset: { theme: '' } });
    res.json({ theme: {} });
  }));

  // profile picture / background image: the browser resizes first, we validate and store it on Hugging Face like song art
  app.post('/me/theme/image/:kind', auth, express.raw({ type: 'image/*', limit: '6mb' }), wrap(async (req, res) => {
    const kind = req.params.kind;
    if (!['avatar', 'bg'].includes(kind)) return res.status(400).json({ error: 'kind must be avatar or bg' });
    const buf = req.body;
    if (!Buffer.isBuffer(buf) || !buf.length) return res.status(400).json({ error: 'send the image as the request body' });
    const t = sniffImage(buf);
    if (!t) return res.status(415).json({ error: 'use a PNG, JPEG, WebP or GIF image' });
    const now = Date.now(), recent = (imgUploads.get(req.uid) || []).filter(x => now - x < 3600e3);
    if (recent.length >= 15) return res.status(429).json({ error: 'too many uploads, try again later' });
    imgUploads.set(req.uid, [...recent, now]);
    const up = await uploadToHost(buf, `profile-${kind}-${req.uid}${t.ext}`, t.mime);
    const field = kind === 'avatar' ? 'avatar' : 'bgImage';
    const r = await users.findOneAndUpdate({ _id: req.uid }, { $set: { [`theme.${field}`]: up.short_url } }, { returnDocument: 'after', projection: { theme: 1 } });
    if (!r) return res.status(404).json({ error: 'user not found' });
    res.json({ url: up.short_url, theme: r.theme || {} });
  }));

  app.delete('/me/theme/image/:kind', auth, wrap(async (req, res) => {
    if (!['avatar', 'bg'].includes(req.params.kind)) return res.status(400).json({ error: 'kind must be avatar or bg' });
    const r = await users.findOneAndUpdate({ _id: req.uid }, { $unset: { [`theme.${req.params.kind === 'avatar' ? 'avatar' : 'bgImage'}`]: '' } }, { returnDocument: 'after', projection: { theme: 1 } });
    res.json({ theme: r?.theme || {} });
  }));

  app.patch('/me/capsules/:cid', auth, wrap(async (req, res) => {
    const name = cleanName(req.body?.name);
    if (!name) return res.status(400).json({ error: 'name required' });
    try {
      const r = await capsules.updateOne({ _id: req.params.cid, user_id: req.uid }, { $set: { name, name_key: name.toLowerCase(), updated_at: new Date() } });
      if (!r.matchedCount) return res.status(404).json({ error: 'capsule not found' });
    } catch (e) { if (dupKey(e)) return res.status(409).json({ error: 'you already have a capsule with that name' }); throw e; }
    res.json({ id: req.params.cid, name });
  }));

  // songs stay in All; only the capsule and its membership go
  app.delete('/me/capsules/:cid', auth, wrap(async (req, res) => {
    const r = await capsules.deleteOne({ _id: req.params.cid, user_id: req.uid });
    if (!r.deletedCount) return res.status(404).json({ error: 'capsule not found' });
    await capSongs.deleteMany({ capsule_id: req.params.cid });
    res.json({ ok: true });
  }));

  // copy songs from All into a capsule (appended at the end; skips ones already inside)
  app.post('/me/capsules/:cid/songs', auth, wrap(async (req, res) => {
    const cid = req.params.cid;
    const capDoc = await capsules.findOne({ _id: cid, user_id: req.uid });
    if (!capDoc) return res.status(404).json({ error: 'capsule not found' });
    const raw = Array.isArray(req.body?.song_ids) ? req.body.song_ids : req.body?.song_id ? [req.body.song_id] : [];
    const want = [...new Set(raw.map(String))].slice(0, 200);
    if (!want.length) return res.status(400).json({ error: 'song_ids required' });
    if (capDoc.genre) {   // genre capsule: adding = un-remove a song, or pin one from another genre
      const mine = await songs.find({ user_id: req.uid, song_id: { $in: want } }).project({ song_id: 1, genre: 1 }).toArray();
      const rx = exactRx(capDoc.genre), exc = new Set(capDoc.excluded || []), inc = new Set(capDoc.include || []);
      const outside = new Set(mine.filter(x => ![].concat(x.genre || []).some(g => rx.test(String(g)))).map(x => x.song_id));
      const ok = mine.map(x => x.song_id);
      const added = ok.filter(i => exc.has(i) || (outside.has(i) && !inc.has(i))).length;
      await capsules.updateOne({ _id: cid }, { $pull: { excluded: { $in: ok } }, $addToSet: { include: { $each: [...outside] } } });
      return res.json({ added, skipped: want.length - added });
    }
    const [mine, have, count, last] = await Promise.all([
      songs.find({ user_id: req.uid, song_id: { $in: want } }).project({ song_id: 1 }).toArray(),
      capSongs.find({ capsule_id: cid, song_id: { $in: want } }).project({ song_id: 1 }).toArray(),
      capSongs.countDocuments({ capsule_id: cid }),
      capSongs.find({ capsule_id: cid }).sort({ pos: -1 }).limit(1).project({ pos: 1 }).toArray(),
    ]);
    const owned = new Set(mine.map(x => x.song_id)), dup = new Set(have.map(x => x.song_id));
    const add = want.filter(i => owned.has(i) && !dup.has(i)).slice(0, Math.max(0, MAX_CAPSULE_SONGS - count));
    const start = last[0] ? last[0].pos : -GAP;
    if (add.length) await capSongs.insertMany(add.map((song_id, i) => ({ capsule_id: cid, user_id: req.uid, song_id, pos: start + GAP * (i + 1), added_at: new Date() })), { ordered: false }).catch(e => { if (!dupKey(e) && e.code !== 65) throw e; });
    res.json({ added: add.length, skipped: want.length - add.length });
  }));

  // :cid is a capsule id, or "all" for the main playlist
  const scopeOf = async (req, res) => {
    if (req.params.cid === 'all') return 'all';
    const c = await capsules.findOne({ _id: req.params.cid, user_id: req.uid });
    req.capDoc = c;
    if (!c) res.status(404).json({ error: 'capsule not found' });
    return c?._id || null;
  };
  const orderOf = async (uid, scope) => scope === 'all'
    ? (await songs.find({ user_id: uid }).sort(SORTS.def).project({ song_id: 1, pos: 1 }).toArray()).map(x => ({ id: x.song_id, pos: x.pos ?? null }))
    : (await capSongs.find({ capsule_id: scope }).sort({ pos: 1 }).project({ song_id: 1, pos: 1 }).toArray()).map(x => ({ id: x.song_id, pos: x.pos }));
  const placePos = (uid, scope, id, pos) => scope === 'all'
    ? songs.updateOne({ user_id: uid, song_id: id }, { $set: { pos } })
    : capSongs.updateOne({ capsule_id: scope, song_id: id }, { $set: { pos } });
  const renumber = (uid, scope, ids) => (scope === 'all' ? songs : capSongs).bulkWrite(ids.map((id, i) => ({
    updateOne: { filter: scope === 'all' ? { user_id: uid, song_id: id } : { capsule_id: scope, song_id: id }, update: { $set: { pos: i * GAP } } } })));

  // body: { index } (0-based in the full list) | { before: song_id } | { after: song_id } | { to: 'top' | 'bottom' }
  app.patch('/me/capsules/:cid/songs/:sid/move', auth, wrap(async (req, res) => {
    const scope = await scopeOf(req, res); if (!scope) return;
    if (req.capDoc?.genre) return res.status(400).json({ error: 'a genre capsule follows your playlist order' });
    const sid = req.params.sid, { index, before, after, to } = req.body || {};
    const list = await orderOf(req.uid, scope);
    const from = list.findIndex(x => x.id === sid);
    if (from < 0) return res.status(404).json({ error: 'song not in this list' });
    const rest = list.filter(x => x.id !== sid);
    let at;
    if (Number.isInteger(index)) at = Math.min(Math.max(index, 0), rest.length);
    else if (before) at = rest.findIndex(x => x.id === String(before));
    else if (after) at = rest.findIndex(x => x.id === String(after)) + 1 || -1;
    else if (to === 'top') at = 0;
    else if (to === 'bottom') at = rest.length;
    else return res.status(400).json({ error: 'give index, before, after or to' });
    if (at < 0) return res.status(400).json({ error: 'anchor song not in this list' });
    if (at === from) return res.json({ ok: true, index: at });

    const prev = rest[at - 1], next = rest[at];
    if (list.some(x => x.pos == null) || (prev && next && next.pos - prev.pos < 1e-6)) {   // legacy songs without a position, or no gap left: number everything
      const ids = rest.map(x => x.id); ids.splice(at, 0, sid);
      await renumber(req.uid, scope, ids);
    } else {
      await placePos(req.uid, scope, sid, prev && next ? (prev.pos + next.pos) / 2 : prev ? prev.pos + GAP : next ? next.pos - GAP : 0);
    }
    res.json({ ok: true, index: at });
  }));

  // capsule: removes the song from that capsule only. "all": deletes the song from the playlist (and every capsule)
  app.delete('/me/capsules/:cid/songs/:sid', auth, wrap(async (req, res) => {
    const scope = await scopeOf(req, res); if (!scope) return;
    const sid = req.params.sid;
    if (scope === 'all') {
      const r = await songs.deleteOne({ user_id: req.uid, song_id: sid });
      if (!r.deletedCount) return res.status(404).json({ error: 'song not found' });
      await Promise.all([capSongs.deleteMany({ user_id: req.uid, song_id: sid }), users.updateOne({ _id: req.uid }, { $inc: { song_count: -1 } })]);
      return res.json({ ok: true, deleted: true });
    }
    if (req.capDoc?.genre) {   // removing from a genre capsule hides the song there (it stays in All and keeps its genre)
      await capsules.updateOne({ _id: scope }, { $addToSet: { excluded: sid }, $pull: { include: sid } });
      return res.json({ ok: true, deleted: false });
    }
    const r = await capSongs.deleteOne({ capsule_id: scope, song_id: sid });
    if (!r.deletedCount) return res.status(404).json({ error: 'song not in this capsule' });
    res.json({ ok: true, deleted: false });
  }));
  app.param('qid', (req, res, next, v) =>
    /^[\w-]{1,64}$/.test(v) ? next() : res.status(400).json({ error: 'invalid queue id' }));

  const okSong = id => songs.findOne({ song_id: String(id), uploaded: true }, { projection: { song_id: 1 } });

  const hydrate = async ids => {
    if (!ids.length) return [];
    const docs = await songs.find({ song_id: { $in: ids } }).toArray();
    const m = new Map(docs.map(d => [d.song_id, shapeSong(d)]));
    return ids.map(i => m.get(i)).filter(Boolean);
  };

  const loadQ = async qid =>
    (await queues.findOne({ _id: qid })) || { _id: qid, items: [], index: 0, shuffle: false, original: null };

  const saveQ = q => queues.updateOne(
    { _id: q._id },
    { $set: { items: q.items, index: q.index, shuffle: q.shuffle, original: q.original, updated_at: new Date() } },
    { upsert: true }
  );

  // up_next[i] sits at absolute position index + 1 + i
  const view = async q => {
    const cur = q.items[q.index];
    const [current] = cur ? await hydrate([cur]) : [];
    const up_next = await hydrate(q.items.slice(q.index + 1, q.index + 101));
    return {
      queue_id: q._id,
      shuffle: q.shuffle,
      index: q.index,
      total: q.items.length,
      current: current || null,
      next: up_next[0] || null, // preload next.upload_url
      up_next,
    };
  };

  app.get('/queue/:qid', wrap(async (req, res) => res.json(await view(await loadQ(req.params.qid)))));

  // body: { song_id?, user_id?, hot?, shuffle? }
  // song_id alone = that song; + user_id/hot = that song inside the playlist; no song_id = start from the top
  app.post('/queue/:qid/play', wrap(async (req, res) => {
    const { song_id, user_id, hot, shuffle, capsule_id } = req.body || {};
    let ids = [];
    if (user_id != null && capsule_id && capsule_id !== 'all') {
      const cdoc = await capsules.findOne({ _id: String(capsule_id), user_id: Number(user_id) });
      const mem = cdoc?.genre
        ? (await songs.find(capFilter(Number(user_id), cdoc)).sort(SORTS.def).limit(500).project({ song_id: 1 }).toArray()).map(x => x.song_id)
        : (await capSongs.find({ capsule_id: String(capsule_id), user_id: Number(user_id) }).sort({ pos: 1 }).limit(500).project({ song_id: 1 }).toArray()).map(x => x.song_id);
      const up = new Set((await songs.find({ song_id: { $in: mem }, uploaded: true }).project({ song_id: 1 }).toArray()).map(x => x.song_id));
      ids = mem.filter(i => up.has(i));
    } else if (user_id != null) {
      ids = (await songs.find({ user_id: Number(user_id), uploaded: true })
        .sort(SORTS.def).limit(500).project({ song_id: 1 }).toArray()).map(s => s.song_id);
    } else if (hot) {
      ids = (await songs.find({ uploaded: true })
        .sort({ listens: -1, created_at: -1 }).limit(HOT_LIMIT).project({ song_id: 1 }).toArray()).map(s => s.song_id);
    }
    if (song_id) {
      if (!(await okSong(song_id))) return res.status(404).json({ error: 'song not found' });
      if (!ids.includes(song_id)) ids.unshift(song_id);
    }
    if (!ids.length) return res.status(400).json({ error: 'nothing to play' });

    const q = { _id: req.params.qid, items: ids, index: song_id ? ids.indexOf(song_id) : 0, shuffle: false, original: null };
    if (shuffle && !song_id) { q.original = ids.slice(); q.items = shuffleArr(ids.slice()); q.shuffle = true; }
    else if (shuffle) shuffleUpcoming(q);
    await saveQ(q);
    res.json(await view(q));
  }));

  // add to end of queue
  app.post('/queue/:qid/add', wrap(async (req, res) => {
    const id = req.body?.song_id;
    if (!id || !(await okSong(id))) return res.status(404).json({ error: 'song not found' });
    const q = await loadQ(req.params.qid);
    q.items.push(id);
    if (q.original) q.original.push(id);
    await saveQ(q);
    res.json(await view(q));
  }));

  // insert right after the current song
  app.post('/queue/:qid/playnext', wrap(async (req, res) => {
    const id = req.body?.song_id;
    if (!id || !(await okSong(id))) return res.status(404).json({ error: 'song not found' });
    const q = await loadQ(req.params.qid);
    if (!q.items.length) { q.items = [id]; q.index = 0; }
    else {
      const cur = q.items[q.index];
      q.items.splice(q.index + 1, 0, id);
      if (q.original) q.original.splice(Math.max(0, q.original.indexOf(cur)) + 1, 0, id);
    }
    await saveQ(q);
    res.json(await view(q));
  }));

  app.post('/queue/:qid/next', wrap(async (req, res) => {
    const q = await loadQ(req.params.qid);
    if (q.index + 1 >= q.items.length) return res.json({ ...(await view(q)), ended: true });
    q.index++;
    await saveQ(q);
    res.json(await view(q));
  }));

  app.post('/queue/:qid/prev', wrap(async (req, res) => {
    const q = await loadQ(req.params.qid);
    q.index = Math.max(0, q.index - 1);
    await saveQ(q);
    res.json(await view(q));
  }));

  // body: { on?: boolean } - omitted = toggle
  app.post('/queue/:qid/shuffle', wrap(async (req, res) => {
    const q = await loadQ(req.params.qid);
    const on = typeof req.body?.on === 'boolean' ? req.body.on : !q.shuffle;
    if (on && !q.shuffle) shuffleUpcoming(q);
    else if (!on && q.shuffle) unshuffle(q);
    await saveQ(q);
    res.json(await view(q));
  }));

  // remove by absolute position (see index / up_next)
  app.delete('/queue/:qid/:pos', wrap(async (req, res) => {
    const pos = parseInt(req.params.pos, 10);
    const q = await loadQ(req.params.qid);
    if (!(pos >= 0 && pos < q.items.length)) return res.status(404).json({ error: 'position not in queue' });
    const [rm] = q.items.splice(pos, 1);
    if (q.original) { const i = q.original.indexOf(rm); if (i >= 0) q.original.splice(i, 1); }
    if (pos < q.index) q.index--;
    q.index = Math.min(q.index, Math.max(0, q.items.length - 1));
    await saveQ(q);
    res.json(await view(q));
  }));

  app.delete('/queue/:qid', wrap(async (req, res) => {
    await queues.deleteOne({ _id: req.params.qid });
    res.json({ cleared: true });
  }));

  const port = process.env.PORT || 3000;
  // short links: /<code>.<ext> -> the file on Hugging Face (keep this last so it never shadows other routes)
  app.get(/^\/([a-z0-9]{6})(\.[a-z0-9]+)?$/, wrap(async (req, res) => {
    const code = req.params[0];
    const toHf = async () => {
      const f = await hfFiles.findOne({ short_code: code }, { projection: { hf_url: 1 } });
      if (!f) return false;
      res.set('Cache-Control', 'public, max-age=86400');
      res.redirect(302, f.hf_url);
      return true;
    };
    if (await toHf()) return;
    const st = await stagedFiles.findOne({ short_code: code }, { projection: { file_name: 1 } });   // not on HF yet: serve the staged copy from Railway (range requests work)
    if (!st) return res.status(404).json({ error: 'file not found' });
    res.sendFile(path.join(STAGE_DIR, st.file_name), { cacheControl: false, headers: { 'Cache-Control': 'public, max-age=86400' } }, async err => {
      if (!err || res.headersSent) return;
      if (!(await toHf())) res.status(404).json({ error: 'file not found' });   // it was just flushed to HF, or the file is gone
    });
  }));

  app.listen(port, () => console.log(`api on :${port}`));
}

// ---------- helpers ----------
async function genSongId() {
  for (;;) {
    const id = crypto.randomBytes(6).toString('base64url'); // 8 chars
    if (!(await songs.findOne({ song_id: id }, { projection: { _id: 1 } }))) return id;
  }
}

// ---------- durable job line ----------
// Every audio message is written to Mongo (collection "jobs") BEFORE anything is processed, then a single worker takes them one at a time, oldest first.
// Nothing lives only in memory: a crash/restart, a hung upload or a failed attempt just puts the job back in line. A song is only given up on after JOB_MAX_ATTEMPTS tries,
// and then the chat is told. A 10s poller is the safety net that also wakes retries and rescues jobs stuck in "processing".
const JOB_MAX_ATTEMPTS = 4, JOB_TIMEOUT_MS = 10 * 60 * 1000, DAY = 86400000;
const withTimeout = (p, ms, label) => { let t; return Promise.race([p, new Promise((_, rej) => { t = setTimeout(() => rej(new Error(`${label} timed out after ${Math.round(ms / 1000)}s`)), ms); })]).finally(() => clearTimeout(t)); };
const jobCtx = chat => ({ chat, telegram: bot.telegram, reply: (text, extra) => bot.telegram.sendMessage(chat.id, text, extra) });   // no live update needed, so jobs survive restarts
let jobSeq = 0, activeWorkers = 0;
const WORKERS = 2;

async function enqueueAudio({ from, chat, message_id }, a, manual = false) {
  const now = Date.now();
  const job = {
    _id: `${chat.id}:${message_id}:${a.file_unique_id}${manual ? ':m' + now : ''}`,
    status: 'pending', attempts: 0, manual,
    order: now * 1000 + (jobSeq++ % 1000),   // arrival order, even for messages that land in the same millisecond
    created_at: new Date(now), retry_at: new Date(now),
    a, message_id,
    from: { id: from.id, first_name: from.first_name || null, last_name: from.last_name || null, username: from.username || null },
    chat: { id: chat.id, title: chat.title || null, type: chat.type },
  };
  for (let i = 0; ; i++) {
    try { await jobs.insertOne(job); break; }
    catch (e) {
      if (e?.code === 11000) { log(`job ${job._id} already in line`); return; }
      if (i >= 4) throw e;
      await sleep(500 * 2 ** i);
    }
  }
  log(`job ${job._id} queued (${a.file_name || a.title || a.file_unique_id})`);
  bot.telegram.setMessageReaction(chat.id, message_id, [{ type: 'emoji', emoji: '👍' }])
    .catch(e => log(`ack reaction failed: ${e.description || e.message}`));
  pump();
}

async function runJob(job) {
  const final = job.attempts >= JOB_MAX_ATTEMPTS, ctx = jobCtx(job.chat);
  log(`job ${job._id} start attempt ${job.attempts}/${JOB_MAX_ATTEMPTS}`);
  try {
    await withTimeout(processAudio(ctx, job.a, { from: job.from, chat: job.chat, message_id: job.message_id }, job.manual, final), JOB_TIMEOUT_MS, 'job');
    await jobs.updateOne({ _id: job._id }, { $set: { status: 'done', done_at: new Date(), expire_at: new Date(Date.now() + 3 * DAY) } });
    log(`job ${job._id} done`);
  } catch (e) {
    const msg = e?.message || String(e);
    console.error(`[${new Date().toISOString()}] [audio] job ${job._id} attempt ${job.attempts} failed:`, e?.stack || msg);
    try {
      if (final) {
        await jobs.updateOne({ _id: job._id }, { $set: { status: 'failed', error: msg, expire_at: new Date(Date.now() + 14 * DAY) } });
        await clearReact(job.chat.id, job.message_id);
        await sayAuto(ctx, job.chat, `⚠️ Could not save this song after ${job.attempts} tries: ${msg}`, job.message_id);
      } else {
        const wait = Math.min(60000, 3000 * 2 ** (job.attempts - 1));
        await jobs.updateOne({ _id: job._id }, { $set: { status: 'pending', error: msg, retry_at: new Date(Date.now() + wait) } });
        log(`job ${job._id} will retry in ${Math.round(wait / 1000)}s`);
      }
    } catch (e2) { console.error(`[${new Date().toISOString()}] [audio] could not update job ${job._id} (the poller will recover it):`, e2.message); }
  }
}

// WORKERS workers, oldest job first; findOneAndUpdate is atomic so two workers never take the same job.
// pump() just tops the pool up; the 10s poller is the safety net if a worker exits right as a job lands
function pump() {
  while (activeWorkers < WORKERS) {
    activeWorkers++;
    (async () => {
      try {
        for (;;) {
          const job = await jobs.findOneAndUpdate(
            { status: 'pending', retry_at: { $lte: new Date() } },
            { $set: { status: 'processing', started_at: new Date() }, $inc: { attempts: 1 } },
            { sort: { order: 1 }, returnDocument: 'after' });
          if (!job) break;
          await runJob(job);
        }
      } catch (e) { console.error(`[${new Date().toISOString()}] [audio] pump error (poller will retry):`, e.message); }
      finally { activeWorkers--; }
    })();
  }
}

// ---------- Hugging Face uploader (ported from uploader.py) ----------
// HF_BACKUP_ACCOUNTS="user1:hf_token1,user2:hf_token2"
const hfAccounts = () => [
  { username: HF_USERNAME, token: HF_TOKEN },
  ...HF_BACKUP_ACCOUNTS.split(',').map(x => x.trim()).filter(Boolean).map(x => {
    const i = x.indexOf(':'); return { username: x.slice(0, i), token: x.slice(i + 1) };
  }),
].filter(a => a.username && a.token);

const hfStorage = (username) => hfSettings.findOneAndUpdate(
  { _id: `account_storage_${username}` },
  { $setOnInsert: { username, total_size: 0, datasets: [] } },
  { upsert: true, returnDocument: 'after' });

async function shortCode(len = 6) {
  const chars = 'abcdefghijklmnopqrstuvwxyz0123456789';
  for (;;) {
    const code = Array.from(crypto.randomBytes(len), b => chars[b % chars.length]).join('');
    if (!(await hfFiles.findOne({ short_code: code }, { projection: { _id: 1 } })) && !(await stagedFiles.findOne({ short_code: code }, { projection: { _id: 1 } }))) return code;
  }
}

// HF caps commits per repo (128/hour). A repo that hits the cap is skipped until its cooldown ends, uploads go to another dataset meanwhile.
const repoCooldown = new Map();   // "user/dataset" -> timestamp when it can be used again
const repoCooling = r => (repoCooldown.get(r) || 0) > Date.now();
function repoCool(r, msg) {
  const m = /in (\d+) minutes?/i.exec(msg || ''), mins = m ? Number(m[1]) + 1 : 10;
  repoCooldown.set(r, Date.now() + mins * 60000);
  log(`hf ${r}: rate limited, skipping it for ${mins} min`);
}

async function ensureDataset(repoName, token) {
  const repo = { type: 'dataset', name: repoName };
  if (await hub.repoExists({ repo, accessToken: token })) return;
  await hub.createRepo({
    repo, accessToken: token, visibility: 'public', license: 'mit',
    files: [{ path: 'README.md', content: new Blob([`---\nlicense: mit\n---\n\n# File Storage Dataset\n\nFiles live in \`${DEST_DIR}/\`.\n`]) }],
  });
}

// uploadToHost stages the file on Railway and returns its short link right away (served from Railway until it reaches Hugging Face).
// returns { short_url, code, hf_url: null }
async function uploadToHost(buf, filename, mime) {
  const ext = path.extname(filename).toLowerCase();
  let code;
  for (let i = 0; ; i++) {
    code = await shortCode();
    try {
      await stagedFiles.insertOne({ short_code: code, ext, file_name: `${code}${ext}`, original_path: filename, mime: mime || null, size: buf.length, created_at: new Date() });
      break;
    } catch (e) { if (e?.code === 11000 && i < 5) continue; throw e; }
  }
  try { await fsp.writeFile(path.join(STAGE_DIR, `${code}${ext}`), buf); }
  catch (e) {
    await stagedFiles.deleteOne({ short_code: code }).catch(() => {});
    console.error(`[${new Date().toISOString()}] [audio] stage write failed:`, e.message);
    throw new Error('upload failed, try again later');
  }
  log(`staged ${code}${ext} size=${mb(buf.length)} (${filename})`);
  setImmediate(() => maybeFlush().catch(e => console.error(`[${new Date().toISOString()}] [audio] flush error:`, e.message)));
  return { short_url: `${SHORT_URL_BASE}${code}${ext}`, code, hf_url: null };
}

// pushes staged files to Hugging Face as one commit once BATCH_SIZE are waiting (or the oldest has waited BATCH_MAX_AGE_MS)
let flushing = false;
async function flushDue() {
  const n = await stagedFiles.countDocuments();
  if (!n) return false;
  if (n >= BATCH_SIZE) return true;
  const oldest = await stagedFiles.find().sort({ created_at: 1 }).limit(1).next();
  return !!oldest && Date.now() - oldest.created_at.getTime() >= BATCH_MAX_AGE_MS;
}
async function maybeFlush() {
  if (flushing) return;
  flushing = true;
  try {
    while (await flushDue()) {
      const batch = await stagedFiles.find().sort({ created_at: 1 }).limit(BATCH_SIZE).toArray();
      if (!batch.length || !(await flushBatch(batch))) break;   // on failure leave everything staged, the 30s timer tries again
    }
  } finally { flushing = false; }
}

async function flushBatch(batch) {
  const items = [];
  for (const d of batch) {
    try { items.push({ d, p: path.join(STAGE_DIR, d.file_name), buf: await fsp.readFile(path.join(STAGE_DIR, d.file_name)) }); }
    catch { console.warn(`[${new Date().toISOString()}] [audio] staged file missing on disk, dropping ${d.file_name}`); await stagedFiles.deleteOne({ _id: d._id }).catch(() => {}); }
  }
  if (!items.length) return true;
  const size = items.reduce((a, x) => a + x.buf.length, 0);
  const errors = [];

  for (const { username, token } of hfAccounts()) {
    const skip = new Set();
    for (let n = 0; n < 4; n++) {   // each retry moves to another dataset when the current one is commit-rate-limited
    let repoName = null;
    try {
      const st = await hfStorage(username);
      if (st.total_size + size > MAX_ACCOUNT_STORAGE) { errors.push(`${username}: full`); log(`hf ${username}: account full, trying next`); break; }

      // newest usable dataset (room left, not rate-limited), else any other usable one, else a fresh one
      const fits = d => d.size + size <= MAX_DATASET_SIZE && !skip.has(d.name) && !repoCooling(`${username}/${d.name}`);
      const last = st.datasets[st.datasets.length - 1];
      let name = last && fits(last) ? last.name : (st.datasets.slice().reverse().find(fits)?.name || null);
      if (!name) {
        do name = `file-storage-${1000 + crypto.randomInt(9000)}`; while (st.datasets.some(d => d.name === name));
      }
      repoName = `${username}/${name}`;
      log(`hf batch ${repoName} files=${items.length} size=${mb(size)}${last && last.name === name ? '' : ' (new dataset)'}`);
      await ensureDataset(repoName, token);

      await hub.uploadFiles({
        repo: { type: 'dataset', name: repoName }, accessToken: token,
        files: items.map(x => ({ path: `${DEST_DIR}/${x.d.file_name}`, content: new Blob([x.buf], { type: x.d.mime || 'application/octet-stream' }) })),
        commitTitle: `Upload ${items.length} file(s)`,
      });

      // record every file in the shared collection BEFORE removing the staged copy so the short link never 404s in between
      const docs = items.map(x => ({ short_code: x.d.short_code, file_name: x.d.file_name, original_path: x.d.original_path, hf_url: `https://huggingface.co/datasets/${repoName}/resolve/main/${DEST_DIR}/${x.d.file_name}`, dataset: name, size: x.buf.length, uploader: username }));
      await hfFiles.insertMany(docs, { ordered: false }).catch(e => { if (e.code !== 11000) throw e; });

      const id = `account_storage_${username}`;
      const r = await hfSettings.updateOne({ _id: id, 'datasets.name': name }, { $inc: { 'datasets.$.size': size, total_size: size } });
      if (!r.matchedCount) await hfSettings.updateOne({ _id: id }, { $inc: { total_size: size }, $push: { datasets: { name, size } } });

      await stagedFiles.deleteMany({ _id: { $in: items.map(x => x.d._id) } });
      await Promise.all(items.map(x => fsp.unlink(x.p).catch(() => {})));
      log(`hf ok ${repoName} files=${items.length} total_used=${mb(st.total_size + size)}`);
      return true;
    } catch (e) {
      errors.push(`${username}: ${e.message}`);
      console.warn(`[${new Date().toISOString()}] [audio] hf FAILED ${username}: ${String(e.message).slice(0, 200)}`);
      if (repoName && /rate limit|\b429\b/i.test(e.message)) { repoCool(repoName, e.message); skip.add(repoName.split('/')[1]); continue; }
      break;
    }
    }
  }
  console.error(`[${new Date().toISOString()}] [audio] batch upload failed, ${items.length} file(s) stay staged: ${errors.join('; ').slice(0, 500) || 'none configured'}`);
  return false;
}

// reply that never throws but always logs why it failed; retries without reply_parameters (deleted msg / topic quirks)
// automatic status messages (saved / failed): shown in private chats only, groups stay quiet (logged instead)
const isGroupChat = c => c?.type === 'group' || c?.type === 'supergroup';
async function sayAuto(ctx, chat, text, replyTo) {
  if (isGroupChat(chat)) return log(`quiet in group chat=${chat.id}: ${text}`);
  return say(ctx, text, replyTo);
}
async function say(ctx, text, replyTo) {
  const chatId = ctx.chat?.id;
  try {
    return await ctx.reply(text, replyTo ? { reply_parameters: { message_id: replyTo, allow_sending_without_reply: true } } : undefined);
  } catch (e) {
    console.error(`[${new Date().toISOString()}] [audio] REPLY FAILED chat=${chatId}: ${e.description || e.message}`);
    if (replyTo) {
      try { return await ctx.reply(text); }
      catch (e2) { console.error(`[${new Date().toISOString()}] [audio] REPLY RETRY FAILED chat=${chatId}: ${e2.description || e2.message}`); }
    }
  }
}

// react to the song file instead of replying. Telegram only allows its fixed reaction set (and whatever the group enables),
// so try REACT_EMOJI first and fall back to the next one; remember what works so we don't retry bad ones
const REACT_TRY = [process.env.REACT_EMOJI || '🔥', '👍'];
const badReact = new Set();
const clearReact = (chatId, messageId) => bot.telegram.setMessageReaction(chatId, messageId, []).catch(() => {});
async function react(ctx, chatId, messageId, tries = REACT_TRY) {
  for (const emoji of tries) {
    if (badReact.has(emoji)) continue;
    try {
      await ctx.telegram.setMessageReaction(chatId, messageId, [{ type: 'emoji', emoji }]);
      log(`reacted ${emoji} chat=${chatId} msg=${messageId}`);
      return true;
    } catch (e) {
      const d = e.description || e.message;
      console.error(`[${new Date().toISOString()}] [audio] REACTION FAILED ${emoji} chat=${chatId}: ${d}`);
      if (/REACTION_INVALID/i.test(d)) badReact.add(emoji); // not an allowed reaction, don't try again
      else return false;                                     // permissions/other error: no point trying another emoji
    }
  }
  return false;
}

const extOf = (name, mime) =>
  (name && name.includes('.') ? name.split('.').pop() : (mime || '').split('/').pop() || 'mp3')
    .toLowerCase().replace(/[^a-z0-9]/g, '') || 'mp3';

const AUDIO_EXT = /\.(mp3|m4a|aac|flac|wav|ogg|oga|opus|wma|aiff?|alac|amr)$/i;
function getAudio(msg) {
  if (msg.audio) return msg.audio;
  const d = msg.document;   // sent "as file": mime is often application/octet-stream, so fall back to the extension
  if (d && (d.mime_type?.startsWith('audio/') || AUDIO_EXT.test(d.file_name || ''))) return d;
  return null;
}

// ---------- core ----------
async function processAudio(ctx, a, msg = ctx.message, manual = false, final = true) {
  const { from, chat, message_id } = msg;

  const t0 = Date.now();
  log(`start msg=${message_id} chat=${chat.id} "${chat.title || chat.type}" user=${who(from)} file="${a.file_name || a.title || '?'}" size=${mb(a.file_size)} mime=${a.mime_type || '?'}`);
  if (a.file_size && a.file_size > 20 * 1024 * 1024) log('WARN file > 20MB, Telegram Bot API cannot download it');
  const dupe = await songs.findOne({ file_unique_id: a.file_unique_id, chat_id: chat.id });
  if (dupe) {
    log(`skip duplicate file_unique_id=${a.file_unique_id} in chat=${chat.id} (song_id=${dupe.song_id})`);
    // ❌ isn't in Telegram's default reaction set, so fall back to 👎 unless the group has ❌ enabled
    if (!(await react(ctx, chat.id, message_id, ['❌', '👎']))) await clearReact(chat.id, message_id);
    return;
  }

  const song = {
    chat_id: chat.id,
    message_id,
    user_id: from.id,
    file_id: a.file_id,
    file_unique_id: a.file_unique_id,
    file_name: a.file_name || null,
    mime_type: a.mime_type || null,
    file_size: a.file_size || null,
    duration: a.duration || null,
    title: a.title || null,
    artist: a.performer || null,
    tg_thumb_file_id: (a.thumbnail || a.thumb)?.file_id || null,
    upload_url: null, hf_url: null, upload_code: null,
    cover_url: null,
    album: null, album_artist: null, year: null, genre: null,
    release_date: null, label: null, explicit: null, deezer_meta: false,
    track_no: null, bitrate: null, sample_rate: null, codec: null,
    uploaded: false, upload_error: null,
    song_id: await genSongId(),
    listens: 0,
    poster_url: null, deezer_id: null, image_url: null,
    created_at: new Date(),
  };

  try {
    const link = await ctx.telegram.getFileLink(a.file_id); // throws if > 20MB
    const dl = await ft(link, 180000);
    if (!dl.ok) throw new Error(`telegram download failed ${dl.status}`);
    const buf = Buffer.from(await dl.arrayBuffer());
    log(`downloaded ${mb(buf.length)} in ${Date.now() - t0}ms`);
    const ext = extOf(a.file_name, a.mime_type);

    // metadata from the actual file
    try {
      const meta = await mm.parseBuffer(buf, { mimeType: a.mime_type?.startsWith('audio/') ? a.mime_type : undefined }, { duration: true });
      const c = meta.common, f = meta.format;
      song.title = c.title || song.title;
      song.artist = c.artist || song.artist;
      song.album = c.album || null;
      song.album_artist = c.albumartist || null;
      song.year = c.year || null;
      song.genre = c.genre || null;
      song.track_no = c.track?.no || null;
      song.bitrate = f.bitrate ? Math.round(f.bitrate) : null;
      song.sample_rate = f.sampleRate || null;
      song.codec = f.codec || f.container || null;
      song.duration = f.duration ? Math.round(f.duration) : song.duration;
      log(`meta title="${song.title}" artist="${song.artist}" album="${song.album}" codec=${song.codec} bitrate=${song.bitrate} dur=${song.duration}s cover=${!!c.picture?.length}`);

      // embedded cover -> upload it too
      const pic = mm.selectCover(c.picture);
      if (pic) {
        const cExt = extOf(null, pic.format) === 'jpeg' ? 'jpg' : extOf(null, pic.format);
        const cr = await uploadToHost(Buffer.from(pic.data), `${a.file_unique_id}_cover.${cExt}`, pic.format);
        song.cover_url = cr.short_url;
        log(`cover uploaded ${cr.short_url}`);
      }
    } catch (e) { console.warn(`[${new Date().toISOString()}] [audio] meta/cover step failed:`, e.message); }

    // better-quality poster from Deezer (title + artist search, regex-matched)
    try {
      const p = await findPosterSmart({
        title: song.title || (a.file_name || '').replace(/\.[^.]+$/, ''),
        artist: song.artist,
        duration: song.duration,
      });
      if (p) {
        applyDeezerMeta(song, p);
        log(`deezer meta deezer=${p.deezerId} genre=${JSON.stringify(song.genre)} released=${song.release_date} label="${song.label || ''}"`);
        if (p.buf) {
          const pr = await uploadToHost(p.buf, `${a.file_unique_id}_poster.jpg`, 'image/jpeg');
          song.poster_url = pr.short_url;
          log(`poster uploaded deezer=${p.deezerId} ${pr.short_url}`);
        }
      } else log('poster: no deezer match');
    } catch (e) { console.warn(`[${new Date().toISOString()}] [audio] poster failed:`, e.message); }

    // last resort: Telegram's own thumbnail of the audio message
    if (!song.poster_url && !song.cover_url && song.tg_thumb_file_id) {
      try {
        const tl = await ctx.telegram.getFileLink(song.tg_thumb_file_id);
        const tr = await ft(tl);
        if (tr.ok) {
          const tb = Buffer.from(await tr.arrayBuffer());
          const up = await uploadToHost(tb, `${a.file_unique_id}_thumb.jpg`, 'image/jpeg');
          song.cover_url = up.short_url;
          log(`telegram thumbnail used as cover ${up.short_url}`);
        }
      } catch (e) { console.warn(`[${new Date().toISOString()}] [audio] thumb fallback failed:`, e.message); }
    }

    // upload the audio
    const r = await uploadToHost(buf, `${a.file_unique_id}.${ext}`, a.mime_type || 'audio/mpeg');
    song.upload_url = r.short_url;
    song.upload_code = r.code;
    song.hf_url = r.hf_url || null;
    song.uploaded = true;
    log(`audio uploaded ${song.upload_url}`);
  } catch (e) {
    // not the last attempt and not a permanent problem (Telegram's 20MB limit): let the job queue retry instead of saving a broken row
    if (!final && !/too big/i.test(e.description || e.message || '')) throw e;
    song.upload_error = e.message;
    console.error(`[${new Date().toISOString()}] [audio] PROCESS ERROR msg=${message_id} user=${who(from)}:`, e.stack || e.message);
  }

  if (!song.title) song.title = (a.file_name || 'Unknown').replace(/\.[^.]+$/, '');

  song.image_url = song.poster_url || song.cover_url;
  try { await songs.insertOne(song); }
  catch (e) { if (e?.code === 11000) { log(`already saved (duplicate insert) file_unique_id=${a.file_unique_id} chat=${chat.id}`); return; } throw e; }
  await users.updateOne(
    { _id: from.id },
    {
      $set: {
        first_name: from.first_name || null,
        last_name: from.last_name || null,
        username: from.username || null,
        updated_at: new Date(),
      },
      $setOnInsert: { first_seen: new Date() },
      $inc: { song_count: 1 },
    },
    { upsert: true }
  );

  log(`saved song_id=${song.song_id} uploaded=${song.uploaded} user=${who(from)} playlist=/playlist/${from.id} total_time=${Date.now() - t0}ms`);

  const label = `${song.title}${song.artist ? ' — ' + song.artist : ''}`;
  if (song.uploaded) {
    if (!(await react(ctx, chat.id, message_id))) await sayAuto(ctx, chat, `✅ Saved: ${label}`, message_id); // fall back to a reply only if reacting is impossible here
  } else {
    await clearReact(chat.id, message_id);
    await sayAuto(ctx, chat, `⚠️ Logged (not uploaded: ${song.upload_error}): ${label}`, message_id);
  }
}

// ---------- Spotify import ----------
// New capsule -> "Import from Spotify". A playlist link becomes one durable item per track (collection spotify_import_items, first IMPORT_LIMIT only),
// worked by IMPORT_WORKERS workers the same way as the audio job line: everything is in Mongo before work starts, a restart / hang / failure puts the item
// back in line (with backoff) and an item is only given up on after IMPORT_MAX_ATTEMPTS tries. The frontend polls GET /me/imports/:id, so progress survives reloads.
// Per track: prexzyapis returns a fresh signed download_url -> download (length + duration verified) -> Hugging Face -> song row -> capsule row at the playlist position.
const IMPORT_LIMIT = 50, IMPORT_MAX_ATTEMPTS = 5, IMPORT_WORKERS = 2, IMPORT_ITEM_TIMEOUT_MS = 8 * 60 * 1000;
const IMPORT_API = process.env.SPOTIFY_DL_API || 'https://prexzyapis.com/download/spotify';
const IMPORT_MIN_BYTES = 100 * 1024, IMPORT_MAX_BYTES = 80 * 1024 ** 2;
const SP_UA = 'Mozilla/5.0 (Linux; Android 13) AppleWebKit/537.36 Chrome/120 Mobile Safari/537.36';
const is11000 = e => e?.code === 11000;
const retry = async (fn, tries, base = 1000) => { for (let i = 1; ; i++) { try { return await fn(i); } catch (e) { if (i >= tries) throw e; await sleep(base * 2 ** (i - 1)); } } };

// ---- reading the playlist (no Spotify API key: the page ships its first 30 tracks as base64 JSON, the embed page up to 100) ----
const spPlaylistId = u => String(u || '').trim().match(/^https?:\/\/open\.spotify\.com\/(?:intl-[a-z-]+\/)?playlist\/([A-Za-z0-9]{10,40})/i)?.[1] || null;   // host is pinned, so a user can't point the server elsewhere
const spTrackId = uri => String(uri || '').match(/track[:/]([A-Za-z0-9]{10,40})/)?.[1] || null;
async function spGet(url) {
  const r = await fetch(url, { headers: { 'User-Agent': SP_UA, 'Accept-Language': 'en' }, signal: AbortSignal.timeout(20000) });
  if (!r.ok) throw new Error(`Spotify HTTP ${r.status}`);
  return r.text();
}
function spParsePage(html, id) {
  const b64 = html.match(/id="initialState"[^>]*>([^<]+)</)?.[1];
  if (!b64) return null;
  const pl = JSON.parse(Buffer.from(b64, 'base64').toString('utf8')).entities?.items?.[`spotify:playlist:${id}`];
  if (!pl) return null;
  const tracks = [];
  for (const i of pl.content?.items || []) {
    const d = i.itemV2?.data, tid = d?.__typename === 'Track' ? spTrackId(d.uri) : null;
    if (!tid) continue;
    const imgs = d.albumOfTrack?.coverArt?.sources || [];
    tracks.push({
      id: tid, title: d.name,
      artist: (d.artists?.items || []).map(a => a.profile?.name).filter(Boolean).join(', '),
      image: imgs.reduce((a, b) => ((b.width || 0) > (a?.width || 0) ? b : a), null)?.url || null,
    });
  }
  return { name: pl.name, total: pl.content?.totalCount ?? tracks.length, tracks };
}
function spParseEmbed(html) {
  const raw = html.match(/<script id="__NEXT_DATA__"[^>]*>([^<]+)<\/script>/)?.[1];
  if (!raw) return [];
  return (JSON.parse(raw).props?.pageProps?.state?.data?.entity?.trackList || [])
    .map(t => ({ id: spTrackId(t.uri), title: t.title, artist: String(t.subtitle || '').replace(/\u00a0/g, ' '), image: null }))
    .filter(t => t.id);
}
// first IMPORT_LIMIT distinct tracks, in playlist order
async function spFetchPlaylist(id) {
  const page = await retry(async () => {
    const p = spParsePage(await spGet(`https://open.spotify.com/playlist/${id}`), id);
    if (!p) throw new Error('playlist page not readable');
    return p;
  }, 3);
  let tracks = page.tracks;
  if (tracks.length < Math.min(IMPORT_LIMIT, page.total)) {   // the page only carries the first 30
    try {
      const emb = await retry(async () => {
        const e = spParseEmbed(await spGet(`https://open.spotify.com/embed/playlist/${id}`));
        if (!e.length) throw new Error('embed has no tracks');
        return e;
      }, 2);
      if (emb.length > tracks.length) { const img = new Map(tracks.map(t => [t.id, t.image])); tracks = emb.map(t => ({ ...t, image: img.get(t.id) || null })); }
    } catch (e) { log(`spotify embed fallback failed: ${e.message}`); }
  }
  tracks = [...new Map(tracks.map(t => [t.id, t])).values()].slice(0, IMPORT_LIMIT);
  if (!tracks.length) throw new Error('no songs found');
  return { name: page.name, total: page.total, tracks };
}

// ---- one track: resolve -> download -> verify ----
async function spResolve(trackId) {
  return retry(async () => {
    const r = await fetch(`${IMPORT_API}?url=${encodeURIComponent(`https://open.spotify.com/track/${trackId}`)}`, { headers: { 'User-Agent': SP_UA, Accept: 'application/json' }, signal: AbortSignal.timeout(45000) });
    const j = await r.json().catch(() => null), d = j?.data;
    if (!r.ok || j?.status !== true || !d?.download_url) throw new Error(`download api: ${j?.message || j?.error || `HTTP ${r.status}`}`);
    if (!/^https:\/\//i.test(d.download_url)) throw new Error('download api: bad download_url');
    return d;
  }, 2, 1500);
}
async function spDownload(url) {
  const r = await fetch(url, { headers: { 'User-Agent': SP_UA }, signal: AbortSignal.timeout(180000) });
  if (!r.ok) throw new Error(`download HTTP ${r.status}`);
  const len = Number(r.headers.get('content-length')) || 0;
  if (len > IMPORT_MAX_BYTES) throw new Error(`file too large (${mb(len)})`);
  const buf = Buffer.from(await r.arrayBuffer());
  if (len && !r.headers.get('content-encoding') && buf.length !== len) throw new Error(`download cut short (${buf.length}/${len} bytes)`);
  if (buf.length < IMPORT_MIN_BYTES || buf.length > IMPORT_MAX_BYTES || buf[0] === 0x7b || buf[0] === 0x3c) throw new Error(`download is not audio (${buf.length} bytes)`);   // { or < = a JSON / HTML error page
  return buf;
}
async function spCover(url, trackId) {
  if (!url) return null;
  const r = await ft(url);
  if (!r.ok) return null;
  const buf = Buffer.from(await r.arrayBuffer()), t = sniffImage(buf);
  if (!t || buf.length < 3000) return null;
  return uploadToHost(buf, `sp_${trackId}_cover${t.ext}`, t.mime);
}

// returns { song_id, reused }. Throws on any failure: nothing half-saved is ever written (the song row is the last step), so a retry starts clean.
async function importTrack(it, ctx) {
  const alive = () => { if (ctx.dead) throw new Error('timed out'); };
  if (!(await capsules.findOne({ _id: it.capsule_id, user_id: it.user_id }, { projection: { _id: 1 } }))) throw Object.assign(new Error('capsule was deleted'), { cancel: true });
  const key = `sp:${it.track_id}`, find = () => songs.findOne({ chat_id: it.user_id, file_unique_id: key }, { projection: { song_id: 1 } });
  let song = await find(), reused = !!song;   // already in this library (earlier import, same track twice): don't download again

  if (!song) {
    const meta = await spResolve(it.track_id);
    alive();
    const ext = /^[a-z0-9]{2,4}$/.test(meta.format || '') ? meta.format : 'mp3', mime = ext === 'mp3' ? 'audio/mpeg' : `audio/${ext}`;
    const buf = await retry(() => spDownload(meta.download_url), 2, 2000);
    alive();

    let tags;
    try { tags = await mm.parseBuffer(buf, { mimeType: mime }, { duration: true }); }
    catch (e) { throw new Error(`downloaded file is not valid audio: ${e.message}`); }
    const c = tags.common, f = tags.format, want = meta.duration_ms ? meta.duration_ms / 1000 : 0;
    if (want && f.duration && f.duration < want - Math.max(5, want * 0.08)) throw new Error(`audio is ${Math.round(f.duration)}s, expected ${Math.round(want)}s (cut short)`);

    const title = meta.title || it.title || 'Unknown', artist = meta.artist || it.artist || null;
    const doc = {
      chat_id: it.user_id, message_id: null, user_id: it.user_id,
      file_id: null, file_unique_id: key,
      file_name: `${artist ? artist + ' - ' : ''}${title}.${ext}`.replace(/[\\/:*?"<>|]+/g, ''),
      mime_type: mime, file_size: buf.length,
      duration: Math.round(f.duration || want) || null,
      title, artist,
      tg_thumb_file_id: null,
      upload_url: null, hf_url: null, upload_code: null,
      cover_url: null,
      album: meta.album || c.album || null, album_artist: c.albumartist || null, year: c.year || null, genre: c.genre || null,
      release_date: null, label: null, explicit: null, deezer_meta: false,
      track_no: c.track?.no || null, bitrate: f.bitrate ? Math.round(f.bitrate) : null, sample_rate: f.sampleRate || null, codec: f.codec || f.container || null,
      uploaded: false, upload_error: null,
      song_id: await genSongId(),
      listens: 0,
      poster_url: null, deezer_id: null, image_url: null,
      source: 'spotify', spotify_id: it.track_id, spotify_url: it.spotify_url, import_id: it.import_id,
      created_at: new Date(),
    };

    try {   // Deezer poster + genre / release date / label, same as audio messages
      const p = await findPosterSmart({ title, artist, duration: doc.duration });
      if (p) {
        applyDeezerMeta(doc, p);
        if (p.buf) doc.poster_url = (await uploadToHost(p.buf, `sp_${it.track_id}_poster.jpg`, 'image/jpeg')).short_url;
      }
    } catch (e) { console.warn(`[${new Date().toISOString()}] [import] poster failed:`, e.message); }
    try { const cv = await spCover(it.image || meta.cover, it.track_id); if (cv) doc.cover_url = cv.short_url; }
    catch (e) { console.warn(`[${new Date().toISOString()}] [import] cover failed:`, e.message); }
    alive();

    const up = await retry(() => uploadToHost(buf, `sp_${it.track_id}.${ext}`, mime), 3, 2000);   // buffer is in hand, so retry the upload alone instead of downloading again
    doc.upload_url = up.short_url; doc.upload_code = up.code; doc.hf_url = up.hf_url || null; doc.uploaded = true;
    doc.image_url = doc.poster_url || doc.cover_url;
    alive();

    try {
      await songs.insertOne(doc);
      await users.updateOne({ _id: it.user_id }, { $set: { updated_at: new Date() }, $setOnInsert: { first_seen: new Date() }, $inc: { song_count: 1 } }, { upsert: true });
      song = doc;
    } catch (e) {
      if (!is11000(e)) throw e;   // a parallel attempt saved it first: use that row
      song = await find(); reused = true;
      if (!song) throw e;
    }
  }

  // capsule order = playlist order, whatever order the workers finish in
  await capSongs.insertOne({ capsule_id: it.capsule_id, user_id: it.user_id, song_id: song.song_id, pos: GAP * (it.idx + 1), added_at: new Date() })
    .catch(e => { if (!is11000(e)) throw e; });
  return { song_id: song.song_id, reused };
}

// ---- progress ----
const importCounts = items => items.reduce((c, x) => (c[x.status] = (c[x.status] || 0) + 1, c), {});
const importStatus = c => ((c.pending || 0) + (c.processing || 0) ? 'running' : c.cancelled ? 'cancelled' : c.failed ? (c.done ? 'partial' : 'failed') : 'done');

async function importView(im, withItems = true) {
  const items = await importItems.find({ import_id: im._id }).sort({ idx: 1 })
    .project({ idx: 1, track_id: 1, title: 1, artist: 1, image: 1, status: 1, attempts: 1, error: 1, reused: 1 }).toArray();
  const counts = importCounts(items);
  return {
    id: im._id, status: importStatus(counts),
    capsule_id: im.capsule_id, capsule_name: im.capsule_name, playlist_name: im.playlist_name, playlist_total: im.playlist_total,
    total: items.length, counts, created_at: im.created_at, finished_at: im.finished_at || null,
    job_url: `${BASE}/manage?import=${im._id}`,
    ...(withItems ? { items: items.map(({ _id, ...x }) => x) } : {}),
  };
}

// stored copy of the status (the API recomputes it live). Finished imports expire after a few days; running ones never do.
async function refreshImport(id) {
  const agg = await importItems.aggregate([{ $match: { import_id: id } }, { $group: { _id: '$status', n: { $sum: 1 } } }]).toArray();
  const c = Object.fromEntries(agg.map(x => [x._id, x.n])), status = importStatus(c), now = new Date();
  if (status === 'running') return imports.updateOne({ _id: id }, { $set: { status, counts: c, updated_at: now }, $unset: { expire_at: '', finished_at: '' } });
  const exp = new Date(Date.now() + (c.failed ? 14 : 3) * DAY);
  await Promise.all([
    imports.updateOne({ _id: id }, { $set: { status, counts: c, updated_at: now, finished_at: now, expire_at: exp } }),
    importItems.updateMany({ import_id: id }, { $set: { expire_at: exp } }),
  ]);
}

// ---- workers ----
async function runImportItem(it) {
  const ctx = { dead: false };
  log(`import ${it._id} start attempt ${it.attempts}/${IMPORT_MAX_ATTEMPTS} (${it.title} - ${it.artist})`);
  let set;
  try {
    const r = await withTimeout(importTrack(it, ctx), IMPORT_ITEM_TIMEOUT_MS, 'track');
    set = { status: 'done', song_id: r.song_id, reused: r.reused, error: null, done_at: new Date() };
    log(`import ${it._id} done song_id=${r.song_id}${r.reused ? ' (already in library)' : ''}`);
  } catch (e) {
    ctx.dead = true;   // a timed-out attempt stops at its next checkpoint instead of racing the retry
    const msg = (e?.message || String(e)).slice(0, 300);
    console.error(`[${new Date().toISOString()}] [import] ${it._id} attempt ${it.attempts} failed: ${msg}`);
    if (e?.cancel) set = { status: 'cancelled', error: msg };
    else if (it.attempts >= IMPORT_MAX_ATTEMPTS) set = { status: 'failed', error: msg };
    else set = { status: 'pending', error: msg, retry_at: new Date(Date.now() + Math.min(120000, 5000 * 3 ** (it.attempts - 1))) };   // 5s, 15s, 45s, 2min
  }
  try {
    await importItems.updateOne({ _id: it._id }, { $set: set });
    if (set.status === 'cancelled') await importItems.updateMany({ import_id: it.import_id, status: 'pending' }, { $set: { status: 'cancelled', error: set.error } });
    await refreshImport(it.import_id);
  } catch (e2) { console.error(`[${new Date().toISOString()}] [import] could not update ${it._id} (the poller will recover it):`, e2.message); }
}

let importWorkers = 0;
function pumpImports() {
  while (importWorkers < IMPORT_WORKERS) {
    importWorkers++;
    (async () => {
      try {
        for (;;) {
          const it = await importItems.findOneAndUpdate(
            { status: 'pending', retry_at: { $lte: new Date() } },
            { $set: { status: 'processing', started_at: new Date() }, $inc: { attempts: 1 } },
            { sort: { order: 1 }, returnDocument: 'after' });
          if (!it) break;
          await runImportItem(it);
        }
      } catch (e) { console.error(`[${new Date().toISOString()}] [import] pump error (poller will retry):`, e.message); }
      finally { importWorkers--; }
    })();
  }
}

// every 10s: rescue items stuck in "processing", fix any stored status that lost a race, wake due retries
async function importTick() {
  try {
    await importItems.updateMany({ status: 'processing', started_at: { $lt: new Date(Date.now() - IMPORT_ITEM_TIMEOUT_MS - 60000) } }, { $set: { status: 'pending', retry_at: new Date() } });
    for (const s of await imports.find({ status: 'running' }).limit(20).project({ _id: 1 }).toArray()) await refreshImport(s._id);
  } catch {}
  pumpImports();
}

// ---------- handlers ----------
bot.use((ctx, next) => {
  const t = ctx.message?.text || ctx.message?.caption || '';
  if (t.startsWith('/')) log(`update: "${t.split(/\s/)[0]}" chat=${ctx.chat?.id} (${ctx.chat?.type}) from=${who(ctx.from)}`);
  return next();
});

bot.command('top', async ctx => {
  const top = await users.find().sort({ song_count: -1 }).limit(10).toArray();
  if (!top.length) return ctx.reply('No songs yet.');
  ctx.reply(top.map((u, i) =>
    `${i + 1}. ${u.username ? '@' + u.username : u.first_name} — ${u.song_count}`).join('\n'));
});

// opens manage.html as a Mini App; that is what signs the owner in (initData -> /auth/tg)
bot.command('manage', ctx => {
  if (ctx.chat.type !== 'private') return ctx.reply('Send /manage to me in a private chat.');
  if (!BASE.startsWith('https://')) return ctx.reply('BASE_URL must be https for Mini Apps.');
  return ctx.reply('Manage your playlist and capsules:', Markup.inlineKeyboard([Markup.button.webApp('Open manager', `${BASE}/manage`)]));
});

bot.command('me', async ctx => {
  const u = await users.findOne({ _id: ctx.from.id });
  ctx.reply(`You've shared ${u?.song_count || 0} songs.`);
});

// ---------- /profile ----------
const fmtTime = s => { s = Math.round(s || 0); const h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60); return h ? `${h}h ${m}m` : m ? `${m}m ${s % 60}s` : `${s}s`; };
const nf = n => Number(n || 0).toLocaleString('en-US');
const dispName = u => [u.first_name, u.last_name].filter(Boolean).join(' ') || (u.username ? '@' + u.username : `User ${u._id ?? u.id}`);
const MINIAPP_NAME = process.env.MINIAPP_NAME || 'playlist';   // short name of the Mini App in BotFather (t.me/<bot>/<MINIAPP_NAME>)

// who: a replied-to user, a text mention, @username / numeric id after the command, else the sender
async function profileTarget(ctx) {
  const m = ctx.message, rep = m.reply_to_message?.from;
  if (rep && !rep.is_bot) return { id: rep.id, tg: rep };
  const ent = (m.entities || []).find(e => e.type === 'text_mention' && e.user);
  if (ent) return { id: ent.user.id, tg: ent.user };
  const arg = (m.text || '').replace(/^\/\w+(@\w+)?\s*/, '').trim().split(/\s+/)[0];
  if (arg) {
    if (/^\d{5,}$/.test(arg)) return { id: Number(arg), tg: null, asked: true };
    const un = arg.replace(/^@/, '');
    if (/^\w{3,32}$/.test(un)) {
      const u = await users.findOne({ username: new RegExp('^' + escRx(un) + '$', 'i') });
      return u ? { id: u._id, tg: null } : { id: null, asked: true };
    }
  }
  return { id: ctx.from.id, tg: ctx.from, self: true };
}

async function profileStats(uid) {
  const [u, capCount, agg, top] = await Promise.all([
    users.findOne({ _id: uid }),
    capsules.countDocuments({ user_id: uid }),
    songs.aggregate([{ $match: { user_id: uid } }, { $group: { _id: null, plays: { $sum: '$listens' }, secs: { $sum: '$listen_seconds' }, songs: { $sum: 1 } } }]).toArray(),
    songs.find({ user_id: uid, listens: { $gt: 0 } }).sort({ listens: -1, created_at: -1 }).limit(1).toArray(),
  ]);
  const plays = agg[0]?.plays || 0;
  const higher = (await songs.aggregate([{ $group: { _id: '$user_id', p: { $sum: '$listens' } } }, { $match: { p: { $gt: plays } } }, { $count: 'n' }]).toArray())[0]?.n || 0;
  return { u, capCount, plays, secs: agg[0]?.secs || 0, songCount: agg[0]?.songs || 0, rank: higher + 1, fav: top[0] || null };
}

bot.command('profile', async ctx => {
  const t = await profileTarget(ctx);
  const replyTo = ctx.message.message_id;
  if (t.id == null) return say(ctx, "I don't know that user.", replyTo);
  const st = await profileStats(t.id);
  if (!st.u && !st.songCount && !t.self) return say(ctx, "That user hasn't shared any songs yet.", replyTo);
  const who_ = st.u ? dispName(st.u) : t.tg ? dispName(t.tg) : `User ${t.id}`;
  const fav = st.fav ? `${st.fav.title || 'Unknown'}${st.fav.artist ? ' — ' + st.fav.artist : ''} (${nf(st.fav.listens)} ${st.fav.listens === 1 ? 'play' : 'plays'})` : '—';
  const text = [`Name: ${who_}`, `Capsules: ${nf(st.capCount)}`, `Listening Time: ${fmtTime(st.secs)}`, `Total Plays: ${nf(st.plays)}`, `Rank: #${st.rank}`, `Favorite Song: ${fav}`].join('\n');
  const botUser = ctx.botInfo?.username || process.env.BOT_USERNAME || DEFAULT_BOT_USERNAME;
  const kb = botUser ? Markup.inlineKeyboard([[Markup.button.url('Playlist', `https://t.me/${botUser}/${MINIAPP_NAME}?startapp=${t.id}`)]]) : {};
  try { await ctx.reply(text, { ...kb, reply_parameters: { message_id: replyTo, allow_sending_without_reply: true } }); }
  catch (e) {
    console.error(`[${new Date().toISOString()}] [audio] /profile reply failed: ${e.description || e.message}`);
    await ctx.reply(text, kb).catch(e2 => console.error(`[${new Date().toISOString()}] [audio] /profile retry failed: ${e2.description || e2.message}`));
  }
});

// ---------- /status ----------
// /status           -> "You’re listening to <song> by <artist>"
// /status (reply)   -> "<Name> is listening to <song> by <artist>"
// Works in groups and in the bot's DM: the listener is identified by the Mini App player (Telegram initData), not by the chat.
bot.command('status', async ctx => {
  const m = ctx.message, replyTo = m.message_id;
  const r = m.reply_to_message;
  const rep = r && !r.forum_topic_created ? r.from : null;   // in forum topics every message "replies" to the topic's first message
  if (rep?.is_bot) return say(ctx, 'Bots don’t listen to music.', replyTo);
  const other = rep && rep.id !== ctx.from.id ? rep : null;
  const target = other || ctx.from;

  const np = await nowp.findOne({ _id: target.id, playing: true, expire_at: { $gt: new Date() } });
  const subject = other ? dispName(other) : 'You’re';
  if (!np) return say(ctx, other ? `${subject} isn’t listening to anything right now.` : 'You’re not listening to anything right now.', replyTo);
  const song = `${np.title}${np.artist ? ' by ' + np.artist : ''}`;
  return say(ctx, other ? `${subject} is listening to ${song}` : `You’re listening to ${song}`, replyTo);
});

// /upload - owner only. Reply to an audio file with /upload to force-process it.
// Commands are always delivered to bots (even with privacy mode on), so this also tells you whether the bot sees the group.
const UPLOAD_ADMIN_ID = Number(process.env.UPLOAD_ADMIN_ID || 8955269933);
bot.command('upload', async ctx => {
  const m = ctx.message;
  log(`/upload command chat=${m.chat.id} (${m.chat.type}) from=${who(ctx.from)} reply=${!!m.reply_to_message}`);
  if (ctx.from.id !== UPLOAD_ADMIN_ID) { log(`/upload denied for ${who(ctx.from)}`); return; }

  const target = m.reply_to_message;
  const a = target && getAudio(target);
  if (!a) {
    return say(ctx, `Reply to an audio file with /upload.\nchat: ${m.chat.id} (${m.chat.type})\nI can see this command, so the bot is receiving updates here.`, m.message_id);
  }
  if (!target.from || target.from.is_bot) return say(ctx, 'That audio was sent by a bot, nothing to attribute it to.');

  await say(ctx, 'Processing…', target.message_id);
  try { await enqueueAudio({ from: target.from, chat: m.chat, message_id: target.message_id }, a, true); }
  catch (e) { console.error(`[${new Date().toISOString()}] [audio] /upload enqueue failed:`, e); await say(ctx, '⚠️ Could not queue this song, try again.', target.message_id); }
});

// =====================================================================================================
// ---------- VC music (AviaxMusic port) ----------
// Commands, permissions, settings and all message UI live here. Streaming, downloading, search and the
// assistant accounts live in vc_server.py (VC_API_URL). The server pushes events (track started, next track
// downloading, download progress, errors ...) which are long-polled from GET /events.
// env: VC_API_URL, VC_API_KEY, OWNER_ID (default UPLOAD_ADMIN_ID), LOGGER_ID, SUPPORT_CHAT, SUPPORT_CHANNEL,
//      SOURCE_URL, START_IMG, PING_IMG, DEFAULT_THUMB, LANG_CODE, VC_LOCALES_DIR (optional *.json from the original repo)
// =====================================================================================================
const vcUtil = require('util');
const VC_URL = (process.env.VC_API_URL || '').replace(/\/+$/, '');
const VC_KEY = process.env.VC_API_KEY || '';
const VC_OWNER = Number(process.env.OWNER_ID || UPLOAD_ADMIN_ID);
const VC_LOGGER = Number(process.env.LOGGER_ID || 0);
const VC_SUPPORT_CHAT = process.env.SUPPORT_CHAT || 'https://t.me/DevilsHeavenMF';
const VC_SUPPORT_CHANNEL = process.env.SUPPORT_CHANNEL || 'https://t.me/fallenx';
const VC_SOURCE = process.env.SOURCE_URL || 'https://github.com/CyberPixelPro/AviaxMusic';
const VC_START_IMG = process.env.START_IMG || 'https://files.catbox.moe/zvziwk.jpg';
const VC_PING_IMG = process.env.PING_IMG || 'https://files.catbox.moe/haagg2.png';
const VC_DEFAULT_THUMB = process.env.DEFAULT_THUMB || 'https://te.legra.ph/file/3e40a408286d4eda24191.jpg';
const VC_LANG_DEFAULT = process.env.LANG_CODE || 'en';
const VC_BOOT = Date.now();

// ---------- strings (English built in; drop the original anony/locales/*.json next to this file in ./locales for the other languages) ----------
const VC_EN = {
  add_me: "Add me to your group",
  admin_required: "Bot requires the <b>invite users via link</b> permission to work.",
  admin_cache_wait: "You can only refresh the admin cache once every 10 minutes.",
  admin_cache_reloading: "Reloading admin cache...",
  admin_cache_reloaded: "Admin cache refreshed successfully!",
  auth_added: "Added {0} to the authorized users list.",
  auth_removed: "Removed {0} from the authorized users list.",
  auth_empty: "Authorized users list is empty.",
  auth_list: "<u><b>List of authorized users in {0}:</b></u>\n",
  auth_is_admin: "The user is already an <b>admin</b> and can't be added to authorized users.",
  auto_left: "I waited, I watched, I yawned... and then I left the video chat.",
  bl_usage: "<b>Usage:</b>\n/{0} [chat_id|user_id]",
  bl_invalid: "Only chat IDs and user IDs are supported.",
  bl_already: "This chat is already blacklisted.",
  bl_not: "This chat is not blacklisted.",
  bl_added: "This chat has been blacklisted.",
  bl_removed: "This chat has been removed from the blacklist.",
  bl_user_notify: "You've been blacklisted from using this bot. Please reach out in the <a href=\"{0}\">support chat</a> for more info.",
  dl_cancel: "Download canceled by {0}",
  dl_complete: "Download completed. Processing file...\nTime elapsed: {0}s",
  dl_cancelling: "Hang on, cancelling the download now!",
  dl_active: "Already downloading that file. Mind waiting?",
  dl_limit: "Failed to process the file. The maximum download limit is <b>200 MB</b>.",
  dl_progress: "<u><b>Downloading file</b></u>\n<b>Progress:</b> {0} / {1} [{2:.1f}%]\n<b>Speed:</b> {3}/s | <b>ETA:</b> {4}",
  dl_not_found: "Download already cancelled.",
  error_no_audio: "Moving to the next track...\nAudio source not found in the file.",
  error_no_call: "<b>No active video chat found.</b>\nPlease start one and <b>try again</b>.",
  error_no_file: "Download failed.\nIf the issue persists, report it to the <a href=\"{0}\">support chat</a>",
  error_tg_server: "<u><b>Telegram server error</b></u>\nTelegram is experiencing internal issues. Clearing the queue and leaving the video chat.",
  error_rtmp: "RTMP streaming is not supported. Please stop the RTMP stream and start a video chat instead.",
  eval_error: "⚠️ Error executing snippet\n",
  eval_inp: "What?",
  eval_out: "<b>Output:</b>\n<code>{0}</code>",
  gcast_usage: "Reply to a message for broadcasting the message.",
  gcast_active: "Please wait for the ongoing broadcast to finish.",
  gcast_inactive: "Broadcasting is currently inactive.",
  gcast_start: "Broadcasting started.",
  gcast_stop: "Broadcast stopped.",
  gcast_stopped: "Broadcasting stopped. (check log group)\nSent to {0} groups and {1} users.",
  gcast_log: "<u><b>Broadcast Log</b></u>\n<b>User:</b> <code>{0}</code> | {1}\n<b>Command:</b> <code>{2}</code>\nUse /stop_gcast to stop the broadcast.",
  gcast_stop_log: "Broadcast stopped by <code>{0}</code> | {1}",
  gcast_end: "Broadcasted the message to {0} groups and {1} users.",
  help_menu: "<b>Click the buttons below to get information about my commands.</b>\n<i><b>Note:</b> All commands can be used with /</i>",
  help_admins: "<u><b>Admin commands:</b></u>\n/pause: Puase the ongoing stream.\n/resume: Resume the paused stream.\n/skip: Skip the current stream.\n/stop: Stop the ongoing stream.\n/seek [duration in seconds]: Seek the ongoing stream.\n/seekback [duration in seconds]: Seek the ongoing stream backward.\n/reload: Reloads the admin cache.",
  help_auth: "<u><b>Auth commands:</b></u>\n<i>Authorized users can control the ongoing stream without being an admin.</i>\n/auth: Add a user to the authorized users list.\n/unauth: Remove a user from the authorized users list.",
  help_blist: "<u><b>Blacklist commands:</b></u>\n<i>Blacklisted chats and users cannot use the bot.</i>\n/blacklist [chat_id|user_id]: Add a chat/user to the blacklist.\n/unblacklist [chat_id|user_id]: Remove a chat/user from the blacklist",
  help_lang: "<u><b>Language commands:</b></u>\n<i>This bot supports multiple languages.</i>\n/lang: Change the language of the bot.",
  help_ping: "<u><b>Ping commands:</b></u>\n/help: Shows the help menu of the bot.\n/ping: Check the ping and memory usage of the bot.\n/start: Start the bot.\n/sudolist: Shows the list of sudo users of the bot.",
  help_play: "<u><b>Play commands:</b></u>\n<i>You can play music in the video chat using the following commands.</i>\n/play [song name/youtube url/reply to audio]: Play music in the video chat.\n/vplay [song name/youtube url/reply to video]: Play music video in the video chat.\n-f: Force play music in the video chat.\n-v: Plays music video in the video chat.\n<b>Example:</b> <code>/play -f -v attention</code>",
  help_queue: "<u><b>Queue commands:</b></u>\n/queue: Shows the currently queued tracks in the queue.",
  help_stats: "<u><b>Stats commands:</b></u>\n/stats: Shows the bot's stats.",
  help_sudo: "<u><b>Sudo commands:</b></u>\n/ac: Shows the active calls count.\n/activevc: Shows the list of the active calls.\n/broadcast [reply to message]: Broadcasts the message to all the chats.\n-nochat: Excludes groups from the broadcast.\n-user: Include users in the broadcast.\n-copy: Removes the forwarded tag from the broadcast message.\n<b>Example:</b> <code>/broadcast -user -copy</code>\n/eval: Executes the given code.\n/logs: Sends the log file.\n/logger [on|off]: Enables/disables the logger.\n/restart: Restarts the bot.\n/addsudo: Add a user to the sudo users list.\n/rmsudo: Remove a user from the sudo users list.",
  lang_choose: "Please choose the language you want to set for the current chat:",
  lang_change: "Changing the language of the current chat to: {0}",
  lang_changed: "The language of the current chat has been changed to: <i>{0}</i>",
  lang_same: "The language of the current chat is already set to: {0}",
  log_fetch: "Fetching logs...",
  log_not_found: "Log file doesn't exist.",
  log_sent: "Log file of {0}",
  log_chat: "<u><b>New Chat Log</b></u>\n<b>Chat:</b> <code>{0}</code> | {1}\n<b>User:</b> <code>{2}</code> | {3}",
  log_user: "<u><b>New User Log</b></u>\n<b>ID:</b> <code>{0}</code>\n<b>Name:</b> {1} | {2}",
  logger_on: "Logger enabled.",
  logger_off: "Logger disabled.",
  logger_usage: "<b>Usage:</b>\n/{0} [on|off]",
  loop_count: "The current loop count is: {0}",
  loop_set: "Loop count set to: {0}",
  loop_off: "Loop disabled.",
  loop_usage: "<b>Usage:</b>\n<code>/loop [count]</code>\n<code>/loop off</code>",
  not_playing: "The bot isn't streaming in the video chat.",
  pinging: "Pinging… please wait…",
  ping_pong: "<u><b>Pong!</b></u>\n<b>Latency:</b> <code>{0}ms</code>\n<b>Uptime:</b> {1}\n<b>CPU:</b> <code>{2}%</code>\n<b>RAM:</b> <code>{3}%</code>\n<b>Disk:</b> <code>{4}%</code>\n<b>PyTgCalls Latency:</b> <code>{5}ms</code>",
  play_admin: "<u><b>Admin only play</b></u>\nOnly admins are allowed to play in this chat.",
  play_banned: "<u><b>{0} assistant is banned your chat</b></u>\n<b>ID:</b> <code>{1}</code>\n<b>Name:</b> {2}\n<b>Username:</b> {3}",
  play_media: "<u><b>| Started streaming</b></u>\n<b>Title:</b> <a href=\"{0}\">{1}</a>\n<b>Duration:</b> {2} min\n<b>Requested by:</b> {3}",
  play_log: "<u>{0} Play Log</u>\n<b>Chat:</b> <code>{1}</code> | {2}\n<b>User:</b> <code>{3}</code> | {4}\n<b>Message link:</b> {5}\n<b>Title:</b> {6}\n<b>Duration:</b> {7} min",
  play_queued: "<u><b>Added to queue: {0}</b></u>\n<b>Title:</b> <a href=\"{1}\">{2}</a>\n<b>Duration:</b> {3} min\n<b>Requested by:</b> {4}",
  play_usage: "<b>Usage:</b>\n<code>/play attention</code>",
  play_seeking: "Seeking the current stream...",
  play_again: "Replaying the current media...",
  play_now: "Play Now",
  play_next: "Hold on...\nDownloading next media from the queue.",
  play_invite: "Hold on a moment...\nInviting {0} assistant to your chat.",
  play_searching: "Searching...",
  play_downloading: "Downloading...",
  play_paused: "<b>Stream paused by</b> {0}",
  play_resumed: "<b>Stream resumed by</b> {0}",
  play_replayed: "<b>Stream replayed by</b> {0}",
  play_skipped: "<b>Stream skipped by</b> {0}",
  play_stopped: "<b>Stream ended by</b> {0}",
  play_seeked: "<b>Stream skipped {0} and started from {1} seconds by</b> {2}",
  play_expired: "This button has expired.",
  play_unsupported: "Live streams are not supported.",
  play_already_paused: "Do you remember that you resumed the stream?",
  play_not_paused: "Do you remember that you paused the stream?",
  play_seek_usage: "<b>Usage:</b> /{0} duration\n<b>Example:</b> <code>/{0} 15</code>",
  play_seek_no_dur: "Failed to fetch the duration of the ongoing stream.",
  play_seek_min: "Minimum seek time is 10 seconds — try a bit longer!",
  play_duration_limit: "Streams longer than {0} minutes are not allowed to play.",
  play_queue_full: "The queue limit ({0}) has been reached. Please wait for the currently queued tracks to finish playing, then try again.",
  play_invite_error: "Failed to invite assistant to the chat.\nReason: <code>{0}</code>",
  play_not_found: "Failed to process the query.\nIf the issue persists, report it to the <a href=\"{0}\">support chat</a>.",
  play_chat_invalid: "This bot can only be used in <b>supergroups</b>.\nTo convert your group to a supergroup, make the chat history <b>visible</b> once.\nLeaving this chat...",
  play_user_invalid: "You're an anonymous admin.\nRevert back to user account.",
  playlist_fetch: "Fetching the playlist...\nPlease hold on.",
  playlist_error: "Something went wrong while fetching the playlist.",
  playlist_queued: "<u><b>Added {0} tracks from the playlist to queue:</b></u>\n",
  queue_curr: "<u><b>Currently playing:</b></u>\n<b>Title:</b> <a href=\"{0}\">{1}</a>\n<b>Duration:</b> {2}\n<b>Requested by:</b> {3}\n",
  queue_item: "<b>{0}. Title:</b> {1}\n     - {2} min\n",
  queue_fetching: "Fetching queue...",
  restarting: "Restarting...",
  restarted: "Restart in progress. Don't worry, it'll only take a few seconds… maybe.",
  start_pm: "Hey {0},\nThis is {1} !\nA music player bot with some awesome and useful features.\n<b><i>Click on the help button for more info.</i></b>",
  start_gp: "Hey,\nThis is {0}\n<u><b>A music player bot with some awesome and useful features.</b></u>",
  start_settings: "<u><b>{0} settings</b></u>\nClick the buttons below to change this chat's current settings.",
  stats_fetching: "Fetching stats...",
  stats_sudo: "\n<b>Modules:</b> {0}\n<b>Platform:</b> {1}\n<b>Ram usage:</b> <code>{2}MB | {3}GB</code>\n<b>CPU usage:</b> <code>{4}% ({5} cores)</code>\n<b>Storage:</b> <code>{6}GB | {7}GB</code>\n<b>Python:</b> <code>v{8}</code>\n<b>Pyrogram:</b> <code>v{9}</code>\n<b>PyTgCalls:</b> <code>v{10}</code>",
  stats_user: "<u><b>{0} stats</b></u>\n<b>Assistants:</b> {1}\n<b>Auto leave:</b> {2}\n<b>Blocked chats:</b> {3}\n<b>Blocked users:</b> {4}\n<b>Sudo users:</b> {5}\n<b>Served chats:</b> {6}\n<b>Served users:</b> {7}",
  sudo_already: "{0} is already an sudo user.",
  sudo_added: "Added {0} to the sudo users list.",
  sudo_not: "{0} is not an sudo user.",
  sudo_removed: "Removed {0} from the sudo users list.",
  sudo_fetching: "Fetching sudo users list...",
  sudo_owner: "<u><b>Owner:</b></u>\n- {0}\n",
  sudo_users: "<u><b>Sudo users:</b></u>",
  user_not_admin: "Oh sure, go ahead and manage the video chat... oh wait, you're not an admin.",
  user_no_perms: "You? Manage the video chat? Not with those permissions, sweetie.",
  user_not_found: "I'll need a user ID — or would you mind replying to someone's message?",
  vc_empty: "Looks like there aren't any active streams on the bot.",
  vc_count: "Active streams on the bot: <b>{0}</b>",
  vc_fetching: "Fetching list of active streams...",
  vc_list: "<u><b>List of active streams:</b></u>",
  back: "Back",
  backward: "backward",
  cancel: "Cancel",
  channel: "Channel",
  close: "Close",
  forward: "forward",
  help: "Help",
  language: "Language",
  paused: "Stream paused",
  cmd_delete: "Command delete",
  play_mode: "Admin only play",
  playing: "Playing",
  processing: "Processing...",
  replayed: "Stream replayed",
  skipped: "Stream skipped",
  stopped: "Stream ended",
  source: "Source",
  support: "Support",
  help_0: "Admins",
  help_1: "Auth",
  help_2: "Blacklist",
  help_3: "Language",
  help_4: "Ping",
  help_5: "Play",
  help_6: "Queue",
  help_7: "Stats",
  help_8: "Sudoers",
};
Object.assign(VC_EN, {
  vc_down: '⚠️ The music server is unreachable, try again in a moment.',
  no_assistant: '⚠️ No assistant account is configured on the music server.',
  vc_error: '⚠️ Something went wrong on the music server.',
});
const VC_LANG_NAMES = { ar: 'العربية', de: 'Deutsch', en: 'English', es: 'Español', fr: 'Français', hi: 'हिन्दी', ja: '日本語', my: 'မြန်မာဘာသာ', pa: 'ਪੰਜਾਬੀ', pt: 'Português', ru: 'Русский', tr: 'Türkçe', zh: '中文' };
const VC_LANGS = { en: VC_EN };
try {
  const dir = process.env.VC_LOCALES_DIR || path.join(__dirname, 'locales');
  for (const f of fs.readdirSync(dir)) if (f.endsWith('.json')) VC_LANGS[f.slice(0, -5)] = { ...VC_EN, ...JSON.parse(fs.readFileSync(path.join(dir, f), 'utf8').replace(/^\uFEFF/, '').replace(/(?:\\n){2,}/g, '\\n')) };
} catch {}
const vcFmt = (s, ...a) => String(s).replace(/\{(\d+)(?::\.(\d)f)?\}/g, (_, i, p) => a[i] === undefined ? '' : p !== undefined ? Number(a[i]).toFixed(p) : a[i]).replace(/\n{2,}/g, '\n');
const vcEsc = s => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const vcPlain = s => String(s).replace(/<[^>]+>/g, '').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
const vcMention = u => `<a href="tg://user?id=${u.id}">${vcEsc(u.first_name || u.title || u.id)}</a>`;
const vcBotName = () => bot.botInfo?.first_name || 'Music Bot';
const vcSize = n => n >= 1024 ** 3 ? `${(n / 1024 ** 3).toFixed(2)} GB` : n >= 1024 ** 2 ? `${(n / 1024 ** 2).toFixed(2)} MB` : `${(n / 1024).toFixed(2)} KB`;
const vcEta = s => s < 60 ? `${s}s` : s < 3600 ? `${Math.floor(s / 60)}:${String(s % 60).padStart(2, '0')} min` : `${Math.floor(s / 3600)}:${String(Math.floor(s % 3600 / 60)).padStart(2, '0')}:${String(s % 60).padStart(2, '0')} h`;
const vcMmss = s => new Date(Math.max(0, s) * 1000).toISOString().slice(14, 19);
const vcUptime = s => { const d = Math.floor(s / 86400), h = Math.floor(s / 3600) % 24, m = Math.floor(s / 60) % 60; return `${d ? d + 'days, ' : ''}${h}h:${m}m:${s % 60}s`; };

// ---------- music server api ----------
async function vcApi(method, p, body, ms = 30000) {
  if (!VC_URL) throw Object.assign(new Error('VC_API_URL is not set'), { vcDown: true });
  let r;
  try { r = await fetch(VC_URL + p, { method, headers: { 'Content-Type': 'application/json', 'X-Api-Key': VC_KEY }, body: body ? JSON.stringify(body) : undefined, signal: AbortSignal.timeout(ms) }); }
  catch (e) { throw Object.assign(new Error(`music server unreachable: ${e.message}`), { vcDown: true }); }
  if (r.status === 401) throw Object.assign(new Error('music server rejected VC_API_KEY'), { vcDown: true });
  if (!(r.headers.get('content-type') || '').includes('json')) return { ok: r.ok, buf: Buffer.from(await r.arrayBuffer()) };   // thumbnails / log file
  return r.json().catch(() => ({ ok: false, error: 'vc_error' }));
}
const vc = { get: (p, ms) => vcApi('GET', p, null, ms), post: (p, b, ms) => vcApi('POST', p, b || {}, ms) };
let vcCfgCache = null, vcCfgAt = 0;
async function vcConfig() {
  if (!vcCfgCache || Date.now() - vcCfgAt > 60000) { try { vcCfgCache = await vc.get('/config'); vcCfgAt = Date.now(); } catch {} }
  return vcCfgCache || { thumb_gen: true, video_play: true, duration_limit: 60 };
}

// ---------- state (mongo collections vc_*, cached in memory) ----------
let vcChatsC, vcUsersC, vcAuthC, vcLangC, vcCacheC;
const vcChats = new Set(), vcUsers = new Set(), vcSudo = new Set([VC_OWNER]), vcBlUsers = new Set(), vcBlChats = new Set();
const vcCmdDel = new Set(), vcAdminPlay = new Set(), vcLangMap = new Map(), vcAuth = new Map(), vcAdmins = new Map(), vcNotified = new Set();
let vcLogger = false, vcCmdCount = 0, vcBroadcasting = false;
const vcMsg = new Map();      // chat -> { id, photo, text }: the message showing the current track
const vcQueued = new Map();   // `${chat}:${trackId}` -> id of its "added to queue" message
const vcDone = new Set();     // `${chat}:${message_id}` of messages already turned into a now-playing card; late status events skip them
const vcPending = new Map();  // event token -> id of the "Hold on..." message

const vcLangOf = async chat => VC_LANGS[vcLangMap.get(chat) || VC_LANG_DEFAULT] || VC_EN;
const vcFlag = async (chat, field, set, on) => { on ? set.add(chat) : set.delete(chat); await vcChatsC.updateOne({ _id: chat }, { $set: { [field]: on } }, { upsert: true }); };
const vcAddChat = async chat => { if (!vcChats.has(chat)) { vcChats.add(chat); await vcChatsC.updateOne({ _id: chat }, { $setOnInsert: { _id: chat } }, { upsert: true }); } };
const vcAddUser = async uid => { if (!vcUsers.has(uid)) { vcUsers.add(uid); await vcUsersC.updateOne({ _id: uid }, { $setOnInsert: { _id: uid } }, { upsert: true }); } };
const vcIsAuth = async (chat, uid) => {
  if (!vcAuth.has(chat)) vcAuth.set(chat, new Set((await vcAuthC.findOne({ _id: chat }))?.user_ids || []));
  return vcAuth.get(chat).has(uid);
};
async function vcGetAdmins(chat, reload = false) {
  if (!vcAdmins.has(chat) || reload) {
    try { vcAdmins.set(chat, new Set((await bot.telegram.getChatAdministrators(chat)).filter(a => !a.user.is_bot).map(a => a.user.id))); }
    catch { vcAdmins.set(chat, new Set()); }
  }
  return vcAdmins.get(chat);
}
async function vcIsAdmin(chat, uid) {
  if ((await vcGetAdmins(chat)).has(uid)) return true;
  try { return ['administrator', 'creator'].includes((await bot.telegram.getChatMember(chat, uid)).status); } catch { return false; }
}
const vcSetBl = async (id, on) => {
  const chat = String(id).startsWith('-'), set = chat ? vcBlChats : vcBlUsers, key = chat ? 'bl_chats' : 'bl_users', f = chat ? 'chat_ids' : 'user_ids';
  on ? set.add(id) : set.delete(id);
  await vcCacheC.updateOne({ _id: key }, on ? { $addToSet: { [f]: id } } : { $pull: { [f]: id } }, { upsert: true });
};

// ---------- reply / edit helpers (HTML, with a plain-text retry when Telegram rejects the markup) ----------
const vcH = { parse_mode: 'HTML', link_preview_options: { is_disabled: true } };
const vcParseErr = e => /parse entities|can't parse/i.test(e?.description || e?.message || '');
const vcQuote = ctx => ctx.chat.type !== 'private' && ctx.message ? { reply_parameters: { message_id: ctx.message.message_id, allow_sending_without_reply: true } } : {};
async function vr(ctx, text, extra = {}) {
  const ex = { ...vcH, ...vcQuote(ctx), ...extra };
  try { return await ctx.reply(text, ex); }
  catch (e) { if (vcParseErr(e)) return ctx.reply(vcPlain(text), { ...ex, parse_mode: undefined }); throw e; }
}
async function ve(chat, mid, text, extra = {}, photo = false) {
  const go = (t, ex) => photo ? bot.telegram.editMessageCaption(chat, mid, undefined, t, ex) : bot.telegram.editMessageText(chat, mid, undefined, t, ex);
  try { return await go(text, { ...vcH, ...extra }); }
  catch (e) {
    if (/not modified/i.test(e.description || '')) return;
    if (vcParseErr(e)) return go(vcPlain(text), { ...extra, parse_mode: undefined, link_preview_options: { is_disabled: true } });
    throw e;
  }
}
const vcDel = (chat, mid) => mid ? bot.telegram.deleteMessage(chat, mid).catch(() => {}) : null;
const vcSay = (chat, text, extra = {}) => bot.telegram.sendMessage(chat, text, { ...vcH, ...extra }).catch(e => { log(`vc send failed chat=${chat}: ${e.description || e.message}`); return null; });
const vcLog = text => VC_LOGGER ? vcSay(VC_LOGGER, text) : null;
function vcErr(e, ctx) {
  const d = e.description || e.message || String(e);
  if (e.vcDown) { const L = VC_EN; return (ctx?.callbackQuery ? ctx.answerCbQuery(L.vc_down, { show_alert: true }) : ctx?.reply?.(L.vc_down)).catch?.(() => {}); }
  if (/not modified|message to edit not found|message can't be edited|query is too old|query ID is invalid|chat not found|bot was kicked|bot was blocked|not enough rights to send|have no rights to send|forbidden/i.test(d)) return log(`vc ignored: ${d}`);
  console.error(`[${new Date().toISOString()}] [vc] handler error:`, e);
}

// ---------- keyboards ----------
const ik = rows => ({ reply_markup: { inline_keyboard: rows } });
const kb = (text, data) => ({ text: String(text), callback_data: data });
const kbu = (text, url) => ({ text: String(text), url });
const kbControls = (chat, { status, timer, remove } = {}) => {
  const rows = [];
  if (status) rows.push([kb(status, `controls status ${chat}`)]); else if (timer) rows.push([kb(timer, `controls status ${chat}`)]);
  if (!remove) rows.push([kb('▷', `controls resume ${chat}`), kb('II', `controls pause ${chat}`), kb('⥁', `controls replay ${chat}`), kb('‣‣I', `controls skip ${chat}`), kb('▢', `controls stop ${chat}`)]);
  return ik(rows);
};
const kbQueued = (chat, id, text) => ik([[kb(text, `controls force ${chat} ${id}`)]]);
const kbQueue = (chat, text, playing) => ik([[kb(text, `controls ${playing ? 'pause' : 'resume'} ${chat} q`)]]);
const kbCancel = text => ik([[kb(text, 'cancel_dl')]]);
const kbHelp = (L, back = false) => {
  if (back) return ik([[kb(L.back, 'help back'), kb(L.close, 'help close')]]);
  const btns = ['admins', 'auth', 'blist', 'lang', 'ping', 'play', 'queue', 'stats', 'sudo'].map((c, i) => kb(L[`help_${i}`], `help ${c}`));
  return ik([btns.slice(0, 3), btns.slice(3, 6), btns.slice(6)]);
};
const kbLang = cur => {
  const b = Object.keys(VC_LANGS).sort().map(c => kb(`${VC_LANG_NAMES[c] || c} (${c}) ${c === cur ? '✔️' : ''}`, `lang_change ${c}`));
  return ik(b.reduce((r, x, i) => (i % 2 ? r[r.length - 1].push(x) : r.push([x]), r), []));
};
const kbSettings = (L, adminOnly, cmdDel, lang) => ik([
  [kb(L.play_mode + ' ➜', 'settings'), kb(adminOnly ? '✅' : '❌', 'settings play')],
  [kb(L.cmd_delete + ' ➜', 'settings'), kb(cmdDel ? '✅' : '❌', 'settings delete')],
  [kb(L.language + ' ➜', 'settings'), kb(VC_LANG_NAMES[lang] || lang, 'language')],
]);
const kbStart = (L, priv) => ik([
  [kbu(L.add_me, `https://t.me/${bot.botInfo?.username}?startgroup=true`)],
  [kb(L.help, 'help')],
  [kbu(L.support, VC_SUPPORT_CHAT), kbu(L.channel, VC_SUPPORT_CHANNEL)],
  ...(priv ? [] : [[kb(L.language, 'language')]]),
]);
const kbYt = link => ik([[{ text: '❐', copy_text: { text: link } }, kbu('Youtube', link)]]);

// ---------- command / callback wrappers ----------
// o: { group, private, sudo, owner, allowBl, play }.  Blacklisted users are ignored, blacklisted chats are left.
function vcCmd(names, fn, o = {}) {
  vcCmdCount++;
  bot.command(names, async ctx => {
    try {
      const chat = ctx.chat, from = ctx.from, grp = chat.type === 'group' || chat.type === 'supergroup';
      if (o.group && !grp) return;
      if (o.private && chat.type !== 'private') return;
      if (!from || ctx.message.sender_chat || from.id === 1087968824) { if (o.play) await vr(ctx, (await vcLangOf(chat.id)).play_user_invalid); return; }   // anonymous admin / channel identity
      if (vcBlChats.has(chat.id)) return bot.telegram.leaveChat(chat.id).catch(() => {});
      if (vcBlUsers.has(from.id) && !o.allowBl) return;
      if (o.sudo && !vcSudo.has(from.id)) return;
      if (o.owner && from.id !== VC_OWNER) return;
      await fn(ctx, await vcLangOf(chat.id));
    } catch (e) { vcErr(e, ctx); }
  });
}
function vcAct(re, fn) {
  bot.action(re, async ctx => {
    try {
      const msg = ctx.callbackQuery.message;
      if (!msg || vcBlUsers.has(ctx.from.id)) return;
      if (vcBlChats.has(msg.chat.id)) return bot.telegram.leaveChat(msg.chat.id).catch(() => {});
      await fn(ctx, await vcLangOf(msg.chat.id), msg.chat.id, msg);
    } catch (e) { vcErr(e, ctx); }
  });
}
const vcCan = async (chat, uid) => vcSudo.has(uid) || await vcIsAuth(chat, uid) || await vcIsAdmin(chat, uid);
async function vcDeny(ctx, L) { return ctx.callbackQuery ? ctx.answerCbQuery(L.user_no_perms, { show_alert: true }).catch(() => {}) : vr(ctx, L.user_no_perms); }
const vcCanManage = async (ctx, L) => { if (await vcCan(ctx.chat.id, ctx.from.id)) return true; await vcDeny(ctx, L); return false; };
const vcAdminOnly = async (ctx, L) => {
  const chat = ctx.chat || ctx.callbackQuery?.message?.chat;
  if (chat.type === 'private' || vcSudo.has(ctx.from.id) || (await vcGetAdmins(chat.id)).has(ctx.from.id)) return true;
  await vcDeny(ctx, L); return false;
};
const vcArgs = ctx => (ctx.message.text || '').split(/\s+/).slice(1);
const vcCmdName = ctx => ((ctx.message.text || '').match(/^\/(\w+)/) || [])[1]?.toLowerCase();
const vcApiErr = (L, code, x = {}) => ({
  no_file: vcFmt(L.error_no_file, VC_SUPPORT_CHAT), no_call: L.error_no_call, no_audio: L.error_no_audio, tg_server: L.error_tg_server, rtmp: L.error_rtmp,
  not_found: vcFmt(L.play_not_found, VC_SUPPORT_CHAT), usage: L.play_usage, duration_limit: vcFmt(L.play_duration_limit, x.limit), queue_full: vcFmt(L.play_queue_full, x.limit),
  playlist_error: L.playlist_error, dl_limit: L.dl_limit, dl_active: L.dl_active, not_playing: L.not_playing, already_paused: L.play_already_paused, not_paused: L.play_not_paused,
  no_assistant: L.no_assistant, expired: L.play_expired,
}[code] || `${L.vc_error}\n<code>${vcEsc(code)}</code>`);

async function vcExtractUser(ctx) {
  const m = ctx.message, rep = m.reply_to_message;
  if (rep?.from && !rep.forum_topic_created) return { id: rep.from.id, mention: vcMention(rep.from) };
  const ent = (m.entities || []).find(e => e.type === 'text_mention' && e.user);
  if (ent) return { id: ent.user.id, mention: vcMention(ent.user) };
  const rest = (m.text || '').replace(/^\/\w+(@\w+)?/, ''), q = rest.match(/@(\w{5,32})/)?.[0] || rest.match(/\b\d{6,15}\b/)?.[0];
  if (q) { const r = await vc.get('/user?q=' + encodeURIComponent(q)).catch(() => null); if (r?.ok) return { id: r.id, mention: r.mention }; }
  return null;
}
const vcUserMention = async id => { const r = await vc.get('/user?q=' + id).catch(() => null); return r?.ok ? r.mention : `<a href="tg://user?id=${id}">${id}</a>`; };
function vcGetUrl(m) {
  let link = null;
  for (const msg of [m, m.reply_to_message].filter(Boolean)) {
    const text = msg.text || msg.caption || '';
    for (const e of msg.entities || msg.caption_entities || []) {
      if (e.type === 'text_link') { link = e.url; break; }
      if (e.type === 'url') { link = text.substr(e.offset, e.length); break; }
    }
  }
  return link ? link.split('&si')[0].split('?si')[0] : null;
}

// ---------- showing a track (edits the status / "Hold on" message into the now-playing card) ----------
async function vcShowTrack(chat, track, mid, L, wantThumb) {
  const text = vcFmt(L.play_media, track.url, vcEsc(track.title), track.duration, track.user), keyboard = kbControls(chat);
  let photo = null;
  if (wantThumb !== false && (await vcConfig()).thumb_gen) {
    photo = VC_DEFAULT_THUMB;
    if (track.kind === 'yt') { const r = await vc.get('/thumb/' + track.id, 5000).catch(() => null); if (r?.buf) photo = { source: r.buf }; }
  }
  const tryIt = async f => { try { await f(); return true; } catch (e) { log(`vc show track: ${e.description || e.message}`); return false; } };
  let id = mid, isPhoto = false;
  if (mid && photo && await tryIt(() => bot.telegram.editMessageMedia(chat, mid, undefined, { type: 'photo', media: photo, caption: text, parse_mode: 'HTML' }, keyboard))) isPhoto = true;
  else if (mid && await tryIt(() => ve(chat, mid, text, keyboard))) { /* edited as text */ }
  else {
    let m = photo ? await bot.telegram.sendPhoto(chat, photo, { caption: text, ...vcH, ...keyboard }).catch(() => null) : null;
    if (m) isPhoto = true; else m = await vcSay(chat, text, keyboard);
    id = m?.message_id;
  }
  if (id) vcMsg.set(chat, { id, photo: isPhoto, text });
}

// ---------- events from the music server ----------
async function vcOnEvent(e) {
  const chat = e.chat_id, L = await vcLangOf(chat);
  switch (e.type) {
    case 'status': {
      let text, extra = {};
      if (e.code === 'playlist_fetch') text = L.playlist_fetch;
      else if (e.code === 'downloading') text = L.play_downloading;
      else if (e.code === 'dl_complete') text = vcFmt(L.dl_complete, e.args.elapsed);
      else if (e.code === 'dl_progress') { const a = e.args; text = vcFmt(L.dl_progress, vcSize(a.cur), vcSize(a.total), a.percent, vcSize(a.speed), vcEta(a.eta)); extra = kbCancel(L.cancel); }
      if (vcDone.has(`${chat}:${e.message_id}`)) break;   // track already started, don't bring back "Downloading..."
      if (text) await ve(chat, e.message_id, text, extra).catch(() => {});
      break;
    }
    case 'next_downloading': {
      if (e.kind === 'force') { vcDel(chat, vcMsg.get(chat)?.id); vcMsg.delete(chat); }
      if (e.kind !== 'replay') { vcDel(chat, vcQueued.get(`${chat}:${e.track_id}`)); vcQueued.delete(`${chat}:${e.track_id}`); }
      const m = await vcSay(chat, e.kind === 'replay' ? L.play_again : L.play_next);
      if (m) vcPending.set(e.token, m.message_id);
      break;
    }
    case 'track_started': {
      const mid = e.message_id || vcPending.get(e.token); vcPending.delete(e.token);
      if (mid) { vcDone.add(`${chat}:${mid}`); if (vcDone.size > 500) vcDone.delete(vcDone.values().next().value); }
      await vcShowTrack(chat, e.track, mid, L, e.thumb || e.track.kind !== 'yt');
      break;
    }
    case 'track_error': {
      const mid = e.message_id || vcPending.get(e.token); vcPending.delete(e.token);
      const text = vcApiErr(L, e.code);
      if (mid) await ve(chat, mid, text).catch(() => vcSay(chat, text)); else await vcSay(chat, text);
      break;
    }
    case 'auto_left': {
      const cur = vcMsg.get(chat);
      if (cur) {
        await bot.telegram.editMessageReplyMarkup(chat, cur.id, undefined, kbControls(chat, { status: L.stopped, remove: true }).reply_markup).catch(() => {});
        await vcSay(chat, L.auto_left, { reply_parameters: { message_id: cur.id, allow_sending_without_reply: true } });
      }
      break;
    }
    case 'stopped': {
      vcMsg.delete(chat);
      for (const k of [...vcQueued.keys()]) if (k.startsWith(chat + ':')) vcQueued.delete(k);
      break;
    }
  }
}
const vcChains = new Map();   // chat_id -> promise chain: events of one chat stay in order, different chats run in parallel
function vcDispatch(e) {
  const key = e.chat_id ?? 0, prev = vcChains.get(key) || Promise.resolve();
  const next = prev.then(() => vcOnEvent(e)).catch(err => log(`vc event ${e.type} failed: ${err.description || err.message}`))
    .finally(() => { if (vcChains.get(key) === next) vcChains.delete(key); });
  vcChains.set(key, next);
}
async function vcPoll() {
  let cursor = -1, boot = null;
  for (;;) {
    try {
      const r = await vc.get(`/events?after=${cursor}&timeout=25`, 40000);
      if (!r.ok) throw new Error(r.error || 'events failed');
      if (cursor < 0) { cursor = r.last; boot = r.boot; continue; }
      if (r.boot !== boot) { boot = r.boot; cursor = 0; log('music server restarted'); continue; }
      for (const e of r.events) { cursor = e.id; vcDispatch(e); }
    } catch (e) { cursor = cursor < 0 ? cursor : cursor; await sleep(3000); }
  }
}
// moving "—◉—" timer under the now-playing card (every 7s, like the original), controls disappear in the last 10s
async function vcTimer() {
  const cfg = await vcConfig(), length = 10;
  let act; try { act = (await vc.get('/active')).active || []; } catch { return; }
  for (const a of act) {
    const cur = vcMsg.get(a.chat_id);
    if (!a.playing || !cur || !a.duration_sec || !a.time) continue;
    const played = a.time, remaining = a.duration_sec - played, pos = Math.min(Math.floor(played / a.duration_sec * length), length - 1);
    let timer = '—'.repeat(pos) + '◉' + '—'.repeat(length - pos - 1), remove = false;
    if (remaining < 10) remove = true;
    else timer = cfg.thumb_gen ? `${vcMmss(played)} | ${timer} | -${vcMmss(remaining)}` : null;
    if (!timer && !remove) continue;
    await bot.telegram.editMessageReplyMarkup(a.chat_id, cur.id, undefined, kbControls(a.chat_id, { timer, remove }).reply_markup).catch(() => {});
  }
}

// =====================================================================================================
// commands
// =====================================================================================================
vcCmd('help', async (ctx, L) => vr(ctx, L.help_menu, kbHelp(L)), { private: true });

vcCmd('start', async (ctx, L) => {
  if (vcBlUsers.has(ctx.from.id)) { if (!vcNotified.has(ctx.from.id)) { vcNotified.add(ctx.from.id); await vr(ctx, vcFmt(L.bl_user_notify, VC_SUPPORT_CHAT)); } return; }
  if (vcArgs(ctx)[0] === 'help' && ctx.chat.type === 'private') return vr(ctx, L.help_menu, kbHelp(L));
  const priv = ctx.chat.type === 'private';
  const caption = priv ? vcFmt(L.start_pm, vcEsc(ctx.from.first_name), vcBotName()) : vcFmt(L.start_gp, vcBotName());
  await ctx.replyWithPhoto(VC_START_IMG, { caption, ...vcH, ...kbStart(L, priv), ...(priv ? {} : vcQuote(ctx)) })
    .catch(() => vr(ctx, caption, kbStart(L, priv)));
  if (priv) { if (!vcUsers.has(ctx.from.id)) { await vcLog(vcFmt(L.log_user, ctx.from.id, '@' + (ctx.from.username || ''), vcMention(ctx.from))); await vcAddUser(ctx.from.id); } }
  else if (!vcChats.has(ctx.chat.id)) { await vcLog(vcFmt(L.log_chat, ctx.chat.id, vcEsc(ctx.chat.title), ctx.from.id, vcMention(ctx.from))); await vcAddChat(ctx.chat.id); }
}, { allowBl: true });

vcCmd(['playmode', 'settings'], async (ctx, L) => vr(ctx, vcFmt(L.start_settings, vcEsc(ctx.chat.title)),
  kbSettings(L, vcAdminPlay.has(ctx.chat.id), vcCmdDel.has(ctx.chat.id), vcLangMap.get(ctx.chat.id) || VC_LANG_DEFAULT)), { group: true });

vcCmd(['ping', 'alive'], async (ctx, L) => {
  const t0 = Date.now(), sent = await vr(ctx, L.pinging), latency = (Date.now() - t0).toFixed(2);
  const st = await vc.get('/stats').catch(() => ({}));
  const caption = vcFmt(L.ping_pong, latency, vcUptime(Math.floor((Date.now() - VC_BOOT) / 1000)), st.cpu ?? '?', st.ram ?? '?', st.disk ?? '?', st.ping ?? '?');
  await bot.telegram.editMessageMedia(ctx.chat.id, sent.message_id, undefined, { type: 'photo', media: VC_PING_IMG, caption, parse_mode: 'HTML' }, ik([[kbu(L.support, VC_SUPPORT_CHAT)]]))
    .catch(() => ve(ctx.chat.id, sent.message_id, caption, ik([[kbu(L.support, VC_SUPPORT_CHAT)]])));
});

vcCmd('stats', async (ctx, L) => {
  const sent = await ctx.replyWithPhoto(VC_PING_IMG, { caption: L.stats_fetching, ...vcQuote(ctx) }).catch(() => vr(ctx, L.stats_fetching));
  const st = await vc.get('/stats').catch(() => ({}));
  let text = vcFmt(L.stats_user, vcBotName(), st.assistants ?? '?', !!st.auto_leave, vcBlChats.size, vcBlUsers.size, vcSudo.size, vcChats.size, vcUsers.size);
  if (vcSudo.has(ctx.from.id)) text += vcFmt(L.stats_sudo, vcCmdCount, st.platform, st.rss_mb, st.total_ram_gb, st.proc_cpu, st.cores, st.disk_used_gb, st.disk_total_gb, st.python, st.pyrogram, st.pytgcalls);
  await ve(ctx.chat.id, sent.message_id, text, {}, !!sent.photo).catch(() => vr(ctx, text));
}, { group: true });

// ---------- /play /vplay /playforce /vplayforce ----------
async function vcAssistantReady(ctx, L, a) {
  const chat = ctx.chat;
  let member; try { member = await bot.telegram.getChatMember(chat.id, a.id); } catch { member = { status: 'left' }; }
  const banned = () => vr(ctx, vcFmt(L.play_banned, vcBotName(), a.id, a.mention, a.username ? '@' + a.username : 'None'));
  if (member.status === 'kicked') { try { await bot.telegram.unbanChatMember(chat.id, a.id, { only_if_banned: true }); } catch { await banned(); return false; } member = { status: 'left' }; }
  else if (member.status === 'restricted') {
    try { await bot.telegram.restrictChatMember(chat.id, a.id, { permissions: { can_send_messages: true, can_send_audios: true, can_send_documents: true, can_send_photos: true, can_send_videos: true, can_send_video_notes: true, can_send_voice_notes: true, can_send_polls: true, can_send_other_messages: true, can_add_web_page_previews: true, can_invite_users: true } }); }
    catch { await banned(); return false; }
  }
  if (member.status !== 'left' && !(member.status === 'restricted' && !member.is_member)) return true;
  let link;
  if (chat.username) link = chat.username;
  else {
    try { link = (await bot.telegram.getChat(chat.id)).invite_link || await bot.telegram.exportChatInviteLink(chat.id); }
    catch (e) { await vr(ctx, /rights|admin/i.test(e.description || '') ? L.admin_required : vcFmt(L.play_invite_error, e.name || 'Error')); return false; }
  }
  const umm = await vr(ctx, vcFmt(L.play_invite, vcBotName()));
  await sleep(2000);
  const j = await vc.post('/join', { chat_id: chat.id, link });
  if (j.status === 'request_sent') {
    await sleep(2000);
    try { await bot.telegram.approveChatJoinRequest(chat.id, a.id); }
    catch (e) { if (!/hide_requester_missing/i.test(e.description || '')) { await ve(chat.id, umm.message_id, vcFmt(L.play_invite_error, e.name || 'Error')); return false; } }
  } else if (!j.ok) { await ve(chat.id, umm.message_id, vcFmt(L.play_invite_error, j.error)); return false; }
  vcDel(chat.id, umm.message_id);
  return true;
}
const vcPlaylistText = (L, list) => {
  let t = '<blockquote expandable>';
  for (const x of list) { const line = `<b>${x.pos}.</b> ${vcEsc(x.title)}\n`; if (t.length + line.length > 1900) break; t += line; }
  return vcFmt(L.playlist_queued, list.length) + t + '</blockquote>';
};
vcCmd(['play', 'playforce', 'vplay', 'vplayforce'], async (ctx, L) => {
  const m = ctx.message, chat = ctx.chat, uid = ctx.from.id, cmd = vcCmdName(ctx), args = vcArgs(ctx);
  if (chat.type !== 'supergroup') { await vr(ctx, L.play_chat_invalid); return bot.telegram.leaveChat(chat.id).catch(() => {}); }
  const rep = m.reply_to_message, hasMedia = rep && (rep.video || rep.audio || rep.document || rep.voice);
  if (!rep && (args.length < 1 || (args.length === 1 && args[0] === '-f'))) return vr(ctx, L.play_usage);
  const cfg = await vcConfig();
  const force = cmd.endsWith('force') || (args[0] || '').includes('-f'), video = cmd[0] === 'v' && cfg.video_play !== false;
  const url = vcGetUrl(m), query = args.filter(a => a !== '-f').join(' ');

  if (vcAdminPlay.has(chat.id) || force) {
    if (!(await vcGetAdmins(chat.id)).has(uid) && !(await vcIsAuth(chat.id, uid)) && !vcSudo.has(uid)) return vr(ctx, L.play_admin);
  }
  const st = await vc.get('/state/' + chat.id);
  if (!st.ok) return vr(ctx, vcApiErr(L, st.error));
  if (!st.active && !(await vcAssistantReady(ctx, L, st.assistant))) return;
  if (vcCmdDel.has(chat.id)) ctx.deleteMessage().catch(() => {});

  const sent = await vr(ctx, L.play_searching), user = vcMention(ctx.from);
  const r = await vc.post('/play', { chat_id: chat.id, user, query, url, reply_message_id: hasMedia ? rep.message_id : null, video, force, status_message_id: sent.message_id }, 600000);
  if (!r.ok) { if (r.error !== 'cancelled') await ve(chat.id, sent.message_id, vcApiErr(L, r.error, r)); return; }

  if (vcLogger && VC_LOGGER && chat.id !== VC_LOGGER) {
    const link = chat.username ? `https://t.me/${chat.username}/${sent.message_id}` : `https://t.me/c/${String(chat.id).replace(/^-100/, '')}/${sent.message_id}`;
    vcLog(vcFmt(L.play_log, vcBotName(), chat.id, vcEsc(chat.title), uid, user, link, vcEsc(r.track.title), r.track.duration));
  }
  if (r.action === 'queued') {
    vcQueued.set(`${chat.id}:${r.track.id}`, sent.message_id);
    await ve(chat.id, sent.message_id, vcFmt(L.play_queued, r.position, r.track.url, vcEsc(r.track.title), r.track.duration, user), kbQueued(chat.id, r.track.id, L.play_now));
  }
  if (r.playlist?.length) await vcSay(chat.id, vcPlaylistText(L, r.playlist));
}, { group: true, play: true });

// ---------- playback controls ----------
const vcSimple = (names, path, ok) => vcCmd(names, async (ctx, L) => {
  if (!(await vcCanManage(ctx, L))) return;
  const r = await vc.post(path, { chat_id: ctx.chat.id });
  if (!r.ok) return vr(ctx, vcApiErr(L, r.error));
  return ok(ctx, L, r);
}, { group: true });
vcSimple('pause', '/pause', (ctx, L) => vr(ctx, vcFmt(L.play_paused, vcMention(ctx.from)), kbControls(ctx.chat.id)));
vcSimple('resume', '/resume', (ctx, L) => vr(ctx, vcFmt(L.play_resumed, vcMention(ctx.from)), kbControls(ctx.chat.id)));
vcSimple(['skip', 'next'], '/skip', (ctx, L) => vr(ctx, vcFmt(L.play_skipped, vcMention(ctx.from))));
vcCmd(['end', 'stop'], async (ctx, L) => {
  if (!(await vcCanManage(ctx, L)) || vcArgs(ctx).length) return;
  const r = await vc.post('/stop', { chat_id: ctx.chat.id });
  return vr(ctx, r.ok ? vcFmt(L.play_stopped, vcMention(ctx.from)) : L.not_playing);
}, { group: true });

vcCmd(['seek', 'seekback'], async (ctx, L) => {
  if (!(await vcCanManage(ctx, L))) return;
  const cmd = vcCmdName(ctx), usage = () => vr(ctx, vcFmt(L.play_seek_usage, cmd)), a = vcArgs(ctx)[0];
  if (!a || !/^-?\d+$/.test(a)) return usage();
  if (Number(a) < 10) return vr(ctx, L.play_seek_min);
  const sent = await vr(ctx, L.play_seeking), back = cmd === 'seekback';
  const r = await vc.post('/seek', { chat_id: ctx.chat.id, seconds: Number(a), back });
  const text = r.ok ? vcFmt(L.play_seeked, back ? L.backward : L.forward, r.start_from, vcMention(ctx.from)) : r.error === 'no_duration' ? L.play_seek_no_dur : vcApiErr(L, r.error);
  await ve(ctx.chat.id, sent.message_id, text);
}, { group: true });

vcCmd('loop', async (ctx, L) => {
  if (!(await vcCanManage(ctx, L))) return;
  const cur = await vc.post('/loop', { chat_id: ctx.chat.id });
  if (!cur.ok) return vr(ctx, L.not_playing);
  const a = vcArgs(ctx)[0];
  if (!a) return vr(ctx, cur.count ? vcFmt(L.loop_count, cur.count) : L.loop_usage);
  const off = ['off', 'disable'].includes(a.toLowerCase());
  if (!/^\d+$/.test(a) && !off) return vr(ctx, L.loop_usage);
  let n = off ? 0 : Number(a); n = n < 1 ? 0 : Math.min(n, 10);
  await vc.post('/loop', { chat_id: ctx.chat.id, count: n });
  return vr(ctx, n === 0 ? L.loop_off : vcFmt(L.loop_set, n));
}, { group: true });

vcCmd(['queue', 'playing'], async (ctx, L) => {
  const chat = ctx.chat.id, q = await vc.get('/queue/' + chat);
  if (!q.active || !q.items?.length) return vr(ctx, L.not_playing);
  const reply = await vr(ctx, L.queue_fetching), cur = q.items[0], rest = q.items.slice(1), cfg = await vcConfig();
  let text = vcFmt(L.queue_curr, cur.url, vcEsc(cur.title.slice(0, 50)), cur.duration, cur.user);
  if (rest.length) {
    text += '<blockquote expandable>';
    rest.slice(0, 14).forEach((t, i) => { text += vcFmt(L.queue_item, i + 2, vcEsc(t.title), t.duration); });
    text += '</blockquote>';
  }
  const keyboard = kbQueue(chat, q.playing ? L.playing : L.paused, q.playing);
  let photo = null;
  if (cfg.thumb_gen) { photo = VC_DEFAULT_THUMB; if (cur.kind === 'yt') { const r = await vc.get('/thumb/' + cur.id).catch(() => null); if (r?.buf) photo = { source: r.buf }; } }
  if (photo) { try { return await bot.telegram.editMessageMedia(chat, reply.message_id, undefined, { type: 'photo', media: photo, caption: text, parse_mode: 'HTML' }, keyboard); } catch (e) { log(`vc queue media: ${e.description || e.message}`); } }
  await ve(chat, reply.message_id, text, keyboard);
}, { group: true });

// ---------- auth / admin cache / language ----------
vcCmd(['auth', 'unauth'], async (ctx, L) => {
  if (!(await vcAdminOnly(ctx, L))) return;
  const u = await vcExtractUser(ctx);
  if (!u) return vr(ctx, L.user_not_found);
  const chat = ctx.chat.id;
  await vcIsAuth(chat, u.id);   // loads the cache
  if (vcCmdName(ctx) === 'auth') {
    if (await vcIsAdmin(chat, u.id)) return vr(ctx, L.auth_is_admin);
    vcAuth.get(chat).add(u.id); await vcAuthC.updateOne({ _id: chat }, { $addToSet: { user_ids: u.id } }, { upsert: true });
    return vr(ctx, vcFmt(L.auth_added, u.mention));
  }
  vcAuth.get(chat).delete(u.id); await vcAuthC.updateOne({ _id: chat }, { $pull: { user_ids: u.id } });
  return vr(ctx, vcFmt(L.auth_removed, u.mention));
}, { group: true });
vcCmd('authlist', async (ctx, L) => {
  if (!(await vcAdminOnly(ctx, L))) return;
  await vcIsAuth(ctx.chat.id, 0);
  const list = [...vcAuth.get(ctx.chat.id)];
  if (!list.length) return vr(ctx, L.auth_empty);
  return vr(ctx, vcFmt(L.auth_list, vcEsc(ctx.chat.title)) + list.map((u, i) => `\n${i + 1}. <a href="tg://user?id=${u}">${u}</a>`).join(''));
}, { group: true });
const vcRel = new Map();
vcCmd(['admincache', 'reload'], async (ctx, L) => {
  if ((vcRel.get(ctx.from.id) || 0) > Date.now()) return vr(ctx, L.admin_cache_wait);
  vcRel.set(ctx.from.id, Date.now() + 600000);
  const sent = await vr(ctx, L.admin_cache_reloading);
  await vcGetAdmins(ctx.chat.id, true);
  await ve(ctx.chat.id, sent.message_id, L.admin_cache_reloaded);
}, { group: true });
vcCmd(['lang', 'language'], async (ctx, L) => vr(ctx, L.lang_choose, kbLang(vcLangMap.get(ctx.chat.id) || VC_LANG_DEFAULT)));

// ---------- sudo / owner ----------
vcCmd(['addsudo', 'delsudo', 'rmsudo'], async (ctx, L) => {
  const u = await vcExtractUser(ctx);
  if (!u) return vr(ctx, L.user_not_found);
  if (vcCmdName(ctx) === 'addsudo') {
    if (vcSudo.has(u.id)) return vr(ctx, vcFmt(L.sudo_already, u.mention));
    vcSudo.add(u.id); await vcCacheC.updateOne({ _id: 'sudoers' }, { $addToSet: { user_ids: u.id } }, { upsert: true });
    return vr(ctx, vcFmt(L.sudo_added, u.mention));
  }
  if (!vcSudo.has(u.id) || u.id === VC_OWNER) return vr(ctx, vcFmt(L.sudo_not, u.mention));
  vcSudo.delete(u.id); await vcCacheC.updateOne({ _id: 'sudoers' }, { $pull: { user_ids: u.id } });
  return vr(ctx, vcFmt(L.sudo_removed, u.mention));
}, { owner: true });
vcCmd(['listsudo', 'sudolist'], async (ctx, L) => {
  const sent = await vr(ctx, L.sudo_fetching), others = [...vcSudo].filter(x => x !== VC_OWNER);
  let txt = vcFmt(L.sudo_owner, await vcUserMention(VC_OWNER));
  if (others.length) txt += L.sudo_users;
  for (const id of others) txt += `\n- ${await vcUserMention(id)}`;
  await ve(ctx.chat.id, sent.message_id, txt);
}, { allowBl: true });

vcCmd(['blacklist', 'unblacklist', 'whitelist'], async (ctx, L) => {
  const cmd = vcCmdName(ctx), a = vcArgs(ctx)[0];
  if (!a) return vr(ctx, vcFmt(L.bl_usage, cmd));
  let id;
  try { id = a.startsWith('@') ? (await bot.telegram.getChat(a)).id : Number(a); if (!Number.isInteger(id)) throw 0; } catch { return vr(ctx, L.bl_invalid); }
  const has = vcBlChats.has(id) || vcBlUsers.has(id);
  if (cmd === 'blacklist') { if (has) return vr(ctx, L.bl_already); await vcSetBl(id, true); return vr(ctx, L.bl_added); }
  if (!has) return vr(ctx, L.bl_not);
  await vcSetBl(id, false); return vr(ctx, L.bl_removed);
}, { sudo: true });

vcCmd(['ac', 'activevc'], async (ctx, L) => {
  const act = (await vc.get('/active')).active || [];
  if (!act.length) return vr(ctx, L.vc_empty);
  if (vcCmdName(ctx) === 'ac') return vr(ctx, vcFmt(L.vc_count, act.length));
  const sent = await vr(ctx, L.vc_fetching);
  const text = act.map((x, i) => `\n${i + 1}. <code>${x.chat_id}</code>\n    ➜ ${vcEsc((x.title || '').slice(0, 25))}`).join('');
  if (text.length < 4000) return ve(ctx.chat.id, sent.message_id, L.vc_list + text);
  vcDel(ctx.chat.id, sent.message_id);
  return ctx.replyWithDocument({ source: Buffer.from(text.replace(/<[^>]+>/g, '')), filename: 'activevc.txt' }, { caption: L.vc_list, ...vcH });
}, { sudo: true });

vcCmd('broadcast', async (ctx, L) => {
  const m = ctx.message, rep = m.reply_to_message, words = (m.text || '').split(/\s+/);
  if (!rep) return vr(ctx, L.gcast_usage);
  if (vcBroadcasting) return vr(ctx, L.gcast_active);
  const sent = await vr(ctx, L.gcast_start), groups = words.includes('-nochat') ? [] : [...vcChats], users = words.includes('-user') ? [...vcUsers] : [], gset = new Set(groups);
  vcBroadcasting = true;
  if (VC_LOGGER) {
    await bot.telegram.forwardMessage(VC_LOGGER, rep.chat.id, rep.message_id).catch(() => {});
    const lm = await vcSay(VC_LOGGER, vcFmt(L.gcast_log, ctx.from.id, vcMention(ctx.from), vcEsc(m.text)));
    if (lm) bot.telegram.pinChatMessage(VC_LOGGER, lm.message_id, { disable_notification: false }).catch(() => {});
  }
  await sleep(5000);
  let count = 0, ucount = 0, failed = '';
  for (const chat of [...groups, ...users]) {
    if (!vcBroadcasting) { vcBroadcasting = false; return ve(ctx.chat.id, sent.message_id, vcFmt(L.gcast_stopped, count, ucount)); }
    try {
      if (words.includes('-copy')) await bot.telegram.copyMessage(chat, rep.chat.id, rep.message_id, rep.reply_markup ? { reply_markup: rep.reply_markup } : {});
      else await bot.telegram.forwardMessage(chat, rep.chat.id, rep.message_id);
      gset.has(chat) ? count++ : ucount++;
      await sleep(100);
    } catch (e) {
      const wait = e.response?.parameters?.retry_after;
      if (wait) await sleep((wait + 30) * 1000); else failed += `${chat} - ${e.description || e.message}\n`;
    }
  }
  vcBroadcasting = false;
  const text = vcFmt(L.gcast_end, count, ucount);
  if (failed) await ctx.replyWithDocument({ source: Buffer.from(failed), filename: 'errors.txt' }, { caption: text });
  await ve(ctx.chat.id, sent.message_id, text);
}, { sudo: true });
vcCmd(['stop_gcast', 'stop_broadcast'], async (ctx, L) => {
  if (!vcBroadcasting) return vr(ctx, L.gcast_inactive);
  vcBroadcasting = false;
  const lm = await vcSay(VC_LOGGER, vcFmt(L.gcast_stop_log, ctx.from.id, vcMention(ctx.from)));
  if (lm) bot.telegram.pinChatMessage(VC_LOGGER, lm.message_id, { disable_notification: false }).catch(() => {});
  return vr(ctx, L.gcast_stop);
}, { sudo: true });

const VC_AsyncFn = Object.getPrototypeOf(async function () {}).constructor;
vcCmd(['eval', 'exec'], async (ctx, L) => {
  const code = (ctx.message.text || '').replace(/^\/\w+(@\w+)?\s*/, '');
  if (!code.trim()) return vr(ctx, L.eval_inp);
  const out = [], print = (...a) => out.push(a.map(x => typeof x === 'string' ? x : vcUtil.inspect(x, { depth: 3 })).join(' '));
  let result;
  try { result = await new VC_AsyncFn('ctx', 'bot', 'vc', 'print', 'send', 'sleep', code)(ctx, bot, vc, print, (t, x) => vr(ctx, t, x), sleep); }
  catch (e) { result = L.eval_error + (e.stack || e); }
  if (result !== undefined || !out.length) print(result);
  const output = out.join('\n').trim(), response = vcFmt(L.eval_out, vcEsc(output));
  if (response.length > 4096) return ctx.replyWithDocument({ source: Buffer.from(output), filename: `${crypto.randomBytes(4).toString('hex')}.txt` }, { disable_notification: true });
  return vr(ctx, response);
}, { owner: true });
vcCmd('logs', async (ctx, L) => {
  const sent = await vr(ctx, L.log_fetch), r = await vc.get('/logs').catch(() => null);
  if (!r?.buf) return ve(ctx.chat.id, sent.message_id, L.log_not_found);
  vcDel(ctx.chat.id, sent.message_id);
  return ctx.replyWithDocument({ source: r.buf, filename: 'log.txt' }, { caption: vcFmt(L.log_sent, vcBotName()), ...vcH });
}, { sudo: true });
vcCmd('logger', async (ctx, L) => {
  const a = vcArgs(ctx)[0];
  if (!['on', 'off'].includes(a)) return vr(ctx, vcFmt(L.logger_usage, vcCmdName(ctx)));
  vcLogger = a === 'on';
  await vcCacheC.updateOne({ _id: 'logger' }, { $set: { status: vcLogger } }, { upsert: true });
  return vr(ctx, vcLogger ? L.logger_on : L.logger_off);
}, { sudo: true });
// restarts the music server (clears its cache/downloads) and exits this process: needs a supervisor (Railway / pm2 / docker restart policy) to bring it back
vcCmd('restart', async (ctx, L) => {
  const sent = await vr(ctx, L.restarting);
  vc.post('/restart').catch(() => {});
  await ve(ctx.chat.id, sent.message_id, L.restarted).catch(() => {});
  setTimeout(() => process.exit(1), 2000);
}, { sudo: true });

// ---------- callbacks ----------
vcAct(/^cancel_dl$/, async (ctx, L, chat, msg) => {
  await ctx.answerCbQuery().catch(() => {});
  const r = await vc.post('/cancel', { key: `${chat}:${msg.message_id}` });
  if (r.ok) return ve(chat, msg.message_id, vcFmt(L.dl_cancel, vcMention(ctx.from)), {}, !!msg.photo);
  return ctx.answerCbQuery(L.dl_not_found, { show_alert: true }).catch(() => {});
});

vcAct(/^controls (\w+) (-?\d+)(?: (\S+))?$/, async (ctx, L, _c, msg) => {
  const [, action, cid, extra] = ctx.match, chat = Number(cid), user = vcMention(ctx.from), qaction = extra === 'q' && action !== 'force';
  if (!(await vcCan(chat, ctx.from.id))) return vcDeny(ctx, L);
  const st = await vc.get('/state/' + chat);
  if (!st.active) { try { return await ctx.answerCbQuery(L.not_playing, { show_alert: true }); } catch { return vcDel(msg.chat.id, msg.message_id); } }
  if (action === 'status') return ctx.answerCbQuery().catch(() => {});
  await ctx.answerCbQuery(L.processing, { show_alert: true }).catch(() => {});
  const warn = text => ctx.answerCbQuery(text, { show_alert: true }).catch(() => {});
  let status, reply;

  if (action === 'pause') {
    const r = await vc.post('/pause', { chat_id: chat }); if (!r.ok) return warn(vcApiErr(L, r.error));
    if (qaction) return bot.telegram.editMessageReplyMarkup(msg.chat.id, msg.message_id, undefined, kbQueue(chat, L.paused, false).reply_markup).catch(() => {});
    status = L.paused; reply = vcFmt(L.play_paused, user);
  } else if (action === 'resume') {
    const r = await vc.post('/resume', { chat_id: chat }); if (!r.ok) return warn(vcApiErr(L, r.error));
    if (qaction) return bot.telegram.editMessageReplyMarkup(msg.chat.id, msg.message_id, undefined, kbQueue(chat, L.playing, true).reply_markup).catch(() => {});
    reply = vcFmt(L.play_resumed, user);
  } else if (action === 'skip') {
    await vc.post('/skip', { chat_id: chat }); status = L.skipped; reply = vcFmt(L.play_skipped, user);
  } else if (action === 'force') {
    const r = await vc.post('/force', { chat_id: chat, track_id: extra }, 120000);
    if (!r.ok) return ve(msg.chat.id, msg.message_id, vcApiErr(L, r.error), {}, !!msg.photo);
    return;   // server emits next_downloading / track_started, the event handlers do the messages
  } else if (action === 'replay') {
    await vc.post('/replay', { chat_id: chat, user }); status = L.replayed; reply = vcFmt(L.play_replayed, user);
  } else if (action === 'stop') {
    await vc.post('/stop', { chat_id: chat }); status = L.stopped; reply = vcFmt(L.play_stopped, user);
  } else return;

  if (['skip', 'replay', 'stop'].includes(action)) {
    await vcSay(msg.chat.id, reply);
    return vcDel(msg.chat.id, msg.message_id);
  }
  const cur = vcMsg.get(chat), base = cur && cur.id === msg.message_id ? cur.text : vcEsc(msg.caption || msg.text || '');
  await ve(msg.chat.id, msg.message_id, `${base}\n<blockquote>${reply}</blockquote>`, kbControls(chat, { status: action === 'resume' ? undefined : status }), !!msg.photo);
});

vcAct(/^help(?: (\w+))?$/, async (ctx, L, chat, msg) => {
  const a = ctx.match[1];
  if (!a) return ctx.answerCbQuery(undefined, { url: `https://t.me/${bot.botInfo?.username}?start=help` }).catch(() => {});
  if (a === 'back') return ve(chat, msg.message_id, L.help_menu, kbHelp(L));
  if (a === 'close') { await vcDel(chat, msg.message_id); return vcDel(chat, msg.reply_to_message?.message_id); }
  return ve(chat, msg.message_id, L[`help_${a}`] || L.help_menu, kbHelp(L, true));
});
vcAct(/^settings(?: (\w+))?$/, async (ctx, L, chat, msg) => {
  if (!(await vcAdminOnly(ctx, L))) return;
  const a = ctx.match[1];
  if (!a) return ctx.answerCbQuery().catch(() => {});
  await ctx.answerCbQuery(L.processing, { show_alert: true }).catch(() => {});
  if (a === 'delete') await vcFlag(chat, 'cmd_delete', vcCmdDel, !vcCmdDel.has(chat));
  else if (a === 'play') await vcFlag(chat, 'admin_play', vcAdminPlay, !vcAdminPlay.has(chat));
  await bot.telegram.editMessageReplyMarkup(chat, msg.message_id, undefined, kbSettings(L, vcAdminPlay.has(chat), vcCmdDel.has(chat), vcLangMap.get(chat) || VC_LANG_DEFAULT).reply_markup).catch(() => {});
});
vcAct(/^(language|lang_change (\w+))$/, async (ctx, L, chat, msg) => {
  if (!(await vcAdminOnly(ctx, L))) return;
  const cur = vcLangMap.get(chat) || VC_LANG_DEFAULT, code = ctx.match[2];
  if (!code) return ve(chat, msg.message_id, L.lang_choose, kbLang(cur), !!msg.photo);
  if (!VC_LANGS[code]) return ctx.answerCbQuery().catch(() => {});
  if (cur === code) return ctx.answerCbQuery(vcFmt(L.lang_same, cur), { show_alert: true }).catch(() => {});
  await ctx.answerCbQuery(vcFmt(L.lang_change, code), { show_alert: true }).catch(() => {});
  vcLangMap.set(chat, code); await vcLangC.updateOne({ _id: chat }, { $set: { lang: code } }, { upsert: true });
  return ve(chat, msg.message_id, vcFmt(VC_LANGS[code].lang_changed, code), {}, !!msg.photo);
});

// ---------- inline search ----------
bot.on('inline_query', async ctx => {
  try {
    const q = (ctx.inlineQuery.query || '').trim().toLowerCase();
    if (!q || vcBlUsers.has(ctx.from.id)) return;
    const r = await vc.get(`/search?q=${encodeURIComponent(q)}&limit=15`);
    const title = s => s.replace(/\w\S*/g, w => w[0].toUpperCase() + w.slice(1).toLowerCase());
    const results = (r.results || []).map(v => ({
      type: 'photo', id: crypto.createHash('md5').update(v.link).digest('hex'), photo_url: v.thumbnail, thumbnail_url: v.thumbnail, title: title(v.title),
      description: `${v.views} | ${v.duration} | ${v.channel} | ${v.published}`, parse_mode: 'HTML',
      caption: `<b>Title:</b> <a href='${v.link}'>${vcEsc(title(v.title).slice(0, 250))}</a>\n<b>Duration:</b> ${vcEsc(v.duration)}\n<b>Views:</b> <code>${vcEsc(v.views)}</code>\n<b>Channel:</b> <a href='${v.channel_link}'>${vcEsc(v.channel)}</a>\n<b>Published:</b> ${vcEsc(v.published)}\n<u><i>Fetched by ${vcEsc(vcBotName())}</i></u>`,
      ...kbYt(v.link),
    })).filter(x => x.photo_url);
    if (results.length) await ctx.answerInlineQuery(results, { cache_time: 5 });
  } catch (e) { log(`vc inline: ${e.description || e.message}`); }
});

// ---------- service messages: new members (log the chat / leave non-supergroups) and voice chat start/end (stop the stream) ----------
bot.on('message', async (ctx, next) => {
  try {
    const m = ctx.message;
    if (m.video_chat_started || m.video_chat_ended) vc.post('/stop', { chat_id: ctx.chat.id }).catch(() => {});
    if (m.new_chat_members?.some(u => u.id === ctx.botInfo?.id)) {
      if (ctx.chat.type !== 'supergroup') await bot.telegram.leaveChat(ctx.chat.id).catch(() => {});
      else { await sleep(3000); if (!vcChats.has(ctx.chat.id)) { await vcLog(vcFmt((await vcLangOf(ctx.chat.id)).log_chat, ctx.chat.id, vcEsc(ctx.chat.title), m.from?.id || 0, m.from ? vcMention(m.from) : 'Anonymous')); await vcAddChat(ctx.chat.id); } }
    }
  } catch (e) { vcErr(e); }
  return next();
});

async function vcInit(db) {
  vcChatsC = db.collection('vc_chats'); vcUsersC = db.collection('vc_users'); vcAuthC = db.collection('vc_auth'); vcLangC = db.collection('vc_lang'); vcCacheC = db.collection('vc_cache');
  for (const c of await vcChatsC.find().toArray()) { vcChats.add(c._id); if (c.cmd_delete) vcCmdDel.add(c._id); if (c.admin_play) vcAdminPlay.add(c._id); }
  for (const u of await vcUsersC.find().toArray()) vcUsers.add(u._id);
  for (const l of await vcLangC.find().toArray()) vcLangMap.set(l._id, l.lang);
  for (const id of (await vcCacheC.findOne({ _id: 'sudoers' }))?.user_ids || []) vcSudo.add(id);
  for (const id of (await vcCacheC.findOne({ _id: 'bl_users' }))?.user_ids || []) vcBlUsers.add(id);
  for (const id of (await vcCacheC.findOne({ _id: 'bl_chats' }))?.chat_ids || []) vcBlChats.add(id);
  vcLogger = !!(await vcCacheC.findOne({ _id: 'logger' }))?.status;
  if (!VC_URL) return console.warn('[vc] VC_API_URL is not set, music commands will answer that the music server is unreachable');
  vcPoll();
  setInterval(() => vcTimer().catch(() => {}), 7000);
  log(`vc music ready: server=${VC_URL} owner=${VC_OWNER} chats=${vcChats.size} users=${vcUsers.size} sudo=${vcSudo.size} langs=${Object.keys(VC_LANGS).join(',')}`);
}
// ---------- end of VC music ----------

// Inline bots (e.g. @music bots) first post a "loading" message and later swap in the real audio with editMessageMedia.
// Telegram delivers that swap as an `edited_message` update, not a `message`, so both are handled by the same function.
async function onAudioMsg(ctx, m, next, edited = false) {
  const a = getAudio(m);
  if (a && (ctx.from?.is_bot || m.sender_chat)) {
    log(`IGNORED audio msg=${m.message_id} chat=${m.chat.id} from=${who(ctx.from)} sender_chat=${m.sender_chat?.id || '-'}`);
    if (!edited && (m.sender_chat || [1087968824, 136817688].includes(ctx.from?.id)))   // anonymous admin / channel identity: no real user to credit
      await sayAuto(ctx, m.chat, '⚠️ I can’t save songs sent anonymously or as a channel. Send it from your own account.', m.message_id);
    return;
  }
  if (!a) {
    if (m.via_bot && !edited) log(`inline message from @${m.via_bot.username} has no audio yet (chat=${m.chat.id} msg=${m.message_id}), waiting for its edit`);
    else if (process.env.DEBUG_ALL === '1') log(`ignored ${edited ? 'edit' : 'msg'} chat=${m.chat.id} from=${who(ctx.from)} kind=${Object.keys(m).filter(k => !['message_id', 'from', 'chat', 'date'].includes(k)).join(',')}`);
    return next();
  }
  if (edited) {   // caption/other edits of a song we already have must not re-trigger anything
    const have = await songs.findOne({ chat_id: m.chat.id, file_unique_id: a.file_unique_id }, { projection: { _id: 1 } });
    if (have) return log(`edit of already-saved audio msg=${m.message_id}, ignoring`);
  }
  log(`received audio${edited ? ' (edited)' : ''}${m.via_bot ? ` via @${m.via_bot.username}` : ''} chat=${m.chat.id} (${m.chat.type}) from=${who(ctx.from)} msg=${m.message_id}`);
  try { await enqueueAudio(m, a); }   // saved to Mongo before we return, so Telegram only moves on once the song is safely in line
  catch (e) { console.error(`[${new Date().toISOString()}] [audio] enqueue failed:`, e); await sayAuto(ctx, m.chat, '⚠️ Could not queue this song, please send it again.', m.message_id); }
}
bot.on('message', (ctx, next) => onAudioMsg(ctx, ctx.message, next));
bot.on('edited_message', (ctx, next) => onAudioMsg(ctx, ctx.editedMessage, next, true));

bot.catch((err, ctx) => console.error(`[${new Date().toISOString()}] [bot] unhandled error on ${ctx.updateType}:`, err));

// ---------- boot ----------
(async () => {
  mm = await import('music-metadata');
  hub = await import('@huggingface/hub');
  const client = await new MongoClient(MONGO_URI).connect();
  const db = client.db('naudio_bot');
  const udb = client.db(UPLOADER_DB);
  hfFiles = udb.collection('xfiles');
  stagedFiles = db.collection('staged_files');
  await stagedFiles.createIndex({ short_code: 1 }, { unique: true });
  await stagedFiles.createIndex({ created_at: 1 });
  hfSettings = udb.collection('xsettings');
  await hfFiles.createIndex({ short_code: 1 }, { unique: true }).catch(e => console.warn('[hf] short_code index skipped:', e.message));
  if (!hfAccounts().length) console.warn('[hf] no Hugging Face accounts configured (HF_USERNAME/HF_TOKEN)');
  users = db.collection('users');
  songs = db.collection('songs');
  queues = db.collection('queues');
  capsules = db.collection('capsules');
  capSongs = db.collection('capsule_songs');
  jobs = db.collection('jobs');
  imports = db.collection('spotify_imports');
  importItems = db.collection('spotify_import_items');
  lhours = db.collection('listen_hours');
  await lhours.createIndex({ h: 1, song_id: 1 });
  await lhours.createIndex({ expire_at: 1 }, { expireAfterSeconds: 0 });
  nowp = db.collection('nowplaying');
  await nowp.createIndex({ expire_at: 1 }, { expireAfterSeconds: 0 });
  await jobs.createIndex({ status: 1, retry_at: 1, order: 1 });
  await jobs.createIndex({ expire_at: 1 }, { expireAfterSeconds: 0 });
  await imports.createIndex({ user_id: 1, created_at: -1 });
  await imports.createIndex({ expire_at: 1 }, { expireAfterSeconds: 0 });
  await importItems.createIndex({ status: 1, retry_at: 1, order: 1 });
  await importItems.createIndex({ import_id: 1, idx: 1 });
  await importItems.createIndex({ expire_at: 1 }, { expireAfterSeconds: 0 });
  const back = await jobs.updateMany({ status: 'processing' }, { $set: { status: 'pending', retry_at: new Date() } });   // interrupted by a restart: back in line
  if (back.modifiedCount) log(`requeued ${back.modifiedCount} interrupted job(s)`);
  const backI = await importItems.updateMany({ status: 'processing' }, { $set: { status: 'pending', retry_at: new Date() } });   // same for Spotify import items
  if (backI.modifiedCount) log(`requeued ${backI.modifiedCount} interrupted import item(s)`);
  await queues.createIndex({ updated_at: 1 }, { expireAfterSeconds: 30 * 24 * 3600 });
  await songs.createIndex({ chat_id: 1, file_unique_id: 1 }, { unique: true });
  await songs.createIndex({ song_id: 1 }, { unique: true, sparse: true });
  await songs.createIndex({ user_id: 1, created_at: -1 });
  await songs.createIndex({ listens: -1, created_at: -1 });
  await songs.createIndex({ user_id: 1, listens: -1, created_at: -1 });
  await songs.createIndex({ user_id: 1, pos: 1, created_at: -1 });
  await capsules.createIndex({ user_id: 1, name_key: 1 }, { unique: true });
  await capSongs.createIndex({ capsule_id: 1, song_id: 1 }, { unique: true });
  await capSongs.createIndex({ capsule_id: 1, pos: 1 });
  await capSongs.createIndex({ user_id: 1, song_id: 1 });
  await songs.createIndex({ user_id: 1, artist: 1 });
  await songs.createIndex({ user_id: 1, genre: 1 });
  await songs.createIndex({ user_id: 1, release_date: -1 });
  // one-time (idempotent) catbox cleanup: delete songs whose audio is on catbox, drop catbox images, delete capsules that only held those songs
  try {
    const cb = /catbox\.moe/i;
    const bad = await songs.find({ upload_url: cb }, { projection: { song_id: 1, user_id: 1 } }).toArray();
    if (bad.length) {
      const ids = bad.map(x => x.song_id).filter(Boolean), chunks = [];
      for (let i = 0; i < ids.length; i += 2000) chunks.push(ids.slice(i, i + 2000));
      const hit = new Set();
      for (const c of chunks) for (const x of await capSongs.find({ song_id: { $in: c } }, { projection: { capsule_id: 1 } }).toArray()) hit.add(x.capsule_id);
      let capsDeleted = 0;
      for (const cid of hit) {   // regular capsule whose songs are all catbox -> delete it (checked before the songs go)
        const total = await capSongs.countDocuments({ capsule_id: cid });
        const nBad = await capSongs.countDocuments({ capsule_id: cid, song_id: { $in: ids } });
        if (total > 0 && total === nBad) { await Promise.all([capsules.deleteOne({ _id: cid }), capSongs.deleteMany({ capsule_id: cid })]); capsDeleted++; }
      }
      const perUser = new Map();
      for (const x of bad) perUser.set(x.user_id, (perUser.get(x.user_id) || 0) + 1);
      for (const c of chunks) {
        await capSongs.deleteMany({ song_id: { $in: c } });
        await capsules.updateMany({}, { $pull: { include: { $in: c }, excluded: { $in: c } } });
        await songs.deleteMany({ song_id: { $in: c } });
      }
      for (const [uid, n] of perUser) await users.updateOne({ _id: uid }, { $inc: { song_count: -n } });
      log(`catbox cleanup: ${bad.length} song(s) deleted, ${capsDeleted} capsule(s) deleted`);
    }
    for (const f of ['cover_url', 'poster_url']) await songs.updateMany({ [f]: cb }, { $set: { [f]: null } });
    await songs.updateMany({ image_url: cb }, [{ $set: { image_url: { $ifNull: ['$poster_url', '$cover_url'] } } }]);
    for (const f of ['theme.avatar', 'theme.bgImage']) await users.updateMany({ [f]: cb }, { $unset: { [f]: '' } });
  } catch (e) { console.warn(`[${new Date().toISOString()}] [audio] catbox cleanup failed:`, e.message); }
  // one-time (idempotent) migration: point every stored short link (<host>/<6 chars>.<ext>) at SHORT_URL_BASE
  try {
    const esc = SHORT_URL_BASE.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const oldLink = /^https?:\/\/(?!huggingface\.co\/)[^\/]+\/[a-z0-9]{6}\.[a-z0-9]+$/, isNew = new RegExp('^' + esc);
    const rewrite = f => [{ $set: { [f]: { $concat: [SHORT_URL_BASE, { $arrayElemAt: [{ $split: ['$' + f, '/'] }, -1] }] } } }];
    for (const [col, f] of [[songs, 'upload_url'], [songs, 'cover_url'], [songs, 'poster_url'], [songs, 'image_url'], [users, 'theme.avatar'], [users, 'theme.bgImage']]) {
      const r = await col.updateMany({ $and: [{ [f]: oldLink }, { [f]: { $not: isNew } }] }, rewrite(f));
      if (r.modifiedCount) log(`url migration: ${f} -> ${r.modifiedCount} updated`);
    }
  } catch (e) { console.warn(`[${new Date().toISOString()}] [audio] url migration failed:`, e.message); }
  await vcInit(db);   // VC music (AviaxMusic port)
  startApi({ songs, users, queues });
  log(`staging dir ${STAGE_DIR} batch=${BATCH_SIZE} max_age=${BATCH_MAX_AGE_MS / 60000}min`);
  setInterval(() => maybeFlush().catch(e => console.error(`[${new Date().toISOString()}] [audio] flush error:`, e.message)), 30000);
  maybeFlush().catch(() => {});
  pump();
  pumpImports();
  setInterval(async () => {   // safety net: wake due retries, rescue jobs stuck in "processing"
    try { await jobs.updateMany({ status: 'processing', started_at: { $lt: new Date(Date.now() - JOB_TIMEOUT_MS - 60000) } }, { $set: { status: 'pending', retry_at: new Date() } }); } catch {}
    pump();
    importTick();
  }, 10000);
  if (process.env.BACKFILL_DEEZER === '1') backfillDeezer().catch(e => console.error('[deezer backfill] failed:', e));
  try {
    const me = await bot.telegram.getMe();
    log(`bot @${me.username} id=${me.id} can_read_all_group_messages=${me.can_read_all_group_messages}${me.can_read_all_group_messages ? '' : '  <-- privacy mode is ON, bot only sees commands/replies in groups'}`);
  } catch (e) { console.error('getMe failed:', e.message); }
  await bot.launch(() => log('polling started - bot is live, send /upload now'));
})().catch(e => { console.error('[FATAL] startup failed:', e); process.exit(1); });

process.once('SIGINT', () => bot.stop('SIGINT'));
process.once('SIGTERM', () => bot.stop('SIGTERM'));
