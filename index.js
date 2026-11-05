require('dotenv').config();
const { Telegraf, Markup } = require('telegraf');
const { MongoClient } = require('mongodb');
const crypto = require('crypto');
const path = require('path');
const express = require('express');
const cors = require('cors');

const { BOT_TOKEN, MONGO_URI, HF_TOKEN, HF_USERNAME, HF_BACKUP_ACCOUNTS = '' } = process.env;
const SHORT_URL_BASE = process.env.SHORT_URL_BASE ?? (process.env.BASE_URL ? process.env.BASE_URL.replace(/\/$/, '') + '/' : ''); // short-link prefix; empty = raw HF urls
const UPLOADER_DB = process.env.UPLOADER_DB || 'xcatbox_clone'; // same db the python uploader / short-url service uses
const MAX_DATASET_SIZE = 12 * 1024 ** 3;   // 12GB per dataset
const MAX_ACCOUNT_STORAGE = 150 * 1024 ** 3; // 150GB per account
const DEST_DIR = 'uploads';
const log = (...a) => console.log(`[${new Date().toISOString()}] [audio]`, ...a);
const who = u => u ? `${u.id}${u.username ? ' @' + u.username : ''}` : '?';
const mb = n => n ? (n / 1048576).toFixed(2) + 'MB' : '?';
const bot = new Telegraf(BOT_TOKEN);
let users, songs, queues, capsules, capSongs, mm, hub, hfFiles, hfSettings;

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
      const r = await fetch(u);
      if (!r.ok) continue;
      const buf = Buffer.from(await r.arrayBuffer());
      if (buf.length > 3000) return buf;
    } catch {}
  }
  return null;
}

const sleep = ms => new Promise(r => setTimeout(r, ms));

// genres / release date / label live on the album endpoint (search results don't carry them)
async function fetchAlbumMeta(albumId) {
  if (!albumId) return {};
  try {
    const r = await fetch(`https://api.deezer.com/album/${albumId}`);
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
  const r = await fetch(`https://api.deezer.com/search?q=${q}&limit=10`);
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
        const r = await fetch(`https://api.deezer.com/track/${s.deezer_id}`);
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
function verifyInitData(raw) {
  const params = new URLSearchParams(String(raw || ''));
  const hash = params.get('hash');
  if (!hash) return null;
  params.delete('hash');
  const check = [...params.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).map(([k, v]) => `${k}=${v}`).join('\n');
  if (!same(Buffer.from(hash, 'hex'), hmac(hmac('WebAppData', BOT_TOKEN), check))) return null;
  if (Date.now() / 1000 - Number(params.get('auth_date')) > INITDATA_MAX_AGE) return null;
  try { const u = JSON.parse(params.get('user')); return Number.isInteger(u?.id) ? u : null; } catch { return null; }
}
const cookieOf = (req, name) => (req.headers.cookie || '').split(';').map(c => c.trim().split(/=(.*)/s)).find(([k]) => k === name)?.[1];

// ---------- api ----------
const BASE = (process.env.BASE_URL || '').replace(/\/$/, '');
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

const HEX = /^#[0-9a-f]{6}$/i;
const THEME_ENUM = {
  mode: ['auto', 'light', 'dark'],
  font: ['system', 'serif', 'mono', 'rounded', 'display', 'condensed'],
  radius: ['sharp', 'soft', 'round'],
  card: ['solid', 'glass', 'outline'],
  effect: ['none', 'petals', 'snow', 'stars', 'hearts', 'fireflies', 'rain', 'bubbles', 'leaves'],
  effectDensity: ['low', 'med', 'high'],
  avatarShape: ['round', 'squircle', 'square'],
  hero: ['auto', 'center', 'left'],
  heroCover: ['art', 'avatar'],
  coverShape: ['square', 'soft', 'round'],
  density: ['comfy', 'compact'],
  player: ['solid', 'glass'],
};
const THEME_NUM = { gradAngle: [0, 360], effectSpeed: [0.3, 2.5], bgBlur: [0, 24], bgDim: [0, 85] };
const THEME_BOOL = ['artColor', 'heroGlow', 'showPlays', 'showStats'];
const THEME_HEX = ['bg', 'accent', 'bg2', 'effectColor'];
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
  setInterval(() => {
    const cut = Date.now() - LISTEN_WINDOW;
    for (const [k, t] of seen) if (t < cut) seen.delete(k);
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

  app.get('/info/:songid', wrap(async (req, res) => {
    const s = await songs.findOne({ song_id: req.params.songid });
    if (!s) return res.status(404).json({ error: 'song not found' });
    const u = await users.findOne({ _id: s.user_id });
    res.json({ song: shapeSong(s), listens: s.listens || 0, added_by: shapeUser(u) });
  }));

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

  // public: [] when the user has no capsules, else [All, ...capsules] with counts and cover art
  app.get('/playlist/:userid/capsules', wrap(async (req, res) => {
    const uid = Number(req.params.userid);
    if (!Number.isInteger(uid)) return res.status(400).json({ error: 'invalid user id' });
    const u = await users.findOne({ _id: uid });
    if (!u) return res.status(404).json({ error: 'user not found' });
    const caps = await capsules.find({ user_id: uid }).sort({ created_at: 1 }).toArray();
    if (!caps.length) return res.json({ user: shapeUser(u), count: 0, capsules: [] });
    const [total, counts] = await Promise.all([
      songs.countDocuments({ user_id: uid }),
      capSongs.aggregate([{ $match: { user_id: uid } }, { $group: { _id: '$capsule_id', n: { $sum: 1 } } }]).toArray(),
    ]);
    const n = new Map(counts.map(c => [c._id, c.n]));
    const gCount = new Map(await Promise.all(caps.filter(c => c.genre).map(async c => [c._id, await songs.countDocuments(capFilter(uid, c))])));
    const out = await Promise.all([{ _id: 'all', name: 'All', count: total }, ...caps.map(c => ({ _id: c._id, name: c.name, genre: c.genre || null, include: c.include, excluded: c.excluded, count: c.genre ? gCount.get(c._id) : n.get(c._id) || 0 }))]
      .map(async c => ({ id: c._id, name: c.name, genre: c.genre || null, count: c.count, covers: await coversOf(uid, c) })));
    res.json({ user: shapeUser(u), count: caps.length, capsules: out });
  }));

  app.post('/me/capsules', auth, wrap(async (req, res) => {
    const name = cleanName(req.body?.name);
    if (!name) return res.status(400).json({ error: 'name required' });
    if (await capsules.countDocuments({ user_id: req.uid }) >= MAX_CAPSULES) return res.status(400).json({ error: `max ${MAX_CAPSULES} capsules` });
    const c = { _id: crypto.randomBytes(5).toString('hex'), user_id: req.uid, name, name_key: name.toLowerCase(), created_at: new Date() };
    try { await capsules.insertOne(c); } catch (e) { if (dupKey(e)) return res.status(409).json({ error: 'you already have a capsule with that name' }); throw e; }
    res.status(201).json({ id: c._id, name: c.name, count: 0 });
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
    const f = await hfFiles.findOne({ short_code: req.params[0] }, { projection: { hf_url: 1 } });
    if (!f) return res.status(404).json({ error: 'file not found' });
    res.set('Cache-Control', 'public, max-age=86400');
    res.redirect(302, f.hf_url);
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

const queue = (() => { let p = Promise.resolve(); return fn => (p = p.then(fn, fn)); })(); // one job at a time

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
    if (!(await hfFiles.findOne({ short_code: code }, { projection: { _id: 1 } }))) return code;
  }
}

async function ensureDataset(repoName, token) {
  const repo = { type: 'dataset', name: repoName };
  if (await hub.repoExists({ repo, accessToken: token })) return;
  await hub.createRepo({
    repo, accessToken: token, visibility: 'public', license: 'mit',
    files: [{ path: 'README.md', content: new Blob([`---\nlicense: mit\n---\n\n# File Storage Dataset\n\nFiles live in \`${DEST_DIR}/\`.\n`]) }],
  });
}

// uploads one buffer straight to Hugging Face, trying each account in order. returns { short_url, code, hf_url }
async function uploadToHost(buf, filename, mime) {
  const size = buf.length;
  const ext = path.extname(filename);
  const errors = [];

  for (const { username, token } of hfAccounts()) {
    try {
      const st = await hfStorage(username);
      if (st.total_size + size > MAX_ACCOUNT_STORAGE) { errors.push(`${username}: full`); log(`hf ${username}: account full, trying next`); continue; }

      // newest dataset, or a fresh one when it would pass 12GB
      const last = st.datasets[st.datasets.length - 1];
      let name = last && last.size + size <= MAX_DATASET_SIZE ? last.name : null;
      if (!name) {
        do name = `file-storage-${1000 + crypto.randomInt(9000)}`; while (st.datasets.some(d => d.name === name));
      }
      const repoName = `${username}/${name}`;
      log(`hf try ${repoName} file=${filename} size=${mb(size)}${last && last.name === name ? '' : ' (new dataset)'}`);
      await ensureDataset(repoName, token);

      const code = await shortCode();
      const dest = `${DEST_DIR}/${code}${ext}`;
      await hub.uploadFile({
        repo: { type: 'dataset', name: repoName }, accessToken: token,
        file: { path: dest, content: new Blob([buf], { type: mime || 'application/octet-stream' }) },
        commitTitle: `Upload ${code}${ext}`,
      });

      const hf_url = `https://huggingface.co/datasets/${repoName}/resolve/main/${dest}`;
      await hfFiles.insertOne({ short_code: code, file_name: `${code}${ext}`, original_path: filename, hf_url, dataset: name, size, uploader: username });

      // bump counters: existing dataset entry first, else push a new one
      const id = `account_storage_${username}`;
      const r = await hfSettings.updateOne({ _id: id, 'datasets.name': name }, { $inc: { 'datasets.$.size': size, total_size: size } });
      if (!r.matchedCount) await hfSettings.updateOne({ _id: id }, { $inc: { total_size: size }, $push: { datasets: { name, size } } });

      log(`hf ok ${repoName}/${dest} total_used=${mb(st.total_size + size)}`);
      return { short_url: SHORT_URL_BASE ? `${SHORT_URL_BASE}${code}${ext}` : hf_url, code, hf_url };
    } catch (e) {
      errors.push(`${username}: ${e.message}`);
      console.warn(`[${new Date().toISOString()}] [audio] hf FAILED ${username}: ${e.message}`);
    }
  }
  throw new Error(`upload failed on all Hugging Face accounts (${errors.join('; ') || 'none configured'})`);
}

// reply that never throws but always logs why it failed; retries without reply_parameters (deleted msg / topic quirks)
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
async function react(ctx, chatId, messageId) {
  for (const emoji of REACT_TRY) {
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

function getAudio(msg) {
  if (msg.audio) return msg.audio;
  if (msg.document?.mime_type?.startsWith('audio/')) return msg.document;
  return null;
}

// ---------- core ----------
async function processAudio(ctx, a, msg = ctx.message, manual = false) {
  const { from, chat, message_id } = msg;

  const t0 = Date.now();
  log(`start msg=${message_id} chat=${chat.id} "${chat.title || chat.type}" user=${who(from)} file="${a.file_name || a.title || '?'}" size=${mb(a.file_size)} mime=${a.mime_type || '?'}`);
  if (a.file_size && a.file_size > 20 * 1024 * 1024) log('WARN file > 20MB, Telegram Bot API cannot download it');
  const dupe = await songs.findOne({ file_unique_id: a.file_unique_id, chat_id: chat.id });
  if (dupe) {
    log(`skip duplicate file_unique_id=${a.file_unique_id} in chat=${chat.id} (song_id=${dupe.song_id})`);
    if (manual) await say(ctx, `Already saved in this chat: ${dupe.title || 'song'} (id ${dupe.song_id}, uploaded=${dupe.uploaded})`, message_id);
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
    const dl = await fetch(link);
    if (!dl.ok) throw new Error(`telegram download failed ${dl.status}`);
    const buf = Buffer.from(await dl.arrayBuffer());
    log(`downloaded ${mb(buf.length)} in ${Date.now() - t0}ms`);
    const ext = extOf(a.file_name, a.mime_type);

    // metadata from the actual file
    try {
      const meta = await mm.parseBuffer(buf, { mimeType: a.mime_type }, { duration: true });
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
        const tr = await fetch(tl);
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
    song.upload_error = e.message;
    console.error(`[${new Date().toISOString()}] [audio] PROCESS ERROR msg=${message_id} user=${who(from)}:`, e.stack || e.message);
  }

  if (!song.title) song.title = (a.file_name || 'Unknown').replace(/\.[^.]+$/, '');

  song.image_url = song.poster_url || song.cover_url;
  await songs.insertOne(song);
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
    if (!(await react(ctx, chat.id, message_id))) await say(ctx, `✅ Saved: ${label}`, message_id); // fall back to a reply only if reacting is impossible here
  } else {
    await say(ctx, `⚠️ Logged (not uploaded: ${song.upload_error}): ${label}`, message_id);
  }
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
  queue(() => processAudio(ctx, a, { from: target.from, chat: m.chat, message_id: target.message_id }, true))
    .catch(e => console.error(`[${new Date().toISOString()}] [audio] /upload error:`, e));
});

bot.on('message', (ctx, next) => {
  const m = ctx.message, a = getAudio(m);
  if (!a || ctx.from.is_bot) {
    if (process.env.DEBUG_ALL === '1') log(`ignored msg chat=${m.chat.id} from=${who(ctx.from)} kind=${Object.keys(m).filter(k => !['message_id', 'from', 'chat', 'date'].includes(k)).join(',')}`);
    return next();
  }
  log(`received audio chat=${m.chat.id} (${m.chat.type}) from=${who(ctx.from)} queued`);
  queue(() => processAudio(ctx, a)).catch(e => console.error(`[${new Date().toISOString()}] [audio] queue error:`, e));
});

bot.catch((err, ctx) => console.error(`[${new Date().toISOString()}] [bot] unhandled error on ${ctx.updateType}:`, err));

// ---------- boot ----------
(async () => {
  mm = await import('music-metadata');
  hub = await import('@huggingface/hub');
  const client = await new MongoClient(MONGO_URI).connect();
  const db = client.db('audio_bot');
  const udb = client.db(UPLOADER_DB);
  hfFiles = udb.collection('xfiles');
  hfSettings = udb.collection('xsettings');
  await hfFiles.createIndex({ short_code: 1 }, { unique: true }).catch(e => console.warn('[hf] short_code index skipped:', e.message));
  if (!hfAccounts().length) console.warn('[hf] no Hugging Face accounts configured (HF_USERNAME/HF_TOKEN)');
  users = db.collection('users');
  songs = db.collection('songs');
  queues = db.collection('queues');
  capsules = db.collection('capsules');
  capSongs = db.collection('capsule_songs');
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
  startApi({ songs, users, queues });
  if (process.env.BACKFILL_DEEZER === '1') backfillDeezer().catch(e => console.error('[deezer backfill] failed:', e));
  try {
    const me = await bot.telegram.getMe();
    log(`bot @${me.username} id=${me.id} can_read_all_group_messages=${me.can_read_all_group_messages}${me.can_read_all_group_messages ? '' : '  <-- privacy mode is ON, bot only sees commands/replies in groups'}`);
  } catch (e) { console.error('getMe failed:', e.message); }
  await bot.launch(() => log('polling started - bot is live, send /upload now'));
})().catch(e => { console.error('[FATAL] startup failed:', e); process.exit(1); });

process.once('SIGINT', () => bot.stop('SIGINT'));
process.once('SIGTERM', () => bot.stop('SIGTERM'));
