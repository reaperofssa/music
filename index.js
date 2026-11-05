require('dotenv').config();
const { Telegraf } = require('telegraf');
const { MongoClient } = require('mongodb');
const crypto = require('crypto');
const path = require('path');
const express = require('express');
const cors = require('cors');

const { BOT_TOKEN, MONGO_URI, HF_TOKEN, HF_USERNAME, HF_BACKUP_ACCOUNTS = '' } = process.env;
const SHORT_URL_BASE = process.env.SHORT_URL_BASE ?? 'https://uploadnx.zone.id/'; // set empty to use raw HF urls
const UPLOADER_DB = process.env.UPLOADER_DB || 'xcatbox_clone'; // same db the python uploader / short-url service uses
const MAX_DATASET_SIZE = 12 * 1024 ** 3;   // 12GB per dataset
const MAX_ACCOUNT_STORAGE = 150 * 1024 ** 3; // 150GB per account
const DEST_DIR = 'uploads';
const log = (...a) => console.log(`[${new Date().toISOString()}] [audio]`, ...a);
const who = u => u ? `${u.id}${u.username ? ' @' + u.username : ''}` : '?';
const mb = n => n ? (n / 1048576).toFixed(2) + 'MB' : '?';
const bot = new Telegraf(BOT_TOKEN);
let users, songs, queues, mm, hub, hfFiles, hfSettings;

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

// returns { buf, deezerId, album } or null
async function findPoster({ title, artist, duration }) {
  if (!title) return null;
  const q = encodeURIComponent(`${title} ${artist || ''}`.trim());
  const r = await fetch(`https://api.deezer.com/search?q=${q}&limit=10`);
  if (!r.ok) return null;
  const { data = [] } = await r.json();
  const v = pickMatch(data, { title, artist, duration });
  if (!v) return null;
  const buf = await fetchCover(v.album);
  return buf ? { buf, deezerId: v.id, album: v.album?.title || null } : null;
}

// ---------- api ----------
const BASE = (process.env.BASE_URL || '').replace(/\/$/, '');
const PER_PAGE = 80;
const HOT_LIMIT = 60;
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

    const u = await users.findOne({ _id: uid });
    if (!u) return res.status(404).json({ error: 'user not found' });

    const [total, items] = await Promise.all([
      songs.countDocuments({ user_id: uid }),
      songs.find({ user_id: uid }).sort({ created_at: -1 }).skip((page - 1) * PER_PAGE).limit(PER_PAGE).toArray(),
    ]);
    res.json({
      user: shapeUser(u),
      page,
      per_page: PER_PAGE,
      total,
      pages: Math.ceil(total / PER_PAGE),
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
    const { song_id, user_id, hot, shuffle } = req.body || {};
    let ids = [];
    if (user_id != null) {
      ids = (await songs.find({ user_id: Number(user_id), uploaded: true })
        .sort({ created_at: -1 }).limit(500).project({ song_id: 1 }).toArray()).map(s => s.song_id);
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

const extOf = (name, mime) =>
  (name && name.includes('.') ? name.split('.').pop() : (mime || '').split('/').pop() || 'mp3')
    .toLowerCase().replace(/[^a-z0-9]/g, '') || 'mp3';

function getAudio(msg) {
  if (msg.audio) return msg.audio;
  if (msg.document?.mime_type?.startsWith('audio/')) return msg.document;
  return null;
}

// ---------- core ----------
async function processAudio(ctx, a) {
  const { from, chat, message_id } = ctx.message;

  const t0 = Date.now();
  log(`start msg=${message_id} chat=${chat.id} "${chat.title || chat.type}" user=${who(from)} file="${a.file_name || a.title || '?'}" size=${mb(a.file_size)} mime=${a.mime_type || '?'}`);
  if (a.file_size && a.file_size > 20 * 1024 * 1024) log('WARN file > 20MB, Telegram Bot API cannot download it');
  if (await songs.findOne({ file_unique_id: a.file_unique_id, chat_id: chat.id })) { log(`skip duplicate file_unique_id=${a.file_unique_id} in chat=${chat.id}`); return; }

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
      const p = await findPoster({
        title: song.title || (a.file_name || '').replace(/\.[^.]+$/, ''),
        artist: song.artist,
        duration: song.duration,
      });
      if (p) {
        const pr = await uploadToHost(p.buf, `${a.file_unique_id}_poster.jpg`, 'image/jpeg');
        song.poster_url = pr.short_url;
        song.deezer_id = p.deezerId;
        if (!song.album) song.album = p.album;
        log(`poster uploaded deezer=${p.deezerId} ${pr.short_url}`);
      } else log('poster: no deezer match');
    } catch (e) { console.warn(`[${new Date().toISOString()}] [audio] poster failed:`, e.message); }

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
  await ctx.reply(song.uploaded ? `✅ Saved: ${label}` : `⚠️ Logged (not uploaded: ${song.upload_error}): ${label}`,
    { reply_parameters: { message_id } }).catch(() => {});
}

// ---------- handlers ----------
bot.command('top', async ctx => {
  const top = await users.find().sort({ song_count: -1 }).limit(10).toArray();
  if (!top.length) return ctx.reply('No songs yet.');
  ctx.reply(top.map((u, i) =>
    `${i + 1}. ${u.username ? '@' + u.username : u.first_name} — ${u.song_count}`).join('\n'));
});

bot.command('me', async ctx => {
  const u = await users.findOne({ _id: ctx.from.id });
  ctx.reply(`You've shared ${u?.song_count || 0} songs.`);
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
  await hfFiles.createIndex({ short_code: 1 }, { unique: true });
  if (!hfAccounts().length) console.warn('[hf] no Hugging Face accounts configured (HF_USERNAME/HF_TOKEN)');
  users = db.collection('users');
  songs = db.collection('songs');
  queues = db.collection('queues');
  await queues.createIndex({ updated_at: 1 }, { expireAfterSeconds: 30 * 24 * 3600 });
  await songs.createIndex({ chat_id: 1, file_unique_id: 1 }, { unique: true });
  await songs.createIndex({ song_id: 1 }, { unique: true, sparse: true });
  await songs.createIndex({ user_id: 1, created_at: -1 });
  await songs.createIndex({ listens: -1, created_at: -1 });
  startApi({ songs, users, queues });
  try {
    const me = await bot.telegram.getMe();
    log(`bot @${me.username} id=${me.id} can_read_all_group_messages=${me.can_read_all_group_messages}${me.can_read_all_group_messages ? '' : '  <-- privacy mode is ON, bot only sees commands/replies in groups'}`);
  } catch (e) { console.error('getMe failed:', e.message); }
  await bot.launch();
  console.log('audio bot running');
})();

process.once('SIGINT', () => bot.stop('SIGINT'));
process.once('SIGTERM', () => bot.stop('SIGTERM'));
