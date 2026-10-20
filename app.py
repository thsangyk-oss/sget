import html, json, os, re, shutil, tempfile, threading, time, urllib.request, urllib.parse, uuid
from collections import deque

import yt_dlp
from flask import Flask, Response, jsonify, request, send_file

BASE = os.path.dirname(os.path.abspath(__file__))
SAVE_DIR = r"E:\devin_task\saved"
SAVE_DIR_D = r"D:\Video"
TMP_DIR = r"E:\devin_task\tmp_dl"
FFMPEG_DIR = r"E:\devin_task\ffmpeg"
SERVER_DIRS = {"server": SAVE_DIR_D, "serverx": SAVE_DIR}
os.makedirs(SAVE_DIR, exist_ok=True)
os.makedirs(SAVE_DIR_D, exist_ok=True)
os.makedirs(TMP_DIR, exist_ok=True)
for _d in os.listdir(TMP_DIR):
    shutil.rmtree(os.path.join(TMP_DIR, _d), ignore_errors=True)

app = Flask(__name__)

RES = {}   # rid -> {url, title, thumb, platform, duration, size, direct_url, headers}
JOBS = {}  # jid -> {status, progress, filename, path, error, for_device}

# ---------- access stats ----------
STATS_FILE = os.path.join(BASE, "stats.json")
HITS = deque()   # timestamps of tracked requests (rolling 24h)
IPS = {}         # ip -> last-seen ts
ACTIVE = [0]     # in-flight tracked requests
TRACK_PATHS = {"/", "/api/resolve", "/api/save"}
DEBUG_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hits_log.txt")
COOKIES_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cookies.txt")
TRACK_PREFIX = ("/api/file/", "/api/proxy/")

def _load_stats():
    try:
        d = json.load(open(STATS_FILE))
        now = time.time()
        HITS.extend(t for t in d.get("hits", []) if now - t <= 86400)
        IPS.update({k: v for k, v in d.get("ips", {}).items() if now - v <= 86400})
    except Exception:
        pass

def _save_stats():
    try:
        json.dump({"hits": list(HITS)[-10000:], "ips": IPS}, open(STATS_FILE, "w"))
    except Exception:
        pass

_load_stats()

@app.before_request
def _trk_in():
    p = request.path
    if p in TRACK_PATHS or p.startswith(TRACK_PREFIX):
        if request.method == "HEAD" or not request.headers.get("User-Agent"):
            return
        request._trk = True
        ACTIVE[0] += 1
        now = time.time()
        HITS.append(now)
        IPS[request.remote_addr or "?"] = now
        while HITS and now - HITS[0] > 86400:
            HITS.popleft()
        if len(IPS) > 3000:
            for k in [k for k, v in IPS.items() if now - v > 86400]:
                del IPS[k]
        _save_stats()

@app.teardown_request
def _trk_out(exc=None):
    if getattr(request, "_trk", False):
        ACTIVE[0] -= 1

@app.get("/api/status")
def api_status():
    now = time.time()
    return jsonify(
        active=ACTIVE[0],
        hits24=sum(1 for t in HITS if now - t <= 86400),
        ips24=sum(1 for t in IPS.values() if now - t <= 86400),
    )
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"

PLATFORM_NAMES = {
    "twitter": "X (Twitter)", "tiktok": "TikTok", "facebook": "Facebook",
    "youtube": "YouTube", "instagram": "Instagram", "bilibili": "Bilibili",
    "generic": "Web",
}

def safe_name(s):
    return re.sub(r'[\\/:*?"<>|\r\n]+', " ", (s or "video")).strip()[:120] or "video"

def resolve_x(url):
    m = re.search(r"(?:x|twitter)\.com/([^/]+)/status/(\d+)", url)
    if not m:
        raise ValueError("not a tweet url")
    api = f"https://api.fxtwitter.com/{m.group(1)}/status/{m.group(2)}"
    r = json.load(urllib.request.urlopen(
        urllib.request.Request(api, headers={"User-Agent": UA}), timeout=25))
    tw = r["tweet"]
    vids = (tw.get("media") or {}).get("videos") or []
    if not vids:
        raise ValueError("tweet has no video")
    fmts = [f for f in vids[0].get("formats", []) if f.get("container") == "mp4"]
    best = max(fmts, key=lambda f: f.get("bitrate", 0))
    v = vids[0]
    return {
        "title": (tw.get("text") or "").strip() or f"x_{m.group(2)}",
        "thumb": v.get("thumbnail_url"),
        "platform": "X (Twitter)",
        "duration": v.get("duration"),
        "size": None,
        "direct_url": best["url"],
        "direct_only": True,
        "headers": {"User-Agent": UA, "Referer": "https://x.com/"},
    }

def resolve_tiktok(url):
    api = "https://www.tikwm.com/api/?url=" + urllib.parse.quote(url, safe="")
    r = json.load(urllib.request.urlopen(
        urllib.request.Request(api, headers={"User-Agent": UA}), timeout=25))
    if r.get("code") != 0 or not r.get("data"):
        raise ValueError(r.get("msg") or "tikwm failed")
    d = r["data"]
    play = d.get("hdplay") or d.get("play")
    if not play:
        raise ValueError("no video in tiktok post")
    return {
        "title": (d.get("title") or "").strip() or f"tiktok_{d.get('id', '')}",
        "thumb": d.get("cover"),
        "platform": "TikTok",
        "duration": d.get("duration"),
        "size": d.get("hd_size") or d.get("size"),
        "direct_url": play,
        "direct_only": True,
        "headers": {"User-Agent": UA},
    }

# threads.net/.com are DNS-poisoned on some VN ISPs — resolve them via DoH
# to 1.1.1.1 (its cert carries IP SANs, so TLS to the literal IP validates).
import socket as _socket
_doh_cache = {}
_orig_getaddrinfo = _socket.getaddrinfo

def _doh_ips(host):
    if host in _doh_cache:
        return _doh_cache[host]
    ips = []
    try:
        j = json.load(urllib.request.urlopen(
            f"https://dns.google/resolve?name={host}&type=A", timeout=8))
        ips = [a["data"] for a in j.get("Answer", []) if a.get("type") == 1]
    except Exception:
        pass
    _doh_cache[host] = ips
    return ips

_DOH_HOSTS = {"threads.net", "www.threads.net", "threads.com", "www.threads.com"}

def _getaddrinfo(host, port, family=0, type=0, proto=0, flags=0):
    if host in _DOH_HOSTS:
        ips = _doh_ips(host)
        if ips:
            return [(_socket.AF_INET, _socket.SOCK_STREAM, 6, "", (ip, port))
                    for ip in ips]
    return _orig_getaddrinfo(host, port, family, type, proto, flags)

_socket.getaddrinfo = _getaddrinfo

def resolve_threads(url):
    # normalize to canonical post URL (follow /share/ redirects)
    pat = r"threads\.(?:com|net)/(?:@[^/]+/post|t)/([A-Za-z0-9_-]+)"
    m = re.search(pat, url)
    code = m.group(1) if m else None
    if not code:
        # share link → canonical post code; direct fetch first, then jina proxy
        # (threads blocks/throttles some IPs with a logged-out gating shell)
        code_pat = r"(?:post/|shortcode=)([A-Za-z0-9_-]{6,})"
        for fetch_url, extra in ((url, {}), ("https://r.jina.ai/" + url,
                                             {"X-Return-Format": "html"})):
            for _ in range(2):
                try:
                    hd = {"User-Agent": UA}
                    hd.update(extra)
                    r = urllib.request.urlopen(urllib.request.Request(
                        fetch_url, headers=hd), timeout=40)
                    mm = re.search(pat, r.geturl()) or re.search(
                        code_pat, r.read().decode("utf-8", "ignore"))
                    if mm:
                        code = mm.group(1)
                except Exception:
                    pass
                if code:
                    break
                time.sleep(1.5)
            if code:
                break
    if not code:
        raise ValueError("not a threads post url")
    # embed page renders media for crawlers — contains direct mp4 in <source>.
    # try both hosts direct, then via jina proxy when our IP is gated.
    h = ""
    for fetch_url, extra in (
            (f"https://www.threads.net/t/{code}/embed", {}),
            (f"https://www.threads.com/t/{code}/embed", {}),
            (f"https://r.jina.ai/https://www.threads.net/t/{code}/embed",
             {"X-Return-Format": "html"})):
        for _ in range(2):
            try:
                hd = {"User-Agent": UA}
                hd.update(extra)
                h = urllib.request.urlopen(urllib.request.Request(
                    fetch_url, headers=hd), timeout=40).read().decode("utf-8", "ignore")
            except Exception:
                h = ""
            if ".mp4" in h:
                break
            h = ""
            time.sleep(1.5)
        if h:
            break
    src = re.search(r'<source[^>]+src="([^"]+\.mp4[^"]*)"', h) if h else None
    if not src:
        raise ValueError("threads post has no video")
    vurl = html.unescape(src.group(1))
    cap = re.search(r'class="BodyTextContainer[^"]*"><span>(.*?)</span>', h, re.S)
    poster = re.search(r'<video[^>]+poster="([^"]+)"', h)
    return {
        "title": (html.unescape(re.sub(r"<[^>]+>", "", cap.group(1))).strip()
                  if cap else f"threads_{code}"),
        "thumb": html.unescape(poster.group(1)) if poster else None,
        "platform": "Threads",
        "duration": None,
        "size": None,
        "direct_url": vurl,
        "direct_only": True,
        "headers": {"User-Agent": UA},
    }

def resolve_threads_srf(url):
    api = "https://www.savereelsfast.com/api/public/extract?url=" + urllib.parse.quote(url, safe="")
    r = json.load(urllib.request.urlopen(
        urllib.request.Request(api, headers={"User-Agent": UA}), timeout=30))
    if not r.get("success") or not r.get("data"):
        raise ValueError((r.get("error") or {}).get("message") or "threads extract failed")
    d = r["data"]
    vurl = d.get("video_url")
    if not vurl:
        items = [i for i in (d.get("items") or []) if i.get("video_url")]
        vurl = items[0]["video_url"] if items else None
    if not vurl:
        raise ValueError("threads post has no video")
    return {
        "title": (d.get("title") or "").strip().split("\n")[0] or "threads_video",
        "thumb": d.get("thumbnail"),
        "platform": "Threads",
        "duration": d.get("duration"),
        "size": None,
        "direct_url": vurl,
        "direct_only": True,
        "headers": {"User-Agent": UA},
    }

def resolve(url):
    if re.search(r"(x|twitter)\.com/", url):
        try:
            return resolve_x(url)
        except Exception:
            pass  # fall through to yt-dlp
    if "tiktok.com" in url:
        try:
            return resolve_tiktok(url)
        except Exception:
            pass  # fall through to yt-dlp
    if re.search(r"threads\.(com|net)/", url):
        for fn in (resolve_threads, resolve_threads_srf):
            try:
                return fn(url)
            except Exception:
                continue
        # fall through to yt-dlp
    opts = {"quiet": True, "no_warnings": True, "noplaylist": True,
            "skip_download": True, "format": "bv*+ba/b",
            "js_runtimes": {"node": {}}, "remote_components": {"ejs:github"}}
    if os.path.exists(COOKIES_FILE):
        opts["cookiefile"] = COOKIES_FILE
        opts["extractor_args"] = {"youtube": {"player_client": ["all"]}}
    info = yt_dlp.YoutubeDL(opts).extract_info(url, download=False)
    if "entries" in info and info["entries"]:
        info = info["entries"][0]
    direct, headers = None, None
    fmts = info.get("formats") or []
    progs = [f for f in fmts if f.get("vcodec") not in (None, "none")
             and f.get("acodec") not in (None, "none") and str(f.get("url", "")).startswith("http")
             and (f.get("protocol") or "https") in ("http", "https")]
    if progs:
        hd = [f for f in progs if f.get("format_id") == "hd"]
        b = max(hd or progs, key=lambda f: f.get("tbr") or f.get("height") or 0)
        direct, headers = b["url"], b.get("http_headers")
    ext = info.get("extractor_key") or "generic"
    return {
        "title": info.get("title") or "video",
        "thumb": info.get("thumbnail"),
        "platform": PLATFORM_NAMES.get(ext.lower(), ext),
        "duration": info.get("duration"),
        "size": info.get("filesize") or info.get("filesize_approx"),
        "direct_url": direct,
        "headers": headers,
        "yt_url": url,
    }

FFMPEG = os.path.join(FFMPEG_DIR, "ffmpeg.exe")
FFPROBE = os.path.join(FFMPEG_DIR, "ffprobe.exe")

AUDIO_EXT = {"aac": "m4a", "mp3": "mp3", "flac": "flac", "vorbis": "ogg",
             "opus": "opus", "pcm_s16le": "wav", "pcm_s24le": "wav"}

def _audio_ext(src):
    import subprocess
    r = subprocess.run([FFPROBE, "-v", "error", "-select_streams", "a:0",
                        "-show_entries", "stream=codec_name", "-of", "csv=p=0", src],
                       capture_output=True, text=True, timeout=60)
    codec = (r.stdout.strip().split(",") or [""])[0].lower()
    return AUDIO_EXT.get(codec, "mka")

def extract_audio(src, tmpdir, afmt):
    import subprocess
    if afmt == "orig":
        ext = _audio_ext(src)
        out = os.path.join(tmpdir, "out." + ext)
        cmd = [FFMPEG, "-y", "-i", src, "-vn", "-c:a", "copy", out]
    else:
        ext = "mp3"
        out = os.path.join(tmpdir, "out.mp3")
        cmd = [FFMPEG, "-y", "-i", src, "-vn", "-c:a", "libmp3lame", "-q:a", "2", out]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
    if r.returncode != 0 or not os.path.exists(out) or os.path.getsize(out) == 0:
        raise ValueError("không trích được audio (video có thể không có tiếng)")
    return out, ext

def run_job(jid, rid, mode, afmt=None):
    job = JOBS[jid]
    meta = RES[rid]
    save_dir = SERVER_DIRS.get(mode)
    tmpdir = os.path.join(TMP_DIR, jid)
    os.makedirs(tmpdir, exist_ok=True)
    try:
        if meta.get("direct_url") and meta.get("direct_only"):
            out = os.path.join(tmpdir, "out.mp4")
            req = urllib.request.Request(meta["direct_url"], headers=meta.get("headers") or {"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=30) as r, open(out, "wb") as f:
                total = int(r.headers.get("Content-Length") or 0)
                got = 0
                while True:
                    b = r.read(1 << 20)
                    if not b:
                        break
                    f.write(b)
                    got += len(b)
                    job["progress"] = got / total * 100 if total else 0
            with open(out, "rb") as f:
                if f.read(8).startswith(b"#EXTM3U"):
                    raise ValueError("link là playlist HLS, không phải file video")
            final = out
        else:
            def hook(d):
                if d["status"] == "downloading" and d.get("total_bytes"):
                    job["progress"] = d.get("downloaded_bytes", 0) / d["total_bytes"] * 100
                elif d["status"] == "downloading" and d.get("total_bytes_estimate"):
                    job["progress"] = d.get("downloaded_bytes", 0) / d["total_bytes_estimate"] * 100
            opts = {
                "quiet": True, "no_warnings": True, "noplaylist": True,
                "format": "bestaudio/best" if afmt else "bv*+ba/b",
                "js_runtimes": {"node": {}}, "remote_components": {"ejs:github"},
                **({"cookiefile": COOKIES_FILE,
                    "extractor_args": {"youtube": {"player_client": ["all"]}}}
                   if os.path.exists(COOKIES_FILE) else {}),
                "merge_output_format": "mp4",
                "ffmpeg_location": FFMPEG_DIR,
                "outtmpl": os.path.join(tmpdir, "out.%(ext)s"),
                "progress_hooks": [hook],
                "http_chunk_size": 10485760, "retries": 10, "file_access_retries": 5,
            }
            yt_dlp.YoutubeDL(opts).download([meta.get("yt_url") or meta["url"]])
            files = [f for f in os.listdir(tmpdir) if not f.endswith((".part", ".ytdl"))]
            final = os.path.join(tmpdir, files[0])
        if afmt:
            final, aext = extract_audio(final, tmpdir, afmt)
            fname = safe_name(meta["title"]) + "." + aext
        else:
            fname = safe_name(meta["title"]) + ".mp4"
        if save_dir:
            dest = os.path.join(save_dir, fname)
            base, ext0 = os.path.splitext(dest)
            n = 1
            while os.path.exists(dest):
                dest = base + f" ({n})" + ext0
                n += 1
            shutil.move(final, dest)
            job.update(status="done", filename=os.path.basename(dest), path=dest)
        else:
            job.update(status="ready", filename=fname, path=final)
    except Exception as e:
        job.update(status="error", error=str(e)[:300])
    finally:
        if save_dir:
            shutil.rmtree(tmpdir, ignore_errors=True)

HTML = """<!doctype html><html lang="vi"><head>
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1">
<meta name="theme-color" content="#0f1115">
<link rel="manifest" href="/manifest.webmanifest">
<link rel="apple-touch-icon" href="/static/icon-192.png">
<title>Get Misalab</title><style>
*{box-sizing:border-box;margin:0;font-family:system-ui,-apple-system,sans-serif}
body{background:#0f1115;color:#e8e8ea;min-height:100vh;display:flex;justify-content:center}
.wrap{width:100%;max-width:460px;padding:24px 16px}
h1{font-size:20px;font-weight:700;margin-bottom:4px}
.sub{color:#8a8f98;font-size:13px;margin-bottom:20px}
input[type=text]{width:100%;padding:16px;border-radius:14px;border:1px solid #2a2f3a;background:#171a21;color:#fff;font-size:16px;outline:none}
input:focus{border-color:#4f7cff}
.btn{width:100%;padding:16px;border:0;border-radius:14px;font-size:16px;font-weight:700;cursor:pointer;margin-top:12px}
.btn:active{transform:scale(.98)}
.btn-p{background:#4f7cff;color:#fff}
.btn:disabled{opacity:.5;cursor:default}
.card{background:#171a21;border:1px solid #2a2f3a;border-radius:16px;padding:14px;margin-top:20px;display:none}
.thumb{width:100%;border-radius:10px;margin-bottom:10px;display:block;background:#000}
.chip{display:inline-block;background:#22304f;color:#9db8ff;font-size:12px;padding:4px 10px;border-radius:999px;margin-bottom:8px}
.title{font-size:15px;font-weight:600;margin-bottom:10px;line-height:1.35;word-break:break-word}
.meta{color:#8a8f98;font-size:12px;margin-bottom:4px}
.row{display:flex;gap:10px;margin-top:8px}
.row .btn{margin-top:0}
.btn-dl{background:#22b573;color:#fff}
.btn-sv{background:#2a2f3a;color:#e8e8ea;border:1px solid #3a4150}
.btn-au{background:transparent;color:#7ea4ff;border:1px solid #2a3a55;font-size:13px;padding:10px;flex:1}
.btn-ic{flex:none;width:56px;background:#2a2f3a;color:#9db8ff;border:1px solid #3a4150;display:flex;align-items:center;justify-content:center;padding:0}
.btn-ic svg{width:22px;height:22px}
.btn{user-select:none;-webkit-user-select:none;-webkit-touch-callout:none}
.btn.armed{background:#d4a017;color:#000}
.prog{height:6px;background:#2a2f3a;border-radius:99px;margin-top:12px;overflow:hidden;display:none}
.prog>div{height:100%;background:#4f7cff;width:0%;transition:width .3s}
.msg{font-size:13px;margin-top:10px;min-height:18px}
.err{color:#ff6b6b}.ok{color:#4ade80}
#stat{position:fixed;bottom:0;left:0;right:0;text-align:center;font-size:11px;color:#5a5f6a;padding:7px;background:rgba(15,17,21,.9);backdrop-filter:blur(4px);border-top:1px solid #1e2229}
.wrap{padding-bottom:56px}
</style></head><body><div class="wrap">
<h1>Get Misalab</h1>
<div class="sub">X · TikTok · Facebook · YouTube · và mọi nền tảng yt-dlp hỗ trợ</div>
<input type="text" id="url" placeholder="Dán link video vào đây..." inputmode="url" autocomplete="off">
<div class="row">
  <button class="btn btn-p" id="go" style="flex:1" onclick="goClick()">GET LINK</button>
  <button class="btn btn-ic" onclick="pasteLink()" title="Dán link từ bộ nhớ" aria-label="Paste"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="8" y="2" width="8" height="4" rx="1"/><path d="M16 4h2a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2h2"/><path d="M9 12h6M9 16h6"/></svg></button>
</div>
<div class="card" id="card">
  <img class="thumb" id="thumb" style="display:none">
  <div><span class="chip" id="plat"></span></div>
  <div class="title" id="title"></div>
  <div class="meta" id="meta"></div>
  <div class="row">
    <button class="btn btn-dl" id="bdl" onclick="save('device')">Tải về máy</button>
    <button class="btn btn-sv" id="bsv" style="display:none" onclick="save('server')">Lưu trên máy chủ</button>
    <button class="btn btn-sv" id="bsx" style="display:none;flex:0 0 64px" onclick="save('serverx')" title="Lưu vào E:\devin_task\saved">X</button>
  </div>
  <div class="row">
    <button class="btn btn-au" onclick="save('device','orig')">🎵 Audio gốc</button>
    <button class="btn btn-au" onclick="save('device','mp3')">MP3</button>
  </div>
  <div class="prog" id="prog"><div id="bar"></div></div>
  <div class="msg" id="msg"></div>
</div>
<div class="msg" id="topmsg"></div>
<div id="stat">—</div>
</div>
<script>
if('serviceWorker' in navigator) navigator.serviceWorker.register('/sw.js').catch(()=>{});
let RID=null, busy=false, DIRECT=null;
let armed=false, suppressClick=false, armT=null;
const $=id=>document.getElementById(id);
function findUrl(s){const m=(s||'').match(/https?:\/\/\S+/);return m?m[0]:''}
function setSV(v){$('bsv').style.display=$('bsx').style.display=v?'':'none'}
function goClick(){if(suppressClick){suppressClick=false;return}resolve()}
addEventListener('DOMContentLoaded',()=>{
  const q=new URLSearchParams(location.search);
  const u=q.get('url')||findUrl(q.get('text'))||findUrl(q.get('title'));
  if(u){$('url').value=u;resolve();}
  setSV(localStorage.getItem('gml_admin')==='1');
  const g=$('go');
  g.addEventListener('pointerdown',()=>{armT=setTimeout(()=>{armed=!armed;g.classList.toggle('armed',armed);suppressClick=true;},5000)});
  ['pointerup','pointerleave','pointercancel'].forEach(e=>g.addEventListener(e,()=>clearTimeout(armT)));
  g.addEventListener('contextmenu',e=>e.preventDefault());
});
function fmtDur(s){if(!s)return'';s=Math.round(s);return Math.floor(s/60)+':'+String(s%60).padStart(2,'0')}
function fmtSize(b){if(!b)return'';return (b/1048576).toFixed(1)+' MB'}
async function resolve(){
  const url=$('url').value.trim(); if(!url||busy)return;
  busy=true;$('go').disabled=true;$('go').textContent='Đang phân tích...';
  $('topmsg').textContent='';$('card').style.display='none';
  try{
    const r=await fetch('/api/resolve',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({url})});
    const d=await r.json();
    if(!r.ok||d.error)throw new Error(d.error||'Không lấy được link');
    RID=d.rid;DIRECT=d.direct||null;$('plat').textContent=d.platform;$('title').textContent=d.title;
    const bits=[fmtDur(d.duration),fmtSize(d.size)].filter(Boolean).join(' · ');
    $('meta').textContent=bits;
    if(d.thumb){$('thumb').src=d.thumb;$('thumb').style.display='block'}else $('thumb').style.display='none';
    $('card').style.display='block';$('msg').textContent='';
  }catch(e){$('topmsg').innerHTML='<span class="err">'+e.message+'</span>'}
  busy=false;$('go').disabled=false;$('go').textContent='GET LINK';
}
async function pasteLink(){
  if(armed){
    armed=false;$('go').classList.remove('armed');
    if(!$('url').value.trim()){
      const v=localStorage.getItem('gml_admin')!=='1';
      localStorage.setItem('gml_admin',v?'1':'0');setSV(v);
      $('topmsg').innerHTML=v?'<span class="ok">Đã mở khoá nút "Lưu trên máy chủ"</span>':'<span class="ok">Đã ẩn nút "Lưu trên máy chủ"</span>';
      return;
    }
  }
  try{
    const t=await navigator.clipboard.readText();
    if(t!==undefined){$('url').value=(t||'').trim();$('topmsg').innerHTML=t?'<span class="ok">Đã dán từ bộ nhớ</span>':'<span class="err">Bộ nhớ đang trống</span>';return}
    throw 0;
  }catch(e){
    $('url').focus();$('url').select();
    $('topmsg').innerHTML='<span class="err">Trình duyệt chặn đọc bộ nhớ — nhấn giữ ô nhập rồi chọn Paste, hoặc dùng get.misalab.com (https)</span>';
  }
}
async function tick(){try{const s=await(await fetch('/api/status')).json();$('stat').textContent='● '+s.active+' đang truy cập · '+s.hits24+' lượt/24h · '+s.ips24+' IP'}catch(e){}}
setInterval(tick,15000);tick();
function postSave(mode,pass,afmt){
  return fetch('/api/save',{method:'POST',headers:{'Content-Type':'application/json','x-gml-pass':pass||''},body:JSON.stringify({rid:RID,mode,afmt})});
}
async function save(mode,afmt){
  if(!RID||busy)return;
  if(mode==='device'&&DIRECT&&!afmt){window.location=DIRECT;$('msg').innerHTML='<span class="ok">Đang tải về máy...</span>';return}
  let pass='';
  if(mode!=='device'&&location.hostname.endsWith('misalab.com')){
    pass=localStorage.getItem('gml_pass')||'';
    if(!pass){
      pass=prompt('Nhập mật khẩu để lưu trên máy chủ:')||'';
      if(!pass)return;
    }
  }
  busy=true;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=true;
  $('msg').innerHTML='';$('prog').style.display='block';$('bar').style.width='2%';
  try{
    let r=await postSave(mode,pass,afmt);
    if(r.status===401&&mode!=='device'){
      localStorage.removeItem('gml_pass');
      pass=prompt('Sai mật khẩu, nhập lại:')||'';
      if(!pass){busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false;$('prog').style.display='none';return}
      r=await postSave(mode,pass,afmt);
    }
    if(r.status===401)throw new Error('Sai mật khẩu');
    const d=await r.json();
    if(mode!=='device')localStorage.setItem('gml_pass',pass);
    if(!r.ok||d.error)throw new Error(d.error||'Lỗi');
    if(d.stream_url){window.location=d.stream_url;$('msg').innerHTML='<span class="ok">Đang tải về máy...</span>';$('prog').style.display='none';busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false;return;}
    const jid=d.job_id;
    if(mode!=='device'){
      $('msg').innerHTML='<span class="ok">Đã nhận — file sẽ tiếp tục tải trên máy chủ</span>';
      $('prog').style.display='none';busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false;
      return;
    }
    const t=setInterval(async()=>{
      const j=await (await fetch('/api/job/'+jid)).json();
      $('bar').style.width=(j.progress||0)+'%';
      if(j.status==='ready'){clearInterval(t);window.location='/api/file/'+jid;
        $('msg').innerHTML='<span class="ok">Đang tải về máy...</span>';$('prog').style.display='none';busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false;}
      else if(j.status==='done'){clearInterval(t);
        $('msg').innerHTML='<span class="ok">Đã lưu: '+j.filename+'</span>';$('prog').style.display='none';busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false;}
      else if(j.status==='error'){clearInterval(t);
        $('msg').innerHTML='<span class="err">Lỗi: '+j.error+'</span>';$('prog').style.display='none';busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false;}
    },800);
  }catch(e){$('msg').innerHTML='<span class="err">'+e.message+'</span>';$('prog').style.display='none';busy=false;$('bdl').disabled=$('bsv').disabled=$('bsx').disabled=false}
}
</script></body></html>"""

MANIFEST = {
    "name": "Get Misalab",
    "short_name": "Get Misalab",
    "start_url": "/",
    "display": "standalone",
    "background_color": "#0f1115",
    "theme_color": "#0f1115",
    "icons": [
        {"src": "/static/icon-192.png", "sizes": "192x192", "type": "image/png"},
        {"src": "/static/icon-512.png", "sizes": "512x512", "type": "image/png"},
        {"src": "/static/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "maskable"},
    ],
    "share_target": {
        "action": "/",
        "method": "GET",
        "params": {"title": "title", "text": "text", "url": "url"},
    },
}

SW_JS = """const C='gml-v1';
self.addEventListener('install',e=>self.skipWaiting());
self.addEventListener('activate',e=>e.waitUntil(self.clients.claim()));
self.addEventListener('fetch',e=>{
  if(e.request.method!=='GET')return;
  e.respondWith(fetch(e.request).catch(()=>caches.match(e.request)));
});
"""

@app.get("/manifest.webmanifest")
def manifest():
    return jsonify(MANIFEST)

@app.get("/sw.js")
def sw():
    return Response(SW_JS, mimetype="text/javascript", headers={"Cache-Control": "no-cache"})

@app.get("/")
def index():
    return HTML

@app.post("/api/resolve")
def api_resolve():
    url = (request.json or {}).get("url", "").strip()
    if not url.startswith("http"):
        return jsonify(error="Link không hợp lệ"), 400
    try:
        meta = resolve(url)
    except Exception as e:
        return jsonify(error=f"Không phân tích được link: {str(e)[:200]}"), 400
    rid = uuid.uuid4().hex[:12]
    meta["url"] = url
    RES[rid] = meta
    return jsonify(rid=rid, platform=meta["platform"], title=meta["title"],
                   thumb=meta.get("thumb"), duration=meta.get("duration"),
                   size=meta.get("size"), can_stream=bool(meta.get("direct_url")),
                   direct=meta.get("direct_url"))

SERVER_PASS = "S@ng1234"

@app.post("/api/save")
def api_save():
    d = request.json or {}
    rid, mode = d.get("rid"), d.get("mode")
    if rid not in RES:
        return jsonify(error="Link hết hạn, hãy Get Link lại"), 400
    if mode in SERVER_DIRS and "misalab.com" in (request.host or ""):
        if request.headers.get("x-gml-pass") != SERVER_PASS:
            return jsonify(error="unauthorized"), 401
    meta = RES[rid]
    afmt = d.get("afmt")
    if mode == "device" and meta.get("direct_url") and not afmt:
        return jsonify(stream_url=meta["direct_url"])
    jid = uuid.uuid4().hex[:12]
    JOBS[jid] = {"status": "downloading", "progress": 0}
    threading.Thread(target=run_job, args=(jid, rid, mode if mode in SERVER_DIRS else "device", afmt), daemon=True).start()
    return jsonify(job_id=jid)

@app.get("/api/job/<jid>")
def api_job(jid):
    j = JOBS.get(jid)
    if not j:
        return jsonify(error="not found"), 404
    return jsonify({k: j.get(k) for k in ("status", "progress", "filename", "error")})

@app.get("/api/proxy/<rid>")
def api_proxy(rid):
    meta = RES.get(rid)
    if not meta or not meta.get("direct_url"):
        return "expired", 404
    req = urllib.request.Request(meta["direct_url"], headers=meta.get("headers") or {"User-Agent": UA})
    try:
        r = urllib.request.urlopen(req, timeout=30)
    except Exception as e:
        return f"CDN error: {e}", 502
    name = urllib.parse.quote(safe_name(meta["title"]) + ".mp4")
    h = {"Content-Disposition": f"attachment; filename*=UTF-8''{name}",
         "Content-Type": r.headers.get("Content-Type") or "video/mp4"}
    if r.headers.get("Content-Length"):
        h["Content-Length"] = r.headers["Content-Length"]
    def gen():
        try:
            while True:
                b = r.read(1 << 16)
                if not b:
                    break
                yield b
        finally:
            r.close()
    return Response(gen(), headers=h)

@app.get("/api/file/<jid>")
def api_file(jid):
    j = JOBS.get(jid)
    if not j or j.get("status") != "ready" or not j.get("path"):
        return "not ready", 404
    path, fname = j["path"], j["filename"]
    return _send_and_cleanup(path, fname, jid)

def _send_and_cleanup(path, fname, jid):
    f = open(path, "rb")
    def gen():
        try:
            while True:
                b = f.read(1 << 18)
                if not b:
                    break
                yield b
        finally:
            f.close()
            shutil.rmtree(os.path.dirname(path), ignore_errors=True)
            JOBS.pop(jid, None)
    name = urllib.parse.quote(fname)
    mime = {"m4a": "audio/mp4", "mp3": "audio/mpeg", "flac": "audio/flac",
            "ogg": "audio/ogg", "opus": "audio/ogg", "wav": "audio/wav",
            "mka": "audio/x-matroska"}.get(fname.rsplit(".", 1)[-1].lower(), "video/mp4")
    return Response(gen(), headers={
        "Content-Disposition": f"attachment; filename*=UTF-8''{name}",
        "Content-Type": mime,
        "Content-Length": str(os.path.getsize(path)),
    })

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, threaded=True)
