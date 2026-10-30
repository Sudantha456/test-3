#!/usr/bin/env python3
from __future__ import annotations

import asyncio
import gc
import hashlib
import html
import json
import logging
import math
import os
import re
import shutil
import signal
import subprocess
import threading
import time
import uuid
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse, parse_qs, urljoin

import yt_dlp
import pyrogram.raw as raw
from pyrogram import Client, StopTransmission, filters, enums
from pyrogram.errors import FloodWait, RPCError
from pyrogram.types import InlineKeyboardButton, InlineKeyboardMarkup
from yt_dlp.utils import DownloadError

try:
    from curl_cffi import requests as cffi_requests
    from curl_cffi.const import CurlHttpVersion
    HAS_CURL_CFFI = True
except ImportError:
    try:
        from curl_cffi import requests as cffi_requests
        CurlHttpVersion = None
        HAS_CURL_CFFI = True
    except ImportError:
        cffi_requests = None
        CurlHttpVersion = None
        HAS_CURL_CFFI = False

try:
    import cloudscraper
    HAS_CLOUDSCRAPER = True
except ImportError:
    cloudscraper = None
    HAS_CLOUDSCRAPER = False

HTTP_V1_1 = getattr(CurlHttpVersion, "V1_1", 2) if CurlHttpVersion else 2
HAS_ARIA2C = bool(shutil.which("aria2c"))
HAS_DENO = bool(shutil.which("deno"))

# ==================== CONFIG ====================

BASE_DIR = Path(__file__).resolve().parent
ENV_FILE = BASE_DIR / ".env"
COOKIE_ROOT = BASE_DIR / "cookies"


def load_env_file():
    if not ENV_FILE.is_file():
        return

    for raw in ENV_FILE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        os.environ.setdefault(
            key.strip(),
            value.strip().strip('"').strip("'"),
        )


load_env_file()

# Resolve paths only after loading .env so DOWNLOAD_DIR works from configuration.
DOWNLOAD_DIR = Path(os.getenv("DOWNLOAD_DIR", str(BASE_DIR / "downloads"))).expanduser()

API_ID = int(os.getenv("API_ID", "0"))
API_HASH = os.getenv("API_HASH", "").strip()
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()

MAX_FILE_SIZE_MB = int(os.getenv("MAX_FILE_SIZE_MB", "2000"))
MAX_CONCURRENT = max(1, int(os.getenv("BOT_MAX_CONCURRENT", "4")))
DIRECT_RANGE_CONNECTIONS = max(2, min(12, int(os.getenv("DIRECT_RANGE_CONNECTIONS", "8"))))
YTDLP_FRAGMENT_CONCURRENCY = max(1, min(16, int(os.getenv("YTDLP_FRAGMENT_CONCURRENCY", "6"))))
MAX_QUEUE_PER_USER = max(1, int(os.getenv("BOT_MAX_QUEUE_PER_USER", "10")))
PROGRESS_INTERVAL = max(1.5, float(os.getenv("PROGRESS_INTERVAL", "2.0")))

# Bounded parallel Telegram MTProto upload settings.
TG_UPLOAD_TRANSMISSIONS = max(1, min(8, int(os.getenv("TG_UPLOAD_TRANSMISSIONS", "4"))))
TG_UPLOAD_WORKERS = max(
    2,
    min(16, int(os.getenv(
        "TG_UPLOAD_WORKERS",
        str(max(4, min(12, TG_UPLOAD_TRANSMISSIONS * 2))),
    ))),
)
TG_UPLOAD_CHUNK_SIZE = 512 * 1024
TG_UPLOAD_CHUNK_TIMEOUT = max(30, int(os.getenv("TG_UPLOAD_CHUNK_TIMEOUT", "90")))

# Cloudflare WARP SOCKS5 Proxy default (socks5://127.0.0.1:40000 on GitHub Actions)
YTDLP_PROXY = os.getenv("YTDLP_PROXY", "socks5://127.0.0.1:40000").strip()

if not API_ID or not API_HASH or not BOT_TOKEN:
    raise SystemExit(f"Missing API_ID, API_HASH or TELEGRAM_BOT_TOKEN in {ENV_FILE}")

DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
COOKIE_ROOT.mkdir(parents=True, exist_ok=True)

try:
    COOKIE_ROOT.chmod(0o700)
except OSError:
    pass

logging.basicConfig(
    level=os.getenv("LOG_LEVEL", "INFO"),
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
)
log = logging.getLogger("reclip")

DEFAULT_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

AD_URL_KEYWORDS = (
    "preroll", "midroll", "postroll", "vast", "adserver", "doubleclick",
    "exoclick", "juicyads", "popads", "trafficjunky", "magsrv", "realsrv",
    "tsyndicate", "banner", "promo", "trailer", "preview", "teaser",
    "thumb", "sprite", "pixel", "analytics",
)

app = Client(
    "reclip_telegram_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN,
    workers=4,
    sleep_threshold=30,
    max_concurrent_transmissions=TG_UPLOAD_TRANSMISSIONS,
    parse_mode=enums.ParseMode.HTML,
)

MAX_CACHE_ENTRIES = 60
MAX_LINK_SESSIONS = 80

link_sessions: dict[str, dict] = {}
url_info_cache: dict[str, tuple[float, dict]] = {}
CACHE_TTL_SECONDS = 900

user_queues: dict[int, deque[dict]] = {}
user_workers: dict[int, asyncio.Task] = {}
jobs_by_id: dict[str, dict] = {}
active_jobs: dict[int, dict] = {}
global_download_sem: asyncio.Semaphore | None = None

cookie_upload_targets = {}
active_lock = threading.Lock()
last_edit = {}


class JobCancelledError(Exception):
    """Raised when a user forcefully cancels an active download/upload job."""


def get_global_sem() -> asyncio.Semaphore:
    global global_download_sem
    if global_download_sem is None:
        global_download_sem = asyncio.Semaphore(MAX_CONCURRENT)
    return global_download_sem


def trim_memory():
    """Prune caches; avoid forcing a full GC on every completed job."""
    now = time.time()
    expired_urls = [k for k, (ts, _) in url_info_cache.items() if now - ts > CACHE_TTL_SECONDS]
    for k in expired_urls:
        url_info_cache.pop(k, None)

    while len(url_info_cache) > MAX_CACHE_ENTRIES:
        oldest_key = next(iter(url_info_cache))
        url_info_cache.pop(oldest_key, None)

    expired_links = [
        lid for lid, s in link_sessions.items()
        if now - s.get("ts", 0) > 3600
    ]
    for lid in expired_links:
        link_sessions.pop(lid, None)

    while len(link_sessions) > MAX_LINK_SESSIONS:
        oldest_lid = next(iter(link_sessions))
        link_sessions.pop(oldest_lid, None)

    gc.collect()


# ==================== PROCESS KILL & LOW-PRIORITY CPU EXECUTION ====================

def cleanup_job_files(job_id: str):
    if not job_id:
        return
    for path in DOWNLOAD_DIR.glob(f"*{job_id}*"):
        try:
            if path.is_file() or path.is_symlink():
                path.unlink(missing_ok=True)
        except OSError as exc:
            log.debug("Failed to delete %s: %s", path, exc)


def _low_priority_preexec():
    os.setsid()
    try:
        os.nice(15)
    except OSError:
        pass


def force_kill_process_tree(proc: subprocess.Popen | None):
    if proc is None:
        return

    try:
        pgid = os.getpgid(proc.pid)
        os.killpg(pgid, signal.SIGKILL)
    except Exception:
        pass

    try:
        proc.kill()
    except Exception:
        pass


def cancel_specific_job(uid: int, job_id: str) -> str:
    with active_lock:
        q = user_queues.get(uid)
        if q:
            for item in list(q):
                if item["job_id"] == job_id:
                    item["cancelled"].set()
                    q.remove(item)
                    jobs_by_id.pop(job_id, None)
                    return "queued"

        job = jobs_by_id.get(job_id)
        if not job or job.get("uid") != uid:
            curr = active_jobs.get(uid)
            if curr and curr.get("job_id") == job_id:
                job = curr
            else:
                return "not_found"

        job["cancelled"].set()
        proc = job.get("proc")

    force_kill_process_tree(proc)

    if job_id:
        try:
            subprocess.run(
                ["pkill", "-9", "-f", job_id],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except Exception:
            pass
        cleanup_job_files(job_id)

    trim_memory()
    return "running"


def cancel_all_user_jobs(uid: int) -> tuple[bool, int]:
    queued_items = []
    with active_lock:
        q = user_queues.get(uid)
        if q:
            queued_items = list(q)
            q.clear()
        for item in queued_items:
            item["cancelled"].set()
            jobs_by_id.pop(item["job_id"], None)

        curr = active_jobs.get(uid)
        curr_id = curr["job_id"] if curr else ""

    was_running = False
    if curr_id:
        res = cancel_specific_job(uid, curr_id)
        was_running = res == "running"

    return was_running, len(queued_items)


def run_tracked_subprocess(cmd: list[str], job_id: str, timeout: int = 900):
    with active_lock:
        job = jobs_by_id.get(job_id)
        if job and job["cancelled"].is_set():
            raise JobCancelledError("Cancelled by user.")

    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=_low_priority_preexec,
    )

    with active_lock:
        job = jobs_by_id.get(job_id)
        if job:
            job["proc"] = proc
            if job["cancelled"].is_set():
                force_kill_process_tree(proc)
                raise JobCancelledError("Cancelled by user.")

    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        force_kill_process_tree(proc)
        raise RuntimeError("Process timed out.")
    finally:
        with active_lock:
            job = jobs_by_id.get(job_id)
            if job and job.get("proc") is proc:
                job["proc"] = None

    with active_lock:
        job = jobs_by_id.get(job_id)
        if job and job["cancelled"].is_set():
            raise JobCancelledError("Cancelled by user.")

    if proc.returncode != 0:
        err_msg = (stderr or b"").decode("utf-8", errors="replace").strip()
        raise RuntimeError(err_msg or f"Command failed with exit code {proc.returncode}")

    return stdout


# ==================== FFMPEG VIDEO VERIFICATION ====================

def probe_video_metadata(video_path: Path) -> dict:
    meta = {
        "duration": 0,
        "width": 0,
        "height": 0,
        "vcodec": "",
        "acodec": "",
        "has_video": False,
        "has_audio": False,
        "faststart_ready": False,
    }
    try:
        out = subprocess.check_output(
            [
                "ffprobe",
                "-threads", "1",
                "-v", "error",
                "-print_format", "json",
                "-show_format",
                "-show_streams",
                str(video_path),
            ],
            stderr=subprocess.DEVNULL,
            timeout=25,
        )
        data = json.loads(out.decode("utf-8", errors="replace"))

        fmt_dur = float((data.get("format") or {}).get("duration") or 0)
        v_stream = None
        a_stream = None
        for s in data.get("streams") or []:
            if s.get("codec_type") == "video" and v_stream is None:
                v_stream = s
            elif s.get("codec_type") == "audio" and a_stream is None:
                a_stream = s

        if a_stream:
            meta["has_audio"] = True
            meta["acodec"] = (a_stream.get("codec_name") or "").lower()

        if v_stream:
            meta["has_video"] = True
            meta["vcodec"] = (v_stream.get("codec_name") or "").lower()
            width = int(v_stream.get("width") or 0)
            height = int(v_stream.get("height") or 0)
            stream_dur = float(v_stream.get("duration") or 0)

            rotation = 0
            tags = v_stream.get("tags") or {}
            if "rotate" in tags:
                try:
                    rotation = abs(int(tags["rotate"]))
                except ValueError:
                    pass
            for side in v_stream.get("side_data_list") or []:
                if "rotation" in side:
                    try:
                        rotation = abs(int(float(side["rotation"])))
                    except ValueError:
                        pass

            if rotation in (90, 270):
                width, height = height, width

            sar = v_stream.get("sample_aspect_ratio")
            if sar and ":" in sar and width > 0:
                try:
                    num, den = map(int, sar.split(":"))
                    if num > 0 and den > 0 and num != den:
                        width = int(round(width * num / den))
                except ValueError:
                    pass

            meta["width"] = width
            meta["height"] = height
            meta["duration"] = int(round(fmt_dur or stream_dur or 0))
        else:
            meta["duration"] = int(round(fmt_dur))

        try:
            with open(video_path, "rb") as f:
                header_bytes = f.read(65536)
                moov_pos = header_bytes.find(b"moov")
                mdat_pos = header_bytes.find(b"mdat")
                if moov_pos != -1 and (mdat_pos == -1 or moov_pos < mdat_pos):
                    meta["faststart_ready"] = True
        except Exception:
            pass

    except Exception as exc:
        log.warning("ffprobe failed for %s: %s", video_path.name, exc)

    return meta


def ensure_playable_seekable_mp4(video_path: Path, job_id: str) -> tuple[Path, dict]:
    if not video_path.is_file() or video_path.stat().st_size < 10 * 1024:
        raise RuntimeError("Downloaded file is empty or corrupted.")

    initial_meta = probe_video_metadata(video_path)
    if not initial_meta["has_video"] or initial_meta["width"] == 0:
        raise RuntimeError("Downloaded file has no playable video stream.")

    vcodec = initial_meta["vcodec"]
    acodec = initial_meta["acodec"]
    can_stream_copy = vcodec in ("h264", "avc1", "hevc", "h265") and acodec in ("aac", "mp3", "")

    if can_stream_copy and initial_meta["faststart_ready"] and initial_meta["duration"] > 0:
        return video_path, initial_meta

    fixed_path = DOWNLOAD_DIR / f"{job_id}_seekable.mp4"

    if can_stream_copy:
        cmd = [
            "ffmpeg", "-y",
            "-threads", "1",
            "-fflags", "+genpts+igndts",
            "-i", str(video_path),
            "-c", "copy",
            "-map", "0:v:0",
            "-map", "0:a:0?",
            "-dn",
            "-movflags", "+faststart",
            str(fixed_path),
        ]
        try:
            run_tracked_subprocess(cmd, job_id, timeout=240)
            if fixed_path.is_file() and fixed_path.stat().st_size > 10 * 1024:
                check_meta = probe_video_metadata(fixed_path)
                if check_meta["has_video"] and check_meta["duration"] >= 0:
                    video_path.unlink(missing_ok=True)
                    fixed_path.rename(video_path)
                    return video_path, check_meta
        except JobCancelledError:
            raise
        except Exception as exc:
            log.warning("Stream copy remux failed (%s), falling back to H.264 encode", exc)
            fixed_path.unlink(missing_ok=True)

    encode_cmd = [
        "ffmpeg", "-y",
        "-threads", "1",
        "-i", str(video_path),
        "-map", "0:v:0",
        "-map", "0:a:0?",
        "-c:v", "libx264",
        "-preset", "ultrafast",
        "-crf", "24",
        "-pix_fmt", "yuv420p",
        "-vf", "scale=trunc(iw/2)*2:trunc(ih/2)*2",
        "-c:a", "aac",
        "-b:a", "128k",
        "-movflags", "+faststart",
        str(fixed_path),
    ]
    try:
        run_tracked_subprocess(encode_cmd, job_id, timeout=900)
        if fixed_path.is_file() and fixed_path.stat().st_size > 10 * 1024:
            video_path.unlink(missing_ok=True)
            fixed_path.rename(video_path)
            return video_path, probe_video_metadata(video_path)
    except JobCancelledError:
        raise
    except Exception as exc:
        log.warning("H.264 re-encode fallback skipped: %s", exc)
        fixed_path.unlink(missing_ok=True)

    return video_path, initial_meta


def generate_video_thumbnail(
    video_path: Path,
    job_id: str,
    duration: int,
) -> Path | None:
    thumb_path = DOWNLOAD_DIR / f"{job_id}_thumb.jpg"
    seek_sec = max(1.0, min(float(duration) * 0.15, 5.0)) if duration > 2 else 0.0

    for ts in ([seek_sec, 0.0] if seek_sec > 0 else [0.0]):
        cmd = [
            "ffmpeg", "-y",
            "-threads", "1",
            "-ss", f"{ts:.2f}",
            "-i", str(video_path),
            "-frames:v", "1",
            "-vf", "scale='min(320,iw)':'min(320,ih)':force_original_aspect_ratio=decrease",
            "-q:v", "4",
            str(thumb_path),
        ]
        try:
            run_tracked_subprocess(cmd, job_id, timeout=20)
            if thumb_path.is_file() and thumb_path.stat().st_size > 0:
                return thumb_path
        except JobCancelledError:
            raise
        except Exception as exc:
            log.debug("Thumbnail capture at %ss failed: %s", ts, exc)

    return None


# ==================== URL HELPERS ====================

def is_youtube_url(url: str) -> bool:
    host = (urlparse(url).hostname or "").lower()
    return host in {"youtube.com", "www.youtube.com", "m.youtube.com", "youtu.be", "music.youtube.com"}


def is_tiktok_url(url: str) -> bool:
    host = (urlparse(url).hostname or "").lower()
    return host == "tiktok.com" or host.endswith(".tiktok.com")


def is_known_ytdlp_site(url: str) -> bool:
    host = (urlparse(url).hostname or "").lower()
    known = (
        "youtube.com", "youtu.be", "facebook.com", "fb.watch", "instagram.com",
        "twitter.com", "x.com", "reddit.com", "redd.it", "vimeo.com",
        "dailymotion.com", "twitch.tv", "soundcloud.com", "pinterest.com",
        "pin.it", "bilibili.com", "vk.com", "ok.ru", "streamable.com",
        "rumble.com", "bitchute.com", "pornhub.com", "xvideos.com",
        "xnxx.com", "xhamster.com", "xhamster2.com", "xhamster3.com", "xhwebsite.com",
        "spankbang.com", "eporner.com", "redtube.com", "youporn.com", "tube8.com", "thumbzilla.com",
    )
    return any(host == d or host.endswith("." + d) for d in known)


def is_ad_or_junk_url(url: str) -> bool:
    low = url.lower()
    return any(kw in low for kw in AD_URL_KEYWORDS)


def normalize_url(url: str) -> str:
    url = url.strip()
    try:
        parsed = urlparse(url)
        host = (parsed.hostname or "").lower()
        video_id = None

        if host == "youtu.be":
            video_id = parsed.path.strip("/").split("/")[0]

        elif host in {"youtube.com", "www.youtube.com", "m.youtube.com", "music.youtube.com"}:
            if parsed.path == "/watch":
                video_id = parse_qs(parsed.query).get("v", [None])[0]
            else:
                match = re.match(r"^/(?:shorts|embed|live)/([A-Za-z0-9_-]{11})", parsed.path)
                if match:
                    video_id = match.group(1)

        if video_id and re.fullmatch(r"[A-Za-z0-9_-]{11}", video_id):
            return f"https://www.youtube.com/watch?v={video_id}"

    except Exception:
        log.debug("URL normalization failed", exc_info=True)

    return url


def valid_url(url: str) -> bool:
    try:
        parsed = urlparse(url.strip())
        return (
            parsed.scheme in ("http", "https")
            and bool(parsed.hostname)
            and not any(c.isspace() for c in url)
        )
    except Exception:
        return False


def normalize_domain(value: str):
    value = value.strip().lower()

    if "://" in value:
        value = urlparse(value).hostname or ""

    value = value.split("/", 1)[0].split(":", 1)[0].strip(".")

    if (
        not value
        or "." not in value
        or ".." in value
        or not re.fullmatch(r"[a-z0-9.-]+", value)
    ):
        return None

    return value


def strip_ansi(text: str) -> str:
    return re.sub(r"\x1b\[[0-9;]*m|\[[0-9;]*m", "", text)


# ==================== COOKIE MANAGER ====================

def cookie_profile_dir(uid: int) -> Path:
    folder = COOKIE_ROOT / str(uid)
    folder.mkdir(parents=True, exist_ok=True)
    try:
        folder.chmod(0o700)
    except OSError:
        pass
    return folder


def parse_cookie_file(path: Path) -> list[dict]:
    records = []
    with open(path, "r", encoding="utf-8", errors="replace") as stream:
        for raw in stream:
            line = raw.rstrip("\r\n")
            if not line:
                continue

            if line.startswith("#HttpOnly_"):
                line = line[len("#HttpOnly_"):]
            elif line.startswith("#"):
                continue

            fields = line.split("\t")
            if len(fields) != 7:
                raise ValueError("Invalid Netscape cookies.txt format.")

            domain, subdomains, cookie_path, secure, expiry, name, value = fields
            if not domain or not name:
                continue

            try:
                expires = int(expiry or "0")
            except ValueError as exc:
                raise ValueError("Invalid cookie expiry timestamp.") from exc

            records.append({
                "domain": domain.lstrip(".").lower(),
                "include_subdomains": (subdomains.upper() == "TRUE" or domain.startswith(".")),
                "path": cookie_path or "/",
                "secure": secure.upper() == "TRUE",
                "expiry": expires,
                "name": name,
            })

    if not records:
        raise ValueError("No valid Netscape cookie records found.")

    return records


def cookie_domain_matches(cookie_domain, include_subdomains, host):
    cookie_domain = cookie_domain.lstrip(".").lower()
    host = (host or "").strip(".").lower()
    if host == cookie_domain or (include_subdomains and host.endswith("." + cookie_domain)):
        return True
    if host.endswith("." + cookie_domain):
        return True
    return False


def cookie_profiles(uid: int) -> list[dict]:
    result = []
    for path in sorted(cookie_profile_dir(uid).glob("*.txt")):
        try:
            records = parse_cookie_file(path)
            now = int(time.time())
            result.append({
                "domain": path.stem,
                "path": path,
                "count": len(records),
                "expired": sum(1 for r in records if r["expiry"] and r["expiry"] <= now),
            })
        except (ValueError, OSError):
            result.append({
                "domain": path.stem,
                "path": path,
                "count": 0,
                "expired": 0,
                "invalid": True,
            })
    return result


def cookie_file_for_url(uid: int, url: str):
    url = normalize_url(url)
    host = (urlparse(url).hostname or "").lower()
    if not host:
        return None

    now = int(time.time())
    candidates = []

    for profile in cookie_profiles(uid):
        if profile.get("invalid"):
            continue

        try:
            records = parse_cookie_file(profile["path"])
        except (ValueError, OSError):
            continue

        matching = [
            r for r in records
            if cookie_domain_matches(r["domain"], r["include_subdomains"], host)
            and not (r["expiry"] and r["expiry"] <= now)
        ]

        if matching:
            candidates.append((len(profile["domain"]), len(matching), profile["path"]))

    selected = max(candidates, default=(0, 0, None), key=lambda item: (item[0], item[1]))[2]
    if selected:
        log.info("Cookie profile selected: %s for host %s", selected.name, host)
    return selected


def cookie_options_for_url(uid: int, url: str) -> dict:
    path = cookie_file_for_url(uid, url)
    if path and path.is_file():
        return {"cookiefile": str(path)}
    return {}


def load_cookies_for_url(uid: int, url: str) -> dict[str, str]:
    """Load only unexpired cookies applicable to this URL's host/path/scheme."""
    path = cookie_file_for_url(uid, url)
    if not path or not path.is_file():
        return {}

    parsed = urlparse(url)
    host = (parsed.hostname or "").lower()
    request_path = parsed.path or "/"
    is_https = parsed.scheme.lower() == "https"
    now = int(time.time())
    result: dict[str, str] = {}

    try:
        with path.open("r", encoding="utf-8", errors="replace") as stream:
            for raw in stream:
                line = raw.rstrip("\r\n")
                if not line:
                    continue
                http_only = line.startswith("#HttpOnly_")
                if line.startswith("#") and not http_only:
                    continue
                if http_only:
                    line = line[len("#HttpOnly_"):]
                fields = line.split("\t")
                if len(fields) != 7:
                    continue
                domain, include_subdomains, cookie_path, secure, expiry, name, value = fields
                domain = domain.lstrip(".").lower()
                domain_ok = host == domain or (include_subdomains.upper() == "TRUE" and host.endswith("." + domain))
                if not domain_ok or (secure.upper() == "TRUE" and not is_https):
                    continue
                cookie_path = cookie_path or "/"
                if not request_path.startswith(cookie_path):
                    continue
                try:
                    if int(expiry or "0") and int(expiry) <= now:
                        continue
                except ValueError:
                    continue
                if name:
                    result[name] = value
    except OSError as exc:
        log.warning("Unable to read cookie file for %s: %s", host, exc)
    return result


# ==================== YT-DLP OPTIONS ====================

def make_ytdlp_options(
    uid,
    url,
    extra=None,
    fast_fetch=False,
    use_proxy=True,
    use_cookies=True,
    yt_clients: list[str] | None = None,
):
    parsed = urlparse(url)
    origin = f"{parsed.scheme}://{parsed.netloc}" if parsed.scheme and parsed.netloc else url
    is_yt = is_youtube_url(url)

    options = {
        "quiet": True,
        "no_warnings": True,
        "no_color": True,
        "noplaylist": True,
        "source_address": "0.0.0.0",
        "socket_timeout": 15 if fast_fetch else 30,
        "retries": 2 if fast_fetch else 3,
        "extractor_retries": 2 if fast_fetch else 3,
        "fragment_retries": 4,
        "http_chunk_size": 10485760,
        "concurrent_fragment_downloads": YTDLP_FRAGMENT_CONCURRENCY,
        "buffersize": 1024 * 64,
        "format_sort": ["res", "vcodec:h264", "acodec:aac", "ext:mp4:m4a"],
    }

    if HAS_DENO:
        options["js_runtimes"] = {"deno": {}}

    if not is_yt:
        options["http_headers"] = {
            "User-Agent": DEFAULT_UA,
            "Referer": url,
            "Origin": origin,
            "Accept-Language": "en-US,en;q=0.9",
        }
    elif yt_clients:
        options["extractor_args"] = {
            "youtube": {
                "player_client": yt_clients,
            },
        }

    if HAS_ARIA2C and not fast_fetch and not is_yt:
        options["external_downloader"] = {"default": "aria2c"}
        options["external_downloader_args"] = {
            "aria2c": [
                "-x", os.getenv("ARIA2_CONNECTIONS", "6"),
                "-s", os.getenv("ARIA2_CONNECTIONS", "6"),
                "-k", "1M",
                "--file-allocation=none",
                "--summary-interval=0",
            ]
        }

    if use_proxy and YTDLP_PROXY:
        options["proxy"] = YTDLP_PROXY

    if use_cookies:
        cookie_options = cookie_options_for_url(uid, url)
        options.update(cookie_options)

    if extra:
        options.update(extra)

    return options


# ==================== SMART QUALITY PARSER & SELECTOR ====================

def infer_format_height(fmt: dict) -> int:
    h = fmt.get("height")
    w = fmt.get("width")
    if isinstance(h, (int, float)) and h > 0:
        if isinstance(w, (int, float)) and w > 0 and h > w:
            return int(w)
        return int(h)

    res = str(fmt.get("resolution") or "")
    m = re.search(r"(\d{3,4})x(\d{3,4})", res)
    if m:
        d1, d2 = int(m.group(1)), int(m.group(2))
        return min(d1, d2)

    for field in ("format_note", "format", "format_id", "url"):
        val = str(fmt.get(field) or "")
        m = re.search(r"(?:^|[^0-9])(144|240|360|480|540|720|1080|1440|2160)[pP]?(?:$|[^0-9])", val)
        if m:
            return int(m.group(1))

    fid_low = str(fmt.get("format_id") or "").lower()
    if "hd" in fid_low or "high" in fid_low:
        return 720
    if "sd" in fid_low or "low" in fid_low:
        return 480

    return 0


def unwrap_main_entry(info: dict) -> dict:
    if not info:
        return info

    entries = info.get("entries")
    if not entries:
        return info

    valid_entries = [e for e in entries if isinstance(e, dict) and (e.get("formats") or e.get("url"))]
    if not valid_entries:
        return info

    non_ad = [
        e for e in valid_entries
        if not is_ad_or_junk_url(str(e.get("url") or e.get("webpage_url") or ""))
        and not is_ad_or_junk_url(str(e.get("title") or ""))
    ]
    pool = non_ad or valid_entries

    best_entry = max(
        pool,
        key=lambda e: (
            float(e.get("duration") or 0),
            len(e.get("formats") or []),
        ),
    )
    return best_entry


def quality_options(info: dict) -> list[tuple[str, str]]:
    info = unwrap_main_entry(info)
    by_height: dict[int, tuple[tuple, str, int]] = {}
    duration = float(info.get("duration") or 0)

    best_audio_bps = 128000 / 8
    for fmt in info.get("formats", []):
        if str(fmt.get("vcodec") or "").lower() == "none" and str(fmt.get("acodec") or "").lower() != "none":
            abr = float(fmt.get("abr") or fmt.get("tbr") or 128)
            if abr > 0:
                best_audio_bps = (abr * 1000) / 8
                break

    for fmt in info.get("formats", []):
        vcodec = str(fmt.get("vcodec") or "").lower()
        acodec = str(fmt.get("acodec") or "").lower()

        if vcodec == "none" or "images" in str(fmt.get("format_note") or "").lower():
            continue
        if fmt.get("ext") in ("mhtml", "jpg", "png", "webp"):
            continue

        fmt_url = str(fmt.get("url") or "")
        if fmt_url and is_ad_or_junk_url(fmt_url):
            continue

        height = infer_format_height(fmt)
        if height < 120 or height > 4320:
            continue

        fmt_id = str(fmt.get("format_id") or "")
        if not fmt_id or len(fmt_id) > 40:
            continue

        is_h264 = 1 if ("avc" in vcodec or "h264" in vcodec) else 0
        has_audio = 1 if (acodec and acodec != "none") else 0
        fsize = int(fmt.get("filesize") or fmt.get("filesize_approx") or 0)
        tbr = float(fmt.get("tbr") or fmt.get("vbr") or 0)
        if not fsize and tbr > 0 and duration > 0:
            fsize = int(tbr * 1000 / 8 * duration)
        if fsize > 0 and not has_audio and duration > 0:
            fsize += int(best_audio_bps * duration)

        score = (is_h264, has_audio, tbr, fsize)
        old = by_height.get(height)

        if old is None or score > old[0]:
            by_height[height] = (score, fmt_id, fsize)

    result = []
    for height, (_, fmt_id, fsize) in sorted(by_height.items(), key=lambda x: x[0], reverse=True):
        if fsize > 0:
            label = f"{height}p ({human_size(fsize)})"
        else:
            label = f"{height}p"
        result.append((f"{fmt_id}|{height}", label))

    return result[:12]


def build_video_format_selector(info: dict, selection: str) -> str:
    if selection == "best" or not selection:
        return "bestvideo+bestaudio/best"

    if "|" in selection:
        fmt_id, height_str = selection.split("|", 1)
        try:
            height = int(height_str)
        except ValueError:
            height = 0
    else:
        fmt_id = selection
        height = 0

    has_bundled_audio = False
    for fmt in info.get("formats", []):
        if str(fmt.get("format_id", "")) == fmt_id:
            acodec = str(fmt.get("acodec") or "").lower()
            if acodec and acodec != "none":
                has_bundled_audio = True
            if not height:
                height = infer_format_height(fmt)
            break

    parts = []
    if has_bundled_audio:
        parts.append(f"{fmt_id}")
        parts.append(f"{fmt_id}+bestaudio")
    else:
        parts.append(f"{fmt_id}+bestaudio")
        parts.append(f"{fmt_id}")

    if height > 0:
        parts.append(f"bestvideo[height={height}]+bestaudio")
        parts.append(f"best[height={height}]")
        parts.append(f"bestvideo[height<={height}]+bestaudio/best[height<={height}]")

    parts.append("bestvideo+bestaudio/best")
    return "/".join(parts)


def can_direct_fast_download(info: dict, mode: str, selection: str) -> bool:
    if info.get("_tiktok_fallback") or info.get("_direct_media"):
        return mode == "video"
    if mode == "audio":
        return False

    formats = info.get("formats") or []
    if not formats:
        return False

    if "|" in selection:
        fmt_id, height_str = selection.split("|", 1)
        try:
            target_h = int(height_str)
        except ValueError:
            target_h = 0
    else:
        fmt_id = selection
        target_h = 0

    for fmt in formats:
        if selection != "best":
            if str(fmt.get("format_id") or "") != fmt_id and (not target_h or infer_format_height(fmt) != target_h):
                continue
        else:
            best_f = max(formats, key=lambda x: infer_format_height(x))
            if fmt is not best_f:
                continue

        f_url = str(fmt.get("url") or "")
        vcodec = str(fmt.get("vcodec") or "").lower()
        acodec = str(fmt.get("acodec") or "").lower()
        protocol = str(fmt.get("protocol") or "").lower()

        if (
            f_url.startswith(("http://", "https://"))
            and vcodec != "none"
            and acodec not in ("", "none")
            and "dash" not in protocol
            and "m3u8" not in f_url.lower()
            and "googlevideo.com" not in f_url.lower()
        ):
            return True

    return False


# ==================== KVS & GENERIC EXTRACTOR ====================

def decrypt_kvs_url(real_url: str, license_code: str) -> str:
    real_url = real_url.strip()
    if not real_url.startswith("function/0/"):
        return real_url

    real_url = real_url[len("function/0/"):]
    if not license_code:
        return real_url

    lic_digits = [int(ch) for ch in license_code if ch.isdigit()]
    if not lic_digits:
        return real_url

    lic_str = "".join(str(d) for d in lic_digits)
    while len(lic_str) < 32:
        lic_str += lic_str
    lic_map = [int(ch) or 10 for ch in lic_str[:32]]

    parts = real_url.split("/")
    if len(parts) < 6:
        return real_url

    hash_part = parts[5][:32]
    if len(hash_part) == 32:
        chars = list(hash_part)
        for idx in range(31, -1, -1):
            swap_idx = (idx + sum(lic_map[idx:])) % 32
            chars[idx], chars[swap_idx] = chars[swap_idx], chars[idx]
        parts[5] = "".join(chars) + parts[5][32:]

    return "/".join(parts)


def extract_kvs_flashvars(page_html: str, base_url: str) -> list[tuple[str, int, str]]:
    lic_match = re.search(r"['\"]?license_code['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
    license_code = lic_match.group(1) if lic_match else ""

    url_keys = [
        ("video_url", "video_url_text", 480),
        ("video_alt_url", "video_alt_url_text", 720),
        ("video_alt_url2", "video_alt_url2_text", 1080),
        ("video_alt_url3", "video_alt_url3_text", 1440),
    ]

    found = []
    seen_urls = set()

    for key, text_key, default_h in url_keys:
        m = re.search(rf"['\"]?{key}['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
        if not m:
            continue

        raw_val = m.group(1).strip().replace("\\/", "/")
        if not raw_val or raw_val.startswith("#"):
            continue

        decrypted = decrypt_kvs_url(raw_val, license_code)
        full_url = urljoin(base_url, decrypted)

        if full_url in seen_urls or not full_url.startswith(("http://", "https://")):
            continue
        if is_ad_or_junk_url(full_url):
            continue
        seen_urls.add(full_url)

        height = default_h
        tm = re.search(rf"['\"]?{text_key}['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
        if tm:
            hm = re.search(r"(\d{3,4})", tm.group(1))
            if hm:
                height = int(hm.group(1))
        else:
            hm = re.search(r"_(\d{3,4})p\.mp4", full_url, re.IGNORECASE)
            if hm:
                height = int(hm.group(1))

        found.append((f"kvs_{height}p", height, full_url))

    return found


def _is_valid_unblocked_html(text: str) -> bool:
    if not text or len(text) < 250:
        return False
    head = text[:1200]
    if "Just a moment..." in head or "Attention Required! | Cloudflare" in head:
        return False
    if "cf-browser-verification" in head or "_cf_chl_opt" in head:
        return False
    return True


def fetch_html_parallel_race(url: str, uid: int) -> tuple[str, dict[str, str], str | None]:
    # Use only real, unexpired cookies exported by the user for this exact host.
    # Do not fabricate age-gate cookies or send unrelated domains' cookies.
    saved_cookies_dict = load_cookies_for_url(uid, url)

    headers = {
        "User-Agent": DEFAULT_UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": url,
    }

    def _try_cffi(proxy_val: str | None, target: str) -> tuple[str, dict[str, str], str | None]:
        if not HAS_CURL_CFFI:
            raise RuntimeError("curl_cffi unavailable")
        resp = cffi_requests.get(
            url,
            impersonate=target,
            headers=headers,
            cookies=saved_cookies_dict or None,
            http_version=HTTP_V1_1,
            proxy=proxy_val,
            timeout=8,
            allow_redirects=True,
        )
        if resp.status_code == 200 and _is_valid_unblocked_html(resp.text):
            cookies = dict(saved_cookies_dict)
            if hasattr(resp, "cookies"):
                cookies.update(dict(resp.cookies))
            return resp.text, cookies, proxy_val
        raise RuntimeError(f"HTTP {resp.status_code}")

    def _try_cloudscraper(proxy_val: str | None) -> tuple[str, dict[str, str], str | None]:
        if not HAS_CLOUDSCRAPER:
            raise RuntimeError("cloudscraper unavailable")
        scraper = cloudscraper.create_scraper(
            browser={"browser": "chrome", "platform": "windows", "mobile": False}
        )
        proxies = {"http": proxy_val, "https": proxy_val} if proxy_val else None
        resp = scraper.get(
            url,
            headers=headers,
            cookies=saved_cookies_dict or None,
            proxies=proxies,
            timeout=8,
        )
        if resp.status_code == 200 and _is_valid_unblocked_html(resp.text):
            cookies = dict(saved_cookies_dict)
            cookies.update(scraper.cookies.get_dict())
            return resp.text, cookies, proxy_val
        raise RuntimeError(f"Cloudscraper HTTP {resp.status_code}")

    # Probe direct and configured proxy routes; a successful response is not a guarantee
    # that the site permits automated downloading. Use only site-provided access/cookies.
    tasks = []
    if HAS_CURL_CFFI:
        tasks.append(lambda: _try_cffi(None, "chrome124"))
    if YTDLP_PROXY and HAS_CURL_CFFI:
        tasks.append(lambda: _try_cffi(YTDLP_PROXY, "chrome124"))
    if HAS_CLOUDSCRAPER:
        tasks.append(lambda: _try_cloudscraper(None))
    if YTDLP_PROXY and HAS_CLOUDSCRAPER:
        tasks.append(lambda: _try_cloudscraper(YTDLP_PROXY))

    last_err = None
    best_fallback = None
    with ThreadPoolExecutor(max_workers=min(4, len(tasks) or 1)) as pool:
        futures = [pool.submit(fn) for fn in tasks]
        for fut in as_completed(futures):
            try:
                html_text, cookies, winning_proxy = fut.result()
                if html_text:
                    # Prefer HTML that actually contains video streams or player data over a region-block page
                    if any(k in html_text for k in (".m3u8", ".mp4", "videoModel", "flashvars", "video_url")):
                        return html_text, cookies, winning_proxy
                    if best_fallback is None:
                        best_fallback = (html_text, cookies, winning_proxy)
            except Exception as exc:
                last_err = exc

    if best_fallback is not None:
        return best_fallback

    raise last_err or RuntimeError("Cloudflare challenge blocked connection.")


def expand_hls_master_playlist(m3u8_url: str, referer: str, cookies: dict[str, str], uid: int) -> list[dict]:
    variants = []
    try:
        m3u8_text, _, _ = fetch_html_parallel_race(m3u8_url, uid)
        if "#EXT-X-STREAM-INF" not in m3u8_text:
            return []

        lines = [ln.strip() for ln in m3u8_text.splitlines() if ln.strip()]
        for i, line in enumerate(lines):
            if line.startswith("#EXT-X-STREAM-INF:") and i + 1 < len(lines):
                stream_line = lines[i + 1]
                if stream_line.startswith("#"):
                    continue
                variant_url = urljoin(m3u8_url, stream_line)
                height = 0
                res_m = re.search(r"RESOLUTION=(\d+)x(\d+)", line, re.IGNORECASE)
                if res_m:
                    height = min(int(res_m.group(1)), int(res_m.group(2)))
                if not height:
                    name_m = re.search(r"NAME=\"?(\d{3,4})p?\"?", line, re.IGNORECASE)
                    if name_m:
                        height = int(name_m.group(1))
                bw_m = re.search(r"BANDWIDTH=(\d+)", line, re.IGNORECASE)
                tbr = int(bw_m.group(1)) // 1000 if bw_m else (height * 3 if height else 1500)
                if height >= 144:
                    variants.append({
                        "format_id": f"hls_{height}p",
                        "height": height,
                        "vcodec": "h264",
                        "acodec": "aac",
                        "tbr": tbr,
                        "url": variant_url,
                    })
    except Exception as exc:
        log.debug("HLS master playlist expansion skipped: %s", exc)

    return variants


def generic_cffi_extract(url: str, uid: int = 0) -> dict:
    page_html, session_cookies, winning_proxy = fetch_html_parallel_race(url, uid)

    if "flashvars" not in page_html and "video_url" not in page_html and "<video" not in page_html.lower() and ".m3u8" not in page_html:
        iframe_match = re.search(
            r'<iframe[^>]+src=["\']([^"\']*(?:embed|player|video)[^"\']*)["\']',
            page_html,
            re.IGNORECASE,
        )
        if iframe_match:
            embed_url = urljoin(url, iframe_match.group(1))
            if not is_ad_or_junk_url(embed_url):
                try:
                    embed_html, embed_cookies, _ = fetch_html_parallel_race(embed_url, uid)
                    page_html = page_html + "\n" + embed_html
                    session_cookies.update(embed_cookies)
                except Exception:
                    pass

    title_match = re.search(r'<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)["\']', page_html, re.IGNORECASE)
    if not title_match:
        title_match = re.search(r"<title[^>]*>(.*?)</title>", page_html, re.IGNORECASE | re.DOTALL)
    title = html.unescape(title_match.group(1).strip()) if title_match else "Video"

    thumb_match = re.search(
        r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']',
        page_html,
        re.IGNORECASE,
    )
    if not thumb_match:
        thumb_match = re.search(r"['\"]?(?:preview_url|thumbUrl|thumbnailUrl)['\"]?\s*:\s*['\"]([^'\"]+)['\"]", page_html)
    thumbnail = urljoin(url, thumb_match.group(1).replace("\\/", "/")) if thumb_match else None

    dur_match = re.search(r'["\']duration["\']\s*:\s*(\d+)', page_html)
    duration = int(dur_match.group(1)) if dur_match else None

    formats = []
    urls_map = {}

    # 1. KVS Flashvars
    kvs_streams = extract_kvs_flashvars(page_html, url)
    for fid, height, stream_url in kvs_streams:
        formats.append({
            "format_id": fid,
            "height": height,
            "vcodec": "h264",
            "acodec": "aac",
            "tbr": height * 3,
            "url": stream_url,
        })
        urls_map[fid] = stream_url

    # 2. Check <link rel="preload" as="fetch" href="...m3u8"> (used by xHamster and modern HLS sites)
    if not formats:
        preload_m3u8 = re.findall(
            r'<link[^>]+href=["\'](https?://[^"\']+\.m3u8(?:\?[^"\']*)?)["\']',
            page_html,
            re.IGNORECASE,
        )
        for m3u8_u in preload_m3u8:
            m3u8_u = html.unescape(m3u8_u.replace("\\/", "/"))
            if is_ad_or_junk_url(m3u8_u):
                continue
            hls_variants = expand_hls_master_playlist(m3u8_u, url, session_cookies, uid)
            if hls_variants:
                for vf in hls_variants:
                    formats.append(vf)
                    urls_map[vf["format_id"]] = vf["url"]
                break

    # 3. HTML5 <source> tags
    if not formats:
        for src_m in re.finditer(r"<source\b([^>]+)>", page_html, re.IGNORECASE):
            attrs = src_m.group(1)
            u_m = re.search(r'src=["\']([^"\']+)["\']', attrs, re.IGNORECASE)
            if not u_m:
                continue
            raw_u = urljoin(url, html.unescape(u_m.group(1).replace("\\/", "/")))
            if is_ad_or_junk_url(raw_u):
                continue
            lbl_m = re.search(r'(?:label|title|res|data-res|size)=["\']?(\d{3,4})p?["\']?', attrs, re.IGNORECASE)
            height = int(lbl_m.group(1)) if lbl_m else 0
            if not height:
                hm = re.search(r"(\d{3,4})p", raw_u, re.IGNORECASE)
                height = int(hm.group(1)) if hm else 720
            fid = f"src_{height}p"
            formats.append({
                "format_id": fid,
                "height": height,
                "vcodec": "h264",
                "acodec": "aac",
                "tbr": height * 3,
                "url": raw_u,
            })
            urls_map[fid] = raw_u

    # 4. General regex scan for JSON/embedded .m3u8 and .mp4 streams
    if not formats:
        raw_urls = re.findall(
            r'(?:https?:)?\\?/\\?/[^\s"\'<>\\]+(?:\.(?:mp4|m3u8)|get_file/[^\s"\'<>\\]+)(?:\?[^\s"\'<>\\]*)?',
            page_html,
            re.IGNORECASE,
        )
        clean_urls = []
        for u in raw_urls:
            u_clean = html.unescape(u.replace("\\/", "/").replace("\\u0026", "&"))
            if u_clean.startswith("//"):
                u_clean = "https:" + u_clean
            if is_ad_or_junk_url(u_clean):
                continue
            if u_clean not in clean_urls:
                clean_urls.append(u_clean)

        for idx, media_url in enumerate(clean_urls[:10]):
            if ".m3u8" in media_url.lower():
                hls_variants = expand_hls_master_playlist(media_url, url, session_cookies, uid)
                if hls_variants:
                    for vf in hls_variants:
                        formats.append(vf)
                        urls_map[vf["format_id"]] = vf["url"]
                    continue

            hm = re.search(r"(?:_|/|-|\.)(144|240|360|480|540|720|1080|1440|2160)p?(?:\.mp4|/|$|\?)", media_url, re.IGNORECASE)
            height = int(hm.group(1)) if hm else (720 if idx == 0 else 480)
            fid = f"stream_{height}p_{idx}"
            formats.append({
                "format_id": fid,
                "height": height,
                "vcodec": "h264",
                "acodec": "aac",
                "tbr": height * 3,
                "url": media_url,
            })
            urls_map[fid] = media_url

    if not formats:
        raise RuntimeError(
            "This site blocked the server's region (e.g., US Texas Age-Verification wall) or requires cookies. "
            "Upload cookies for this site using /cookies domain.com"
        )

    best_fmt = max(formats, key=lambda f: f.get("height") or 0)
    urls_map["best"] = best_fmt["url"]

    return {
        "id": uuid.uuid4().hex[:8],
        "title": title,
        "uploader": urlparse(url).hostname or "Web",
        "duration": duration,
        "thumbnail": thumbnail,
        "formats": formats,
        "_tiktok_fallback": True,
        "_tiktok_urls": urls_map,
        "_referer": url,
        "_session_cookies": session_cookies,
        "_use_proxy": bool(winning_proxy),
    }


def tiktok_fallback_extract(url: str) -> dict:
    if HAS_CURL_CFFI:
        payload = None
        for prx in ([YTDLP_PROXY, None] if YTDLP_PROXY else [None]):
            try:
                resp = cffi_requests.post(
                    "https://www.tikwm.com/api/",
                    data={"url": url, "hd": "1"},
                    impersonate="chrome124",
                    http_version=HTTP_V1_1,
                    proxy=prx,
                    timeout=8,
                )
                payload = resp.json()
                if payload and payload.get("code") == 0:
                    break
            except Exception:
                pass
        if not payload:
            raise RuntimeError("TikTok API unreachable.")
    else:
        import urllib.request
        import urllib.parse

        data = urllib.parse.urlencode({"url": url, "hd": "1"}).encode()
        req = urllib.request.Request("https://www.tikwm.com/api/", data=data)
        with urllib.request.urlopen(req, timeout=10) as resp:
            payload = json.loads(resp.read().decode())

    if payload.get("code") != 0 or not payload.get("data"):
        raise RuntimeError(payload.get("msg") or "TikTok fallback API returned an error.")

    d = payload["data"]

    def abs_tikwm_url(u: str | None) -> str | None:
        if not u:
            return None
        if u.startswith("//"):
            return "https:" + u
        if u.startswith("/"):
            return "https://www.tikwm.com" + u
        return u

    hd_play = abs_tikwm_url(d.get("hdplay") or d.get("play"))
    sd_play = abs_tikwm_url(d.get("play") or d.get("wmplay"))
    cover = abs_tikwm_url(d.get("cover") or d.get("origin_cover"))

    formats = []
    if hd_play:
        formats.append({
            "format_id": "hd",
            "height": 1080,
            "vcodec": "h264",
            "acodec": "aac",
            "tbr": 4000,
            "filesize": d.get("hd_size") or d.get("size") or 0,
            "url": hd_play,
        })
    if sd_play and sd_play != hd_play:
        formats.append({
            "format_id": "sd",
            "height": 540,
            "vcodec": "h264",
            "acodec": "aac",
            "tbr": 1500,
            "filesize": d.get("size") or 0,
            "url": sd_play,
        })

    return {
        "id": str(d.get("id") or uuid.uuid4().hex[:8]),
        "title": d.get("title") or "TikTok Video",
        "uploader": (d.get("author") or {}).get("nickname") or "TikTok User",
        "duration": d.get("duration"),
        "thumbnail": cover,
        "formats": formats,
        "_tiktok_fallback": True,
        "_tiktok_urls": {
            "hd": hd_play or sd_play,
            "sd": sd_play or hd_play,
            "best": hd_play or sd_play,
        },
        "_use_proxy": False,
    }


def resolve_fallback_stream_url(info: dict, selection: str) -> tuple[str, dict[str, str]]:
    if info.get("_direct_input"):
        return str(info["url"]), {}
    if "|" in selection:
        fmt_id, height_str = selection.split("|", 1)
        try:
            target_h = int(height_str)
        except ValueError:
            target_h = 0
    else:
        fmt_id = selection
        target_h = 0

    urls_map = info.get("_tiktok_urls") or {}
    video_url = urls_map.get(fmt_id)
    fmt_headers: dict[str, str] = {}

    for fmt in info.get("formats") or []:
        if str(fmt.get("format_id", "")) == fmt_id and fmt.get("url"):
            video_url = fmt["url"]
            if isinstance(fmt.get("http_headers"), dict):
                fmt_headers.update(fmt["http_headers"])
            break

    if not video_url and target_h > 0:
        for fmt in info.get("formats") or []:
            if infer_format_height(fmt) == target_h and fmt.get("url"):
                video_url = fmt["url"]
                if isinstance(fmt.get("http_headers"), dict):
                    fmt_headers.update(fmt["http_headers"])
                break

    if not video_url:
        if selection == "best" and info.get("formats"):
            best_f = max(info["formats"], key=lambda x: infer_format_height(x))
            video_url = best_f.get("url")
            if isinstance(best_f.get("http_headers"), dict):
                fmt_headers.update(fmt["http_headers"])
        if not video_url:
            video_url = urls_map.get("best") or info.get("url")

    return video_url or "", fmt_headers


def _multi_connection_range_download(
    final_url: str,
    total_size: int,
    headers: dict[str, str],
    cookies: dict[str, str] | None,
    proxy: str | None,
    dest_path: Path,
    job_id: str,
    download_hook,
    num_connections: int = 8,
) -> bool:
    """Download disjoint byte ranges and reject incomplete/invalid segments."""
    if not HAS_CURL_CFFI or total_size <= 0:
        return False

    num_connections = max(2, min(12, int(num_connections), total_size))
    with open(dest_path, "wb") as f:
        f.truncate(total_size)

    # Distribute the remainder across early segments so every byte is covered once.
    base, remainder = divmod(total_size, num_connections)
    ranges = []
    start_byte = 0
    for i in range(num_connections):
        length = base + (1 if i < remainder else 0)
        end_byte = start_byte + length - 1
        ranges.append((start_byte, end_byte))
        start_byte = end_byte + 1

    progress_lock = threading.Lock()
    downloaded_total = [0]
    start_ts = time.monotonic()

    def _download_segment(seg_range: tuple[int, int]):
        s_byte, e_byte = seg_range
        expected = e_byte - s_byte + 1
        seg_headers = dict(headers)
        seg_headers["Range"] = f"bytes={s_byte}-{e_byte}"

        resp = cffi_requests.get(
            final_url,
            impersonate="chrome124",
            headers=seg_headers,
            cookies=cookies or None,
            http_version=HTTP_V1_1,
            proxy=proxy,
            stream=True,
            allow_redirects=True,
            timeout=(15, 45),
        )
        try:
            if resp.status_code != 206:
                raise RuntimeError(f"Range segment expected HTTP 206, got {resp.status_code}")

            content_range = (resp.headers.get("content-range") or "").strip()
            match = re.fullmatch(r"bytes\s+(\d+)-(\d+)/(\d+|\*)", content_range, re.I)
            if not match or int(match.group(1)) != s_byte or int(match.group(2)) != e_byte:
                raise RuntimeError(f"Invalid Content-Range for segment {s_byte}-{e_byte}: {content_range!r}")
            if match.group(3) != "*" and int(match.group(3)) != total_size:
                raise RuntimeError("Content-Range total size changed during download")

            received = 0
            with open(dest_path, "r+b") as fh:
                fh.seek(s_byte)
                try:
                    iterator = resp.iter_content(chunk_size=262144)
                except TypeError:
                    iterator = resp.iter_content()

                for chunk in iterator:
                    with active_lock:
                        job = jobs_by_id.get(job_id)
                        if job and job["cancelled"].is_set():
                            raise JobCancelledError("Cancelled by user.")
                    if not chunk:
                        continue
                    if received + len(chunk) > expected:
                        raise RuntimeError("Range server returned more bytes than requested")
                    fh.write(chunk)
                    received += len(chunk)
                    with progress_lock:
                        downloaded_total[0] += len(chunk)
                        done = downloaded_total[0]
                    elapsed = max(0.001, time.monotonic() - start_ts)
                    speed = done / elapsed
                    download_hook({
                        "status": "downloading",
                        "downloaded_bytes": done,
                        "total_bytes": total_size,
                        "speed": speed,
                        "eta": int(max(0, total_size - done) / speed) if speed > 0 else None,
                    })

            if received != expected:
                raise RuntimeError(f"Incomplete range {s_byte}-{e_byte}: got {received}/{expected} bytes")
        finally:
            if hasattr(resp, "close"):
                try:
                    resp.close()
                except Exception:
                    pass

    with ThreadPoolExecutor(max_workers=num_connections) as pool:
        futures = [pool.submit(_download_segment, r) for r in ranges]
        for fut in as_completed(futures):
            fut.result()

    return dest_path.is_file() and dest_path.stat().st_size == total_size and downloaded_total[0] == total_size


def direct_cffi_download(
    info: dict,
    mode: str,
    selection: str,
    job_id: str,
    uid: int,
    download_hook,
) -> Path:
    video_url, fmt_headers = resolve_fallback_stream_url(info, selection)
    if not video_url:
        raise RuntimeError("No direct stream URL found for selected quality.")

    raw_video_path = DOWNLOAD_DIR / f"{job_id}.mp4"
    referer = info.get("_referer") or info.get("webpage_url") or video_url
    parsed_ref = urlparse(referer)
    origin = f"{parsed_ref.scheme}://{parsed_ref.netloc}" if parsed_ref.scheme else ""

    headers = {
        "User-Agent": DEFAULT_UA,
        "Accept": "*/*",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": referer,
    }
    headers.update(fmt_headers)

    # Keep session cookies scoped to the source page's domain.
    session_cookies = load_cookies_for_url(uid, referer)
    session_cookies.update(info.get("_session_cookies") or {})

    cookie_header_str = "; ".join(f"{k}={v}" for k, v in session_cookies.items())

    if ".m3u8" in video_url.lower():
        # FFmpeg is not configured here to use the local SOCKS5/WARP proxy.
        # If the page was only accessible through WARP, let the caller fall back
        # to yt-dlp, whose proxy option is configured from info["_use_proxy"].
        if info.get("_use_proxy") and YTDLP_PROXY:
            raise RuntimeError(
                "HLS stream was extracted through WARP; use the proxy-aware yt-dlp fallback"
            )

        hdr_lines = [
            f"Referer: {referer}",
            f"User-Agent: {headers['User-Agent']}",
        ]
        if cookie_header_str:
            hdr_lines.append(f"Cookie: {cookie_header_str}")
        hdr_blob = "\r\n".join(hdr_lines) + "\r\n"

        run_tracked_subprocess(
            [
                "ffmpeg", "-y",
                "-threads", "1",
                "-headers", hdr_blob,
                "-i", video_url,
                "-c", "copy", "-bsf:a", "aac_adtstoasc",
                "-movflags", "+faststart",
                str(raw_video_path),
            ],
            job_id,
            timeout=900,
        )
    else:
        downloaded_ok = False
        proxy_candidates = (
            [YTDLP_PROXY, None] if info.get("_use_proxy") and YTDLP_PROXY
            else ([None, YTDLP_PROXY] if YTDLP_PROXY else [None])
        )

        if HAS_CURL_CFFI:
            for prx in proxy_candidates:
                if downloaded_ok:
                    break
                try:
                    probe_headers = dict(headers)
                    probe_headers["Range"] = "bytes=0-0"
                    probe_resp = cffi_requests.get(
                        video_url,
                        impersonate="chrome124",
                        headers=probe_headers,
                        cookies=session_cookies or None,
                        http_version=HTTP_V1_1,
                        proxy=prx,
                        stream=True,
                        allow_redirects=True,
                        timeout=15,
                    )
                    final_url = str(getattr(probe_resp, "url", None) or video_url)
                    status_code = probe_resp.status_code
                    ctype = (probe_resp.headers.get("content-type") or "").lower()
                    content_range = probe_resp.headers.get("content-range") or ""
                    content_len = int(probe_resp.headers.get("content-length") or 0)
                    if hasattr(probe_resp, "close"):
                        try:
                            probe_resp.close()
                        except Exception:
                            pass

                    if "text/html" in ctype or status_code >= 400:
                        raise RuntimeError(f"CDN rejected probe (HTTP {status_code})")

                    total_size = 0
                    if "/" in content_range:
                        try:
                            total_size = int(content_range.split("/")[-1])
                        except ValueError:
                            total_size = 0
                    elif status_code == 200 and content_len > 0:
                        total_size = content_len

                    if status_code == 206 and total_size > 1536 * 1024:
                        try:
                            downloaded_ok = _multi_connection_range_download(
                                final_url=final_url,
                                total_size=total_size,
                                headers=headers,
                                cookies=session_cookies,
                                proxy=prx,
                                dest_path=raw_video_path,
                                job_id=job_id,
                                download_hook=download_hook,
                                num_connections=DIRECT_RANGE_CONNECTIONS,
                            )
                            if downloaded_ok:
                                break
                        except JobCancelledError:
                            raise
                        except Exception as rng_exc:
                            log.debug("Multi-connection range download fallback: %s", rng_exc)

                    resp = cffi_requests.get(
                        final_url,
                        impersonate="chrome124",
                        headers=headers,
                        cookies=session_cookies or None,
                        http_version=HTTP_V1_1,
                        proxy=prx,
                        stream=True,
                        allow_redirects=True,
                        timeout=30,
                    )
                    try:
                        resp.raise_for_status()
                        ctype = (resp.headers.get("content-type") or "").lower()
                        if "text/html" in ctype:
                            raise RuntimeError("CDN returned HTML instead of video stream.")

                        total = int(resp.headers.get("content-length") or total_size or 0)
                        done = 0
                        start = time.monotonic()

                        with open(raw_video_path, "wb") as f:
                            if hasattr(resp, "iter_content"):
                                try:
                                    iterator = resp.iter_content(chunk_size=262144)
                                except TypeError:
                                    iterator = resp.iter_content()

                                for chunk in iterator:
                                    with active_lock:
                                        job = jobs_by_id.get(job_id)
                                        if job and job["cancelled"].is_set():
                                            raise JobCancelledError("Cancelled by user.")
                                    if not chunk:
                                        continue
                                    f.write(chunk)
                                    done += len(chunk)
                                    elapsed = max(0.001, time.monotonic() - start)
                                    download_hook({
                                        "status": "downloading",
                                        "downloaded_bytes": done,
                                        "total_bytes": total,
                                        "speed": done / elapsed,
                                        "eta": int((total - done) / (done / elapsed)) if total and done else None,
                                    })
                            else:
                                content = resp.content
                                f.write(content)
                                done = len(content)
                                download_hook({
                                    "status": "downloading",
                                    "downloaded_bytes": done,
                                    "total_bytes": done,
                                    "speed": done,
                                    "eta": 0,
                                })
                        if raw_video_path.is_file() and raw_video_path.stat().st_size > 20 * 1024:
                            downloaded_ok = True
                    finally:
                        if hasattr(resp, "close"):
                            try:
                                resp.close()
                            except Exception:
                                pass
                except JobCancelledError:
                    raise
                except Exception as cffi_exc:
                    log.debug("curl_cffi stream (proxy=%s) failed: %s", prx, cffi_exc)

        if not downloaded_ok:
            raise RuntimeError("HTTP 403 Forbidden or stream blocked by CDN.")

    if mode == "audio":
        mp3_path = DOWNLOAD_DIR / f"{job_id}.mp3"
        run_tracked_subprocess(
            [
                "ffmpeg", "-y", "-threads", "1", "-i", str(raw_video_path),
                "-vn", "-acodec", "libmp3lame", "-b:a", "192k",
                str(mp3_path),
            ],
            job_id,
            timeout=300,
        )
        raw_video_path.unlink(missing_ok=True)
        download_hook({"status": "finished"})
        return mp3_path

    download_hook({"status": "finished"})
    return raw_video_path


# ==================== EXTRACTION ROUTING ====================

def extract_youtube_resilient(url: str, uid: int) -> dict:
    has_saved_cookies = bool(cookie_file_for_url(uid, url))

    attempts: list[tuple[bool, list[str] | None]] = []

    if has_saved_cookies:
        attempts.append((True, None))
        attempts.append((True, ["mweb", "web", "tv"]))
        attempts.append((True, ["web_safari", "mweb"]))

    attempts.append((False, ["ios", "web_safari", "mweb"]))
    attempts.append((False, None))
    attempts.append((False, ["tv_embedded", "ios", "android"]))

    proxy_attempts = [True, False] if YTDLP_PROXY else [False]

    best_candidate: dict | None = None
    best_qual_count = -1
    last_err = None

    for use_prx in proxy_attempts:
        for use_ck, clients in attempts:
            opts = make_ytdlp_options(
                uid,
                url,
                {
                    "skip_download": True,
                    "format": None,
                    "ignore_no_formats_error": True,
                },
                fast_fetch=True,
                use_proxy=use_prx,
                use_cookies=use_ck,
                yt_clients=clients,
            )
            opts.pop("format_sort", None)

            try:
                with yt_dlp.YoutubeDL(opts) as ydl:
                    raw_info = ydl.extract_info(url, download=False)
                    info = unwrap_main_entry(raw_info)
                    if not info:
                        continue

                    quals = quality_options(info)
                    q_count = len(quals)
                    has_valid_streams = q_count > 0 or bool(info.get("url"))

                    if has_valid_streams:
                        info["_use_proxy"] = use_prx
                        info["_yt_use_cookies"] = use_ck
                        info["_yt_clients"] = clients
                        log.info(
                            "YouTube extract candidate (proxy=%s, cookies=%s, clients=%s) -> %d qualities",
                            use_prx,
                            use_ck,
                            clients,
                            q_count,
                        )

                        if q_count > best_qual_count:
                            best_qual_count = q_count
                            best_candidate = info

                        if q_count >= 3:
                            return info

            except Exception as exc:
                last_err = exc
                log.info(
                    "YouTube attempt (proxy=%s, cookies=%s, clients=%s) failed: %s",
                    use_prx,
                    use_ck,
                    clients,
                    str(exc)[:140],
                )

        if best_candidate is not None:
            return best_candidate

    if best_candidate is not None:
        return best_candidate

    raise last_err or RuntimeError(
        "YouTube blocked this request on this server IP. Check if Cloudflare WARP is running."
    )


def direct_media_info(url: str) -> dict | None:
    """Recognize actual media URLs without fetching a page or invoking site extractors."""
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https"):
        return None
    # Match extension in URL path, including signed URLs with query parameters.
    extension = Path(parsed.path).suffix.lower()
    if extension not in (".m3u8", ".mp4", ".m4v", ".mov", ".webm", ".mkv", ".ts", ".mp3", ".m4a", ".aac"):
        return None
    title = Path(parsed.path).stem or "Direct media"
    return {
        "id": "direct", "title": title[:180], "webpage_url": url,
        "url": url, "extractor": "direct", "_direct_media": True,
        "formats": [{"format_id": "direct", "url": url, "ext": extension.lstrip("."),
                     "protocol": "m3u8_native" if extension == ".m3u8" else "https"}],
    }


def extract_info(url: str, uid: int) -> dict:
    url = normalize_url(url)
    direct = direct_media_info(url)
    if direct:
        return direct

    cached = url_info_cache.get(url)
    if cached and (time.time() - cached[0] < CACHE_TTL_SECONDS):
        return dict(cached[1])

    if is_tiktok_url(url):
        try:
            info = tiktok_fallback_extract(url)
            url_info_cache[url] = (time.time(), info)
            return info
        except Exception as tk_exc:
            log.debug("TikWM fast-path failed (%s), falling back to yt-dlp", tk_exc)

    if is_youtube_url(url):
        info = extract_youtube_resilient(url, uid)
        url_info_cache[url] = (time.time(), info)
        return info

    # For non-YouTube sites (e.g. xHamster, IG, FB), try Direct IP first then WARP Proxy
    # because WARP in US (Texas/Utah) triggers strict state age-verification blocks on adult sites!
    if is_known_ytdlp_site(url):
        for use_prx in ([False, True] if YTDLP_PROXY else [False]):
            fast_options = make_ytdlp_options(
                uid,
                url,
                {"skip_download": True, "ignore_no_formats_error": True},
                fast_fetch=True,
                use_proxy=use_prx,
            )
            try:
                with yt_dlp.YoutubeDL(fast_options) as ydl:
                    raw_info = ydl.extract_info(url, download=False)
                    info = unwrap_main_entry(raw_info)
                    if info and (info.get("formats") or info.get("url")):
                        info["_use_proxy"] = use_prx
                        url_info_cache[url] = (time.time(), info)
                        return info
            except Exception as exc:
                log.info("Native extract (proxy=%s) failed: %s", use_prx, str(exc)[:120])

        # If native yt-dlp extractor failed (e.g. KeyError('videoModel') on xHamster), immediately fall back to generic_cffi_extract
        log.info("Native extractor failed for %s, trying generic HTML/HLS extraction", url)
        try:
            info = generic_cffi_extract(url, uid)
        except Exception as generic_exc:
            log.warning("Generic extractor failed for %s: %s", url, str(generic_exc)[:200])
            raise
        url_info_cache[url] = (time.time(), info)
        return info

    # Generic & KVS Sites
    try:
        info = generic_cffi_extract(url, uid)
        if info and info.get("formats"):
            url_info_cache[url] = (time.time(), info)
            return info
    except Exception as gen_exc:
        log.debug("Fast generic extractor skipped (%s), trying yt-dlp", gen_exc)

    try:
        fast_options = make_ytdlp_options(
            uid,
            url,
            {"skip_download": True, "ignore_no_formats_error": True},
            fast_fetch=True,
            use_proxy=False,
        )
        with yt_dlp.YoutubeDL(fast_options) as ydl:
            raw_info = ydl.extract_info(url, download=False)
            info = unwrap_main_entry(raw_info)
            if info and (info.get("formats") or info.get("url")):
                url_info_cache[url] = (time.time(), info)
                return info
    except Exception as ytdl_exc:
        log.debug("Fallback yt-dlp failed: %s", ytdl_exc)

    try:
        info = generic_cffi_extract(url, uid)
    except Exception as generic_exc:
        log.warning("Final generic extraction failed for %s: %s", url, str(generic_exc)[:200])
        raise
    url_info_cache[url] = (time.time(), info)
    return info


def run_ytdlp_fast(options: dict, url: str):
    try:
        with yt_dlp.YoutubeDL(options) as ydl:
            ydl.download([url])
    except JobCancelledError:
        raise
    except Exception as exc:
        if "Cancelled by user" in str(exc):
            raise JobCancelledError("Cancelled by user.") from exc
        raise


# ==================== DISPLAY HELPERS ====================

def duration_text(seconds):
    if seconds is None:
        return "Unknown"

    seconds = int(seconds)
    hours, rem = divmod(seconds, 3600)
    minutes, seconds = divmod(rem, 60)

    return (
        f"{hours}:{minutes:02d}:{seconds:02d}"
        if hours else f"{minutes}:{seconds:02d}"
    )


def human_size(value):
    if value is None:
        return "Unknown"

    size = float(value)

    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024 or unit == "TB":
            return f"{size:.1f} {unit}"
        size /= 1024

    return "Unknown"


def progress_bar(percent, width=14):
    filled = max(0, min(width, int(percent * width / 100)))
    return "█" * filled + "░" * (width - filled)


def safe_filename(name):
    name = re.sub(r'[\\/:*?"<>|\x00-\x1f]', "", name).strip(" .")
    name = re.sub(r"\s+", " ", name)[:140].strip()
    return name or "reclip-media"


async def edit_progress(message, text, force=False, reply_markup=None):
    key = (message.chat.id, message.id)
    now = time.monotonic()

    if not force and now - last_edit.get(key, 0) < PROGRESS_INTERVAL:
        return

    last_edit[key] = now

    try:
        await message.edit_text(
            text,
            parse_mode=enums.ParseMode.HTML,
            disable_web_page_preview=True,
            reply_markup=reply_markup,
        )
    except Exception as exc:
        if "MESSAGE_NOT_MODIFIED" not in str(exc).upper():
            log.debug("Progress edit failed: %s", exc)


# ==================== KEYBOARDS ====================

def cancel_keyboard(uid: int, job_id: str, is_queued: bool = False) -> InlineKeyboardMarkup:
    btn_text = "🗑 Remove from Queue" if is_queued else "⛔ Cancel Download (Next in Queue)"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(btn_text, callback_data=f"cancel:{uid}:{job_id}")]
    ])


def format_keyboard(uid: int, link_id: str):
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🎬 MP4 Video", callback_data=f"mode:video:{uid}:{link_id}"),
            InlineKeyboardButton("🎵 MP3 Audio", callback_data=f"mode:audio:{uid}:{link_id}"),
        ],
        [InlineKeyboardButton("🔄 New link", callback_data="new")],
    ])


def quality_keyboard(uid: int, link_id: str, qualities: list[tuple[str, str]]):
    rows = []
    row = []

    for selector_token, label in qualities:
        row.append(
            InlineKeyboardButton(label, callback_data=f"q:{uid}:{link_id}:{selector_token}")
        )

        if len(row) == 2:
            rows.append(row)
            row = []

    if row:
        rows.append(row)

    rows.append([
        InlineKeyboardButton("⭐ Best available", callback_data=f"q:{uid}:{link_id}:best")
    ])
    rows.append([
        InlineKeyboardButton("⬅️ Format", callback_data=f"back:{uid}:{link_id}")
    ])

    return InlineKeyboardMarkup(rows)


# ==================== COOKIE COMMANDS ====================

@app.on_message(filters.private & filters.command("cookies"))
async def cookies_command(client, message):
    uid = message.from_user.id
    args = message.text.split(maxsplit=1)

    if len(args) == 2:
        domain = normalize_domain(args[1])
        if not domain:
            await message.reply_text("Send a valid domain, e.g. /cookies youtube.com")
            return

        cookie_upload_targets[uid] = domain
        await message.reply_text(
            f"🍪 Upload target: <code>{html.escape(domain)}</code>\n"
            "Now upload your Netscape-format cookies.txt as a document."
        )
        return

    profiles = cookie_profiles(uid)
    if not profiles:
        await message.reply_text(
            "🍪 No cookie profiles saved.\n"
            "Use /cookies youtube.com, then upload cookies.txt."
        )
        return

    lines = ["🍪 <b>Your cookie profiles</b>"]
    for profile in profiles:
        status = (
            "invalid format"
            if profile.get("invalid")
            else f"{profile['count']} cookies · {profile['expired']} expired"
        )
        lines.append(f"• <code>{html.escape(profile['domain'])}</code> — {status}")

    lines.append("\nUse /cookieinfo, /checkcookies URL, or /deletecookies domain.")
    await message.reply_text("\n".join(lines))


@app.on_message(filters.private & filters.command("cookieinfo"))
async def cookieinfo_command(client, message):
    profiles = cookie_profiles(message.from_user.id)
    if not profiles:
        await message.reply_text("No cookie profiles saved.")
        return

    lines = ["🍪 <b>Cookie profile details</b>"]
    for profile in profiles:
        lines.append(f"\n<b>{html.escape(profile['domain'])}</b>")
        if profile.get("invalid"):
            lines.append("Invalid cookie format")
            continue

        records = parse_cookie_file(profile["path"])
        domains = sorted({r["domain"] for r in records})
        lines.append(f"Records: {len(records)}")
        lines.append(
            "Expired: " + str(sum(
                1 for r in records
                if r["expiry"] and r["expiry"] <= int(time.time())
            ))
        )
        lines.append("Domains: " + html.escape(", ".join(domains[:15])))

    lines.append("\nCookie values are never displayed.")
    await message.reply_text("\n".join(lines))


@app.on_message(filters.private & filters.command("checkcookies"))
async def checkcookies_command(client, message):
    args = message.text.split(maxsplit=1)
    if len(args) != 2 or not valid_url(args[1]):
        await message.reply_text("Usage: /checkcookies https://www.youtube.com/watch?v=VIDEO_ID")
        return

    uid = message.from_user.id
    url = normalize_url(args[1])
    path = cookie_file_for_url(uid, url)

    if not path:
        await message.reply_text("❌ No unexpired cookie records match this URL.")
        return

    status = await message.reply_text("⚡ Testing URL with saved cookies…")
    try:
        url_info_cache.pop(url, None)
        info = direct_media_info(url) if is_direct_media_url(url) else await asyncio.to_thread(extract_info, url, uid)
        quals = quality_options(info)

        await status.edit_text(
            "✅ <b>Extraction succeeded</b>\n"
            f"Title: {html.escape(str(info.get('title') or 'Unknown')[:180])}\n"
            f"Qualities: <code>{', '.join(lbl for _, lbl in quals) or 'Best available'}</code>\n"
            f"Cookie profile: <code>{html.escape(path.name)}</code>"
        )
    except Exception as exc:
        log.warning("Cookie extraction test failed: %s", exc)
        await status.edit_text(
            "⚠️ <b>Extraction failed</b>\n"
            + html.escape(strip_ansi(str(exc))[:700])
            + "\nThe site may reject this session or require verification."
        )


@app.on_message(filters.private & filters.command("deletecookies"))
async def deletecookies_command(client, message):
    args = message.text.split(maxsplit=1)
    if len(args) != 2:
        await message.reply_text("Usage: /deletecookies youtube.com")
        return

    domain = normalize_domain(args[1])
    if not domain:
        await message.reply_text("Invalid domain.")
        return

    path = cookie_profile_dir(message.from_user.id) / f"{domain}.txt"
    if not path.exists():
        await message.reply_text("No exact cookie profile found.")
        return

    path.unlink()
    cookie_upload_targets.pop(message.from_user.id, None)
    await message.reply_text(f"🗑 Deleted <code>{html.escape(domain)}</code> cookie profile.")


@app.on_message(filters.private & filters.document)
async def cookie_upload_handler(client, message):
    uid = message.from_user.id
    target = cookie_upload_targets.get(uid)
    document = message.document
    filename = (document.file_name or "").lower()

    if not target:
        await message.reply_text("First send /cookies youtube.com, then upload cookies.txt.")
        return

    if not filename.endswith((".txt", ".cookies")):
        await message.reply_text("Upload a Netscape-format .txt cookie file.")
        return

    if document.file_size and document.file_size > 5 * 1024 * 1024:
        await message.reply_text("Cookie file maximum size is 5 MB.")
        return

    folder = cookie_profile_dir(uid)
    temp = folder / f".upload-{uuid.uuid4().hex}.tmp"

    try:
        await message.reply_text("🔎 Validating cookie file…")
        downloaded = await client.download_media(message, file_name=str(temp))

        if not downloaded or not temp.exists():
            raise ValueError("Uploaded file was not saved.")

        records = parse_cookie_file(temp)
        profile_path = folder / f"{target}.txt"
        os.replace(temp, profile_path)

        try:
            profile_path.chmod(0o600)
        except OSError:
            pass

        matched = sum(1 for r in records if cookie_domain_matches(r["domain"], r["include_subdomains"], target))
        cookie_upload_targets.pop(uid, None)
        url_info_cache.clear()

        await message.reply_text(
            "✅ <b>Cookies saved</b>\n"
            f"Profile: <code>{html.escape(target)}</code>\n"
            f"Records: {len(records)}\n"
            f"Matching domain records: {matched}\n"
            "Now use /checkcookies URL to test it."
        )
    except Exception as exc:
        temp.unlink(missing_ok=True)
        await message.reply_text(
            "❌ Could not save cookies: "
            + html.escape(str(exc)[:500])
            + "\nExport Netscape-format cookies.txt and try again."
        )


# ==================== START / HELP / QUEUE / CANCEL ====================

@app.on_message(filters.private & filters.command(["start", "help"]))
async def start_handler(client, message):
    await message.reply_text(
        "👋 <b>Welcome to ReClip (Turbo Edition)</b>\n\n"
        "Send multiple media URLs! You can choose separate qualities and queue up to <b>10 downloads</b> at once.\n\n"
        "• 🚀 <b>Multi-Connection Turbo Speed</b>\n"
        "• 📋 <b>10-Item Smart Queue</b> (/queue to view)\n"
        "• ⚡ <b>Zero-Delay Instant Start</b>\n"
        "• 🎬 <b>Independent Per-Video Quality Selection</b>\n"
        "• 🛑 <b>Smart Cancel</b> (Cancels current & auto-starts next)\n"
        "• 🍪 Per-user cookie profiles (/cookies domain.com)\n"
        "• /queue · /cancel"
    )


@app.on_message(filters.private & filters.command("queue"))
async def queue_command(client, message):
    uid = message.from_user.id
    with active_lock:
        curr = active_jobs.get(uid)
        queued = list(user_queues.get(uid, []))

    if not curr and not queued:
        await message.reply_text("📭 <b>Your download queue is empty.</b>\nSend any link to start!")
        return

    lines = ["📋 <b>Your Download Queue</b>\n"]
    if curr:
        lines.append(
            f"▶️ <b>Now Downloading:</b> {html.escape(curr['title'][:70])} "
            f"(<code>{html.escape(curr['quality_label'])}</code>)"
        )
    if queued:
        lines.append(f"\n⏳ <b>Waiting in Queue ({len(queued)}/{MAX_QUEUE_PER_USER}):</b>")
        for idx, item in enumerate(queued, start=1):
            lines.append(
                f"{idx}. {html.escape(item['title'][:65])} — <code>{html.escape(item['quality_label'])}</code>"
            )

    await message.reply_text("\n".join(lines))


@app.on_message(filters.private & filters.command("cancel"))
async def cancel_handler(client, message):
    uid = message.from_user.id
    was_running, cleared_count = cancel_all_user_jobs(uid)

    if was_running or cleared_count > 0:
        await message.reply_text(
            f"🛑 <b>Cancelled active download & cleared {cleared_count} queued item(s)!</b>"
        )
    else:
        await message.reply_text("🧹 No active or queued downloads found.")


# ==================== LINK HANDLER ====================

def is_direct_media_url(url: str) -> bool:
    """Skip webpage extraction for explicit media/playlist URLs."""
    return urlparse(url).path.lower().endswith((".m3u8", ".mp4", ".m4v", ".mov", ".webm", ".mkv", ".mp3", ".m4a", ".aac", ".ts"))


def direct_media_info(url: str) -> dict:
    name = Path(urlparse(url).path).name or "Direct media"
    ext = Path(urlparse(url).path).suffix.lower().lstrip(".")
    return {
        "id": uuid.uuid4().hex[:12], "title": name[:180],
        "webpage_url": url, "url": url,
        "ext": "mp4" if ext == "m3u8" else ext,
        "_direct_input": True,
        "formats": [{"format_id": "direct", "url": url,
                     "ext": "mp4" if ext == "m3u8" else ext,
                     "protocol": "m3u8_native" if ext == "m3u8" else "https"}],
    }


@app.on_message(
    filters.private
    & filters.text
    & ~filters.command([
        "start", "help", "cancel", "queue", "cookies",
        "cookieinfo", "checkcookies", "deletecookies",
    ])
)
async def link_handler(client, message):
    uid = message.from_user.id
    url = normalize_url(message.text.strip())

    if not valid_url(url):
        await message.reply_text("Send a valid http:// or https:// URL.")
        return

    direct = direct_media_info(url)
    if direct:
        with active_lock:
            q = user_queues.setdefault(uid, deque())
            if len(q) >= MAX_QUEUE_PER_USER:
                await message.reply_text("⚠️ Download queue is full.")
                return
            is_busy = uid in active_jobs or bool(q)
            job_id = uuid.uuid4().hex[:12]
        status_msg = await message.reply_text(
            "⏳ Direct media queued…" if is_busy else "⚡ Direct media detected. Downloading immediately…",
            reply_markup=cancel_keyboard(uid, job_id, is_queued=is_busy),
        )
        job_obj = {
            "job_id": job_id, "uid": uid, "chat_id": message.chat.id,
            "url": url, "info": direct, "mode": "audio" if Path(urlparse(url).path).suffix.lower() in (".mp3", ".m4a", ".aac") else "video", "selection": "best",
            "quality_label": "Direct stream", "title": direct["title"],
            "status_message": status_msg, "cancelled": threading.Event(), "proc": None,
        }
        with active_lock:
            jobs_by_id[job_id] = job_obj
            user_queues[uid].append(job_obj)
            if uid not in user_workers or user_workers[uid].done():
                user_workers[uid] = asyncio.create_task(process_user_queue(client, uid))
        return

    status = await message.reply_text("<b>⚡ FETCHING MEDIA DETAILS</b>\n<blockquote>Analyzing source and available formats…</blockquote>")

    try:
        t0 = time.monotonic()
        info = await asyncio.to_thread(extract_info, url, uid)
        qualities = quality_options(info)
        elapsed = time.monotonic() - t0

        trim_memory()
        link_id = uuid.uuid4().hex[:8]
        link_sessions[link_id] = {
            "uid": uid,
            "url": url,
            "info": info,
            "qualities": qualities,
            "mode": None,
            "ts": time.time(),
        }

        title = html.escape(str(info.get("title") or "Untitled")[:180])
        uploader = html.escape(str(info.get("uploader") or info.get("channel") or "Unknown")[:100])
        qual_count = len(qualities)
        qual_badge = f"{qual_count} video qualities found" if qual_count > 0 else "Best available stream ready"

        text = (
            f"<b>🎬 MEDIA FOUND</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━━━\n"
            f"<b>{title}</b>\n"
            f"<blockquote>👤 <b>Source:</b> {uploader}\n"
            f"⏱ <b>Duration:</b> {duration_text(info.get('duration'))}\n"
            f"⚡ <b>Analyzed:</b> {elapsed:.1f}s\n"
            f"🎚 <b>Available:</b> {html.escape(qual_badge)}</blockquote>\n"
            f"<i>Select your preferred output format below.</i>"
        )

        thumbnail = info.get("thumbnail")
        if thumbnail and thumbnail.startswith(("https://", "http://")):
            try:
                await client.send_photo(
                    message.chat.id,
                    thumbnail,
                    caption=text,
                    parse_mode=enums.ParseMode.HTML,
                    reply_markup=format_keyboard(uid, link_id),
                )
                await status.delete()
                return
            except Exception:
                log.debug("Thumbnail preview failed", exc_info=True)

        await status.edit_text(
            text,
            reply_markup=format_keyboard(uid, link_id),
            disable_web_page_preview=True,
        )

    except Exception as exc:
        log.warning("Metadata extraction failed: %s", exc)
        await status.edit_text(
            "❌ <b>Could not fetch this URL</b>\n"
            + html.escape(strip_ansi(str(exc))[:900])
        )



# ==================== FAST PARALLEL TELEGRAM UPLOADER ====================

async def fast_telegram_upload(
    client, chat_id: int, file_path: Path, mode: str, title: str,
    duration: int, width: int, height: int, thumb_path: Path | None,
    caption: str, progress_cb, cancel_event: threading.Event,
):
    """Bounded parallel MTProto uploader with retry, FloodWait and cancellation."""
    file_path = Path(file_path)
    file_size = file_path.stat().st_size
    if file_size <= 0:
        raise RuntimeError("Cannot upload an empty file.")

    file_name = file_path.name
    chunk_size = TG_UPLOAD_CHUNK_SIZE
    total_parts = math.ceil(file_size / chunk_size)
    if total_parts > 4000:
        raise RuntimeError("File is too large for Telegram's MTProto part limit.")

    is_big = file_size > 10 * 1024 * 1024
    file_id = client.rnd_id()
    workers = min(TG_UPLOAD_WORKERS, total_parts)
    uploaded_bytes = 0
    completed_parts = 0
    last_progress_bytes = 0
    last_progress_at = 0.0
    progress_tasks: set[asyncio.Task] = set()
    reconnect_lock = asyncio.Lock()
    abort_event = asyncio.Event()
    part_queue: asyncio.Queue[int] = asyncio.Queue()
    for part_idx in range(total_parts):
        part_queue.put_nowait(part_idx)

    fd = os.open(str(file_path), os.O_RDONLY)

    async def ensure_connected():
        if client.is_connected:
            return
        async with reconnect_lock:
            if not client.is_connected:
                log.warning("Telegram connection lost during upload; reconnecting...")
                await client.connect()

    async def report_progress(force=False):
        nonlocal last_progress_bytes, last_progress_at
        if not progress_cb:
            return
        now = time.monotonic()
        min_delta = max(chunk_size * 2, file_size // 100)
        if not force and uploaded_bytes < file_size:
            if uploaded_bytes - last_progress_bytes < min_delta and now - last_progress_at < 1.0:
                return
        last_progress_bytes = uploaded_bytes
        last_progress_at = now
        task = asyncio.create_task(progress_cb(min(uploaded_bytes, file_size), file_size))
        progress_tasks.add(task)
        task.add_done_callback(progress_tasks.discard)

    async def upload_part(part_idx):
        nonlocal uploaded_bytes, completed_parts
        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")
        offset = part_idx * chunk_size
        chunk = os.pread(fd, min(chunk_size, file_size - offset), offset)
        if not chunk:
            raise RuntimeError(f"Could not read upload part {part_idx} from disk.")

        for attempt in range(5):
            if cancel_event.is_set():
                raise JobCancelledError("Cancelled by user.")
            try:
                await ensure_connected()
                if is_big:
                    request = raw.functions.upload.SaveBigFilePart(
                        file_id=file_id, file_part=part_idx,
                        file_total_parts=total_parts, bytes=chunk,
                    )
                else:
                    request = raw.functions.upload.SaveFilePart(
                        file_id=file_id, file_part=part_idx, bytes=chunk,
                    )
                result = await asyncio.wait_for(
                    client.invoke(request), timeout=float(TG_UPLOAD_CHUNK_TIMEOUT)
                )
                if result is False:
                    raise RuntimeError(f"Telegram rejected upload part {part_idx}.")
                uploaded_bytes += len(chunk)
                completed_parts += 1
                await report_progress(force=(completed_parts == total_parts))
                return
            except asyncio.CancelledError:
                raise
            except FloodWait as exc:
                wait_for = max(1, int(getattr(exc, "value", 1))) + 1
                log.warning("Telegram FloodWait on part %s: waiting %ss", part_idx, wait_for)
                await asyncio.sleep(wait_for)
            except asyncio.TimeoutError:
                if attempt == 4:
                    raise RuntimeError(f"Telegram upload part {part_idx} timed out after 5 attempts.")
                delay = min(2 ** attempt, 12)
                log.warning(
                    "Upload chunk timeout (part %s, attempt %s/5); retrying in %ss",
                    part_idx, attempt + 1, delay,
                )
                await asyncio.sleep(delay)
            except RPCError as exc:
                if attempt == 4:
                    raise
                delay = min(2 ** attempt, 12)
                log.warning("Telegram RPC error on part %s: %s; retry in %ss", part_idx, exc, delay)
                await asyncio.sleep(delay)
            except Exception as exc:
                if attempt == 4:
                    raise
                delay = min(2 ** attempt, 12)
                log.warning("Upload part %s failed: %s; retry in %ss", part_idx, exc, delay)
                await asyncio.sleep(delay)

        raise RuntimeError(f"Telegram upload part {part_idx} failed.")

    async def worker_loop():
        while not abort_event.is_set():
            try:
                part_idx = part_queue.get_nowait()
            except asyncio.QueueEmpty:
                return
            try:
                await upload_part(part_idx)
            except BaseException:
                abort_event.set()
                raise
            finally:
                part_queue.task_done()

    log.info(
        "Parallel MTProto upload: %s | %s | %s parts | %s workers | %s chunk",
        file_name, human_size(file_size), total_parts, workers, human_size(chunk_size),
    )
    worker_tasks = [asyncio.create_task(worker_loop()) for _ in range(workers)]
    try:
        results = await asyncio.gather(*worker_tasks, return_exceptions=True)
        errors = [item for item in results if isinstance(item, BaseException)]
        if errors:
            for task in worker_tasks:
                if not task.done():
                    task.cancel()
            await asyncio.gather(*worker_tasks, return_exceptions=True)
            raise errors[0]
        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")
        if completed_parts != total_parts or uploaded_bytes != file_size:
            raise RuntimeError(
                f"Upload incomplete: {completed_parts}/{total_parts} parts, "
                f"{human_size(uploaded_bytes)}/{human_size(file_size)}."
            )
        if progress_tasks:
            await asyncio.gather(*list(progress_tasks), return_exceptions=True)
    finally:
        os.close(fd)
        for task in worker_tasks:
            if not task.done():
                task.cancel()
        if worker_tasks:
            await asyncio.gather(*worker_tasks, return_exceptions=True)
        if progress_tasks:
            await asyncio.gather(*list(progress_tasks), return_exceptions=True)

    if cancel_event.is_set():
        raise JobCancelledError("Cancelled by user.")

    if is_big:
        input_file = raw.types.InputFileBig(id=file_id, parts=total_parts, name=file_name)
    else:
        digest = hashlib.md5()
        with file_path.open("rb") as small_file:
            for block in iter(lambda: small_file.read(1024 * 1024), b""):
                digest.update(block)
        input_file = raw.types.InputFile(
            id=file_id,
            parts=total_parts,
            name=file_name,
            md5_checksum=digest.hexdigest(),
        )

    thumb_input = None
    if thumb_path and Path(thumb_path).is_file():
        try:
            thumb_input = await client.save_file(str(thumb_path))
        except Exception as exc:
            log.warning("Thumbnail upload failed; sending without thumbnail: %s", exc)

    attributes = []
    if mode == "video":
        attributes.append(raw.types.DocumentAttributeVideo(
            duration=duration or 0, w=width or 0, h=height or 0,
            supports_streaming=True,
        ))
        mime_type = "video/mp4"
        telegram_filename = safe_filename(title) + ".mp4"
    elif mode == "audio":
        attributes.append(raw.types.DocumentAttributeAudio(
            duration=duration or 0, title=title or "Audio", performer="ReClip",
        ))
        mime_type = "audio/mpeg"
        telegram_filename = safe_filename(title) + ".mp3"
    else:
        mime_type = "application/octet-stream"
        telegram_filename = safe_filename(title) + file_path.suffix

    attributes.append(raw.types.DocumentAttributeFilename(file_name=telegram_filename))
    media = raw.types.InputMediaUploadedDocument(
        file=input_file, thumb=thumb_input, mime_type=mime_type,
        attributes=attributes, force_file=False,
    )

    peer = await client.resolve_peer(chat_id)
    parsed_caption = await client.parser.parse(caption, enums.ParseMode.HTML)
    request = raw.functions.messages.SendMedia(
        peer=peer, media=media,
        message=parsed_caption["message"],
        entities=parsed_caption["entities"],
        random_id=client.rnd_id(),
    )
    # No blind commit retry: a timeout can mean Telegram already accepted the message.
    await asyncio.wait_for(client.invoke(request), timeout=180.0)


# ==================== SMART QUEUE WORKER & FAST EXECUTION ====================

async def refresh_user_queue_positions(uid: int):
    with active_lock:
        queued_list = list(user_queues.get(uid, []))

    for idx, item in enumerate(queued_list, start=1):
        if item["cancelled"].is_set():
            continue
        text = (
            f"<b>⏳ QUEUED · #{idx}</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━━━\n"
            f"🎞 <b>{html.escape(item['title'][:120])}</b>\n"
            f"<blockquote>🎚 <b>Quality:</b> <code>{html.escape(item['quality_label'])}</code>\n"
            f"<i>Will start automatically when the current task finishes.</i></blockquote>"
        )
        await edit_progress(
            item["status_message"],
            text,
            force=True,
            reply_markup=cancel_keyboard(uid, item["job_id"], is_queued=True),
        )


async def process_user_queue(client, uid: int):
    sem = get_global_sem()
    try:
        while True:
            with active_lock:
                q = user_queues.get(uid)
                if not q:
                    user_workers.pop(uid, None)
                    active_jobs.pop(uid, None)
                    return
                job = q.popleft()
                if job["cancelled"].is_set():
                    jobs_by_id.pop(job["job_id"], None)
                    continue
                active_jobs[uid] = job

            await refresh_user_queue_positions(uid)

            async with sem:
                if not job["cancelled"].is_set():
                    await execute_single_job(client, job)

            with active_lock:
                jobs_by_id.pop(job["job_id"], None)
                if active_jobs.get(uid) is job:
                    active_jobs.pop(uid, None)

            trim_memory()
    finally:
        with active_lock:
            user_workers.pop(uid, None)


async def execute_single_job(client, job: dict):
    uid = job["uid"]
    chat_id = job["chat_id"]
    job_id = job["job_id"]
    url = job["url"]
    info = job["info"]
    mode = job["mode"]
    selection = job["selection"]
    quality_label = job["quality_label"]
    status_message = job["status_message"]
    cancel_event: threading.Event = job["cancelled"]

    title = str(info.get("title") or "ReClip media")
    template = str(DOWNLOAD_DIR / f"{job_id}.%(ext)s")
    loop = asyncio.get_running_loop()
    last_hook = [0.0, -1.0]
    cancel_markup = cancel_keyboard(uid, job_id, is_queued=False)

    def download_hook(data):
        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        state = data.get("status")
        if state == "finished":
            asyncio.run_coroutine_threadsafe(
                edit_progress(
                    status_message,
                    f"<b>✅ DOWNLOAD FINISHED</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"<blockquote>🎚 <b>Quality:</b> <code>{html.escape(quality_label)}</code>\n"
                    f"<i>Verifying media and preparing Telegram upload…</i></blockquote>",
                    True,
                    reply_markup=cancel_markup,
                ),
                loop,
            )
            return

        if state != "downloading":
            return

        total = data.get("total_bytes") or data.get("total_bytes_estimate") or 0
        done = data.get("downloaded_bytes") or 0
        percent = done * 100 / total if total else 0
        now = time.monotonic()

        if (
            percent >= 100
            or last_hook[1] < 0
            or (
                percent - last_hook[1] >= 2
                and now - last_hook[0] >= PROGRESS_INTERVAL
            )
        ):
            last_hook[:] = [now, percent]
            speed = f"{human_size(data.get('speed'))}/s" if data.get("speed") else "boosting…"
            eta = duration_text(data.get("eta")) if data.get("eta") is not None else "—"

            text = (
                f"<b>⬇️ DOWNLOADING</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"🎞 <b>{html.escape(title[:85])}</b>\n"
                f"<blockquote>🎚 <b>Quality:</b> <code>{html.escape(quality_label)}</code>\n"
                f"<code>{progress_bar(percent, 18)}</code> <b>{percent:.1f}%</b>\n"
                f"📦 <b>{human_size(done)}</b> / {human_size(total)}\n"
                f"🚀 <b>Speed:</b> {html.escape(speed)}\n"
                f"⏳ <b>ETA:</b> {html.escape(eta)}</blockquote>"
            )

            asyncio.run_coroutine_threadsafe(
                edit_progress(status_message, text, reply_markup=cancel_markup),
                loop,
            )

    use_proxy = info.get("_use_proxy", False)
    yt_use_cookies = info.get("_yt_use_cookies", True)
    yt_clients = info.get("_yt_clients", None)

    options = make_ytdlp_options(
        uid,
        url,
        {
            "outtmpl": template,
            "progress_hooks": [download_hook],
            "continuedl": True,
            "overwrites": True,
        },
        fast_fetch=False,
        use_proxy=use_proxy,
        use_cookies=yt_use_cookies,
        yt_clients=yt_clients,
    )

    if mode == "audio":
        options.update({
            "format": "bestaudio/best",
            "postprocessors": [{
                "key": "FFmpegExtractAudio",
                "preferredcodec": "mp3",
                "preferredquality": "192",
            }],
        })
    else:
        options.update({
            "format": build_video_format_selector(info, selection),
            "merge_output_format": "mp4",
            "postprocessor_args": {
                "merger": ["-threads", "1", "-movflags", "+faststart"],
            },
        })

    thumb_path: Path | None = None

    try:
        await edit_progress(
            status_message,
            f"🚀 <b>Starting download ({html.escape(quality_label)})…</b>\n"
            f"🎞 {html.escape(title[:100])}",
            True,
            reply_markup=cancel_markup,
        )

        if info.get("_direct_input") or can_direct_fast_download(info, mode, selection):
            try:
                await asyncio.to_thread(
                    direct_cffi_download,
                    info,
                    mode,
                    selection,
                    job_id,
                    uid,
                    download_hook,
                )
            except JobCancelledError:
                raise
            except Exception as direct_err:
                if info.get("_tiktok_fallback"):
                    raise
                log.info("Direct fast-path skipped (%s), using yt-dlp", direct_err)
                cleanup_job_files(job_id)
                await asyncio.to_thread(run_ytdlp_fast, options, url)
        else:
            try:
                await asyncio.to_thread(run_ytdlp_fast, options, url)
            except JobCancelledError:
                raise
            except Exception as ytdl_err:
                if cancel_event.is_set():
                    raise JobCancelledError("Cancelled by user.") from ytdl_err

                if is_youtube_url(url):
                    log.info("Primary YouTube download failed (%s), retrying with fallback client via WARP", ytdl_err)
                    cleanup_job_files(job_id)
                    fb_options = make_ytdlp_options(
                        uid,
                        url,
                        {
                            "outtmpl": template,
                            "progress_hooks": [download_hook],
                            "continuedl": True,
                            "overwrites": True,
                            "format": "bestaudio/best" if mode == "audio" else build_video_format_selector(info, selection),
                            "merge_output_format": "mp4" if mode == "video" else None,
                        },
                        fast_fetch=False,
                        use_proxy=True,
                        use_cookies=bool(cookie_file_for_url(uid, url)),
                        yt_clients=None,
                    )
                    if mode == "audio":
                        fb_options["postprocessors"] = [{
                            "key": "FFmpegExtractAudio",
                            "preferredcodec": "mp3",
                            "preferredquality": "192",
                        }]
                    await asyncio.to_thread(run_ytdlp_fast, fb_options, url)
                elif is_tiktok_url(url):
                    cleanup_job_files(job_id)
                    fb_info = await asyncio.to_thread(tiktok_fallback_extract, url)
                    await asyncio.to_thread(
                        direct_cffi_download,
                        fb_info,
                        mode,
                        selection,
                        job_id,
                        uid,
                        download_hook,
                    )
                else:
                    log.info("Primary yt-dlp download failed (%s), trying smart fallback", ytdl_err)
                    cleanup_job_files(job_id)
                    try:
                        await asyncio.to_thread(
                            direct_cffi_download,
                            info,
                            mode,
                            selection,
                            job_id,
                            uid,
                            download_hook,
                        )
                    except JobCancelledError:
                        raise
                    except Exception:
                        cleanup_job_files(job_id)
                        fb_info = await asyncio.to_thread(generic_cffi_extract, url, uid)
                        await asyncio.to_thread(
                            direct_cffi_download,
                            fb_info,
                            mode,
                            selection,
                            job_id,
                            uid,
                            download_hook,
                        )

        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        candidates = [
            path for path in DOWNLOAD_DIR.glob(f"{job_id}.*")
            if path.is_file()
            and not path.name.endswith((".part", ".ytdl", ".aria2", "_thumb.jpg", "_seekable.mp4"))
        ]

        if not candidates:
            raise RuntimeError("Download finished but no valid output file was produced.")

        wanted_ext = ".mp3" if mode == "audio" else ".mp4"
        preferred = [path for path in candidates if path.suffix.lower() == wanted_ext]
        path = max(preferred or candidates, key=lambda p: p.stat().st_size)

        video_meta = {"duration": int(info.get("duration") or 0), "width": 0, "height": 0}
        if mode == "video":
            await edit_progress(
                status_message,
                "<b>🛠 FINALIZING VIDEO</b>\n━━━━━━━━━━━━━━━━━━━━━━\n<blockquote>Verifying playback compatibility and generating thumbnail…</blockquote>",
                True,
                reply_markup=cancel_markup,
            )
            path, probed = await asyncio.to_thread(ensure_playable_seekable_mp4, path, job_id)
            if probed["duration"] > 0:
                video_meta["duration"] = probed["duration"]
            video_meta["width"] = probed["width"]
            video_meta["height"] = probed["height"]

            thumb_path = await asyncio.to_thread(
                generate_video_thumbnail,
                path,
                job_id,
                video_meta["duration"],
            )

        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        size = path.stat().st_size
        if size > MAX_FILE_SIZE_MB * 1024 * 1024:
            raise RuntimeError(
                f"File size {human_size(size)} exceeds the configured {MAX_FILE_SIZE_MB} MB limit."
            )

        res_badge = f" · {video_meta['height']}p" if video_meta.get("height") else f" · {quality_label}"
        caption = (
            f"<b>🎬 {html.escape(title[:180])}</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━━━\n"
            f"<blockquote>"
            f"⏱ <b>Duration:</b> {duration_text(video_meta['duration'] or info.get('duration'))}\n"
            f"🎚 <b>Quality:</b> {html.escape(str(video_meta['height']) + 'p' if video_meta.get('height') else quality_label)}\n"
            f"📦 <b>Size:</b> {human_size(size)}\n"
            f"📁 <b>Format:</b> {html.escape(path.suffix[1:].upper())}"
            f"</blockquote>\n"
            f"<i>⚡ Delivered by ReClip</i>"
        )

        last_upload = [0.0, -1.0]
        upload_last_sample = [time.monotonic(), 0]
        upload_speed = [0.0]

        async def upload_progress(current, total, *args):
            if cancel_event.is_set():
                return
            now = time.monotonic()
            elapsed = max(now - upload_last_sample[0], 0.001)
            delta = max(0, current - upload_last_sample[1])
            instant = delta / elapsed
            upload_speed[0] = instant if upload_speed[0] <= 0 else (
                upload_speed[0] * 0.65 + instant * 0.35
            )
            upload_last_sample[:] = [now, current]
            percent = current * 100 / max(total, 1)

            if (
                percent >= 100 or last_upload[1] < 0
                or (percent - last_upload[1] >= 2 and now - last_upload[0] >= PROGRESS_INTERVAL)
            ):
                last_upload[:] = [now, percent]
                eta = duration_text((total - current) / upload_speed[0]) if upload_speed[0] > 0 else "—"
                speed = f"{human_size(upload_speed[0])}/s" if upload_speed[0] > 0 else "Calculating…"
                await edit_progress(
                    status_message,
                    (
                        f"<b>📤 TELEGRAM UPLOAD</b>\n"
                        f"━━━━━━━━━━━━━━━━━━━━━━\n"
                        f"🎞 <b>{html.escape(title[:90])}</b>\n"
                        f"<blockquote><code>{progress_bar(percent, 18)}</code> <b>{percent:.1f}%</b>\n"
                        f"📦 <b>{human_size(current)}</b> / {human_size(total)}\n"
                        f"🚀 <b>Speed:</b> {html.escape(speed)}\n"
                        f"⏳ <b>ETA:</b> {html.escape(eta)}</blockquote>\n"
                        f"<i>⚡ Parallel MTProto · {TG_UPLOAD_WORKERS} workers</i>"
                    ),
                    force=percent >= 100,
                    reply_markup=None if percent >= 100 else cancel_markup,
                )

        await edit_progress(
            status_message,
            (
                f"<b>📤 PREPARING TELEGRAM UPLOAD</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"🎞 <b>{html.escape(title[:90])}</b>\n"
                f"<blockquote>⚡ Initializing parallel MTProto uploader…\n"
                f"🧩 Chunk size: <code>{human_size(TG_UPLOAD_CHUNK_SIZE)}</code>\n"
                f"🔗 Workers: <code>{TG_UPLOAD_WORKERS}</code></blockquote>"
            ),
            True,
            reply_markup=cancel_markup,
        )

        await fast_telegram_upload(
            client=client,
            chat_id=chat_id,
            file_path=path,
            mode=mode,
            title=title,
            duration=video_meta["duration"] if mode == "video" else int(info.get("duration") or 0),
            width=video_meta["width"],
            height=video_meta["height"],
            thumb_path=thumb_path,
            caption=caption,
            progress_cb=upload_progress,
            cancel_event=cancel_event,
        )

        if cancel_event.is_set():
            raise JobCancelledError("Cancelled by user.")

        await edit_progress(
            status_message,
            f"<b>🎉 UPLOAD COMPLETE</b>\n"
            f"━━━━━━━━━━━━━━━━━━━━━━\n"
            f"🎞 <b>{html.escape(title[:100])}</b>\n"
            f"<blockquote>🎚 <b>Quality:</b> <code>{html.escape(quality_label)}</code>\n"
            f"📦 <b>Size:</b> {human_size(size)}\n"
            f"✅ Successfully delivered to Telegram.</blockquote>",
            True,
            reply_markup=None,
        )

    except (JobCancelledError, StopTransmission):
        log.info("Job forcefully cancelled by user %s (job_id=%s)", uid, job_id)
        cleanup_job_files(job_id)
        with active_lock:
            rem = len(user_queues.get(uid, []))
        next_note = f"\n⏭ Starting next queued video ({rem} remaining)…" if rem > 0 else ""
        await edit_progress(
            status_message,
            "🛑 <b>Download Cancelled!</b>\nProcess killed & storage cleared." + next_note,
            True,
            reply_markup=None,
        )

    except (DownloadError, RPCError, FloodWait, RuntimeError, OSError) as exc:
        if cancel_event.is_set() or "Cancelled by user" in str(exc):
            cleanup_job_files(job_id)
            await edit_progress(
                status_message,
                "🛑 <b>Download Cancelled!</b>\nProcess killed & storage cleared.",
                True,
                reply_markup=None,
            )
        else:
            log.warning("Job failed for user %s: %s", uid, exc)
            await edit_progress(
                status_message,
                "❌ <b>Failed</b>\n" + html.escape(strip_ansi(str(exc))[:900]),
                True,
                reply_markup=None,
            )

    except Exception as exc:
        if cancel_event.is_set() or "Cancelled by user" in str(exc):
            cleanup_job_files(job_id)
            await edit_progress(
                status_message,
                "🛑 <b>Download Cancelled!</b>\nProcess killed & storage cleared.",
                True,
                reply_markup=None,
            )
        else:
            log.exception("Unexpected download/upload failure")
            await edit_progress(
                status_message,
                "❌ Unexpected error:\n" + html.escape(strip_ansi(str(exc))[:700]),
                True,
                reply_markup=None,
            )

    finally:
        cleanup_job_files(job_id)


# ==================== CALLBACK HANDLER ====================

@app.on_callback_query()
async def callback_handler(client, query):
    uid = query.from_user.id
    data = query.data or ""

    if data == "new":
        await query.answer("Send another link anytime!")
        await client.send_message(query.message.chat.id, "🔗 Send the next URL (you can queue up to 10!).")
        return

    parts = data.split(":", 3)

    if parts[0] == "cancel":
        try:
            owner = int(parts[1])
        except (ValueError, IndexError):
            owner = -1

        if owner != uid:
            await query.answer("This job belongs to another user.", show_alert=True)
            return

        target_job_id = parts[2] if len(parts) >= 3 else ""
        if not target_job_id:
            with active_lock:
                curr = active_jobs.get(uid)
                target_job_id = curr["job_id"] if curr else ""

        result = cancel_specific_job(uid, target_job_id)
        if result == "queued":
            await query.answer("🗑 Removed from queue!", show_alert=False)
            await edit_progress(query.message, "🗑 <b>Removed from queue.</b>", True, reply_markup=None)
            await refresh_user_queue_positions(uid)
        elif result == "running":
            await query.answer("🛑 Force-killing download & starting next in queue…", show_alert=False)
            with active_lock:
                rem = len(user_queues.get(uid, []))
            next_note = f"\n⏭ Starting next queued video ({rem} remaining)…" if rem > 0 else ""
            await edit_progress(
                query.message,
                "🛑 <b>Download Cancelled!</b>\nProcess killed & storage cleared." + next_note,
                True,
                reply_markup=None,
            )
        else:
            await query.answer("No active download found.", show_alert=False)
        return

    if parts[0] in ("mode", "back", "q"):
        owner_index = 2 if parts[0] == "mode" else 1
        link_index = 3 if parts[0] == "mode" else 2

        try:
            owner = int(parts[owner_index])
            link_id = parts[link_index]
        except (ValueError, IndexError):
            owner = -1
            link_id = ""

        if owner != uid:
            await query.answer("This menu belongs to another user.", show_alert=True)
            return

        session = link_sessions.get(link_id)
        if not session or session.get("uid") != uid:
            await query.answer("Session expired. Send URL again.", show_alert=True)
            return

        session["ts"] = time.time()
        is_photo = bool(getattr(query.message, "photo", None))

        async def edit_menu(text, markup):
            if is_photo:
                await query.message.edit_caption(text, parse_mode=enums.ParseMode.HTML, reply_markup=markup)
            else:
                await query.message.edit_text(
                    text,
                    parse_mode=enums.ParseMode.HTML,
                    reply_markup=markup,
                    disable_web_page_preview=True,
                )

        if parts[0] == "mode" and len(parts) == 4:
            mode = parts[1]
            if mode not in ("video", "audio"):
                await query.answer("Unknown format.")
                return

            session["mode"] = mode
            await query.answer("Selected.")

            if mode == "audio":
                markup = InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬇️ Download MP3", callback_data=f"q:{uid}:{link_id}:best")],
                    [InlineKeyboardButton("⬅️ Format", callback_data=f"back:{uid}:{link_id}")],
                ])
                await edit_menu("<b>🎵 AUDIO MODE SELECTED</b>\n━━━━━━━━━━━━━━━━━━━━━━\n<blockquote>🎧 Output: <b>MP3 · 192 kbps</b>\n<i>Ready to download and upload.</i></blockquote>", markup)
            else:
                quals = session.get("qualities", [])
                if quals:
                    await edit_menu(
                        "<b>🎬 SELECT VIDEO QUALITY</b>\n━━━━━━━━━━━━━━━━━━━━━━\n<blockquote>Choose the resolution you want to receive.</blockquote>",
                        quality_keyboard(uid, link_id, quals),
                    )
                else:
                    markup = InlineKeyboardMarkup([
                        [InlineKeyboardButton("⭐ Download Best MP4", callback_data=f"q:{uid}:{link_id}:best")],
                        [InlineKeyboardButton("⬅️ Format", callback_data=f"back:{uid}:{link_id}")],
                    ])
                    await edit_menu("<b>⭐ BEST VIDEO READY</b>\n━━━━━━━━━━━━━━━━━━━━━━\n<blockquote>Telegram-compatible MP4 will be prepared automatically.</blockquote>", markup)
            return

        if parts[0] == "back":
            await query.answer()
            await edit_menu("<b>📥 CHOOSE OUTPUT FORMAT</b>\\n━━━━━━━━━━━━━━━━━━━━━━\\n<blockquote>Select video or audio to continue.</blockquote>", format_keyboard(uid, link_id))
            return

        if parts[0] == "q" and len(parts) == 4:
            mode = session.get("mode")
            if mode not in ("video", "audio"):
                await query.answer("Choose MP4 or MP3 first.", show_alert=True)
                return

            selection = parts[3] if mode == "video" else "best"
            qualities_map = dict(session.get("qualities", []))

            if selection != "best" and selection not in qualities_map:
                await query.answer("Invalid quality choice.", show_alert=True)
                return

            if mode == "audio":
                quality_label = "MP3 Audio"
            elif selection == "best":
                quality_label = "Best MP4"
            else:
                quality_label = qualities_map.get(selection, "MP4")

            with active_lock:
                q = user_queues.setdefault(uid, deque())
                is_busy = (uid in active_jobs) or (len(q) > 0)
                if len(q) >= MAX_QUEUE_PER_USER:
                    await query.answer(
                        f"⚠️ Queue full! Maximum {MAX_QUEUE_PER_USER} pending downloads allowed.",
                        show_alert=True,
                    )
                    return

                job_id = uuid.uuid4().hex[:12]
                queue_pos = len(q) + 1

            await query.answer(
                f"⏳ Added to Queue (#{queue_pos})" if is_busy else "🚀 Starting download immediately!"
            )

            title_str = str((session.get("info") or {}).get("title") or "Media")
            if is_busy:
                init_text = (
                    f"<b>⏳ ADDED TO QUEUE · #{queue_pos}</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"🎞 <b>{html.escape(title_str[:120])}</b>\n"
                    f"<blockquote>🎚 <b>Quality:</b> <code>{html.escape(quality_label)}</code>\n"
                    f"<i>Will start automatically when the current task finishes.</i></blockquote>"
                )
            else:
                init_text = (
                    f"<b>🚀 DOWNLOAD STARTED</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"🎞 <b>{html.escape(title_str[:120])}</b>\n"
                    f"<blockquote>🎚 <b>Quality:</b> <code>{html.escape(quality_label)}</code>\n"
                    f"<i>Preparing the download route…</i></blockquote>"
                )

            status_msg = await client.send_message(
                query.message.chat.id,
                init_text,
                reply_markup=cancel_keyboard(uid, job_id, is_queued=is_busy),
            )

            job_obj = {
                "job_id": job_id,
                "uid": uid,
                "chat_id": query.message.chat.id,
                "url": session["url"],
                "info": dict(session["info"]),
                "mode": mode,
                "selection": selection,
                "quality_label": quality_label,
                "title": title_str,
                "status_message": status_msg,
                "cancelled": threading.Event(),
                "proc": None,
            }

            with active_lock:
                jobs_by_id[job_id] = job_obj
                user_queues[uid].append(job_obj)
                if uid not in user_workers or user_workers[uid].done():
                    user_workers[uid] = asyncio.create_task(process_user_queue(client, uid))

            return

    await query.answer("Unknown action.")


# ==================== START BOT ====================

if __name__ == "__main__":
    log.info(
        "Starting ReClip Telegram bot (Optimized | downloads=%s | range_connections=%s | aria2c=%s | deno=%s)",
        MAX_CONCURRENT,
        DIRECT_RANGE_CONNECTIONS,
        HAS_ARIA2C,
        HAS_DENO,
    )
    app.run()
