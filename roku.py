#!/usr/bin/env python3
"""
Standalone The Roku Channel (US live TV) extractor.
Writes an M3U playlist and XMLTV guide. No credentials required.

Usage:
    python roku.py
    python roku.py --out-dir playlists --m3u roku.m3u --epg roku.xml
    python roku.py --workers 4 --stream-rate 2 --max-lookups 200
    python roku.py --no-epg            # playlist only
    python roku.py -v                  # debug logging

Options:
    --out-dir DIR           Output directory, created if missing        (default: .)
    --m3u FILE              Playlist filename, relative to --out-dir    (default: roku.m3u)
    --epg FILE              XMLTV filename, relative to --out-dir       (default: roku.xml)
    --cache FILE            Cache filename, relative to --out-dir       (default: roku_cache.json)
    --no-cache              Ignore and don't write the cache
    --cache-hours N         How long a cached playId is trusted         (default: 12)
    --gracenote-map FILE    CSV of key,tmsid rows mapping Roku station
                            ids to Gracenote ids (default: roku_gracenote.csv
                            next to this script; skipped if missing)
    --update-gracenote      Refresh --gracenote-map from the FastChannels
                            community Gist before using it (Roku rows
                            only, known-bad ids dropped); keeps the local
                            file if either download fails
    --gracenote-url URL     Override the community map URL
    --gracenote-exclusions-url URL
                            Override the known-bad id list URL
    --workers N             Concurrent requests                         (default: 4)
    --stream-rate R         Max playback/lookup requests/sec            (default: 3.0)
    --max-lookups N         Cap on uncached playId lookups per run, so a
                            cold cache fills over several runs; 0 = no
                            cap                                         (default: 300)
    --epg-rate R            Max guide requests/sec                      (default: 3.0)
    --min-guide-hours N     Re-fetch a channel's guide when its stored
                            guide covers less than N hours ahead        (default: 8)
    --max-epg-requests N    Cap on guide requests per run, least-covered
                            channels first; 0 = no cap                  (default: 250)
    --epg-budget SEC        Max seconds spent on guide requests         (default: 600)
    --include-dash          Keep channels whose playback URL is a DASH
                            (.mpd) manifest instead of HLS; these need
                            Widevine and are skipped by default
    --no-epg                Write the playlist only
    -v, --verbose           Debug logging

Notes:
    - Stream URLs come from the playback API and are signed (JWT + traceId). They
      stay valid for roughly 5-6 hours, so run this at least every 6 hours.
    - Roku's channel list carries no playIds, so each channel needs a content lookup
      before playback. Those playIds (and selector URLs) are cached in --cache, which
      you should commit so it survives between runs. A cached playId that playback
      rejects with 401/404 is dropped and looked up again.
    - Roku blocks bursts with HTTP 403 (and 452 outside the US). After 8 consecutive
      401/403 responses, or any 403/429 on the guide, all further requests stop for
      the run. Channels already resolved are still written, and the cache is saved,
      so the next run carries on from there.
    - Only channels that resolve to a stream are written. Channels the playback API
      refuses (403, usually DRM-locked) are skipped.
    - If a playback call fails with 502/503/504, a URL is built from the channel's
      selector UUID plus the OSM session token of a channel that did resolve.
    - The guide is incremental: programmes from the previous --epg file are kept for
      channels that don't need a refresh this run. Channels Roku returns no schedule
      for are remembered in the cache and not retried for --cache-hours.
      Delete the XML to force a full refetch.
    - Gracenote ids come from Roku's response when it has one, else from the
      --gracenote-map CSV, and are written as tvc-guide-stationid.
    - --update-gracenote rewrites that CSV (only if something changed), so commit it
      along with the other outputs. It refuses to apply a download that has under half
      as many Roku rows as the local file, or whose id list can't be fetched.

Deps: pip install requests
"""
import argparse
import base64
import csv
import json
import logging
import os
import re
import sys
import threading
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from urllib.parse import parse_qs, quote, urlparse

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

BASE        = "https://therokuchannel.roku.com"
HOME        = f"{BASE}/"
CSRF_URL    = f"{BASE}/api/v1/csrf"
PLAYBACK    = f"{BASE}/api/v3/playback"
EPG_URL     = f"{BASE}/api/v2/epg"
EPG_SCHEDULE_TPL = f"{BASE}/api/v4/epg/{{sid}}"
BILLBOARD_URL = f"{BASE}/api/v1/billboard/landing/trc-us-live-ml-page-en-current"
CONTENT_TPL = "https://content.sr.roku.com/content/v1/roku-trc/{sid}"
PROXY_BASE  = f"{BASE}/api/v2/homescreen/content/"
OSM_BASE    = "https://osm.sr.roku.com"

EPG_SCHEDULE_INCLUDE = (
    "seasonNumber,episodeNumber,description,descriptions,title,"
    "imageMap.gridEpg,series.title,parentalRatings,contentRatingClass"
)

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/145.0.0.0 Safari/537.36"
)

HOME_403_RETRIES = 3     # CloudFront 403s are often edge-specific; retry on a fresh connection
CSRF_ATTEMPTS    = 5
BLOCK_LIMIT      = 8     # consecutive 401/403 responses before the run stops sending requests
DEFAULT_WORKERS  = 4
CACHE_VERSION    = 1

OSM_STREAM_RE    = re.compile(r"/osm/v1/hls/master/([0-9a-f-]{36})/([0-9a-f]+)/index\.m3u8")
SELECTOR_UUID_RE = re.compile(r"/v1/([0-9a-f-]{36})$")
GRACENOTE_ID_RE  = re.compile(r"^(EP|SH|MV|SP|TR)\d+$", re.IGNORECASE)

# Community Gracenote map and known-bad id list maintained for FastChannels.
GRACENOTE_MAP_URL = ("https://gist.githubusercontent.com/kineticman/"
                     "87765d469610233f894c9c225cb4f2ca/raw/gistfile1.txt")
GRACENOTE_EXCLUSIONS_URL = ("https://gist.githubusercontent.com/kineticman/"
                            "d15d0d96ef09b0c159f016f8d4b881d7/raw/gistfile1.txt")

# Tags on the EPG station object -> category (checked in order)
TAG_CATEGORY_PRIORITY = [
    ("news",               "News"),
    ("spanish-language",   "Spanish"),
    ("music",              "Music"),
    ("kids_music",         "Kids"),
    ("kids_linear",        "Kids"),
    ("ages_1-3",           "Kids"),
    ("ages_4-6",           "Kids"),
    ("ages_7-9",           "Kids"),
    ("ages_10plus",        "Kids"),
    ("educational",        "Kids"),
    ("preschool_specials", "Kids"),
]

CAT_ID_MAP = {
    "cat-news": "News", "cat-national-news": "News", "cat-epg-news-opinion": "News",
    "cat-sports": "Sports", "cat-sports-general": "Sports",
    "cat-movies": "Movies", "cat-movie": "Movies",
    "cat-comedy": "Comedy", "cat-drama": "Drama",
    "cat-reality": "Reality TV", "cat-lifestyle": "Lifestyle",
    "cat-food": "Food", "cat-music": "Music",
    "cat-kids": "Kids", "cat-family": "Kids",
}

# Channel-name keyword rules, checked in order (ported from FastChannels category_utils).
_NAME_CATEGORY_RULES: list[tuple[set[str], str]] = [
    # Sports — checked before News so "CBS Sports" doesn't fall through
    ({
        'sport', 'deportes',
        'nfl', 'nba ', 'nhl', 'mlb', 'nascar', 'nhra', 'pga tour',
        'ufc', 'mma', 'tennis', 'golf', 'wrestling', 'boxing', 'ringside',
        'billiard', 'pickleball', 'bassmaster', 'x games', 'pbr:',
        'motocross', 'f1 channel', 'espn', 'fubo', 'fanduel tv', 'fanduel',
        'draftkings', 'sportsgrid', 'speed sport', 'swerve combat',
        'swerve women', 'hbo boxing', 'one championship', 'pfl mma',
        'dazn', 'top rank', 'lucha plus', 'big 12 studios', 'acc digital',
        'red bull tv', 'outside tv', 'myoutdoortv', 'racer select',
        'racing america', 'top barça', 'uefa', 'fifa+', 'pursuitup',
        'rig tv', 'monster jam', 'hong kong fight', 'hi-yah',
        'american ninja', 'american gladiator', 'meateater',
        'nesn', 'overtime', 'fuel tv', 'team usa tv', 'fear factor',
        'jim rome',
        'nhl network', 'nbc sports', 'bowling', 'poker', 'surf league',
        'baseball tv', 'beinsport', 'bein sport', 'sportsnet', 'willow sport',
        # Spectrum's numbered MLB Extra Innings out-of-market feed slots (e.g.
        # "iND Game 02 HD IP") — the channel name itself carries no other
        # sports keyword; confirmed live 2026-09-17 by cross-referencing the
        # channel's own EPG (100% MLB programming) since the raw genre field
        # is empty for most of these slots.
        'ind game',
    }, 'Sports'),
    # Music
    ({
        'iheart', 'vevo', 'stingray', 'tiktok radio', 'revolt mixtape',
        'circle country', 'electric now', 'mvstv', 'lamusica', 'lamúsica',
        'musica tv', 'música tv', 'fuse +',
        'bet pluto', 'mtv pluto',
        'mtv ', 'concerts by stingray', 'country network',
        'b4u music', 'yrf music', 'raj mus', 'saga music', 'aghani',
    }, 'Music'),
    # Local News — checked before general News so local stations don't fall through
    ({
        'local now',           # Local Now city-specific channels (all markets)
        'abc7', 'abc13', 'abc30', 'abc6 ', 'abc11',
        'kiro 7', 'wpxi', 'wsb ', 'wsoc', 'wftv', 'wapa+',
        "arizona's family", 'first alert',
        'abc localish',
        'news center',         # e.g. News Center Maine
    }, 'Local News'),
    # News / Weather
    ({
        'news', 'noticias', 'weather', 'cnn', 'fox local',
        'usa today', 'the hill', 'tyt-go', 'newsmax', 'oan plus',
        'liveno', 'scripps', 'rcn noticias', 'telemundo al día',
        'telemundo ahora', 'fuerza informativa', 'telediario',
        'inside edition',
        'cheddar', 'bloomberg', 'euronews', 'france 24',
        'al jazeera', 'al arabiya', 'al hadath', 'al araby',
    }, 'News'),
    # True Crime & Mystery
    ({
        'crime', 'mystery', 'court tv', 'cold case', 'first 48', 'cops',
        'jail', 'law & crime', 'forensic files', 'dateline', 'live pd',
        'to catch a', 'american crimes', 'trublu', 'total crime',
        'unsolved', 'i (almost)', 'living with evil', 'dr. g:',
        'chaos on cam', 'untold stories of the er',
        'murder she wrote', 'mysteria', 'mysterious', 'caught in providence',
        'confess by nosey', 'paternity court', 'ghost hunter',
        '48 hours', '20/20',
        'murder', 'killer', 'chasing criminal', 'bounty hunter',
    }, 'True Crime'),
    # Horror
    ({
        'horror', 'scary', 'screambox', 'haunt', 'fear zone', 'dark fears',
        'cine de horror', 'scares by shudder', 'universal monsters',
        'z nation', 'unxplained', 'ghosts are real', 'survive or die',
    }, 'Horror'),
    # Sci-Fi
    ({
        'sci-fi', 'star trek', 'stargate', 'outersphere', 'space & beyond',
        'alien nation', 'sci fi', 'doctor who', 'pluto tv fantastic',
    }, 'Sci-Fi'),
    # Anime
    ({
        'anime', 'crunchyroll', 'retrocrush', 'retro crush', 'yu-gi-oh',
        'hidive',
    }, 'Anime'),
    # Food & Cooking
    ({
        'food network', 'tastemade', 'cooking', 'kitchen', 'chef',
        'emeril', 'jamie oliver', 'bon appetit', 'pbs food',
        "america's test kitchen", 'bobby flay', 'martha stewart',
        'great british baking', 'bbc food', 'delicious eats',
        'gusto', 'foodxp',
    }, 'Food'),
    # Nature & Wildlife
    ({
        'nature', 'wildlife', 'wildearth', 'love nature', 'jack hanna',
        'naturaleza', 'national geographic', 'wicked tuna', 'life below zero',
        'dog whisperer', 'incredible dr. pol', 'paws & claws',
        'magellan', 'curiosity', 'earthday', 'love the planet',
        'bbc earth', 'real disaster', 'pet collective',
        'earth touch', 'wild ocean', 'terra mater',
    }, 'Nature'),
    # Home & DIY
    ({
        'this old house', 'home & diy', 'home crashers', 'homeful',
        'chip & jo', 'gardening', 'tiny house', 'home improvement',
        'powernation', 'inside outside', 'at home with', 'rustic retreat',
        'home.made', 'ultimate builds', 'bbc home & garden', 'repair shop',
    }, 'Home & DIY'),
    # Reality TV
    ({
        'real housewives', 'bravo vault', 'bridezillas', 'braxton family',
        'dance moms', 'jersey shore', 'love & hip hop', 'love after lockup',
        'million dollar listing', 'project runway', 'say yes to the dress',
        'storage wars', 'teen mom', 'bad girls club', 'growing up hip hop',
        'all reality', 'reality rocks', 'pawn stars', 'duck dynasty',
        'survivor', 'the challenge', 'shark tank', 'deal or no deal',
        'supermarket sweep', 'supernanny', 'the masked singer',
        'extreme makeover', 'extreme jobs', 'bachelor nation',
        "dallas cowboys cheerleader", 'world of love island',
        'matched married', 'ax men', 'ice road trucker', 'dog the bounty',
        'the amazing race', 'e! keeping up', 'cheaters',
        'divorce court', 'judge nosey', 'the judge judy channel',
        'judge judy', 'dr. phil', 'the doctors',
        'caso cerrado', 'ellen channel', 'nosey',
    }, 'Reality TV'),
    # Game Shows
    ({
        'game show', 'price is right', 'family feud', 'buzzr',
        "let's make a deal", 'who wants to be a millionaire',
        'celebrity name game',
    }, 'Game Shows'),
    # Comedy
    ({
        'comedy', 'laugh', 'lol network', 'just for laughs', 'sitcom',
        'snl vault', 'portlandia', 'get comedy', 'laff',
        'funniest home video', 'mst3k', 'failarmy', "wild 'n out",
        'national lampoon', 'pink panther', 'johnny carson',
        'carol burnett', 'anger management',
        'cheers + frasier', 'cougar town', 'according to jim',
        'are we there yet', 'saved by the bell', 'my wife and kids',
        'the conners', 'bernie mac', 'dick van dyke', 'life with derek',
        'blossom', 'seinfeld', 'the goldbergs', 'leave it to beaver',
        'ed sullivan', 'the red green channel',
        'funny', 'gags', 'always funny', 'comedy central',
    }, 'Comedy'),
    # Kids & Family
    ({
        'kids', 'family', 'children',
        'dino', 'animation+', 'animation +',
        'junior', 'jr.', 'cartoon', 'barney', 'dinos 24',
        'my little pony', 'strawberry shortcake', 'power rangers',
        'kartoon', 'pocket.watch', 'baby', 'toons',
    }, 'Kids'),
    # Drama & Soaps
    ({
        'drama', 'primetime soaps', 'lifetime love', 'lifetime movie',
        'hallmark', 'tv land drama', 'tv amor', 'kanal d drama',
        'novela', 'supernatural drama', 'general hospital',
        'law & order', 'nypd blue', 'csi', 'the practice',
        'the walking dead', 'silent witness', 'midsomer', 'felicity',
        'degrassi', 'baywatch', 'beverly hills 90210', 'xena',
        'nash bridges', 'bull ', 'heartland classic', 'acorn tv',
        'britbox', 'sundance now',
        'cw forever', 'cw gold', 'allblk', 'alfred hitchcock',
        'tyler perry', 'in the heat of the night', 'tribeca',
        'shout factory',
    }, 'Drama'),
    # Movies
    ({
        'movies', 'movie', 'cinema', 'film', 'cinevault', 'miramax',
        'mgm', 'filmrise', 'samuel goldwyn', 'gravitas', 'asylum',
        'lionsgate', 'paramount movie', 'universal action', 'universal crime',
        'universal westerns', 'xumo free', 'just movies', 'cine',
        'filmex', 'great american rom', 'my time movie', 'cinépolis',
        'maverick black cinema', 'pam grier',
        'amc+', 'kino lorber', 'blackpix', 'shades of black',
        'cinemax', 'mgm+', 'mgm plus', 'ifc', 'sundance channel',
    }, 'Movies'),
    # Westerns
    ({
        'western', 'gunsmoke', 'wild west', 'lone ranger', 'virginian',
        'classic movie western',
    }, 'Westerns'),
    # Faith & Inspiration
    ({
        'dove channel', 'osteen', 'up faith', 'aspire', 'highway to heaven',
        'little house',
        'holiday', 'christmas', 'lifestyle',
        'tbn', 'quran', 'bhajan', 'dharm', 'faith & family', 'christian',
        'padre pio', 'noursat', 'aastha',
    }, 'Faith'),
    # Travel & Adventure
    ({
        'travel', 'adventure', 'exploration', 'xplore', 'places & spaces',
        'no reservations', 'bizarre foods', 'highway thru hell',
        'locked up abroad',
        'voyage', 'travelxp', 'go traveler', 'tv5monde voyage',
    }, 'Travel'),
    # History — checked before Science so "history" keyword routes correctly
    ({
        'history', 'smithsonian', 'ancient aliens', 'modern marvels',
        'military heroes', 'history & warfare', 'combat war',
        'antiques roadshow', 'american pickers',
    }, 'History'),
    # Documentary
    ({
        'docu', 'docurama', 'magellan tv', 'pbs genealogy',
        'documentary', 'curiosity stream', 'nhk', 'get factual', 'pbs',
    }, 'Documentary'),
    # Science
    ({
        'science', 'mythbusters', 'science is amazing', 'science quest',
        'modern innovations', 'classic car auction',
    }, 'Science'),
    # Gaming & Esports
    ({
        'gaming', 'esports', 'league of legends', 'fgteev', 'unspeakable',
        'mrbeast', 'mythical', 'team liquid',
    }, 'Gaming'),
    # Automotive
    ({
        'top gear', 'torque tv', 'mecum', 'discovery turbo',
        'in the garage', 'car chase', 'motortrend', 'velocity',
        'roadkill channel', 'hot rod',
    }, 'Automotive'),
    # Outdoors
    ({
        'outdoor', 'waypoint tv', 'wired2fish', 'xtreme outdoor',
    }, 'Outdoors'),
    # Latino — name-based fallback for channels without a language tag
    ({
        'flixlatino', 'vix ', 'vix+', 'canela.tv', 'canela tv',
        'venevisión', 'novelísima', 'novelisima',
        'remezcla', 'en español', 'atresplayer', 'pitufo',
        'mi raza', 'sobreviví', 'sobrevivi', 'c4 en alerta',
        'telemundo acción', 'telemundo accion', 'telemundo puerto',
        'emoción atres', 'emocion atres', 'única tv', 'unica tv',
        'cine exclusivo', 'azteca', 'univision', 'canal estrellas',
        'imagen tv', 'tvnotas', 'bandamax', 'ritmoson',
        # Estrella TV (Liberman Broadcasting) local affiliates, e.g.
        # "Estrella (KVPA)" — confirmed live 2026-09-17 via its own EPG (all
        # Spanish-language telenovelas/variety/news; "Noticiero Estrella TV").
        # Distinct from 'canal estrellas' above (TV Azteca's unrelated network).
        'estrella',
    }, 'Latino'),
    # Shopping
    ({
        'qvc', 'hsn', 'jewelry television', 'deal zone', 'shopping',
        'amazon live',
    }, 'Shopping'),
]

# Spanish-language markers matched against accent-folded name/category/tags
# (ported from FastChannels scrapers/base.py).
_SPANISH_LANGUAGE_MARKERS = (
    'en espanol',
    'espanol',
    'español',
    'spanish',
    'latino',
    'latina',
    'latinos',
    'latinas',
    'noticias',
    'deportes',
    'novelas',
    'telenovela',
    'telemundo',
    'univision',
    'canela',
    'estrella',
    'azteca',
    'nuevo latino',
    'siempre latino',
    # Spanish-language channel names / phrases
    'cine de',       # "Cine de Horror", "Cine de Accion"
    'todo cine',     # "Todo Cine"
    'lamusica',      # "LaMúsica TV" (accent stripped by fold)
    'tv amor',       # "TV Amor"
    'multimedios',   # Mexican broadcast network
    'bandamax',      # Mexican music channel
    'ritmoson',      # Latin music channel
    'tele hit',      # Mexican pop music channel
    # Spanish channel names / title words
    'cuando',        # "Cuando Los Angeles Caen"
    'unica',         # "ÚNICA TV" (accent stripped)
    'vas o no',      # "Vas O No Vas USA"
    'en alerta',     # "C4 en Alerta"
    'apostaria',     # "Apostarías por Mí" (accent stripped)
    'naturaleza',    # "Naturaleza Salvaje"
    'atresplayer',   # AtresmediaPlayer (Spanish broadcaster)
    'el rey',        # El Rey Network (Robert Rodriguez's Spanish channel)
    'pitufo',        # "Pitufo TV" (Los Pitufos = The Smurfs, Spanish)
    'vix',           # ViX / Vix+ (Univision/Televisa FAST service)
    'caracol',       # Caracol TV (Colombian network)
    'tudn',          # Telemundo/Univision Deportes Network
    'exitos',        # "Éxitos del Momento" (accent stripped by fold)
    'parejas',       # "Grandes Parejas" (Spanish for couples)
    'ahora',         # "Aqui y Ahora" (Spanish for now)
    'lo mejor de',   # "Lo Mejor de Liga" (Spanish for the best of)
    'desimpedidos',  # Brazilian Portuguese football channel
    # Additional Spanish words / brand names found during language audit
    'accion',        # fold of acción — "FreeTV Acción", "FILMEX Acción"
    'cinepolis',     # Cinépolis (Mexican cinema chain)
    'crimen',        # Spanish for crime — "Crimen", "Todo Crimen"
    'filmex',        # FILMEX Spanish-language movie service
    'lucha',         # Lucha Libre — "Lucha Plus", "Lucha Libre AAA"
    'saborear',      # "Saborear TV" (Mexican food/lifestyle)
    'sangre',        # Spanish for blood — "Runtime Sangre Fría"
    'sureno',        # fold of sureño — "FreeTV Sureño"
    # Common unambiguous Spanish words
    'miedo',         # Spanish for fear — "Mi Miedo Canal"
    'pelicula',      # fold of película — Spanish for movie
    'corazon',       # fold of corazón — Spanish for heart
    'tvoai',         # TVOAI Channel (Spanish-language Roku brand)
    'astro ciencia', # multi-word to avoid substring collisions on the common word "ciencia"
)

log = logging.getLogger("roku")


# ── Session ───────────────────────────────────────────────────────────────────

def make_session(workers: int = DEFAULT_WORKERS) -> requests.Session:
    s = requests.Session()
    s.headers.update({"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"})
    # No read retries: content-proxy timeouts don't recover on retry, they just burn time.
    retry = Retry(total=3, connect=3, read=0, status=2, backoff_factor=1.0,
                  status_forcelist=(429, 500, 502, 503, 504),
                  allowed_methods=None, raise_on_status=False)
    s.mount("https://", HTTPAdapter(max_retries=retry, pool_connections=1,
                                    pool_maxsize=max(workers, 4)))
    return s


class RateLimiter:
    """Shared across workers; spaces requests by 1/rate seconds."""

    def __init__(self, rate: float):
        self.interval = 1.0 / rate if rate > 0 else 0.0
        self.next_at = 0.0
        self.lock = threading.Lock()

    def wait(self) -> None:
        if not self.interval:
            return
        with self.lock:
            now = time.monotonic()
            at = max(now, self.next_at)
            self.next_at = at + self.interval
        if at > now:
            time.sleep(at - now)


class Gate:
    """Run-wide circuit breaker: once Roku starts refusing, stop sending requests."""

    def __init__(self, limit: int = BLOCK_LIMIT):
        self.limit = limit
        self.bad_run = 0
        self.lock = threading.Lock()
        self.blocked = threading.Event()

    def ok(self) -> None:
        with self.lock:
            self.bad_run = 0

    def bad(self, what: str) -> None:
        with self.lock:
            self.bad_run += 1
            n = self.bad_run
        if n >= self.limit:
            self.trip(f"{n} consecutive 401/403 responses, last from {what}")

    def trip(self, why: str) -> None:
        if not self.blocked.is_set():
            log.warning("Roku is blocking requests (%s); stopping further requests this run", why)
            self.blocked.set()


class Roku:
    """Holds the browser-style session (cookies + csrf) and makes authenticated API calls."""

    def __init__(self, workers: int = DEFAULT_WORKERS):
        self.workers = workers
        self.s = make_session(workers)
        self.csrf = ""
        self.gen = 0
        self.lock = threading.Lock()
        self.tl = threading.local()

    @staticmethod
    def _home_headers() -> dict:
        return {
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
            "Cache-Control": "max-age=0",
            "Pragma": "no-cache",
            "Referer": HOME,
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "same-origin",
            "Sec-Fetch-User": "?1",
            "Upgrade-Insecure-Requests": "1",
        }

    def api_headers(self) -> dict:
        return {
            "csrf-token":                         self.csrf,
            "origin":                             BASE,
            "referer":                            HOME,
            "content-type":                       "application/json",
            "x-roku-reserved-amoeba-ids":         "",
            "x-roku-reserved-experiment-configs": "e30=",
            "x-roku-reserved-experiment-state":   "W10=",
            "x-roku-reserved-lat":                "0",
        }

    def bootstrap(self) -> bool:
        """Home page for anonymous cookies, then the csrf token."""
        try:
            self.s.cookies.clear()
            self.csrf = ""
            # /live-tv is intermittently blocked by CloudFront; the root page yields the
            # same anonymous cookies.
            for attempt in range(HOME_403_RETRIES + 1):
                r = self.s.get(HOME, headers=self._home_headers(), timeout=15)
                if r.status_code == 200:
                    break
                if r.status_code == 403 and attempt < HOME_403_RETRIES:
                    log.warning("home bootstrap 403 (cf_pop=%s), retrying on a fresh connection",
                                r.headers.get("x-amz-cf-pop"))
                    self.s.close()
                    time.sleep(2 ** attempt)
                    continue
                log.error("home bootstrap returned %d", r.status_code)
                return False

            csrf = None
            for attempt in range(CSRF_ATTEMPTS):
                r2 = self.s.get(CSRF_URL, timeout=10)
                if r2.status_code == 200:
                    csrf = r2.json().get("csrf")
                    break
                wait = 2 ** attempt
                log.warning("csrf attempt %d returned %d, retry in %ds", attempt + 1, r2.status_code, wait)
                time.sleep(wait)
            if not csrf:
                log.error("could not obtain csrf token")
                return False
            self.csrf = csrf
            self.gen += 1
            log.debug("session ready, csrf=%s...", csrf[:12])
            return True
        except Exception as exc:
            log.error("session bootstrap failed: %s", exc)
            return False

    def refresh(self, seen_gen: int) -> bool:
        """Re-bootstrap once even if several workers hit a 401 at the same time."""
        with self.lock:
            if self.gen != seen_gen:
                return True
            return self.bootstrap()

    def worker_session(self) -> requests.Session:
        sess = getattr(self.tl, "session", None)
        if sess is None:
            sess = make_session(self.workers)
            self.tl.session = sess
        sess.cookies.update(self.s.cookies.get_dict())
        return sess

    def call(self, method: str, url: str, *, json_body=None, params=None, timeout: int = 10):
        """Authenticated request; refreshes the session and retries once on 401."""
        for attempt in range(2):
            gen = self.gen
            sess = self.worker_session()
            r = sess.request(method, url, headers=self.api_headers(), json=json_body,
                             params=params, timeout=timeout)
            if r.status_code == 401 and attempt == 0:
                log.warning("401 from %s, refreshing session", urlparse(url).path)
                if self.refresh(gen):
                    continue
            return r
        return r  # pragma: no cover


# ── Cache ─────────────────────────────────────────────────────────────────────
# {"v": 1,
#  "play":  {station_id: {"p": playId, "s": selector_url, "t": epoch}},
#  "empty": {station_id: epoch}}      # stations Roku returned no schedule for

def load_cache(path: str) -> dict:
    cache = {"v": CACHE_VERSION, "play": {}, "empty": {}}
    try:
        with open(path, encoding="utf-8") as f:
            raw = json.load(f)
    except FileNotFoundError:
        return cache
    except Exception as exc:
        log.warning("could not read cache %s: %s", path, exc)
        return cache
    if isinstance(raw, dict) and raw.get("v") == CACHE_VERSION:
        for key in ("play", "empty"):
            if isinstance(raw.get(key), dict):
                cache[key] = raw[key]
    return cache


def save_cache(path: str, cache: dict, live_ids: set, ttl: float) -> None:
    now = time.time()
    out = {
        "v": CACHE_VERSION,
        "play": {sid: e for sid, e in cache["play"].items()
                 if sid in live_ids and isinstance(e, dict) and now - e.get("t", 0) < ttl},
        "empty": {sid: t for sid, t in cache["empty"].items()
                  if sid in live_ids and isinstance(t, (int, float)) and now - t < ttl},
    }
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(out, f, separators=(",", ":"), sort_keys=True)
        log.info("wrote %s (%d playIds, %d empty guides)", path, len(out["play"]), len(out["empty"]))
    except Exception as exc:
        log.warning("could not write cache %s: %s", path, exc)


# ── Gracenote ─────────────────────────────────────────────────────────────────

def normalize_gracenote_id(value) -> str:
    raw = str(value or "").strip()
    if not raw:
        return ""
    if raw.isdigit():
        return raw if len(raw) >= 5 else ""
    if GRACENOTE_ID_RE.match(raw):
        return raw[:2].upper() + raw[2:]
    return ""


def load_gracenote_map(path: str) -> dict[str, str]:
    out: dict[str, str] = {}
    try:
        with open(path, encoding="utf-8", newline="") as f:
            for row in csv.DictReader(f):
                tms = normalize_gracenote_id(row.get("tmsid"))
                if tms and row.get("key"):
                    out[row["key"].strip()] = tms
    except FileNotFoundError:
        log.info("no Gracenote map at %s; only ids Roku supplies are used", path)
    except Exception as exc:
        log.warning("could not read Gracenote map %s: %s", path, exc)
    return out


def _fetch_csv_rows(url: str, header_word: str) -> list[dict] | None:
    """Download a CSV and return its rows, or None if it fails or doesn't look right."""
    try:
        r = requests.get(url, timeout=30, headers={"User-Agent": UA})
        r.raise_for_status()
        text = r.text.lstrip("\ufeff")
    except Exception as exc:
        log.warning("Gracenote download failed (%s): %s", url, exc)
        return None
    lines = text.strip().splitlines()
    if not lines or header_word not in lines[0].lower():
        log.warning("Gracenote download from %s doesn't look like the expected CSV", url)
        return None
    return list(csv.DictReader(lines))


def update_gracenote_map(path: str, map_url: str, exclusions_url: str) -> bool:
    """Merge the community Roku rows into the local CSV. Returns True if the file changed."""
    remote = _fetch_csv_rows(map_url, "provider")
    excl_rows = _fetch_csv_rows(exclusions_url, "tmsid")
    if remote is None or excl_rows is None:
        log.warning("Gracenote update skipped; keeping %s as is", path)
        return False
    excluded = {normalize_gracenote_id(r.get("tmsid")) for r in excl_rows} - {""}

    local: dict[str, dict] = {}
    try:
        with open(path, encoding="utf-8", newline="") as f:
            for row in csv.DictReader(f):
                if row.get("key"):
                    local[row["key"].strip()] = {"tmsid": normalize_gracenote_id(row.get("tmsid")),
                                                 "notes": (row.get("notes") or "").strip()}
    except FileNotFoundError:
        pass
    except Exception as exc:
        log.warning("could not read %s (%s); Gracenote update skipped", path, exc)
        return False

    incoming: dict[str, dict] = {}
    for row in remote:
        if (row.get("provider") or "").strip().lower() != "roku":
            continue
        key, tms = (row.get("key") or "").strip(), normalize_gracenote_id(row.get("tmsid"))
        if key and tms:
            incoming[key] = {"tmsid": tms, "notes": (row.get("notes") or "").strip()}
    if not incoming or (local and len(incoming) < len(local) / 2):
        log.warning("Gracenote download has %d Roku rows vs %d local; update skipped",
                    len(incoming), len(local))
        return False

    merged = {**local, **incoming}
    merged = {k: v for k, v in merged.items() if v["tmsid"] and v["tmsid"] not in excluded}
    added = len(merged.keys() - local.keys())
    changed = sum(1 for k, v in merged.items() if k in local and local[k]["tmsid"] != v["tmsid"])
    removed = len(local.keys() - merged.keys())
    if merged == local:
        log.info("Gracenote map up to date (%d Roku rows)", len(local))
        return False

    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["key", "tmsid", "notes"])
        for key in sorted(merged):
            w.writerow([key, merged[key]["tmsid"], merged[key]["notes"]])
    os.replace(tmp, path)
    log.info("Gracenote map updated: %d rows (%d added, %d changed, %d removed)",
             len(merged), added, changed, removed)
    return True


# ── Channels ──────────────────────────────────────────────────────────────────

def fold(value: str | None) -> str:
    if not value:
        return ""
    normalized = unicodedata.normalize("NFKD", value)
    return "".join(ch for ch in normalized if not unicodedata.combining(ch)).casefold()


def infer_language(*values: str | None, default: str = "en") -> str:
    for value in values:
        folded = fold(value)
        if any(marker in folded for marker in _SPANISH_LANGUAGE_MARKERS):
            return "es"
    return default


def infer_category_from_name(title: str) -> str | None:
    tl = (title or "").lower()
    for keywords, label in _NAME_CATEGORY_RULES:
        if any(kw in tl for kw in keywords):
            return label
    return None


def category_from_station(station: dict) -> str:
    if station.get("kidsDirected"):
        return "Kids"
    tags = set(station.get("tags") or [])
    for tag, label in TAG_CATEGORY_PRIORITY:
        if tag in tags:
            return label
    for tag in tags:
        tl = tag.lower()
        if "reality" in tl or "wedding" in tl:
            return "Reality TV"
        if "thriller" in tl or "movie" in tl or "film" in tl or "ifc" in tl:
            return "Movies"
        if "comedy" in tl:
            return "Comedy"
        if "drama" in tl or "stories" in tl:
            return "Drama"
    return infer_category_from_name(station.get("title") or "") or "Live TV"


def extract_selector_url(view_opts: list | None) -> str | None:
    media = (view_opts[0].get("media") or {}) if view_opts else {}
    for video in media.get("videos") or []:
        if (isinstance(video, dict) and str(video.get("videoType", "")).upper() == "HLS"
                and video.get("url")):
            return video["url"]
    return None


def first_image_path(image_map: dict, keys: tuple) -> str | None:
    for key in keys:
        img = image_map.get(key)
        if img and img.get("path"):
            return img["path"]
    return None


def channel_from_station(sid: str, station: dict) -> dict:
    view_opts = station.get("viewOptions") or []
    tags = station.get("tags") or []
    title = (station.get("title") or station.get("shortName") or "Unknown").strip()
    category = category_from_station(station)
    return {
        "id":       sid,
        "name":     title,
        "number":   station.get("displayNumber"),
        "logo":     first_image_path(station.get("imageMap") or {},
                                     ("gridEpg", "epgLogo", "liveHudLogo", "epgLogoDark")),
        "category": category,
        "language": infer_language(title, category, " ".join(tags)),
        "gracenote": station.get("gracenoteStationId") or station.get("stationId") or "",
        "play_id":  view_opts[0].get("playId") if view_opts else None,
        "selector": extract_selector_url(view_opts),
    }


def channel_from_content(sid: str, item: dict) -> dict:
    view_opts = item.get("viewOptions") or [{}]
    cats = item.get("categories") or []
    title = (item.get("title") or "Unknown").strip()
    category = (CAT_ID_MAP.get(cats[0], "Live TV") if cats
                else (infer_category_from_name(title) or "Live TV"))
    return {
        "id":       sid,
        "name":     title,
        "number":   None,
        "logo":     first_image_path(item.get("imageMap") or {},
                                     ("grid", "gridEpg", "detailBackground", "detailPoster")),
        "category": category,
        "language": infer_language(title, category),
        "gracenote": item.get("gracenoteStationId") or item.get("stationId") or "",
        "play_id":  view_opts[0].get("playId") if view_opts else None,
        "selector": extract_selector_url(view_opts),
    }


def fetch_channels(api: Roku) -> list[dict]:
    channels: list[dict] = []
    seen: set[str] = set()

    # Phase 1: /api/v2/epg lists every live channel under features.station
    try:
        r = api.call("GET", EPG_URL, timeout=20)
        if r.status_code == 200:
            for col in r.json().get("collections", []):
                station = (col.get("features") or {}).get("station")
                if not station:
                    continue
                sid = (station.get("meta") or {}).get("id")
                if not sid or sid in seen:
                    continue
                seen.add(sid)
                channels.append(channel_from_station(sid, station))
        else:
            log.warning("channel list returned %d", r.status_code)
    except Exception as exc:
        log.warning("channel list failed: %s", exc)

    # Phase 2: billboard (hero channels) fills any gaps
    try:
        r2 = api.call("GET", BILLBOARD_URL, timeout=10)
        if r2.status_code == 200:
            for item in r2.json():
                sid = (item.get("meta") or {}).get("id")
                if not sid or sid in seen:
                    continue
                seen.add(sid)
                channels.append(channel_from_content(sid, item))
        else:
            log.debug("billboard returned %d", r2.status_code)
    except Exception as exc:
        log.warning("billboard failed: %s", exc)

    return channels


# ── Stream URLs ───────────────────────────────────────────────────────────────

def media_format(play_id: str) -> str:
    """The playId's payload says whether Roku wants DASH or HLS for the channel."""
    try:
        payload = play_id.split(".", 1)[1].replace("-", "+").replace("_", "/")
        payload += "=" * (-len(payload) % 4)
        decoded = base64.b64decode(payload).decode(errors="ignore")
        return "mpeg-dash" if "dash" in decoded.lower() else "m3u"
    except Exception:
        return "m3u"


def synthetic_osm_url(selector_url: str, session_token: str, trace_id: str) -> str | None:
    m = SELECTOR_UUID_RE.search(urlparse(selector_url).path)
    if not m:
        return None
    url = f"{OSM_BASE}/osm/v1/hls/master/{m.group(1)}/{session_token}/index.m3u8"
    return f"{url}?traceId={trace_id}" if trace_id else url


def osm_session_from_url(stream_url: str) -> tuple[str, str] | None:
    m = OSM_STREAM_RE.search(stream_url)
    if not m:
        return None
    trace = (parse_qs(urlparse(stream_url).query).get("traceId") or [""])[0]
    return m.group(2), trace


def playback_body(sid: str, play_id: str, session_id: str, fmt: str) -> dict:
    return {
        "rokuId":      sid,
        "playId":      play_id,
        "mediaFormat": fmt,
        "drmType":     "widevine",
        "quality":     "fhd",
        "bifUrl":      None,
        "adPolicyId":  "",
        "providerId":  "rokuavod",
        "playbackContextParams": (
            f"sessionId={session_id}"
            "&pageId=trc-us-live-ml-page-en-current"
            "&isNewSession=0&idType=roku-trc"
        ),
    }


def resolve_streams(api: Roku, channels: list[dict], workers: int, rate: float,
                    include_dash: bool, cache: dict, ttl: float, max_lookups: int,
                    gate: Gate) -> list[dict]:
    """Fill ch['stream_url'] for each channel; return the channels that resolved."""
    limiter = RateLimiter(rate)
    lock = threading.Lock()
    state = {"osm": None, "lookups": 0}
    stats: Counter = Counter()
    session_id = api.s.cookies.get("_usn", "roku-scraper")
    start = time.time()

    def cached(sid: str) -> tuple[str | None, str | None]:
        e = cache["play"].get(sid)
        if isinstance(e, dict) and e.get("p") and start - e.get("t", 0) < ttl:
            return e["p"], e.get("s")
        return None, None

    def lookup(sid: str) -> tuple[str | None, str | None, str]:
        """Content-proxy lookup of a channel's playId; stores it in the cache."""
        limiter.wait()
        content_url = CONTENT_TPL.format(sid=sid) + "?featureInclude=linearSchedule"
        r = api.call("GET", PROXY_BASE + quote(content_url, safe=""), timeout=10)
        if r.status_code == 200:
            gate.ok()
            view_opts = r.json().get("viewOptions") or [{}]
            play_id = view_opts[0].get("playId") if view_opts else None
            selector = extract_selector_url(view_opts)
            if not play_id:
                return None, None, "no_play_id"
            with lock:
                cache["play"][sid] = {"p": play_id, "s": selector, "t": time.time()}
            return play_id, selector, "ok"
        if r.status_code in (401, 403):
            gate.bad("content lookup")
        return None, None, f"lookup_{r.status_code}"

    def playback(sid: str, play_id: str) -> tuple[int, str, str]:
        fmt = media_format(play_id)
        limiter.wait()
        r = api.call("POST", PLAYBACK, json_body=playback_body(sid, play_id, session_id, fmt))
        code = r.status_code
        if code in (401, 403):
            gate.bad("playback")
        elif code in (451, 452):
            gate.trip(f"HTTP {code}: Roku is geo-blocking this IP")
        elif code == 200:
            gate.ok()
        url = ""
        if code == 200:
            try:
                url = r.json().get("url", "") or ""
            except ValueError:
                url = ""
        return code, url, fmt

    def one(ch: dict) -> tuple[dict, str | None, str]:
        sid = ch["id"]
        if gate.blocked.is_set():
            return ch, None, "skipped"
        try:
            play_id, selector = ch.get("play_id"), ch.get("selector")
            used_cache = False
            if not play_id:
                play_id, sel = cached(sid)
                if play_id:
                    selector = selector or sel
                    used_cache = True
            if not play_id:
                with lock:
                    if max_lookups > 0 and state["lookups"] >= max_lookups:
                        return ch, None, "deferred"
                    state["lookups"] += 1
                play_id, sel, status = lookup(sid)
                if not play_id:
                    return ch, None, status
                selector = selector or sel

            code, url, fmt = playback(sid, play_id)
            if code in (401, 404) and used_cache and not gate.blocked.is_set():
                # stale cached playId: drop it and look the channel up again
                with lock:
                    cache["play"].pop(sid, None)
                play_id, sel, status = lookup(sid)
                if not play_id:
                    return ch, None, status
                selector = sel or selector
                code, url, fmt = playback(sid, play_id)
        except Exception as exc:
            log.debug("playback error for %s: %s", sid, exc)
            return ch, None, "error"

        ch["play_id"], ch["selector"] = play_id, selector
        if code != 200:
            return ch, None, f"http_{code}"
        if not url:
            return ch, None, "no_url"
        if fmt != "m3u" or ".m3u8" not in urlparse(url).path:
            if not include_dash:
                return ch, None, "dash"
        else:
            sess = osm_session_from_url(url)
            if sess:
                with lock:
                    state["osm"] = sess
        return ch, url, "ok"

    resolved: list[dict] = []
    failed_5xx: list[dict] = []
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for fut in as_completed([pool.submit(one, ch) for ch in channels]):
            ch, url, status = fut.result()
            stats[status] += 1
            if url:
                ch["stream_url"] = url
                resolved.append(ch)
            elif status in ("http_502", "http_503", "http_504") and ch.get("selector"):
                failed_5xx.append(ch)

    # Playback 5xx: build the URL from the selector UUID and a session token that worked.
    if failed_5xx and state["osm"]:
        token, trace = state["osm"]
        for ch in failed_5xx:
            if media_format(ch.get("play_id") or "") != "m3u":
                continue
            url = synthetic_osm_url(ch["selector"], token, trace)
            if url:
                ch["stream_url"] = url
                resolved.append(ch)
                stats["synthetic"] += 1

    log.info("streams: %d/%d resolved, %d new lookups (%s)", len(resolved), len(channels),
             state["lookups"], ", ".join(f"{k}={v}" for k, v in sorted(stats.items())))
    if stats.get("deferred"):
        log.info("%d channels deferred to later runs (--max-lookups %d)", stats["deferred"], max_lookups)
    return resolved


# ── M3U ───────────────────────────────────────────────────────────────────────

def q(v: str) -> str:
    return str(v).replace('"', "'")


def write_m3u(channels: list[dict], path: str, epg_path: str | None) -> None:
    def sort_key(ch):
        num = str(ch.get("number") or "")
        return (int(num) if num.isdigit() else 999999, ch["name"].lower())

    header = "#EXTM3U"
    if epg_path:
        header += f' url-tvg="{epg_path}"'
    lines = [header]
    for ch in sorted(channels, key=sort_key):
        attrs = [f'tvg-id="roku.{ch["id"]}"', f'tvg-name="{q(ch["name"])}"']
        if ch.get("logo"):
            attrs.append(f'tvg-logo="{ch["logo"]}"')
        if str(ch.get("number") or "").isdigit():
            attrs.append(f'tvg-chno="{ch["number"]}"')
        attrs.append(f'tvg-language="{ch.get("language") or "en"}"')
        if ch.get("gracenote"):
            attrs.append(f'tvc-guide-stationid="{ch["gracenote"]}"')
        attrs.append(f'group-title="{q(ch["category"])}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch["name"].replace(",", ";")}')
        lines.append(ch["stream_url"])
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    log.info("wrote %s (%d channels)", path, len(channels))


# ── EPG ───────────────────────────────────────────────────────────────────────

class EPGRateLimited(Exception):
    def __init__(self, status: int):
        self.status = status
        super().__init__(f"dated EPG returned HTTP {status}")


def parse_program(entry: dict) -> dict | None:
    try:
        start = datetime.fromtimestamp(int(entry["start"]), timezone.utc)
        end = datetime.fromtimestamp(int(entry["end"]), timezone.utc)
    except (KeyError, TypeError, ValueError, OverflowError, OSError):
        return None
    if end <= start:
        return None

    c = entry.get("content") or {}
    series_title = ((c.get("series") or {}).get("title") or "").strip()
    ep_title = (c.get("title") or "").strip()
    title = series_title or ep_title or "Unknown"

    # The dated guide wraps descriptions as {"text": ...}; other payloads use plain strings.
    descs = c.get("descriptions") or {}
    desc = None
    for size in ("250", "100", "60", "40"):
        v = descs.get(size)
        if isinstance(v, dict):
            v = v.get("text")
        if isinstance(v, str) and v.strip():
            desc = v.strip()
            break
    if not desc and isinstance(c.get("description"), str):
        desc = c["description"].strip() or None

    poster = first_image_path(c.get("imageMap") or {}, ("gridEpg", "grid"))

    ratings = c.get("parentalRatings") or []
    rating = ratings[0].get("code") if ratings and isinstance(ratings[0], dict) else None

    try:
        season = int(c["seasonNumber"]) if c.get("seasonNumber") else None
        episode = int(c["episodeNumber"]) if c.get("episodeNumber") else None
    except (ValueError, TypeError):
        season = episode = None
    if not (season and episode):
        season = episode = None

    cats: list[str] = []
    for g in c.get("genres") or []:
        g = g.strip() if isinstance(g, str) else ""
        if g:
            label = g[0].upper() + g[1:]
            if label not in cats:
                cats.append(label)

    return {
        "title":         title,
        "episode_title": ep_title if series_title and ep_title and ep_title != series_title else None,
        "desc":          desc,
        "poster":        poster,
        "categories":    cats,
        "rating":        rating,
        "season":        season,
        "episode":       episode,
        "start":         start,
        "end":           end,
    }


def null_placeholder_season_episode(progs: list[dict], min_titles: int = 3,
                                    min_repeats: int = 3) -> None:
    """Null season/episode where it looks like a source-assigned placeholder.

    Ported from FastChannels. Real per-episode numbers don't repeat across unrelated
    titles, so a (season, episode) pair shared by several distinct titles on a channel
    is a placeholder. A single title repeating one pair many times with differing
    descriptions or episode titles is the same problem under one title. Identical
    repeats (real reruns) are left alone. Pass one channel's programmes at a time.
    """
    chan = [p for p in progs
            if not any(c.casefold() in ("movie", "movies") for c in p.get("categories") or [])]
    pair_titles: dict[tuple, set] = {}
    title_pair_progs: dict[tuple, list] = {}
    for p in chan:
        if p.get("season") is not None and p.get("episode") is not None:
            pair_titles.setdefault((p["season"], p["episode"]), set()).add(p["title"])
            title_pair_progs.setdefault((p["title"], p["season"], p["episode"]), []).append(p)

    placeholder_pairs = {pair for pair, titles in pair_titles.items() if len(titles) >= min_titles}

    placeholder_title_keys = set()
    for key, grp in title_pair_progs.items():
        if len(grp) < min_repeats:
            continue
        descs = {(p.get("desc") or "").strip() for p in grp}
        descs.discard("")
        eps = {(p.get("episode_title") or "").strip() for p in grp}
        eps.discard("")
        if len(descs) >= 2 or len(eps) >= 2:
            placeholder_title_keys.add(key)

    if not placeholder_pairs and not placeholder_title_keys:
        return
    for p in chan:
        if p.get("season") is None or p.get("episode") is None:
            continue
        if ((p["season"], p["episode"]) in placeholder_pairs
                or (p["title"], p["season"], p["episode"]) in placeholder_title_keys):
            p["season"] = p["episode"] = None


def fetch_station_epg(api: Roku, sid: str, now: datetime) -> list[dict]:
    r = api.call("GET", EPG_SCHEDULE_TPL.format(sid=sid), params={
        "tpl_date": now.strftime("%Y-%m-%d"),
        "tpl_hour": now.hour,
        "include":  EPG_SCHEDULE_INCLUDE,
        "expand":   "series",
    })
    if r.status_code in (403, 429):
        raise EPGRateLimited(r.status_code)
    if r.status_code != 200:
        raise RuntimeError(f"HTTP {r.status_code}")
    out = []
    for entry in r.json().get("view") or []:
        window = (entry.get("features") or {}).get("otaOptions") or {}
        prog = parse_program({"start": window.get("start"), "end": window.get("end"),
                              "content": entry.get("content") or {}})
        if prog:
            out.append(prog)
    return out


def xmltv_time(dt: datetime) -> str:
    return dt.strftime("%Y%m%d%H%M%S +0000")


def parse_xmltv_time(s: str) -> datetime | None:
    try:
        return datetime.strptime(s, "%Y%m%d%H%M%S %z").astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None


def load_previous_epg(path: str) -> dict[str, list[dict]]:
    """Read last run's XMLTV back into {station_id: [programme dicts]}."""
    try:
        root = ET.parse(path).getroot()
    except (FileNotFoundError, ET.ParseError, OSError):
        return {}
    out: dict[str, list[dict]] = {}
    for e in root.findall("programme"):
        ch = e.get("channel") or ""
        sid = ch[len("roku."):] if ch.startswith("roku.") else ch
        start, end = parse_xmltv_time(e.get("start")), parse_xmltv_time(e.get("stop"))
        title = e.findtext("title")
        if not sid or not start or not end or not title:
            continue
        season = episode = None
        for en in e.findall("episode-num"):
            if en.get("system") == "onscreen":
                m = re.fullmatch(r"S(\d+)E(\d+)", (en.text or "").strip())
                if m:
                    season, episode = int(m.group(1)), int(m.group(2))
        icon = e.find("icon")
        out.setdefault(sid, []).append({
            "title":         title,
            "episode_title": e.findtext("sub-title"),
            "desc":          e.findtext("desc"),
            "poster":        icon.get("src") if icon is not None else None,
            "categories":    [c.text for c in e.findall("category") if c.text],
            "rating":        e.findtext("rating/value"),
            "season":        season,
            "episode":       episode,
            "start":         start,
            "end":           end,
        })
    return out


def plan_epg_requests(sids: list[str], prev: dict[str, list[dict]], now: datetime,
                      min_hours: float, cap: int, skip: set | None = None) -> list[str]:
    """Channels whose stored guide runs out within min_hours, least-covered first."""
    skip = skip or set()
    need = []
    for sid in sids:
        if sid in skip:
            continue
        ends = [p["end"] for p in prev.get(sid, []) if p["end"] > now]
        hours = (max(ends) - now).total_seconds() / 3600 if ends else -1.0
        if hours < min_hours:
            need.append((hours, sid))
    need.sort()
    ids = [sid for _, sid in need]
    return ids[:cap] if cap > 0 else ids


def fetch_epg(api: Roku, channels: list[dict], prev: dict[str, list[dict]], workers: int,
              min_hours: float, cap: int, budget: float, rate: float, gate: Gate,
              cache: dict, empty_ttl: float) -> dict[str, list[dict]]:
    """Return {station_id: programmes} for every channel: fresh where fetched, else carried over."""
    now = datetime.now(timezone.utc)
    sids = [ch["id"] for ch in channels]
    empty_recent = {sid for sid, t in cache["empty"].items()
                    if isinstance(t, (int, float)) and time.time() - t < empty_ttl}
    targets = plan_epg_requests(sids, prev, now, min_hours, cap, empty_recent)
    log.info("guide: %d/%d channels need a refresh (<%.0fh stored, %d known empty)%s",
             len(targets), len(sids), min_hours, len(empty_recent & set(sids)),
             f", capped at {cap}" if cap > 0 and len(targets) == cap else "")

    fresh: dict[str, list[dict]] = {}
    limiter = RateLimiter(rate)
    deadline = time.monotonic() + budget
    out_of_time = threading.Event()
    stats: Counter = Counter()

    def one(sid: str):
        if gate.blocked.is_set():
            return sid, None, "skipped"
        if out_of_time.is_set() or time.monotonic() > deadline:
            out_of_time.set()
            return sid, None, "skipped"
        try:
            limiter.wait()
            progs = fetch_station_epg(api, sid, now)
            gate.ok()
            return sid, progs, "ok"
        except EPGRateLimited as exc:
            gate.trip(f"guide HTTP {exc.status}")
            return sid, None, f"http_{exc.status}"
        except Exception as exc:
            log.debug("guide error for %s: %s", sid, exc)
            return sid, None, "error"

    with ThreadPoolExecutor(max_workers=workers) as pool:
        for fut in as_completed([pool.submit(one, sid) for sid in targets]):
            sid, progs, status = fut.result()
            stats[status] += 1
            if progs is not None:
                fresh[sid] = progs
                if progs:
                    cache["empty"].pop(sid, None)
                else:
                    cache["empty"][sid] = time.time()
    if stats:
        log.info("guide: %s", ", ".join(f"{k}={v}" for k, v in sorted(stats.items())))
    if gate.blocked.is_set():
        log.warning("guide stopped by Roku blocking; keeping previous data for channels not fetched")
    elif stats.get("skipped"):
        log.warning("guide budget used up; %d channels keep previous data this run", stats["skipped"])

    merged: dict[str, list[dict]] = {}
    for sid in sids:
        progs = fresh[sid] if sid in fresh else prev.get(sid, [])
        progs = [p for p in progs if p["end"] > now]
        null_placeholder_season_episode(progs)
        merged[sid] = progs
    return merged


def write_xmltv(channels: list[dict], guide: dict[str, list[dict]], path: str) -> None:
    tv = ET.Element("tv", {"generator-info-name": "roku_extract"})
    for ch in channels:
        c = ET.SubElement(tv, "channel", {"id": f"roku.{ch['id']}"})
        ET.SubElement(c, "display-name").text = ch["name"]
        if ch.get("logo"):
            ET.SubElement(c, "icon", {"src": ch["logo"]})

    count = 0
    for ch in channels:
        sid = ch["id"]
        seen = set()
        for p in sorted(guide.get(sid, []), key=lambda x: x["start"]):
            if (p["start"], p["title"]) in seen:
                continue
            seen.add((p["start"], p["title"]))
            e = ET.SubElement(tv, "programme", {
                "start":   xmltv_time(p["start"]),
                "stop":    xmltv_time(p["end"]),
                "channel": f"roku.{sid}",
            })
            ET.SubElement(e, "title", {"lang": "en"}).text = p["title"]
            if p.get("episode_title"):
                ET.SubElement(e, "sub-title", {"lang": "en"}).text = p["episode_title"]
            if p.get("desc"):
                ET.SubElement(e, "desc", {"lang": "en"}).text = p["desc"]
            for cat in p.get("categories") or []:
                ET.SubElement(e, "category", {"lang": "en"}).text = cat
            if p.get("poster"):
                ET.SubElement(e, "icon", {"src": p["poster"]})
            if p.get("season") and p.get("episode"):
                s_, ep = p["season"], p["episode"]
                ET.SubElement(e, "episode-num", {"system": "onscreen"}).text = f"S{s_:02d}E{ep:02d}"
                ET.SubElement(e, "episode-num", {"system": "xmltv_ns"}).text = f"{s_ - 1}.{ep - 1}."
            if p.get("rating"):
                r = ET.SubElement(e, "rating")
                ET.SubElement(r, "value").text = p["rating"]
            count += 1

    ET.indent(tv)
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)
    log.info("wrote %s (%d programmes, %d/%d channels with guide)", path, count,
             sum(1 for ch in channels if guide.get(ch["id"])), len(channels))


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="The Roku Channel m3u + XMLTV extractor")
    ap.add_argument("--out-dir", default=".", help="output directory (created if missing)")
    ap.add_argument("--m3u", default="roku.m3u", help="playlist filename (relative to --out-dir)")
    ap.add_argument("--epg", default="roku.xml", help="XMLTV filename (relative to --out-dir)")
    ap.add_argument("--cache", default="roku_cache.json", help="cache filename (relative to --out-dir)")
    ap.add_argument("--no-cache", action="store_true", help="ignore and don't write the cache")
    ap.add_argument("--cache-hours", type=float, default=12.0,
                    help="how long a cached playId is trusted (default 12)")
    ap.add_argument("--gracenote-map",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "roku_gracenote.csv"),
                    help="CSV of key,tmsid rows (default: roku_gracenote.csv next to this script)")
    ap.add_argument("--update-gracenote", action="store_true",
                    help="refresh --gracenote-map from the community Gist before using it")
    ap.add_argument("--gracenote-url", default=GRACENOTE_MAP_URL, help="community map CSV URL")
    ap.add_argument("--gracenote-exclusions-url", default=GRACENOTE_EXCLUSIONS_URL,
                    help="known-bad Gracenote id list URL")
    ap.add_argument("--workers", type=int, default=DEFAULT_WORKERS,
                    help="concurrent requests (default %d)" % DEFAULT_WORKERS)
    ap.add_argument("--stream-rate", type=float, default=3.0,
                    help="max playback/lookup requests/sec across all workers (default 3.0)")
    ap.add_argument("--max-lookups", type=int, default=300,
                    help="cap on uncached playId lookups per run; 0 = no cap (default 300)")
    ap.add_argument("--epg-rate", type=float, default=3.0,
                    help="max guide requests/sec across all workers (default 3.0)")
    ap.add_argument("--min-guide-hours", type=float, default=8.0,
                    help="re-fetch a channel's guide when its stored guide covers less than N hours (default 8)")
    ap.add_argument("--max-epg-requests", type=int, default=250,
                    help="cap on guide requests per run, least-covered first; 0 = no cap (default 250)")
    ap.add_argument("--epg-budget", type=float, default=600.0,
                    help="max seconds spent on guide requests (default 600)")
    ap.add_argument("--include-dash", action="store_true",
                    help="keep channels whose playback URL is DASH instead of HLS")
    ap.add_argument("--no-epg", action="store_true", help="playlist only")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S")

    os.makedirs(args.out_dir, exist_ok=True)
    m3u_path = os.path.join(args.out_dir, args.m3u)
    epg_path = os.path.join(args.out_dir, args.epg)
    cache_path = os.path.join(args.out_dir, args.cache)
    ttl = args.cache_hours * 3600

    cache = {"v": CACHE_VERSION, "play": {}, "empty": {}} if args.no_cache else load_cache(cache_path)
    gate = Gate()
    api = Roku(args.workers)
    if not api.bootstrap():
        log.error("could not establish a Roku session (403 or no data); often a regional/CDN block")
        return 1

    channels = fetch_channels(api)
    if not channels:
        log.error("no channels returned")
        return 1
    log.info("%d channels (%d playIds cached)", len(channels),
             sum(1 for ch in channels if ch["id"] in cache["play"]))
    live_ids = {ch["id"] for ch in channels}

    if args.update_gracenote:
        update_gracenote_map(args.gracenote_map, args.gracenote_url, args.gracenote_exclusions_url)
    gmap = load_gracenote_map(args.gracenote_map)
    for ch in channels:
        ch["gracenote"] = normalize_gracenote_id(ch.get("gracenote")) or gmap.get(ch["id"], "")

    channels = resolve_streams(api, channels, args.workers, args.stream_rate, args.include_dash,
                               cache, ttl, args.max_lookups, gate)
    if not args.no_cache:
        save_cache(cache_path, cache, live_ids, ttl)
    if not channels:
        log.error("no channels resolved to a stream; keeping previous output")
        return 1

    write_m3u(channels, m3u_path, None if args.no_epg else args.epg)

    if not args.no_epg:
        prev = load_previous_epg(epg_path)
        guide = fetch_epg(api, channels, prev, args.workers, args.min_guide_hours,
                          args.max_epg_requests, args.epg_budget, args.epg_rate, gate,
                          cache, ttl)
        write_xmltv(channels, guide, epg_path)
        if not args.no_cache:
            save_cache(cache_path, cache, live_ids, ttl)
    return 0


if __name__ == "__main__":
    sys.exit(main())
