#!/usr/bin/env python3
import collections
import hashlib
import io
import itertools
import json
import os
import queue
import random
import re
import shutil
import socket
import sqlite3
import ssl
import struct
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import zipfile
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from tkinter import ttk, messagebox, simpledialog, filedialog
from urllib.parse import urlparse, parse_qs, unquote_plus, quote_plus

# Optional - only used for animated GIF previews in the admin GUI (Gifs tab). Plain
# tkinter can only ever decode a single frame of a GIF, with no per-frame timing; the
# rest of this file has no dependency on PIL and works the same without it, so the
# preview just falls back to a static first-frame image when it's not installed.
try:
    from PIL import Image as _PILImage, ImageTk as _PILImageTk
    _PIL_AVAILABLE = True
except ImportError:
    _PIL_AVAILABLE = False

# ---------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------
HTTP_PORT = 4451
HTTPS_PORT = 443
DNS_PORT = 53
MIN_BUILD_VERSION = 371

TARGET_HOSTS = {
    "woeprod.traplightgames.com",
    "woeprod-1324136205.us-west-1.elb.amazonaws.com",
    "graph.facebook.com",
}
UPSTREAM_DNS = ("8.8.8.8", 53)

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# Certificate and private key combined into one PEM (concatenated, cert first) -
# ssl.SSLContext.load_cert_chain() reads the key from the same file as the cert when
# no separate keyfile is given, so this doesn't need to be two files.
CERT_FILE = os.path.join(SCRIPT_DIR, "server.pem")
DB_FILE = os.path.join(SCRIPT_DIR, "game.db")
SERVER_DATA_DIR = os.path.join(SCRIPT_DIR, "ServerData")
# Ships in the repo as this single zip instead of thousands of loose files;
# ensureServerDataExtracted() unpacks it into ServerData/ the first time the
# server runs and deletes the zip, same idea as the auto-generated Root CA.
SERVER_DATA_ZIP = os.path.join(SCRIPT_DIR, "ServerData.zip")
INITIAL_DATA_DIR = os.path.join(SERVER_DATA_DIR, "InitialData")
LEVELS_DIR = os.path.join(SERVER_DATA_DIR, "Levels")
GIFS_DIR = os.path.join(SERVER_DATA_DIR, "Gifs")

# Reimplementation of Unity's legacy pseudo-random algorithm (UnityEngine.Random,
# seeded via Random.seed = X), based on Xorshift128. Algorithm documented and
# verified against several independent, concordant implementations (C#, Rust,
# JavaScript, Lua), tested against Unity 4.7 through 2020.1 - comfortably covers our
# target (Unity 2017.3.1f1). Source: https://gist.github.com/macklinb/a00be6b616cbf20fa95e4227575fe50b
_UNITY_RAND_MASK32 = 0xFFFFFFFF
_UNITY_RAND_MT_CONST = 1812433253  # 0x6C078965


class _UnityRandomState:
    def __init__(self, seed: int):
        x = seed & _UNITY_RAND_MASK32
        y = (_UNITY_RAND_MT_CONST * x + 1) & _UNITY_RAND_MASK32
        z = (_UNITY_RAND_MT_CONST * y + 1) & _UNITY_RAND_MASK32
        w = (_UNITY_RAND_MT_CONST * z + 1) & _UNITY_RAND_MASK32
        self.x, self.y, self.z, self.w = x, y, z, w

    def next_u32(self) -> int:
        t = (self.x ^ ((self.x << 11) & _UNITY_RAND_MASK32)) & _UNITY_RAND_MASK32
        self.x, self.y, self.z = self.y, self.z, self.w
        self.w = (self.w ^ (self.w >> 19) ^ t ^ (t >> 8)) & _UNITY_RAND_MASK32
        return self.w

    def range_int(self, min_val: int, max_val: int) -> int:
        """Equivalent of UnityEngine.Random.Range(int min, int max): min inclusive,
        max EXCLUSIVE."""
        if max_val == min_val:
            return min_val
        r = self.next_u32()
        if max_val < min_val:
            return min_val - (r % (min_val - max_val))
        return min_val + (r % (max_val - min_val))


def gpw(s: str, seed: int = 97139634) -> str:
    """Exactly reproduces the game's ClientTools.gpw(): shuffles the characters of s
    with a Fisher-Yates shuffle using UnityEngine.Random, seeded with the fixed
    value 97139634."""
    state = _UnityRandomState(seed)
    arr = list(s)
    i = len(arr)
    while i > 1:
        num = state.range_int(0, i)
        arr[num], arr[i - 1] = arr[i - 1], arr[num]
        i -= 1
    return "".join(arr)


HPW = "bfid3Z53SFib325PJGFasae"

DEFAULT_TOURNAMENT_SHARES = [
    10000, 5000, 2500, 1000, 900, 810, 729, 656, 590, 531,
    478, 430, 387, 348, 313, 282, 254, 229, 206, 185,
    167, 150, 135, 122, 110
]

PLANET_IDS = [
    "AdventureOffroadCar",
    "AdventureMotorcycle",
    "RacingOffroadCar",
    "RacingMotorcycle",
    "Metadata",
]

# ---------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------
_oidRandom = random.getrandbits(40)
_oidCounter = random.randint(0, 0xFFFFFF)

def genOid():
    global _oidCounter
    timestamp = int(time.time()) & 0xFFFFFFFF
    _oidCounter = (_oidCounter + 1) & 0xFFFFFF
    return f"{timestamp:08x}{_oidRandom:010x}{_oidCounter:06x}"

def genSid():
    return genOid() + genOid()

def genTag():
    alphabet = "23456789ABCDEFGHJKLMNPQRSTUVWXYZ"
    return "".join(random.choice(alphabet) for _ in range(6))

def nowIso():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.000Z")

def nowEpochMs():
    return int(datetime.now(timezone.utc).timestamp() * 1000)

def safeStr(value, default=""):
    if value is None: return default
    return str(value)

def safeInt(value, default=0):
    if value is None: return default
    try: return int(value)
    except (ValueError, TypeError): return default

def safeJsonLoads(value, default):
    if not value: return default
    try: return json.loads(value)
    except (ValueError, TypeError): return default

def sanitizeGachaData(val) -> str:
    s = safeStr(val).strip()
    if not s or s == "{}" or ":" not in s:
        return ""
    return s

def sanitizeCardPurchases(val) -> str:
    s = safeStr(val).strip()
    if not s or s == "{}" or (";" not in s and ":" not in s):
        return ""
    return s

def filepackerZipBytes(rawBytes: bytes, entryName: str = "LevelData") -> bytes:
    lengthPrefix = struct.pack("<I", len(rawBytes))
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr(entryName, rawBytes)
    return lengthPrefix + buf.getvalue()

def filepackerCombine(byteArrays: list) -> tuple:
    body = b"".join(byteArrays)
    fileSizes = ",".join(str(len(b)) for b in byteArrays)
    return body, fileSizes

def _buildGhostHeaderedBlob(ghostBytes: bytes, row, playerUnit: str = "Any") -> tuple:
    """Builds a (binBytes, headerText) pair for a ghosts/<stem>.bin + <stem>.header
    export - the exact 2-segment [JSON meta][raw ghost bytes] shape _loadGhostFile
    expects on the way back in. The meta segment is built by _buildGhostMetaDict
    (defined further down, but Python only resolves this at call time so the forward
    reference is fine) - the SAME full field set (playerId/name/time/trophyWin/
    trophyLose/ghostWin/ghostLose/ghostId/trophies/facebookId/gameCenterId/
    countryCode/teamId/teamName/version) a live ghost-list response already sends,
    not a hand-picked subset. An earlier version of this only wrote playerId/name/
    time - technically enough for _syncLevelGhostsFolder to re-import correctly, but
    it silently dropped everything ClientTools.ParseGhostDatas ALSO reads once that
    ghost is actually displayed in-game - countryCode missing is why every ghost
    exported that way showed the US flag regardless of the real player's country."""
    meta = _buildGhostMetaDict(row, playerUnit)
    metaBytes = json.dumps(meta, separators=(",", ":")).encode("utf-8")
    binBytes, headerText = filepackerCombine([metaBytes, ghostBytes])
    return binBytes, headerText

def isVersionSupported(rawVersion: str, minBuild: int = 371) -> bool:
    if not rawVersion: return True
    firstToken = rawVersion.strip().split()[0]
    if "." in firstToken:
        parts = [int(p) for p in re.findall(r"\d+", firstToken)]
        while len(parts) < 3: parts.append(0)
        return (parts[0], parts[1], parts[2]) >= (3, 7, 1)
    digits = "".join(c for c in firstToken if c.isdigit())
    if digits:
        try: return int(digits) >= minBuild
        except ValueError: return True
    return True

def buildFakeGhostSegments(timeScore: int = 0, name: str = "Ghost") -> tuple:
    meta = {
        "playerId": "server_ghost", "name": name,
        "time": safeInt(timeScore, 0), "ghostId": genOid(),
        "trophyWin": 0, "trophyLose": 0,
        "ghostWin": 0, "ghostLose": 0,
        "trophies": 0, "countryCode": "US", "version": 1,
    }
    metaBytes = json.dumps(meta, separators=(",", ":")).encode("utf-8")
    return metaBytes, b""

def buildSingleFakeGhostResponse(timeScore: int = 0, name: str = "Ghost") -> dict:
    metaBytes, ghostBytes = buildFakeGhostSegments(timeScore, name)
    bodyBytes, fileSizes = filepackerCombine([metaBytes, ghostBytes])
    return {"_binary": bodyBytes, "_content_type": "application/octet-stream",
            "_headers": {"FILE_SIZES": fileSizes}}

def firstTimeFromCsvParam(params, key) -> int:
    raw = params.get(key, [""])[0]
    if not raw: return 0
    first = raw.split(",")[0].strip()
    try: return int(float(first))
    except ValueError: return 0

def injectWalletData(result: dict, playerId: str):
    if not playerId: return result
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT coins, diamonds, mcTrophies, carTrophies FROM players WHERE id = ?", (playerId,))
    pRow = c.fetchone()
    conn.close()
    if pRow:
        result["coins"] = safeInt(pRow["coins"])
        result["diamonds"] = safeInt(pRow["diamonds"])
        result["mcTrophies"] = safeInt(pRow["mcTrophies"])
        result["carTrophies"] = safeInt(pRow["carTrophies"])
    return result

# ---------------------------------------------------------------------
# Safe Row Getter (protects against missing columns in older DBs)
# ---------------------------------------------------------------------
def rowGet(row, keys, default=None):
    if row is None:
        return default
    try:
        row_keys = row.keys()
    except Exception:
        return default
    if isinstance(keys, str):
        keys = [keys]
    for k in keys:
        if k in row_keys:
            val = row[k]
            if val is not None:
                return val
    return default

def rowHasColumn(row, colName):
    try:
        return colName in row.keys()
    except Exception:
        try:
            return colName in row
        except Exception:
            return False

# ---------------------------------------------------------------------
# Planet Resolution
# ---------------------------------------------------------------------
def planetIdFromFilename(filename: str) -> str:
    stem = filename[:-4] if filename.endswith(".txt") else filename
    if stem.endswith("LocalInitialData"):
        stem = stem[: -len("LocalInitialData")]
    return stem

def planetFileCandidates(planet: str) -> list:
    planet = (planet or "").strip()
    names = [f"{planet}.txt", f"{planet}LocalInitialData.txt", f"{planet}_LocalInitialData.txt"]
    if planet.endswith("LocalInitialData"):
        names.append(f"{planet}.txt")
        base = planet[: -len("LocalInitialData")]
        names.append(f"{base}.txt")
        names.append(f"{base}LocalInitialData.txt")
    return names

def resolvePlanetTxtPath(planet: str):
    if not os.path.isdir(INITIAL_DATA_DIR): return None
    for name in planetFileCandidates(planet):
        path = os.path.join(INITIAL_DATA_DIR, name)
        if os.path.isfile(path): return path
    want = planet.replace("LocalInitialData", "").lower()
    for filename in os.listdir(INITIAL_DATA_DIR):
        if not filename.endswith(".txt"): continue
        stem = filename[:-4]
        stemNorm = stem.replace("LocalInitialData", "").lower()
        if stemNorm == want or stem.lower() == planet.lower():
            return os.path.join(INITIAL_DATA_DIR, filename)
    return None

def getAvailablePlanets():
    planets = []
    seen = set()
    if os.path.isdir(INITIAL_DATA_DIR):
        for filename in sorted(os.listdir(INITIAL_DATA_DIR)):
            if not filename.endswith(".txt"): continue
            planetId = planetIdFromFilename(filename)
            if not planetId or planetId in seen: continue
            if planetId in ("Obsolete", "Adventure"): continue
            seen.add(planetId)
            planets.append({"planet": planetId, "version": 1})
    for pid in PLANET_IDS:
        if pid in seen or pid == "Metadata": continue
        if resolvePlanetTxtPath(pid):
            planets.append({"planet": pid, "version": 1})
            seen.add(pid)
    return planets

# ---------------------------------------------------------------------
# Minigame Metadata Handling (Pure CamelCase)
# ---------------------------------------------------------------------
_VALID_MINIGAME_COLUMNS = {
    "name", "description", "creatorId", "creatorName",
    "creatorFacebookId", "creatorGameCenterId", "countryCode", "videoUrl",
    "gameMode", "playerUnit", "difficulty", "rating", "state",
    "clientVersion", "gameQuality", "levelRequirement", "complexity",
    "overrideCC", "researchIdentifier", "publishTime",
    "itemsUsed", "itemsCount", "creatorUpgrades",
    "editSessionCount", "groundsModificationCount", "itemsModificationCount",
    "lastPlaySessionStartCount", "timeSpentInEditMode", "timeSpentEditing",
    "timesPlayed", "timesLiked", "timesRated", "timesSuperLiked", "timesAbused",
    "upThumbs", "downThumbs", "bestTime", "participantCount",
    "totalWinners", "oneStarWinners", "twoStarWinners", "threeStarWinners",
    "rewardCoins", "totalCoinsEarned", "editorMeta"
}

def getMinigameRow(minigameId: str):
    if not minigameId: return None
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM minigames WHERE id = ?", (minigameId,))
    row = c.fetchone()
    conn.close()
    return row

def minigameRowToMetaDict(row: sqlite3.Row, playerId: str = None) -> dict:
    itemsUsed = safeJsonLoads(rowGet(row, "itemsUsed", "[]"), [])
    itemsCount = safeJsonLoads(rowGet(row, "itemsCount", "{}"), {})
    if not isinstance(itemsUsed, list): itemsUsed = []
    if not isinstance(itemsCount, dict): itemsCount = {}

    meta = {
        "id": safeStr(rowGet(row, "id")),
        "name": safeStr(rowGet(row, "name", "Unnamed Track")),
        "creatorId": safeStr(rowGet(row, "creatorId", "??")),
        "creatorName": safeStr(rowGet(row, "creatorName", "??")),
        "description": safeStr(rowGet(row, "description", "")),
        "videoUrl": safeStr(rowGet(row, "videoUrl", "")),
        "countryCode": safeStr(rowGet(row, "countryCode", "US")),
        "timesPlayed": safeInt(rowGet(row, "timesPlayed", 0)),
        "timesLiked": safeInt(rowGet(row, "timesLiked", 0)),
        "timesRated": safeInt(rowGet(row, "timesRated", 0)),
        "timesSuperLiked": safeInt(rowGet(row, "timesSuperLiked", 0)),
        "timesAbused": safeInt(rowGet(row, "timesAbused", 0)),
        "upThumbs": safeInt(rowGet(row, "upThumbs", 0)),
        "downThumbs": safeInt(rowGet(row, "downThumbs", 0)),
        "clientVersion": safeInt(rowGet(row, "clientVersion", MIN_BUILD_VERSION)),
        "levelRequirement": safeInt(rowGet(row, "levelRequirement", 0)),
        "complexity": safeInt(rowGet(row, "complexity", 0)),
        "playerUnit": safeStr(rowGet(row, "playerUnit", "Any")),
        "rating": safeStr(rowGet(row, "rating", "Unrated")),
        "gameQuality": float(rowGet(row, "gameQuality", 1.0) or 1.0),
        "itemsUsed": itemsUsed,
        "itemsCount": itemsCount,
        "difficulty": safeStr(rowGet(row, "difficulty", "New")),
        "gameMode": safeStr(rowGet(row, "gameMode", "Race")),
        "rewardCoins": safeInt(rowGet(row, "rewardCoins", 0)),
        "totalCoinsEarned": safeInt(rowGet(row, "totalCoinsEarned", 0)),
        "bestTime": safeInt(rowGet(row, "bestTime", 0)),
        "totalWinners": safeInt(rowGet(row, "totalWinners", 0)),
        "oneStarWinners": safeInt(rowGet(row, "oneStarWinners", 0)),
        "twoStarWinners": safeInt(rowGet(row, "twoStarWinners", 0)),
        "threeStarWinners": safeInt(rowGet(row, "threeStarWinners", 0)),
        "participantCount": safeInt(rowGet(row, "participantCount", 0)),
        "overrideCC": float(rowGet(row, "overrideCC", -1.0) or -1.0),
        "timeSpentEditing": safeInt(rowGet(row, "timeSpentEditing", 0)),
        "timeSpentInEditMode": safeInt(rowGet(row, "timeSpentInEditMode", 0)),
        "editSessionCount": safeInt(rowGet(row, "editSessionCount", 0)),
        "groundsModificationCount": safeInt(rowGet(row, "groundsModificationCount", 0)),
        "itemsModificationCount": safeInt(rowGet(row, "itemsModificationCount", 0)),
        "lastPlaySessionStartCount": safeInt(rowGet(row, "lastPlaySessionStartCount", 0)),
        "state": safeStr(rowGet(row, "state", "public")),
    }

    creatorFb = safeStr(rowGet(row, "creatorFacebookId", ""))
    creatorGc = safeStr(rowGet(row, "creatorGameCenterId", ""))
    if creatorFb: meta["creatorFacebookId"] = creatorFb
    if creatorGc: meta["creatorGameCenterId"] = creatorGc

    # ClientTools.ParseMinigameMetaData does `new Hashtable(_dict["creatorUpgrades"] as
    # Dictionary<string, object>)` - the `as` cast silently yields null for anything
    # that isn't a JSON object, and Hashtable's constructor throws on a null argument,
    # crashing every player who loads this level's metadata (not just one account) -
    # same class of bug as the isinstance guards in getPlayerPayload, but reachable
    # here via the Levels tab's "More..." row editor accepting any text for this
    # column with no shape validation.
    creatorUpgrades = safeJsonLoads(rowGet(row, "creatorUpgrades", None), None)
    if isinstance(creatorUpgrades, dict):
        meta["creatorUpgrades"] = creatorUpgrades

    publishTime = safeStr(rowGet(row, "publishTime", ""))
    if publishTime:
        meta["publishTime"] = publishTime

    # hMinigameMetaFind (fixed-id fetch) already overrides "rating" with the requesting
    # player's own levelRatings entry - but PsGameLoop.LoadMinigame() falls back to
    # SearchMinigame() -> /v2/minigame/meta/search (and the other queryMinigames()-based
    # list endpoints) whenever m_minigameId is empty, which is how adventure/"fresh"
    # random content gets fetched. Without this, a rating submitted via /v1/rating/save
    # IS persisted but never echoed back for that content, so it looks unrated again
    # every time.
    if playerId:
        meta["rating"] = getPlayerRatingForLevel(meta["id"], playerId)

    return meta

def buildMinigameMeta(minigameId: str, playerUnit: str = "Any", gameMode: str = "Race") -> dict:
    return {
        "id": minigameId or genOid(),
        "name": "Level",
        "creatorId": "??",
        "creatorName": "??",
        "gameMode": gameMode or "Race",
        "playerUnit": playerUnit or "Any",
        "difficulty": "New",
        "gameQuality": 1.0,
        "clientVersion": MIN_BUILD_VERSION,
        "itemsUsed": [],
        "itemsCount": {},
        "levelRequirement": 0,
        "rating": "Unrated",
        "timesPlayed": 0,
        "state": "public",
    }

def queryMinigames(gameMode=None, playerUnit=None, difficulty=None,
                   creatorId=None, state=None, searchStr=None, items=None,
                   orderBy="createdAt DESC", limit=20, playerId=None) -> list:
    conn = getDbConnection()
    c = conn.cursor()
    clauses, values = [], []

    if gameMode and gameMode != "Any":
        clauses.append("gameMode = ?"); values.append(gameMode)
    if playerUnit and playerUnit != "Any":
        clauses.append("playerUnit = ?"); values.append(playerUnit)
    if difficulty and difficulty != "Any":
        clauses.append("difficulty = ?"); values.append(difficulty)
    if creatorId:
        clauses.append("creatorId = ?"); values.append(creatorId)
    if state:
        clauses.append("state = ?"); values.append(state)
    if searchStr:
        clauses.append("(name LIKE ? OR creatorName LIKE ?)")
        values.extend([f"%{searchStr}%", f"%{searchStr}%"])
    if items:
        itemList = [i.strip() for i in items.split(",")] if isinstance(items, str) else items
        for item in itemList:
            if item:
                clauses.append("itemsUsed LIKE ?")
                values.append(f"%{item}%")

    where = f"WHERE {' AND '.join(clauses)}" if clauses else ""
    try:
        limit = max(1, min(safeInt(limit, 20), 200))
    except Exception:
        limit = 20

    query = f"SELECT * FROM minigames {where} ORDER BY {orderBy} LIMIT ?"
    values.append(limit)
    c.execute(query, values)
    rows = c.fetchall()
    conn.close()
    return [minigameRowToMetaDict(r, playerId) for r in rows]

def upsertMinigame(minigameId: str, fields: dict = None, levelData: bytes = None):
    fields = dict(fields or {})
    for key in ("itemsUsed", "itemsCount", "creatorUpgrades", "editorMeta"):
        if key in fields and not isinstance(fields[key], str):
            fields[key] = json.dumps(fields[key])

    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT id FROM minigames WHERE id = ?", (minigameId,))
    exists = c.fetchone() is not None

    if not exists:
        c.execute("INSERT INTO minigames (id) VALUES (?)", (minigameId,))

    if fields:
        setParts = [f"{k} = ?" for k in fields.keys()]
        values = list(fields.values())
        setParts.append("updatedAt = CURRENT_TIMESTAMP")
        values.append(minigameId)
        c.execute(f"UPDATE minigames SET {', '.join(setParts)} WHERE id = ?", values)

    if levelData is not None:
        c.execute("UPDATE minigames SET levelData = ?, updatedAt = CURRENT_TIMESTAMP WHERE id = ?",
                  (levelData, minigameId))

    conn.commit()
    conn.close()

def deleteMinigameSafely(minigameId: str):
    """Deletes a level and, if it was the currently-configured tournament level,
    disables the tournament along with it - PsGameLoopTournament crashes trying to
    load a level that no longer exists (the same class of bug as the "Shared" planet
    crash: stale state referencing content the server can no longer serve), so a
    deleted level can never be left dangling as the active tournament."""
    if not minigameId: return
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("DELETE FROM minigames WHERE id = ?", (minigameId,))
    conn.commit()
    conn.close()
    if minigameId == safeStr(getTournamentConfig().get("minigameId")):
        setTournamentConfig({"minigameId": "", "startTime": 0, "endTime": 0})
        print(f"[Tournament] Configured level {minigameId} was deleted - tournament disabled to avoid a client crash")

# ---------------------------------------------------------------------
# Level Import
# ---------------------------------------------------------------------
_LEVEL_FILE_CANDIDATES = ("level.bin", "level.dat", "data.bin", "data.dat")
_SCREENSHOT_CANDIDATES = ("screenshot.bin", "screenshot.png", "screenshot.jpg", "screenshot.jpeg")
_SCREENSHOT_EXTENSIONS = ("_screenshot.bin", ".png", ".jpg", ".jpeg")

# A level's ghosts now live in a dedicated "ghosts" folder (LevelData/<id>/ghosts/ for
# subfolder-style levels, LevelData/<id>_ghosts/ for flat-file-style levels) instead of
# fixed ghost.bin/.header filenames. Every non-".header" file inside is a ghost payload;
# its optional counterpart is "<stem>.header" in the same folder, same FILE_SIZES-style
# 2-segment convention as before (see _loadGhostFile). One reserved stem, "creatorGhost",
# becomes minigames.creatorGhost; every other stem becomes/updates a row in `scores`
# (see _syncLevelGhostsFolder for why `scores`, not the `ghosts` table).
_GHOSTS_SUBFOLDER = "ghosts"
_CREATOR_GHOST_STEM = "creatorGhost"
_GHOST_ROW_ID_PREFIX = "levelghost"

def _loadLevelMetaJson(path):
    if not path or not os.path.isfile(path): return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            raw = json.load(f)
        return raw if isinstance(raw, dict) else {}
    except Exception as e:
        print(f"[LevelImport] Bad meta.json at {path}: {e}")
        return {}

# Every server-generated meta.json uses "state" values of exactly "public"/"saved"/
# "hidden" (see _handleMinigameSaveVariant), but level dumps captured from the
# original real game use "published" instead of "public" for the same thing. Every
# browse/search query here filters on the literal string "public", so an imported
# level stuck at "published" is invisible in every list (and, if picked as the
# tournament level, unreachable by anyone but the creator going in through
# "My Levels") even though it looks perfectly normal in the admin GUI.
_IMPORTED_STATE_ALIASES = {"published": "public"}

def _normalizeImportedState(fields: dict) -> dict:
    if "state" in fields:
        fields["state"] = _IMPORTED_STATE_ALIASES.get(fields["state"], fields["state"])
    return fields

_INTERNAL_STRING_COMPARER_NAME = b"System.Collections.Generic.InternalStringComparer"
_GENERIC_EQUALITY_COMPARER_NAME = (
    b"System.Collections.Generic.GenericEqualityComparer`1[[System.String, mscorlib, "
    b"Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089]]"
)

def _encode7BitLength(n: int) -> bytes:
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)

def _stripInternalStringComparerRefs(data: bytes) -> bytes:
    """Old-client ghost data can embed a Dictionary<string, T> (Ghost's
    vehicleUpgradeItems) that a .NET Framework/mscorlib build serializes using its
    internal System.Collections.Generic.InternalStringComparer as the dictionary's
    default string-key comparer - an implementation-internal BCL type, not part of
    the public API, that the actual 2015-era Mono/IL2CPP runtime on the real client
    does not have under that name. BinaryFormatter resolves every referenced type as
    it walks the record stream, well before any of the C# reader's per-field
    try/except blocks ever run - confirmed empirically (a real .NET BinaryFormatter,
    told to refuse resolving this one type name, throws a SerializationException that
    escapes Ghost's constructor entirely, uncaught by Ghost.DeSerializeFromBytes's
    catch(InvalidCastException) too). That's the tournament-only crash on "The Climb":
    unlike every other level's ghosts, its creator ghost's vehicleUpgradeItems dict
    happens to have been serialized this way.
    This renames every occurrence of the type name to
    System.Collections.Generic.GenericEqualityComparer`1[[System.String]] - the real,
    ordinary BCL type that EqualityComparer<string>.Default itself resolves to on any
    .NET/Mono/IL2CPP build (string implements IEquatable<string>), so it's always
    resolvable - instead of touching the record structure at all: the standalone
    comparer instance keeps its ObjectId and stays a stateless 0-member class, and
    every MemberReference to it remains valid, since renaming a class in place doesn't
    change any ObjectId. An EARLIER version of this function instead deleted the
    comparer instance and replaced every reference to it with ObjectNull; that looked
    correct under a desktop .NET Framework BinaryFormatter test, but a live on-device
    capture during an actual "The Climb" tournament crash (attached over gdb-remote
    mid-SIGTRAP) showed IL2CPP's own Dictionary`2.Add(), called from
    OnDeserialization(), throwing "A null value was found where an object instance was
    required." - i.e. a null Comparer is NOT a safe substitute on the real runtime,
    unlike on desktop .NET. Renaming to a real, always-present comparer type instead of
    nulling it out was verified end-to-end afterwards: a real Dictionary<string,object>
    (using its actual Add()/OnDeserialization() codepath, not a stubbed-out reader)
    deserializes all 24 vehicleUpgradeItems entries with no exception, both patched and
    plain. Raises ValueError if a type-name occurrence's length-prefix byte doesn't
    match what's described above - callers should catch this and fall back to the
    original bytes rather than risk a wrong edit."""
    nameLen = len(_INTERNAL_STRING_COMPARER_NAME)
    occurrences = [m.start() for m in re.finditer(re.escape(_INTERNAL_STRING_COMPARER_NAME), data)]
    if not occurrences:
        return data

    newNameBytes = _encode7BitLength(len(_GENERIC_EQUALITY_COMPARER_NAME)) + _GENERIC_EQUALITY_COMPARER_NAME
    edits = []  # (start, end, replacementBytes) in original-data offsets
    for occ in occurrences:
        lenPos = occ - 1
        if data[lenPos] != nameLen:
            raise ValueError(f"unexpected length-prefix byte before InternalStringComparer name at {occ}")
        edits.append((lenPos, occ + nameLen, newNameBytes))

    edits.sort(key=lambda e: e[0])
    out = io.BytesIO()
    cursor = 0
    for start, end, replacement in edits:
        if start < cursor:
            raise ValueError("overlapping edits while patching InternalStringComparer refs")
        out.write(data[cursor:start])
        out.write(replacement)
        cursor = end
    out.write(data[cursor:])
    return out.getvalue()

def _findGhostEventDeclarationObjectId(data: bytes, declIdx: int) -> int:
    """The GhostEvent ClassWithMembersAndTypes record that owns the member-list at
    declIdx has its own ObjectId written right before its name (record type 0x05,
    then a 4-byte ObjectId, then the length-prefixed "GhostEvent" string). Located
    by scanning backward for that exact 5-byte-prefixed name instead of assuming a
    fixed offset, since unrelated records precede it by a varying amount."""
    nameTag = bytes([0x0a]) + b"GhostEvent"  # 0x0a = 7-bit length prefix for 10 chars
    searchStart = max(0, declIdx - 200)
    idx = data.rfind(nameTag, searchStart, declIdx)
    if idx == -1 or data[idx - 5] != 0x05:
        raise ValueError("could not locate GhostEvent's own ClassWithMembersAndTypes header")
    return struct.unpack_from("<i", data, idx - 4)[0]

def _stripGhostEventMDataRefs(data: bytes) -> bytes:
    """Old-client ghost data can serialize Ghost.m_events (a List<GhostEvent>) with
    an extra "m_data" (string) field per GhostEvent that the current client's
    GhostEvent struct (m_tick, m_event only) doesn't have. GhostEvent is a plain
    [Serializable] struct with no custom ISerializable constructor, so .NET/IL2CPP's
    BinaryFormatter populates its fields purely by reflection - when a member name in
    the stream (m_data) has no matching field on the resolved runtime type, it throws
    SerializationException("Field 'm_data' not found in class 'GhostEvent'"), and
    like the InternalStringComparer case this happens while BinaryFormatter is still
    walking the object graph, before any of Ghost's own per-field try/except blocks
    run - confirmed live on-device via a debugger attach during an actual crash: the
    exact same "at ObjectReader.ReadGenericArray -> ReadValue -> ReadObjectInstance ->
    ReadTypeMetadata" stack and "Field \"m_data\" not found in class GhostEvent"
    message were sitting in memory at the SIGTRAP.
    This removes the "m_data" member from the ClassInfo (member count 3 -> 2, drops
    its name and its BinaryTypeEnum entry) and strips the per-instance null value
    that went with it. Every GhostEvent instance observed in practice serializes
    m_data as ObjectNull (the old client always left it unset) - each removal is
    still verified byte-for-byte before being applied, and this raises ValueError
    (never guesses) if any instance's m_data isn't null or the array's instances
    aren't evenly spaced, so a caller can fall back to the original bytes instead of
    risking a wrong edit. Returns data unchanged if it has no GhostEvent m_data
    field to strip (e.g. a normal, new-client-recorded ghost)."""
    memberCount3 = struct.pack("<I", 3)
    memberNamesBlock = bytes([0x06]) + b"m_tick" + bytes([0x07]) + b"m_event" + bytes([0x06]) + b"m_data"
    declIdx = data.find(memberCount3 + memberNamesBlock)
    if declIdx == -1:
        return data

    afterNames = declIdx + 4
    namesEnd = afterNames + len(memberNamesBlock)
    typeArrayPos = namesEnd
    typeArray = data[typeArrayPos:typeArrayPos + 3]
    if typeArray != bytes([0x00, 0x04, 0x01]):  # [m_tick=Primitive, m_event=Class, m_data=String]
        raise ValueError(f"unexpected GhostEvent member type array {typeArray!r}")

    pos = typeArrayPos + 3
    pos += 1  # m_tick's PrimitiveTypeEnum byte (its own value, not checked here)
    classNameLen = data[pos]
    pos += 1
    className = data[pos:pos + classNameLen]
    pos += classNameLen
    if className != b"GhostEventType":
        raise ValueError(f"unexpected m_event class name {className!r}")
    pos += 4  # this ClassInfo's own LibraryId
    firstInstanceStart = pos

    ghostEventObjId = _findGhostEventDeclarationObjectId(data, declIdx)
    metaRef = struct.pack("<i", ghostEventObjId)

    positions = []  # offsets of the 0x01 byte starting each non-first instance's ClassWithId
    searchPos = firstInstanceStart
    while True:
        idx = data.find(metaRef, searchPos)
        if idx == -1:
            break
        if data[idx - 5] == 0x01:
            positions.append(idx - 5)
        searchPos = idx + 1
    if not positions:
        raise ValueError("found GhostEvent member declaration but no ClassWithId instance markers")
    strides = {positions[i + 1] - positions[i] for i in range(len(positions) - 1)}
    if len(strides) > 1:
        raise ValueError(f"GhostEvent instance markers are not evenly spaced: {sorted(strides)}")
    stride = next(iter(strides)) if strides else None
    if stride is None:
        raise ValueError("only one GhostEvent instance found - can't verify a safe stride")

    # Each marker P is the 0x01 byte starting some instance's own ClassWithId header;
    # that instance's m_data (ObjectNull) byte sits right before the *next*
    # instance's header, i.e. at P + stride - 1. The very first GhostEvent instance
    # (the one using the full inline declaration, no ClassWithId of its own) ends
    # the same way, one stride before the first marker.
    mdataPositions = [positions[0] - 1] + [p + stride - 1 for p in positions]

    edits = [
        (declIdx, declIdx + 4, struct.pack("<I", 2)),
        (afterNames + (1 + 6) + (1 + 7), namesEnd, b""),  # remove "m_data" name
        (typeArrayPos + 2, typeArrayPos + 3, b""),          # remove its BinaryTypeEnum byte
    ]
    for mp in mdataPositions:
        if data[mp] != 0x0a:
            raise ValueError(f"GhostEvent instance m_data at {mp} is not ObjectNull "
                              f"(byte=0x{data[mp]:02x}) - won't strip a non-null value blind")
        edits.append((mp, mp + 1, b""))

    edits.sort(key=lambda e: e[0])
    out = io.BytesIO()
    cursor = 0
    for start, end, replacement in edits:
        if start < cursor:
            raise ValueError("overlapping edits while patching GhostEvent m_data refs")
        out.write(data[cursor:start])
        out.write(replacement)
        cursor = end
    out.write(data[cursor:])
    return out.getvalue()

def _repairFilepackerBlob(blobBytes: bytes) -> bytes:
    """Levels dumped from an older client build carry level geometry AND ghost replay
    data whose FilePacker-zipped payload (see filepackerZipBytes) has a wrong leading
    4-byte length prefix - that old exporter wrote the size of a scratch buffer it had
    allocated (always a round power of two: 8192/16384/32768/.../4194304...) instead of
    the actual number of bytes it wrote into the zip. This isn't a one-off: EVERY
    level's levelData and EVERY ghost dumped from that old client build has this same
    mismatch. The CURRENT client's own FilePacker.UnZipBytes() trusts the prefix
    completely: it allocates a buffer of exactly that (wrong, too-large) size and does
    a single Stream.Read() into it, which is not guaranteed to fill the buffer - the
    tail ends up as zero-byte garbage past the real data.
    Separately, the decompressed content itself can carry an old-client-vs-new-client
    BinaryFormatter incompatibility - see _stripInternalStringComparerRefs - so that
    check always runs on the extracted bytes too, regardless of whether the length
    prefix needed fixing. Detects the length-prefix mismatch by re-deriving the TRUE
    length from the zip's own entry metadata (always correct - only the leading
    prefix lies) and re-packs with a matching prefix via filepackerZipBytes(), so
    data from an old-client level dump works with the current client without any
    manual fix-up - this runs on every import, so any future level with either
    old-client quirk is repaired automatically instead of needing another one-off DB
    patch. Returns blobBytes completely unchanged if it isn't a FilePacker-zipped
    blob at all (e.g. a genuinely raw/legacy format), or if neither issue applies."""
    if not blobBytes or len(blobBytes) < 4:
        return blobBytes
    try:
        claimedLength = struct.unpack("<I", blobBytes[:4])[0]
        with zipfile.ZipFile(io.BytesIO(blobBytes[4:])) as zf:
            names = zf.namelist()
            if not names:
                return blobBytes
            entryName = "LevelData" if "LevelData" in names else names[0]
            realBytes = zf.read(entryName)
    except Exception:
        return blobBytes

    lengthWasWrong = claimedLength != len(realBytes)
    try:
        patchedBytes = _stripInternalStringComparerRefs(realBytes)
        comparerWasPatched = patchedBytes != realBytes
    except ValueError as e:
        print(f"[LevelImport] Could not patch an InternalStringComparer reference ({e}), "
              f"leaving that part of the data as-is")
        patchedBytes = realBytes
        comparerWasPatched = False

    try:
        afterGhostEventFix = _stripGhostEventMDataRefs(patchedBytes)
        ghostEventWasPatched = afterGhostEventFix != patchedBytes
        patchedBytes = afterGhostEventFix
    except ValueError as e:
        print(f"[LevelImport] Could not patch a GhostEvent m_data reference ({e}), "
              f"leaving that part of the data as-is")
        ghostEventWasPatched = False

    if not lengthWasWrong and not comparerWasPatched and not ghostEventWasPatched:
        return blobBytes

    if lengthWasWrong:
        print(f"[LevelImport] Repairing old-client FilePacker data: length prefix said "
              f"{claimedLength} bytes, real payload is {len(realBytes)} bytes - re-packing.")
    if comparerWasPatched:
        print("[LevelImport] Renamed an old-client-incompatible InternalStringComparer "
              "reference (Dictionary field) to a real resolvable comparer type - re-packing.")
    if ghostEventWasPatched:
        print("[LevelImport] Removed an old-client-only GhostEvent.m_data field "
              "reference from a ghost's event list - re-packing.")
    return filepackerZipBytes(patchedBytes)

def _loadGhostFile(ghostPath, headerPath=None):
    """Reads a single ghost payload file for import, returning (meta, ghostBytes).
    If a matching .header file exists (holding a FILE_SIZES-style comma-separated
    length list, same convention as Trophy.SaveGhostData/splitFileSizesBody elsewhere
    in this file), the ghost binary is a 2-segment blob - [0] JSON metadata (name,
    time, playerId, etc. - same shape as buildFakeGhostSegments), [1] the actual ghost
    replay bytes. Without a header, the whole file is already just the raw ghost bytes
    and meta comes back empty - this is also how old-client dumps like a bare
    "ghost.bin" (no matching .header) show up, and that raw content is itself
    typically still a FilePacker-zipped blob, so the ghost bytes are auto-repaired
    (see _repairFilepackerBlob) on every return path here, header or not. Returns
    None if the file is missing/empty."""
    if not ghostPath or not os.path.isfile(ghostPath):
        return None
    with open(ghostPath, "rb") as f:
        raw = f.read()
    if not raw:
        return None
    if not headerPath or not os.path.isfile(headerPath):
        return {}, _repairFilepackerBlob(raw)
    try:
        with open(headerPath, "r", encoding="utf-8") as f:
            fileSizes = f.read().strip()
    except Exception as e:
        print(f"[LevelImport] Could not read {headerPath}: {e}")
        return {}, _repairFilepackerBlob(raw)
    segments = splitFileSizesBody(fileSizes, raw)
    if len(segments) < 2:
        print(f"[LevelImport] {headerPath} did not yield 2 segments (got {len(segments)}), "
              f"treating {ghostPath} as raw ghost bytes")
        return {}, _repairFilepackerBlob(raw)
    metaBytes, ghostBytes = segments[0], segments[1]
    ghostBytes = _repairFilepackerBlob(ghostBytes)
    meta = {}
    try:
        parsed = json.loads(metaBytes.decode("utf-8"))
        if isinstance(parsed, dict):
            meta = parsed
    except Exception:
        pass
    return meta, (ghostBytes if ghostBytes else b"")

def _loadGhostBytes(ghostPath, headerPath=None):
    """Back-compat convenience wrapper around _loadGhostFile for callers that only
    want the payload bytes (e.g. the single creatorGhost slot)."""
    loaded = _loadGhostFile(ghostPath, headerPath)
    if loaded is None:
        return None
    meta, ghostBytes = loaded
    if meta:
        print(f"[LevelImport] Ghost metadata from {os.path.basename(headerPath)}: "
              f"name={meta.get('name')!r} time={meta.get('time')}")
    return ghostBytes if ghostBytes else None

def _listGhostsFolderFiles(ghostsDir):
    """Returns {stem: (payloadPath, headerPathOrNone)} for every ghost payload file
    directly inside a ghosts folder. Any file not ending in ".header" is a payload;
    its optional counterpart is "<stem>.header" in the same folder, e.g. "flash.bin"
    pairs with "flash.header"."""
    result = {}
    if not os.path.isdir(ghostsDir):
        return result
    for fname in os.listdir(ghostsDir):
        fpath = os.path.join(ghostsDir, fname)
        if not os.path.isfile(fpath) or fname.lower().endswith(".header"):
            continue
        stem = os.path.splitext(fname)[0]
        headerPath = os.path.join(ghostsDir, stem + ".header")
        result[stem] = (fpath, headerPath if os.path.isfile(headerPath) else None)
    return result

def _syncCreatorGhost(minigameId, creatorGhostBytesFromFile):
    """Keeps minigames.creatorGhost workable on every import pass, without ever
    letting a re-import silently replace what's already stored. Still backfill-only
    in the sense that matters: creatorGhost can be overwritten live at runtime when
    the creator submits a validation ghost through the game (see the
    /v1/trophy/... SaveGhostData path), and a raw bytes comparison against the
    ghosts/creatorGhost.* file can't tell "the file is newer" apart from "the DB has
    a live-submitted run the file predates" - so once a row has ANY stored value, the
    file is never used to replace it outright, no matter how different the two are.
    What it adds over the original backfill-only behavior: when a row's EXISTING
    value has a known, fixable byte-level issue (see _repairFilepackerBlob - a wrong
    FilePacker length prefix, or an old-client BinaryFormatter incompatibility), it
    gets healed IN PLACE, since that's a pure bug fix to bytes already committed to
    this row, not a competing data source - upgrading this script and re-running
    import, with no file changes at all, is enough to fix an already-imported level's
    stale value. True backfill (nothing stored yet) still uses the file's ghost."""
    row = getMinigameRow(minigameId)
    if row is None:
        return False
    existing = row["creatorGhost"]
    if not existing:
        if creatorGhostBytesFromFile:
            upsertMinigame(minigameId, {"creatorGhost": creatorGhostBytesFromFile})
            print(f"[LevelImport] {minigameId}: backfilled creatorGhost ({len(creatorGhostBytesFromFile)} bytes)")
        return True
    healed = _repairFilepackerBlob(bytes(existing))
    if healed != bytes(existing):
        upsertMinigame(minigameId, {"creatorGhost": healed})
        print(f"[LevelImport] {minigameId}: healed a stale/corrupt existing creatorGhost "
              f"in place ({len(healed)} bytes)")
    return True

def _syncLevelData(minigameId, levelBytesFromFile):
    """Same idea as _syncCreatorGhost, for minigames.levelData: heals an already-
    stored value's known byte-level issues in place (see _repairFilepackerBlob), but
    never lets a re-import replace an existing value with the file's version outright
    - only a row with nothing stored yet (true backfill) uses the file directly."""
    row = getMinigameRow(minigameId)
    if row is None:
        return False
    existing = row["levelData"]
    if not existing:
        if levelBytesFromFile is not None:
            upsertMinigame(minigameId, {}, levelBytesFromFile)
            print(f"[LevelImport] {minigameId}: backfilled levelData ({len(levelBytesFromFile)} bytes)")
        return True
    healed = _repairFilepackerBlob(bytes(existing))
    if healed != bytes(existing):
        upsertMinigame(minigameId, {}, healed)
        print(f"[LevelImport] {minigameId}: healed stale/corrupt existing levelData in place "
              f"({len(healed)} bytes)")
    return True

def _syncLevelGhostsFolder(minigameId, ghostFiles):
    """Full resync of a level's ghosts folder into the `scores` table. The `ghosts`
    table declared in initDb() (playerId/ghostWin/ghostLose/ghostData) is schema-only
    dead weight kept for Traplight backend parity - nothing ever queries it. The
    real ghost lists (/v1/trophy/ghostsbytime, ghostsbytrophies, ghostsbyids) all read
    from `scores`, so that's where imported extra ghosts need to live to actually show
    up in-game. Each non-creatorGhost stem becomes/updates one `scores` row, keyed by a
    deterministic id so re-imports update in place instead of duplicating; any
    previously-synced row for a stem no longer present on disk gets deleted, so the DB
    always exactly mirrors the folder. Note: ghostsbytime/ghostsbytrophies filter on
    `time > 0`, so a ghost whose header has no "time" (or a headerless/raw payload
    file, which has no metadata at all) still gets stored here but won't surface in
    those lists - only via ghostsbyids, which doesn't filter on time.
    Returns (currentCount, removedCount)."""
    files = dict(ghostFiles)
    files.pop(_CREATOR_GHOST_STEM, None)

    # Old-client level dumps can carry several DIFFERENT real players' ghosts that were
    # all mis-tagged with the level creator's own playerId in their metadata (seen on
    # "The Climb": two ghosts named "Airhead"/"Drater", neither the creator, both
    # stamped with the creator's UDID). Every tournament/leaderboard query here dedups
    # `scores` by (gameId, playerId), so trusting that playerId verbatim silently
    # collapses these into a single, wrong entry - the surviving row's own ghost time
    # doesn't match the level's own recorded creator bestTime either, since it's really
    # a different person's run. Detect the collision (declared playerId == this level's
    # creatorId, but the ghost's own name says otherwise) and give that ghost a
    # distinct synthetic id instead of reusing the creator's.
    levelRow = getMinigameRow(minigameId)
    creatorId = safeStr(levelRow["creatorId"]) if levelRow is not None else ""
    creatorName = safeStr(levelRow["creatorName"]) if levelRow is not None else ""

    conn = getDbConnection()
    c = conn.cursor()
    idPrefix = f"{_GHOST_ROW_ID_PREFIX}:{minigameId}:"

    desiredIds = set()
    for stem, (payloadPath, headerPath) in files.items():
        loaded = _loadGhostFile(payloadPath, headerPath)
        if loaded is None:
            continue
        meta, ghostBytes = loaded
        if not ghostBytes:
            print(f"[LevelImport] {minigameId}: ghosts/{stem} has no ghost payload bytes, skipping")
            continue
        rowId = idPrefix + stem
        desiredIds.add(rowId)
        playerName = safeStr(meta.get("name")) or stem
        metaPlayerId = safeStr(meta.get("playerId"))
        if metaPlayerId and creatorId and metaPlayerId == creatorId and playerName != creatorName:
            # A synthetic id shaped like a real UDID (24 hex chars, same as genOid())
            # rather than the raw "levelghost:..." row id - some client-side code may
            # assume playerId always looks like a real backend id.
            playerId = hashlib.md5(rowId.encode("utf-8")).hexdigest()[:24]
            print(f"[LevelImport] {minigameId}: ghosts/{stem} ({playerName!r}) was mis-tagged with "
                  f"the creator's playerId - assigning it a distinct synthetic id ({playerId}) instead")
        else:
            playerId = metaPlayerId or rowId
        timeScore = safeInt(meta.get("time"), 0)
        # A header can carry countryCode/facebookId/gameCenterId/teamId/teamName/
        # trophies (the full shape _buildGhostMetaDict builds on export, or a real
        # legacy-client ghost export) for a player that doesn't exist as a row on
        # THIS server at all - nowhere else to keep that than on the ghost's own
        # row, so it isn't silently dropped on import (see the ghostCountryCode
        # etc. columns' own comment in initDb() for why these exist).
        ghostCountryCode = safeStr(meta.get("countryCode"))
        ghostFacebookId = safeStr(meta.get("facebookId"))
        ghostGameCenterId = safeStr(meta.get("gameCenterId"))
        ghostTeamId = safeStr(meta.get("teamId"))
        ghostTeamName = safeStr(meta.get("teamName"))
        ghostTrophies = safeInt(meta.get("trophies"), 0)
        c.execute("""INSERT INTO scores (id, gameId, playerId, playerName, playerUnit, time,
                                          stars, boost, upgradeSum, deathCount, starts, mainPath, ghostData,
                                          ghostCountryCode, ghostFacebookId, ghostGameCenterId,
                                          ghostTeamId, ghostTeamName, ghostTrophies)
                     VALUES (?, ?, ?, ?, 'Any', ?, 0, 'false', 0, 0, 1, 'false', ?, ?, ?, ?, ?, ?, ?)
                     ON CONFLICT(id) DO UPDATE SET
                       gameId=excluded.gameId, playerId=excluded.playerId,
                       playerName=excluded.playerName, time=excluded.time,
                       ghostData=excluded.ghostData,
                       ghostCountryCode=excluded.ghostCountryCode, ghostFacebookId=excluded.ghostFacebookId,
                       ghostGameCenterId=excluded.ghostGameCenterId, ghostTeamId=excluded.ghostTeamId,
                       ghostTeamName=excluded.ghostTeamName, ghostTrophies=excluded.ghostTrophies""",
                  (rowId, minigameId, playerId, playerName, timeScore, ghostBytes,
                   ghostCountryCode, ghostFacebookId, ghostGameCenterId, ghostTeamId, ghostTeamName, ghostTrophies))

    c.execute("SELECT id FROM scores WHERE id LIKE ?", (idPrefix + "%",))
    existingIds = {r["id"] for r in c.fetchall()}
    staleIds = existingIds - desiredIds
    for sid in staleIds:
        c.execute("DELETE FROM scores WHERE id = ?", (sid,))

    conn.commit()
    conn.close()
    return len(desiredIds), len(staleIds)

def _importSubfolderLevel(minigameId: str) -> bool:
    """Imports LevelData/<minigameId>/{meta.json,level.bin,screenshot.bin,ghosts/,...}.
    ghosts/ holds any number of extra ghosts (synced into `scores`, see
    _syncLevelGhostsFolder) plus one optional creatorGhost.<ext> (+ matching
    creatorGhost.header) that becomes minigames.creatorGhost. The ghosts/ resync runs
    every pass regardless of whether the level is new, so dropping/editing/removing
    files there is picked up on already-imported levels too.
    Returns True if a new level row was created (False for a ghost-only backfill/resync
    or a level that was already imported and needs nothing else)."""
    sub = os.path.join(LEVELS_DIR, minigameId)
    ghostsDir = os.path.join(sub, _GHOSTS_SUBFOLDER)
    ghostFiles = _listGhostsFolderFiles(ghostsDir)

    added, removed = _syncLevelGhostsFolder(minigameId, ghostFiles)
    if added or removed:
        print(f"[LevelImport] {minigameId}: synced ghosts/ ({added} ghost(s) current, {removed} removed)")

    creatorGhostBytes = None
    creatorPayload = ghostFiles.get(_CREATOR_GHOST_STEM)
    if creatorPayload:
        loaded = _loadGhostFile(*creatorPayload)
        if loaded:
            _, creatorGhostBytes = loaded

    levelBytes = None
    for cand in _LEVEL_FILE_CANDIDATES:
        cpath = os.path.join(sub, cand)
        if os.path.isfile(cpath):
            with open(cpath, "rb") as f: levelBytes = f.read()
            break
    if levelBytes is not None:
        levelBytes = _repairFilepackerBlob(levelBytes)

    if getMinigameRow(minigameId) is not None:
        _syncCreatorGhost(minigameId, creatorGhostBytes)
        _syncLevelData(minigameId, levelBytes)
        return False

    metaPath = os.path.join(sub, "meta.json")
    meta = _loadLevelMetaJson(metaPath if os.path.isfile(metaPath) else None)

    screenshotBytes = None
    for sCand in _SCREENSHOT_CANDIDATES:
        spath = os.path.join(sub, sCand)
        if os.path.isfile(spath):
            with open(spath, "rb") as f: screenshotBytes = f.read()
            break

    if levelBytes is None:
        others = [f for f in os.listdir(sub)
                  if f != "meta.json" and f.lower() not in _SCREENSHOT_CANDIDATES
                  and f != _GHOSTS_SUBFOLDER
                  and os.path.isfile(os.path.join(sub, f))
                  and not f.lower().endswith(('.png', '.jpg', '.jpeg'))]
        if len(others) == 1:
            with open(os.path.join(sub, others[0]), "rb") as f: levelBytes = f.read()
            levelBytes = _repairFilepackerBlob(levelBytes)

    fields = _normalizeImportedState({k: v for k, v in meta.items() if k in _VALID_MINIGAME_COLUMNS})
    if screenshotBytes: fields["screenshot"] = screenshotBytes
    if creatorGhostBytes: fields["creatorGhost"] = creatorGhostBytes
    upsertMinigame(minigameId, fields, levelBytes)

    scInfo = f"screenshot={len(screenshotBytes)} bytes" if screenshotBytes else "screenshot=no"
    gInfo = f", creatorGhost={len(creatorGhostBytes)} bytes" if creatorGhostBytes else ""
    print(f"[LevelImport] {minigameId}: meta={'yes' if meta else 'defaults'}, "
          f"levelData={len(levelBytes) if levelBytes else 0} bytes, {scInfo}{gInfo}")
    return True

def _importFlatLevel(minigameId: str, flatFiles: list) -> bool:
    """Imports flat LevelData/<minigameId>.bin (+ optional .json/_screenshot siblings
    and a <minigameId>_ghosts/ folder - same ghosts/ convention as
    _importSubfolderLevel, just named "<id>_ghosts" since flat-style levels don't
    have their own subfolder to nest one in).
    Returns True if a new level row was created."""
    ghostsDir = os.path.join(LEVELS_DIR, minigameId + "_ghosts")
    ghostFiles = _listGhostsFolderFiles(ghostsDir)

    added, removed = _syncLevelGhostsFolder(minigameId, ghostFiles)
    if added or removed:
        print(f"[LevelImport] {minigameId}: synced {minigameId}_ghosts/ ({added} ghost(s) current, {removed} removed)")

    creatorGhostBytes = None
    creatorPayload = ghostFiles.get(_CREATOR_GHOST_STEM)
    if creatorPayload:
        loaded = _loadGhostFile(*creatorPayload)
        if loaded:
            _, creatorGhostBytes = loaded

    levelBytes = None
    for f in flatFiles:
        stem, ext = os.path.splitext(f)
        if stem == minigameId and ext.lower() not in (".json", ".png", ".jpg", ".jpeg") \
           and not stem.endswith("_screenshot"):
            with open(os.path.join(LEVELS_DIR, f), "rb") as fh: levelBytes = fh.read()
            break
    if levelBytes is not None:
        levelBytes = _repairFilepackerBlob(levelBytes)

    if getMinigameRow(minigameId) is not None:
        _syncCreatorGhost(minigameId, creatorGhostBytes)
        _syncLevelData(minigameId, levelBytes)
        return False

    jsonPath = os.path.join(LEVELS_DIR, minigameId + ".json")
    meta = _loadLevelMetaJson(jsonPath if os.path.isfile(jsonPath) else None)
    screenshotBytes = None
    for ext in _SCREENSHOT_EXTENSIONS:
        spath = os.path.join(LEVELS_DIR, minigameId + ext)
        if os.path.isfile(spath):
            with open(spath, "rb") as fh: screenshotBytes = fh.read()
            break
    fields = _normalizeImportedState({k: v for k, v in meta.items() if k in _VALID_MINIGAME_COLUMNS})
    if screenshotBytes: fields["screenshot"] = screenshotBytes
    if creatorGhostBytes: fields["creatorGhost"] = creatorGhostBytes
    upsertMinigame(minigameId, fields, levelBytes)
    scInfo = f"screenshot={len(screenshotBytes)} bytes" if screenshotBytes else "screenshot=no"
    gInfo = f", creatorGhost={len(creatorGhostBytes)} bytes" if creatorGhostBytes else ""
    print(f"[LevelImport] {minigameId}: meta={'yes' if meta else 'defaults'}, "
          f"levelData={len(levelBytes) if levelBytes else 0} bytes, {scInfo}{gInfo}")
    return True

def importLevelsFromFolder():
    if not os.path.isdir(LEVELS_DIR): return 0
    entries = os.listdir(LEVELS_DIR)
    imported = 0

    # Both layouts are scanned unconditionally in the same pass (rather than picking
    # one mode for the whole folder) so a mix of subfolder-style and flat-file-style
    # levels - e.g. dropping one new flat <id>.bin next to already-imported subfolders -
    # doesn't silently leave one style unimported. "<id>_ghosts" directories are a
    # flat-style level's ghost folder, not a level of their own, so they're excluded here.
    subfolders = sorted(e for e in entries
                         if os.path.isdir(os.path.join(LEVELS_DIR, e)) and not e.endswith("_ghosts"))
    for minigameId in subfolders:
        try:
            if _importSubfolderLevel(minigameId):
                imported += 1
        except Exception as e:
            print(f"[LevelImport] Failed to import {minigameId!r} (subfolder): {e}")

    flatFiles = [e for e in entries if os.path.isfile(os.path.join(LEVELS_DIR, e))]
    flatIds = {os.path.splitext(e)[0].replace("_screenshot", "") for e in flatFiles}
    for minigameId in sorted(flatIds):
        try:
            if _importFlatLevel(minigameId, flatFiles):
                imported += 1
        except Exception as e:
            print(f"[LevelImport] Failed to import {minigameId!r} (flat file): {e}")

    return imported

# ---------------------------------------------------------------------
# SQLite Database Setup
# ---------------------------------------------------------------------
def getDbConnection():
    conn = sqlite3.connect(DB_FILE)
    conn.row_factory = sqlite3.Row
    return conn

def splitFileSizesBody(fileSizesHeader: str, body: bytes) -> list:
    if not fileSizesHeader:
        return [body] if body else []
    try:
        lengths = [int(x) for x in fileSizesHeader.split(",") if x.strip() != ""]
    except ValueError:
        return [body] if body else []
    segments = []
    offset = 0
    for length in lengths:
        segments.append(body[offset:offset + length])
        offset += length
    return segments

def upsertMinigameFromMetaSegment(metaJsonBytes: bytes, existingId: str = None) -> str:
    try:
        meta = json.loads(metaJsonBytes.decode("utf-8"))
    except Exception:
        meta = {}
    if not isinstance(meta, dict): meta = {}
    minigameId = existingId or safeStr(meta.get("id")).strip() or genOid()
    fields = {k: v for k, v in meta.items() if k in _VALID_MINIGAME_COLUMNS}
    fields["editorMeta"] = json.dumps(meta)
    upsertMinigame(minigameId, fields, levelData=None)
    return minigameId

def initDb():
    conn = getDbConnection()
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS players (
        id TEXT PRIMARY KEY,
        playerId TEXT,
        sessionId TEXT,
        name TEXT,
        tag TEXT DEFAULT '',
        coins INTEGER DEFAULT 2000000000,
        copper INTEGER DEFAULT 90,
        diamonds INTEGER DEFAULT 200000000,
        shards INTEGER DEFAULT 0,
        stars INTEGER DEFAULT 0,
        level INTEGER DEFAULT 1,
        mcBoosters INTEGER DEFAULT 50,
        maxMcBoosters INTEGER DEFAULT 99,
        carBoosters INTEGER DEFAULT 50,
        maxCarBoosters INTEGER DEFAULT 99,
        tournamentBoosters INTEGER DEFAULT 10,
        itemLevel INTEGER DEFAULT 1,
        cups INTEGER DEFAULT 0,
        mcRank INTEGER DEFAULT 1,
        carRank INTEGER DEFAULT 1,
        -- 3000 matches _LEAGUE_TROPHY_THRESHOLDS' top ("Big Bang") league threshold -
        -- the main-menu league BANNER is derived live from these raw trophy values
        -- (PsMetagameData.GetCurrentLeagueIndex), separately from mcRank/carRank
        -- (which only gate collectible unlocks, forced to MAX_LEAGUE_INDEX in
        -- getPlayerPayload) - without this, a brand new player would show the
        -- bottom league's banner while already having every league's items unlocked.
        mcTrophies INTEGER DEFAULT 3000,
        carTrophies INTEGER DEFAULT 3000,
        bigBangPoints INTEGER DEFAULT 0,
        completedAdventures INTEGER DEFAULT 0,
        racesWon INTEGER DEFAULT 0,
        goodOrBadLevelsRated INTEGER DEFAULT 0,
        xp INTEGER DEFAULT 0,
        gender TEXT DEFAULT 'male',
        ageGroup TEXT DEFAULT 'all',
        mcHandicap REAL DEFAULT 1.0,
        carHandicap REAL DEFAULT 1.0,
        fbClaimed INTEGER DEFAULT 0,
        igClaimed INTEGER DEFAULT 0,
        forumClaimed INTEGER DEFAULT 0,
        cardPurchases TEXT DEFAULT '',
        gachaData TEXT DEFAULT '',
        upgrades TEXT DEFAULT '{}',
        offroadCarUpgrades TEXT DEFAULT '{}',
        motorcycleUpgrades TEXT DEFAULT '{}',
        upgradesResources TEXT DEFAULT '{}',
        offroadCarVisual TEXT DEFAULT '{"MotocrossHelmet": true}',
        motorcycleVisual TEXT DEFAULT '{"MotocrossHelmet": true}',
        characterVisual TEXT DEFAULT '{"MotocrossHelmet": true}',
        offroadCarLevel INTEGER DEFAULT 0,
        motorcycleLevel INTEGER DEFAULT 0,
        chest TEXT DEFAULT '[]',
        acceptNotifications INTEGER DEFAULT 1,
        locale TEXT DEFAULT 'en',
        facebookId TEXT DEFAULT '',
        gameCenterId TEXT DEFAULT '',
        ninjaCreationTimestamp TEXT DEFAULT '',
        countryCode TEXT DEFAULT 'US',
        itemDbVersion INTEGER DEFAULT 1,
        teamId TEXT DEFAULT '',
        teamName TEXT DEFAULT '',
        teamRole TEXT DEFAULT 'Member',
        hasJoinedTeam INTEGER DEFAULT 0,
        teamKickReason TEXT DEFAULT '',
        lastSeasonEndCarTrophies INTEGER DEFAULT 0,
        lastSeasonEndMcTrophies INTEGER DEFAULT 0,
        seasonReward INTEGER DEFAULT 0,
        racesThisSeason INTEGER DEFAULT 0,
        youtuber TEXT DEFAULT '',
        youtuberId TEXT DEFAULT '',
        youtubeSubscriberCount INTEGER DEFAULT 0,
        coinDoubler INTEGER DEFAULT 0,
        dirtBikeBundle INTEGER DEFAULT 0,
        bundles TEXT DEFAULT '[]',
        trails TEXT DEFAULT '[]',
        purchasedHats TEXT DEFAULT '["MotocrossHelmet"]',
        pendingChests TEXT DEFAULT '[]',
        nameChangesDone INTEGER DEFAULT 0,
        editorResources TEXT DEFAULT '{}',
        claimedTutorials TEXT DEFAULT '[]',
        data TEXT DEFAULT '{}',
        progressionPaths TEXT DEFAULT '',
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP
    )''')

    c.execute('''CREATE TABLE IF NOT EXISTS follows (
        followerId TEXT,
        followeeId TEXT,
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (followerId, followeeId)
    )''')

    c.execute('''CREATE TABLE IF NOT EXISTS chatMessages (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        playerId TEXT DEFAULT '',
        name TEXT DEFAULT 'Player',
        facebookId TEXT DEFAULT '',
        gameCenterId TEXT DEFAULT '',
        tag TEXT DEFAULT '',
        comment TEXT DEFAULT '',
        timestamp INTEGER DEFAULT 0,
        type TEXT DEFAULT 'chat',
        teamName TEXT DEFAULT '',
        admin INTEGER DEFAULT 0,
        customData TEXT DEFAULT '{}'
    )''')

    # Server.Comment (client) backs BOTH team chat and level comments through the
    # same /v2/minigame/comment/save|find pair, keyed by a "gameId" param that's
    # really either a level id or (for team chat, PsUICenterTeamChat.cs) the
    # team's own id - so this table is keyed the same generic way.
    c.execute('''CREATE TABLE IF NOT EXISTS comments (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        gameId TEXT DEFAULT '',
        playerId TEXT DEFAULT '',
        name TEXT DEFAULT 'Player',
        facebookId TEXT DEFAULT '',
        gameCenterId TEXT DEFAULT '',
        tag TEXT DEFAULT '',
        comment TEXT DEFAULT '',
        timestamp INTEGER DEFAULT 0,
        admin INTEGER DEFAULT 0
    )''')
    c.execute('''CREATE INDEX IF NOT EXISTS idx_comments_gameId ON comments (gameId)''')

    # Per-player thumbs up/down on a level. PsUICenterWinRace initializes its thumb
    # buttons from PsState.m_activeGameLoop.GetRating(), which comes from the "rating"
    # key in that level's own metadata (ClientTools.ParseMinigameMetaData) - a STRING
    # among "Positive"/"Negative"/"Neutral"/etc, not the numeric upThumbs/downThumbs
    # aggregate. That per-player value has nowhere to live without this table, so the
    # win-screen always came back as neutral/unrated on every replay.
    c.execute('''CREATE TABLE IF NOT EXISTS levelRatings (
        gameId TEXT NOT NULL,
        playerId TEXT NOT NULL,
        rating TEXT NOT NULL DEFAULT 'Neutral',
        updatedAt TEXT DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (gameId, playerId)
    )''')

    # Singleton row (id=1) describing the one tournament this server ever runs.
    # ClientTools.ParseEventMessageFromDict / LoginFlow.cs expect the tournament's
    # rich metadata (minigameId etc.) to arrive as an eventType="Tournament" entry
    # inside the login's "eventList" - this table is what the admin GUI edits and
    # _buildTournamentEventMessage() turns into that entry.
    c.execute('''CREATE TABLE IF NOT EXISTS tournamentConfig (
        id INTEGER PRIMARY KEY CHECK (id = 1),
        tournamentId TEXT DEFAULT 'tour_main',
        minigameId TEXT DEFAULT '',
        header TEXT DEFAULT '',
        message TEXT DEFAULT '',
        prizeCoins INTEGER DEFAULT 500,
        ccCap REAL DEFAULT -1.0,
        playerUnit TEXT DEFAULT 'Any',
        useCreatorUpgrades INTEGER DEFAULT 0,
        acceptingNewScores INTEGER DEFAULT 1,
        ownerName TEXT DEFAULT '',
        startTime INTEGER DEFAULT 0,
        endTime INTEGER DEFAULT 0,
        floatingNode INTEGER DEFAULT 0
    )''')
    c.execute("PRAGMA table_info(tournamentConfig)")
    if "floatingNode" not in {col["name"] for col in c.fetchall()}:
        c.execute("ALTER TABLE tournamentConfig ADD COLUMN floatingNode INTEGER DEFAULT 0")
        print("[DB Migration] Added column 'tournamentConfig.floatingNode'")

    # Generic news-feed events (Event.GetFeed / PsUICenterNewsPopup.cs), same
    # EventMessage shape as the tournament entry above minus the tournament-specific
    # eventData sub-fields. Admin GUI adds/removes rows here directly.
    c.execute('''CREATE TABLE IF NOT EXISTS events (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        eventName TEXT DEFAULT '',
        eventType TEXT DEFAULT 'Event',
        header TEXT DEFAULT '',
        message TEXT DEFAULT '',
        label TEXT DEFAULT '',
        popup INTEGER DEFAULT 0,
        newsFeed INTEGER DEFAULT 1,
        startTime INTEGER DEFAULT 0,
        endTime INTEGER DEFAULT 0,
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP,
        floatingNode INTEGER DEFAULT 0,
        giftType TEXT DEFAULT '',
        giftIdentifier TEXT DEFAULT '',
        giftAmount INTEGER DEFAULT 0,
        giftTexture INTEGER DEFAULT -1
    )''')
    c.execute("PRAGMA table_info(events)")
    _eventsCols = {col["name"] for col in c.fetchall()}
    for col_name, col_def in (("floatingNode", "INTEGER DEFAULT 0"), ("giftType", "TEXT DEFAULT ''"),
                               ("giftIdentifier", "TEXT DEFAULT ''"), ("giftAmount", "INTEGER DEFAULT 0"),
                               ("giftTexture", "INTEGER DEFAULT -1")):
        if col_name not in _eventsCols:
            c.execute(f"ALTER TABLE events ADD COLUMN {col_name} {col_def}")
            print(f"[DB Migration] Added column 'events.{col_name}'")

    c.execute('''CREATE TABLE IF NOT EXISTS minigames (
        id TEXT PRIMARY KEY,
        name TEXT DEFAULT 'Unnamed Track',
        description TEXT DEFAULT '',
        creatorId TEXT DEFAULT 'system',
        creatorName TEXT DEFAULT 'System',
        creatorFacebookId TEXT DEFAULT '',
        creatorGameCenterId TEXT DEFAULT '',
        countryCode TEXT DEFAULT 'US',
        videoUrl TEXT DEFAULT '',
        gameMode TEXT DEFAULT 'Race',
        playerUnit TEXT DEFAULT 'Any',
        difficulty TEXT DEFAULT 'New',
        rating TEXT DEFAULT 'Unrated',
        state TEXT DEFAULT 'public',
        clientVersion INTEGER DEFAULT 371,
        gameQuality REAL DEFAULT 1.0,
        levelRequirement INTEGER DEFAULT 0,
        complexity INTEGER DEFAULT 0,
        researchIdentifier TEXT DEFAULT '',
        itemsUsed TEXT DEFAULT '[]',
        itemsCount TEXT DEFAULT '{}',
        publishTime TEXT DEFAULT '',
        timesPlayed INTEGER DEFAULT 0,
        timesLiked INTEGER DEFAULT 0,
        timesRated INTEGER DEFAULT 0,
        timesSuperLiked INTEGER DEFAULT 0,
        timesAbused INTEGER DEFAULT 0,
        upThumbs INTEGER DEFAULT 0,
        downThumbs INTEGER DEFAULT 0,
        bestTime INTEGER DEFAULT 0,
        totalWinners INTEGER DEFAULT 0,
        oneStarWinners INTEGER DEFAULT 0,
        twoStarWinners INTEGER DEFAULT 0,
        threeStarWinners INTEGER DEFAULT 0,
        participantCount INTEGER DEFAULT 0,
        rewardCoins INTEGER DEFAULT 0,
        totalCoinsEarned INTEGER DEFAULT 0,
        editSessionCount INTEGER DEFAULT 0,
        groundsModificationCount INTEGER DEFAULT 0,
        itemsModificationCount INTEGER DEFAULT 0,
        lastPlaySessionStartCount INTEGER DEFAULT 0,
        timeSpentInEditMode INTEGER DEFAULT 0,
        timeSpentEditing INTEGER DEFAULT 0,
        creatorUpgrades TEXT,
        overrideCC REAL DEFAULT -1.0,
        levelData BLOB,
        screenshot BLOB,
        creatorGhost BLOB,
        editorMeta TEXT DEFAULT '{}',
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP,
        updatedAt TEXT DEFAULT CURRENT_TIMESTAMP
    )''')

    # ---------------------------------------------------------------
    # Replicated 1:1 with official Traplight backend:
    # Separate `ghosts` table stores physical recorded runs.
    # ---------------------------------------------------------------
    c.execute('''CREATE TABLE IF NOT EXISTS ghosts (
        id TEXT PRIMARY KEY,
        gameId TEXT,
        playerId TEXT,
        name TEXT,
        playerUnit TEXT,
        time INTEGER DEFAULT 0,
        trophies INTEGER DEFAULT 0,
        countryCode TEXT DEFAULT 'US',
        facebookId TEXT DEFAULT '',
        gameCenterId TEXT DEFAULT '',
        teamId TEXT DEFAULT '',
        teamName TEXT DEFAULT '',
        trophyWin INTEGER DEFAULT 0,
        trophyLose INTEGER DEFAULT 0,
        ghostWin INTEGER DEFAULT 1,
        ghostLose INTEGER DEFAULT 0,
        version INTEGER DEFAULT 3,
        ghostData BLOB,
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP
    )''')

    c.execute('''CREATE TABLE IF NOT EXISTS scores (
        id TEXT PRIMARY KEY,
        gameId TEXT,
        playerId TEXT,
        playerName TEXT,
        playerUnit TEXT,
        time INTEGER DEFAULT 0,
        stars INTEGER DEFAULT 0,
        boost TEXT DEFAULT 'false',
        upgradeSum INTEGER DEFAULT 0,
        deathCount INTEGER DEFAULT 0,
        starts INTEGER DEFAULT 1,
        mainPath TEXT DEFAULT 'false',
        ghostData BLOB,
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP,
        ghostCountryCode TEXT DEFAULT '',
        ghostFacebookId TEXT DEFAULT '',
        ghostGameCenterId TEXT DEFAULT '',
        ghostTeamId TEXT DEFAULT '',
        ghostTeamName TEXT DEFAULT '',
        ghostTrophies INTEGER DEFAULT 0
    )''')

    # DATA REPAIR: hHighscoreSend/hTrophyScoreSend both insert into a
    # ghostData column - a scores table created before this column was added
    # to the CREATE TABLE above would 500 (silently, caught by _handle()'s
    # try/except) on every single race completion.
    c.execute("PRAGMA table_info(scores)")
    existingScoreCols = {row[1] for row in c.fetchall()}
    if "ghostData" not in existingScoreCols:
        try:
            c.execute("ALTER TABLE scores ADD COLUMN ghostData BLOB")
            print("[DB Migration] Added column 'scores.ghostData'")
        except sqlite3.OperationalError as e:
            print(f"[DB Migration] Could not add 'scores.ghostData': {e}")

    # DATA REPAIR: a ghost imported from a ghosts/<stem>.header file (or shared via
    # "Extract to ZIP") can carry countryCode/teamId/teamName/trophies that don't
    # belong to any LOCAL player row at all (an old-client dump's player was never
    # registered on this server) - without somewhere to keep that on the ghost's own
    # row, _syncLevelGhostsFolder had nowhere to put it but the bare name/time/
    # playerId, and it was silently discarded. These columns let a ghost's own header
    # data override the LEFT JOIN players fallback used everywhere ghosts are served
    # back out (see _buildGhostMetaDict) - empty/0 by default so a normal LIVE score
    # submission (a real, currently-registered player) is untouched and still reads
    # entirely from that player's own row, as before.
    for ghostCol, ghostColDef in [
        ("ghostCountryCode", "TEXT DEFAULT ''"), ("ghostFacebookId", "TEXT DEFAULT ''"),
        ("ghostGameCenterId", "TEXT DEFAULT ''"), ("ghostTeamId", "TEXT DEFAULT ''"),
        ("ghostTeamName", "TEXT DEFAULT ''"), ("ghostTrophies", "INTEGER DEFAULT 0"),
    ]:
        if ghostCol not in existingScoreCols:
            try:
                c.execute(f"ALTER TABLE scores ADD COLUMN {ghostCol} {ghostColDef}")
                print(f"[DB Migration] Added column 'scores.{ghostCol}'")
            except sqlite3.OperationalError as e:
                print(f"[DB Migration] Could not add 'scores.{ghostCol}': {e}")

    # DATA REPAIR: tournament runs used to be stored under a synthetic
    # "tournament:<tournamentId>" gameId shared by every tournament level ever
    # configured (see tournamentGameId()'s docstring) instead of the level's own
    # real id - those old rows can never be reached by anything anymore now that
    # tournament runs are stored under the level's actual id, so they're just
    # dead weight; clean them out rather than leaving stale data behind.
    c.execute("DELETE FROM scores WHERE gameId LIKE 'tournament:%'")
    if c.rowcount:
        print(f"[DB Migration] Removed {c.rowcount} orphaned tournament score row(s) "
              f"from the old synthetic gameId scheme")

    # Strip any already-persisted "Shared" planet path (see getPlayerPayload) - left
    # over from before that endpoint filtered it, it would crash any affected player's
    # client with a NullReferenceException in PlanetTools.CreateInitialLevelsIfNeeded
    # the next time they log in.
    c.execute("SELECT id, progressionPaths FROM players WHERE progressionPaths LIKE '%\"Shared\"%'")
    sharedRows = c.fetchall()
    fixedCount = 0
    for r in sharedRows:
        paths = safeJsonLoads(r["progressionPaths"], None)
        if not isinstance(paths, list): continue
        cleaned = [p for p in paths if not (isinstance(p, dict) and p.get("planet") == "Shared")]
        if len(cleaned) != len(paths):
            c.execute("UPDATE players SET progressionPaths = ? WHERE id = ?", (json.dumps(cleaned), r["id"]))
            fixedCount += 1
    if fixedCount:
        print(f"[DB Migration] Stripped stale 'Shared' planet path from {fixedCount} player(s)' "
              f"saved progression (crash-fix)")

    # -----------------------------------------------------------------
    # Teams: previously the players table had teamId/teamName/teamRole
    # columns but nothing ever created or persisted an actual team, so
    # creating a team silently did nothing. This table is the real
    # team entity; players.teamId points into it.
    # -----------------------------------------------------------------
    c.execute('''CREATE TABLE IF NOT EXISTS teams (
        id TEXT PRIMARY KEY,
        name TEXT DEFAULT '',
        tag TEXT DEFAULT '',
        description TEXT DEFAULT '',
        countryCode TEXT DEFAULT 'US',
        ownerId TEXT DEFAULT '',
        createdAt TEXT DEFAULT CURRENT_TIMESTAMP
    )''')

    # -----------------------------------------------------------------
    # AUTO-MIGRATION: Adds any missing columns to older game.db files
    # so existing accounts don't crash when new schema fields are added
    # -----------------------------------------------------------------
    c.execute("PRAGMA table_info(players)")
    existing_cols = {col["name"] for col in c.fetchall()}
    columns_to_add = [
        ("reward", "INTEGER DEFAULT 0"),
        ("completedAdventures", "INTEGER DEFAULT 0"),
        ("goodOrBadLevelsRated", "INTEGER DEFAULT 0"),
        ("youtuber", "TEXT DEFAULT ''"),
        ("youtuberId", "TEXT DEFAULT ''"),
        ("youtubeSubscriberCount", "INTEGER DEFAULT 0"),
        ("bundles", "TEXT DEFAULT '[]'"),
        ("trails", "TEXT DEFAULT '[]'"),
        ("purchasedHats", "TEXT DEFAULT '[\"MotocrossHelmet\"]'"),
        ("data", "TEXT DEFAULT '{}'"),
        ("progressionPaths", "TEXT DEFAULT ''"),
        ("locale", "TEXT DEFAULT 'en'"),
        ("tag", "TEXT DEFAULT ''"),
        ("offroadCarLevel", "INTEGER DEFAULT 0"),
        ("motorcycleLevel", "INTEGER DEFAULT 0"),
        ("nameChangesDone", "INTEGER DEFAULT 0"),
        ("editorResources", "TEXT DEFAULT '{}'"),
        ("claimedTutorials", "TEXT DEFAULT '[]'"),
        ("pendingChests", "TEXT DEFAULT '[]'"),
        ("coinDoubler", "INTEGER DEFAULT 0"),
        ("dirtBikeBundle", "INTEGER DEFAULT 0"),
        ("lastSeasonEndCarTrophies", "INTEGER DEFAULT 0"),
        ("lastSeasonEndMcTrophies", "INTEGER DEFAULT 0"),
        ("racesThisSeason", "INTEGER DEFAULT 0"),
        ("teamId", "TEXT DEFAULT ''"),
        ("teamName", "TEXT DEFAULT ''"),
        ("teamRole", "TEXT DEFAULT 'Member'"),
        ("hasJoinedTeam", "INTEGER DEFAULT 0"),
        ("teamKickReason", "TEXT DEFAULT ''"),
        ("itemDbVersion", "INTEGER DEFAULT 1"),
        ("customProfilePicture", "BLOB"),
    ]
    for col_name, col_def in columns_to_add:
        if col_name not in existing_cols:
            try:
                c.execute(f"ALTER TABLE players ADD COLUMN {col_name} {col_def}")
                print(f"[DB Migration] Added column 'players.{col_name}'")
            except sqlite3.OperationalError as e:
                print(f"[DB Migration] Could not add 'players.{col_name}': {e}")

    # Same story for 'teams': older game.db files were created before the
    # 'tag'/'countryCode' columns existed on this table, and CREATE TABLE
    # IF NOT EXISTS does nothing once the table is already there - so those
    # columns were silently missing, and INSERT INTO teams(...) crashed the
    # request with "table teams has no column named tag" on every attempt
    # to create a team.
    c.execute("PRAGMA table_info(teams)")
    existing_team_cols = {col["name"] for col in c.fetchall()}
    team_columns_to_add = [
        ("name", "TEXT DEFAULT ''"),
        ("tag", "TEXT DEFAULT ''"),
        ("description", "TEXT DEFAULT ''"),
        ("countryCode", "TEXT DEFAULT 'US'"),
        ("ownerId", "TEXT DEFAULT ''"),
        ("createdAt", "TEXT DEFAULT CURRENT_TIMESTAMP"),
    ]
    for col_name, col_def in team_columns_to_add:
        if col_name not in existing_team_cols:
            try:
                c.execute(f"ALTER TABLE teams ADD COLUMN {col_name} {col_def}")
                print(f"[DB Migration] Added column 'teams.{col_name}'")
            except sqlite3.OperationalError as e:
                print(f"[DB Migration] Could not add 'teams.{col_name}': {e}")

    # DATA REPAIR: the client's TeamRole enum only accepts exactly
    # "NotInTeam", "Creator" or "Member" - Enum.Parse() throws on anything
    # else, which is an *uncaught* exception in the client -> hard crash.
    # This field is included on every player payload (i.e. on every single
    # login), so a bad value here doesn't just break team screens, it
    # crashes the game on every startup until the DB value is corrected.
    # Earlier versions of this server wrote "Owner"/"Admin" instead of the
    # client's real "Creator" - fix up any rows still carrying those.
    ROLE_FIX_MAP = {"Owner": "Creator", "Admin": "Creator"}
    VALID_TEAM_ROLES = ("NotInTeam", "Creator", "Member")
    c.execute("SELECT id, teamRole FROM players WHERE teamRole IS NOT NULL AND teamRole NOT IN (?,?,?)", VALID_TEAM_ROLES)
    badRoleRows = c.fetchall()
    for row in badRoleRows:
        oldRole = row["teamRole"]
        newRole = ROLE_FIX_MAP.get(oldRole, "Member")
        c.execute("UPDATE players SET teamRole = ? WHERE id = ?", (newRole, row["id"]))
        print(f"[DB Migration] Fixed invalid players.teamRole '{oldRole}' -> '{newRole}' for player {row['id']}")

    # Tiny key/value store for admin-GUI preferences (language, dialog "don't ask
    # again" flags, etc.) - folded into the DB instead of its own JSON file so the
    # project keeps as few loose files on disk as possible.
    c.execute('''CREATE TABLE IF NOT EXISTS guiSettings (
        key TEXT PRIMARY KEY,
        value TEXT
    )''')

    # Seed the "secret hat" follow-reward NPC profiles (see FOLLOW_REWARD_USERS) so
    # they exist as real, searchable/followable players. INSERT OR IGNORE so re-running
    # this never clobbers anything if the admin GUI has since edited one of these rows.
    for fruId, fruName, fruTag, _hatId in FOLLOW_REWARD_USERS:
        c.execute("INSERT OR IGNORE INTO players (id, playerId, sessionId, name, tag) VALUES (?,?,?,?,?)",
                  (fruId, fruId, "", fruName, fruTag))

    # Before FOLLOW_REWARD_HATS existed, every player (including ones who logged in
    # before this feature was added) got these 10 hats unlocked for free via the old
    # "everyone gets every hat" merge in getPlayerPayload(). That merge no longer grants
    # them, but it also never TAKES BACK a key that's already persisted - so anyone who
    # logged in earlier still has them unlocked. Strip them back out here, unless the
    # player actually already follows the matching NPC (genuinely earned = keep it).
    c.execute("SELECT followerId, followeeId FROM follows WHERE followeeId IN ({})".format(
        ",".join("?" * len(FOLLOW_REWARD_USERS))), [u[0] for u in FOLLOW_REWARD_USERS])
    earnedPairs = {(r["followerId"], r["followeeId"]) for r in c.fetchall()}

    c.execute("SELECT id, characterVisual, offroadCarVisual, motorcycleVisual FROM players")
    for row in c.fetchall():
        pid = row["id"]
        updates = {}
        for col in ("characterVisual", "offroadCarVisual", "motorcycleVisual"):
            visDict = safeJsonLoads(row[col], None)
            if not isinstance(visDict, dict):
                continue
            newVisDict = dict(visDict)
            colChanged = False
            for fruId, _name, _tag, hatId in FOLLOW_REWARD_USERS:
                if hatId in newVisDict and (pid, fruId) not in earnedPairs:
                    del newVisDict[hatId]
                    colChanged = True
            if colChanged:
                updates[col] = newVisDict
        if updates:
            setParts = [f"{col} = ?" for col in updates]
            values = [json.dumps(v) for v in updates.values()] + [pid]
            c.execute(f"UPDATE players SET {', '.join(setParts)} WHERE id = ?", values)
            print(f"[DB Migration] Stripped un-earned follow-reward hat(s) from player {pid}")

    conn.commit()
    conn.close()
    print("[DB] SQLite database initialized.")

# ---------------------------------------------------------------------
# Player Helpers
# ---------------------------------------------------------------------
# League trophy thresholds (PsMetagameData.cs: League1..League8), index = league rank
# (0-based). mcRank/carRank gate which league-collectible reward tiers are unlocked
# (EventGiftUpgradeItem/PsGachaManager loop "for i in 0..rank"), separately from the
# league banner shown on the main menu (which is derived live from raw trophies via
# GetCurrentLeagueIndex and always looks correct even when rank is stale) - so if
# trophies are ever set directly (e.g. via the admin GUI) without the matching rank
# ever being incremented, the player LOOKS like they're in the top league but most of
# its collectibles stay locked, exactly as if every intermediate league was skipped.
_LEAGUE_TROPHY_THRESHOLDS = [0, 120, 400, 700, 1100, 1500, 2000, 3000]
MAX_LEAGUE_INDEX = len(_LEAGUE_TROPHY_THRESHOLDS) - 1  # 7 = top league ("Big Bang")

def leagueIndexForTrophies(trophies: int) -> int:
    idx = 0
    for i, threshold in enumerate(_LEAGUE_TROPHY_THRESHOLDS):
        if threshold <= trophies:
            idx = i
    return idx

# Every vehicle trail cosmetic identifier (PsCustomisationManager.cs) - the client only
# shows a trail as unlocked/selectable when its identifier is present in the player's
# "trails" list (ClientTools.ParsePlayerData -> PlayerStats.trailsPurchased). Includes
# the three PsRarity.Exclusive ones (trail_snow/trail_kittypaw/trail_anniversary) -
# PsUITrailSelectionView hides Exclusive items entirely unless already unlocked, so
# leaving them out would make them invisible rather than just locked.
ALL_VEHICLE_TRAILS = {
    "trail_bubble", "trail_feather", "trail_fire", "trail_cash", "trail_rainbow",
    "trail_scifi", "trail_death", "trail_bat", "trail_snow", "trail_kittypaw",
    "trail_anniversary",
}

# Every character hat identifier (PsCustomisationManager.cs, CustomisationCategory.HAT,
# m_characterCustomisationData). Unlike trails, a hat is unlocked purely by its
# identifier being PRESENT AS A KEY in the "CharacterVisual" dict (SetData's first
# check, line ~48: `if (dictionary3.ContainsKey(identifier)) unlocked = true`) - the
# boolean value only controls which one is currently worn/installed, not unlock
# status. The separate "purchasedHats" list (-> PlayerStats.hatsPurchased) is checked
# against each item's IAP sku (m_iapIdentifier) in a second, vehicle-loop-only unlock
# path - populated too as a defensive extra, using the non-empty IAP ids below.
ALL_HATS = {
    "MotocrossHelmet", "BaseballHat", "MushroomHat", "BarbarianHelmet", "CowboyHat",
    "HorseHead", "BootHat", "WitchHat", "GirlyHair", "ChickenHat", "KnightHelmet",
    "Mask", "PaperBag", "PilotHat", "DealWithItGlasses", "PumpkinHat", "GoldenShades",
    "Fish", "VR", "WerewolfMask", "Helmet", "MrBaconHair", "ReversalCrown", "HawkMask",
    "SteelMask", "PowerHelmet", "CatHat", "FeatherHat", "OrangeHat", "ToadHat",
    "BuilderHat", "WinterHat", "WinterCap", "UnicornMask", "LovelyHat", "ReindeerHat",
    "GoldenCarHelmet", "AnglerFishHat", "BobbleHat", "MilkJugHat", "TimeTravellerHat",
    "LorpHeadband", "AnniversaryPartyHat", "AnniversaryCandleHat", "IceCreamHat",
}
ALL_HAT_IAP_IDS = {
    "hat_common_mushroomhat", "hat_common_barbarianhelmet", "hat_common_cowboyhat",
    "hat_common_horsehead", "hat_common_boothat", "hat_common_witchhat",
    "hat_common_girlyhair", "hat_rare_chickenhat", "hat_rare_knighthelmet",
    "hat_rare_mask", "hat_rare_paperbag", "hat_rare_pilothat",
    "hat_rare_dealwithitglasses", "hat_rare_pumpkinhat", "hat_epic_goldenshades",
    "hat_epic_fish", "hat_epic_vr", "hat_epic_werewolfmask",
}

# "Secret hat" NPC accounts from the original game's creator-partnership program -
# following one of these grants a hidden hat (PsUIHiddenHatPopup, "Hat found!" popup).
# Entirely client-driven: PsUIFollowButton.FollowCreator() reads
# PsMetagameManager.GetFollowRewards(targetPlayerId), which just looks up
# PsMetagameManager.m_followRewardData - a list parsed ONCE at login time
# (ClientTools.ParseFollowRewadData, Server/LoginFlow.cs:322) from the login
# response's "followRewardUsers": [{"id", "facebookId", "followRewards": [...]}] (see
# the "followRewardUsers" key built into the login payload below). If the reward
# hat is already unlocked, FollowCreator() silently skips it (itemByIdentifier.m_unlocked
# check) - so these 10 hats must be excluded from the "everyone gets every hat" merge
# in getPlayerPayload() below, or the popup/unlock never fires. ids are arbitrary
# (hardcoded, never logged into for real); names/tags match the real accounts.
FOLLOW_REWARD_USERS = [
    ("fru_camarobro",    "CamaroBro",        "c8nop", "BobbleHat"),
    ("fru_drbuttfarts2", "Dr. Buttfarts II", "j1h9",  "OrangeHat"),
    ("fru_larploggins",  "Larp Loggins",     "rdt2",  "LorpHeadband"),
    ("fru_alvaro845",    "Alvaro845",        "bw5c",  "CatHat"),
    ("fru_nickatnyte",   "nickatnyte",       "n1u7",  "AnglerFishHat"),
    ("fru_papajake",     "PapaJake",         "dbwmb", "MilkJugHat"),
    ("fru_reversal",     "Reversal",         "bw5d",  "ReversalCrown"),
    ("fru_androimers",   "AndroiMers",       "bw5a",  "MrBaconHair"),
    ("fru_dejotacdi",    "DeJota CDI",       "b2wyu", "TimeTravellerHat"),
    ("fru_bootrampyt",   "BootrampYoutube",  "bw48",  "SteelMask"),
]
FOLLOW_REWARD_HATS = {row[3] for row in FOLLOW_REWARD_USERS}

# Every garage upgrade item identifier (PsUpgradeManager.GetDefaultUpgradeItems) - 4
# stat categories (Speed/Grip/Handling/Special, covering things like turbo/speed,
# grip "spikes", flip-boost power/count/duration, nitro count, coin magnet etc, all
# folded under "Special") x 6 card-rarity tiers each, per vehicle. Sent back verbatim
# in OffroadCarUpgrades/MotorcycleUpgrades as {identifier: level}; the client clamps
# whatever level we send to that item's own real max via
# Mathf.Clamp(_currentLevel, 0, m_maxLevel) (PsUpgradeItem.SetCurrentLevel), so a
# single safely-large flat level works for every item without needing each one's
# actual (and differing, by rarity) individual max level.
MAX_UPGRADE_LEVEL = 99
ALL_CAR_UPGRADES = {
    "CarSpeed1", "CarSpeed2", "CarSpeed3", "CarSpeed4", "CarSpeed5", "CarSpeed6",
    "CarGrip1", "CarGrip2", "CarGrip3", "CarGrip4", "CarGrip5", "CarGrip6",
    "CarHandling1", "CarHandling2", "CarHandling3", "CarHandling4", "CarHandling5", "CarHandling6",
    "CarSpecial1", "CarSpecial2", "CarSpecial3", "CarSpecial4", "CarSpecial5", "CarSpecial6",
}
ALL_MC_UPGRADES = {
    "Speed1", "Speed2", "Speed3", "Speed4", "Speed5", "Speed6",
    "Grip1", "Grip2", "Grip3", "Grip4", "Grip5", "Grip6",
    "Handling1", "Handling2", "Handling3", "Handling4", "Handling5", "Handling6",
    "Special1", "Special2", "Special3", "Special4", "Special5", "Special6",
}

# Valid "identifier" values per gift eventData["type"] (EventGift*.cs, ClientTools.cs:
# 255-316) - used by the admin GUI to populate the Identifier dropdown for whichever
# Gift Type is selected. "editorItem" has no canonical list here (any real
# PsEditorItem.m_identifier), so it's left free-text.
_GIFT_IDENTIFIER_CHOICES = {
    "upgradeItem": ["Common", "Rare", "Epic", "Exclusive"],
    "chest": ["WOOD", "COMMON", "BRONZE", "SILVER", "GOLD", "RARE", "EPIC", "SUPER", "BOSS"],
    "resource": ["coins", "gems", "nitros"],
    "hat": sorted(ALL_HATS),
    "trail": sorted(ALL_VEHICLE_TRAILS),
    "timed": ["goldCoinStreak", "unlimitedNitros", "upgrade50discount", "upgradeItem90discount"],
    "editorItem": [],
}


def getFollowPlayerDict(playerRow: sqlite3.Row) -> dict:
    pId = safeStr(rowGet(playerRow, ["id", "playerId"], ""))
    pTag = safeStr(rowGet(playerRow, ["tag"], ""))
    
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT COUNT(*) AS count FROM minigames WHERE creatorId = ? AND state = 'public'", (pId,))
    pubCount = safeInt(c.fetchone()["count"], 0)
    conn.close()

    return {
        "id": pId,
        "playerId": pId,
        "name": safeStr(rowGet(playerRow, ["name"], "Player")),
        "tag": pTag,
        "level": safeInt(rowGet(playerRow, ["level"], 1)),
        "mcRank": MAX_LEAGUE_INDEX,
        "carRank": MAX_LEAGUE_INDEX,
        "mcTrophies": safeInt(rowGet(playerRow, ["mcTrophies"], 0)),
        "carTrophies": safeInt(rowGet(playerRow, ["carTrophies"], 0)),
        "facebookId": safeStr(rowGet(playerRow, ["facebookId"], "")),
        "gameCenterId": safeStr(rowGet(playerRow, ["gameCenterId"], "")),
        "countryCode": safeStr(rowGet(playerRow, ["countryCode"], "US")),
        "youtuber": safeStr(rowGet(playerRow, ["youtuber", "youtubeName"], "")),
        "youtubeName": safeStr(rowGet(playerRow, ["youtuber", "youtubeName"], "")),
        "youtuberId": safeStr(rowGet(playerRow, ["youtuberId", "youtubeId"], "")),
        "youtubeId": safeStr(rowGet(playerRow, ["youtuberId", "youtubeId"], "")),
        "youtubeSubscriberCount": safeInt(rowGet(playerRow, ["youtubeSubscriberCount"], 0)),
        "publishedMinigameCount": pubCount
    }

DEFAULT_PATHS = [
    {
        "name": "MainPath", "type": "Main", "planet": "AdventureOffroadCar",
        "currentNode": 1, "startNode": 1,
        "nodes": [{"id": 1, "levelNumber": 1, "score": 0}]
    }
]

def getPlayerPayload(playerRow: sqlite3.Row) -> dict:
    pId = safeStr(rowGet(playerRow, ["id", "playerId"], ""))
    pName = safeStr(rowGet(playerRow, ["name"], "Player"))
    pTag = safeStr(rowGet(playerRow, ["tag"], ""))

    storedMcTrophies = safeInt(rowGet(playerRow, ["mcTrophies"], 0))
    storedCarTrophies = safeInt(rowGet(playerRow, ["carTrophies"], 0))
    storedMcRank = safeInt(rowGet(playerRow, ["mcRank"], 1))
    storedCarRank = safeInt(rowGet(playerRow, ["carRank"], 1))
    # Every league-collectible reward tier unlocked for every player (current and
    # future) by pinning mcRank/carRank to the top league's index, rather than just
    # catching them up to what current trophies would justify. Trophies themselves are
    # floored to that same top league's threshold too - PlayerStats.trophies (which
    # drives the main-menu league BANNER, separately from mcRank/carRank) reads raw
    # mcTrophies/carTrophies directly, so without this a new player would show the
    # bottom league's banner while already having every league's items unlocked.
    # players.mcTrophies/carTrophies do default to this value now, but that default
    # only takes effect on a brand-new game.db - CREATE TABLE IF NOT EXISTS doesn't
    # retroactively change an existing table's column default, hence flooring here too.
    minTrophies = _LEAGUE_TROPHY_THRESHOLDS[MAX_LEAGUE_INDEX]
    mcRankVal = MAX_LEAGUE_INDEX
    carRankVal = MAX_LEAGUE_INDEX
    mcTrophiesVal = max(storedMcTrophies, minTrophies)
    carTrophiesVal = max(storedCarTrophies, minTrophies)
    storedTrails = safeJsonLoads(rowGet(playerRow, ["trails", "trailsPurchased"], "[]"), [])
    if not isinstance(storedTrails, list): storedTrails = []
    trails = sorted(set(storedTrails) | ALL_VEHICLE_TRAILS)
    trailsChanged = set(trails) != set(storedTrails)

    storedCharVis = safeJsonLoads(rowGet(playerRow, ["characterVisual"], '{"MotocrossHelmet": true}'),
                                   {"MotocrossHelmet": True})
    if not isinstance(storedCharVis, dict): storedCharVis = {"MotocrossHelmet": True}
    charVis = dict(storedCharVis)
    # FOLLOW_REWARD_HATS excluded here - those must stay locked (absent as a key)
    # until actually earned by following the matching NPC, at which point the client's
    # own SetData call persists them into storedCharVis directly, so dict(storedCharVis)
    # above already carries them forward once earned.
    for hatId in ALL_HATS - FOLLOW_REWARD_HATS:
        if hatId not in charVis:
            charVis[hatId] = False  # unlocked (present as a key) but not the equipped one
    charVisChanged = charVis != storedCharVis

    # PsCustomisationManager.SetData unlocks hats from CharacterVisual unconditionally
    # (present as a key = unlocked, same as above), but the hat list actually shown/
    # selectable per-vehicle (what you see while riding) comes from a SEPARATE,
    # per-vehicle customisation dataset gated by OffroadCarVisual/MotorcycleVisual -
    # without the same ALL_HATS merge here, only whatever subset the old
    # achievement/IAP-purchased checks happen to satisfy shows as unlocked there,
    # even though CharacterVisual already reports everything unlocked.
    storedCarVis = safeJsonLoads(rowGet(playerRow, ["offroadCarVisual"], '{"MotocrossHelmet": true}'),
                                  {"MotocrossHelmet": True})
    if not isinstance(storedCarVis, dict): storedCarVis = {"MotocrossHelmet": True}
    carVisVal = dict(storedCarVis)
    for cosmeticId in (ALL_HATS - FOLLOW_REWARD_HATS) | ALL_VEHICLE_TRAILS:
        if cosmeticId not in carVisVal:
            carVisVal[cosmeticId] = False
    carVisChanged = carVisVal != storedCarVis

    storedMcVis = safeJsonLoads(rowGet(playerRow, ["motorcycleVisual"], '{"MotocrossHelmet": true}'),
                                 {"MotocrossHelmet": True})
    if not isinstance(storedMcVis, dict): storedMcVis = {"MotocrossHelmet": True}
    mcVisVal = dict(storedMcVis)
    for cosmeticId in (ALL_HATS - FOLLOW_REWARD_HATS) | ALL_VEHICLE_TRAILS:
        if cosmeticId not in mcVisVal:
            mcVisVal[cosmeticId] = False
    mcVisChanged = mcVisVal != storedMcVis

    storedHats = safeJsonLoads(rowGet(playerRow, ["purchasedHats", "hatsPurchased"], '["MotocrossHelmet"]'),
                                ["MotocrossHelmet"])
    if not isinstance(storedHats, list): storedHats = ["MotocrossHelmet"]
    hats = sorted(set(storedHats) | ALL_HAT_IAP_IDS)
    hatsChanged = set(hats) != set(storedHats)

    storedCarUpgrades = safeJsonLoads(rowGet(playerRow, ["offroadCarUpgrades"], "{}"), {})
    if not isinstance(storedCarUpgrades, dict): storedCarUpgrades = {}
    carUpgradesVal = dict(storedCarUpgrades)
    for upgId in ALL_CAR_UPGRADES:
        carUpgradesVal[upgId] = MAX_UPGRADE_LEVEL
    carUpgradesChanged = carUpgradesVal != storedCarUpgrades

    storedMcUpgrades = safeJsonLoads(rowGet(playerRow, ["motorcycleUpgrades"], "{}"), {})
    if not isinstance(storedMcUpgrades, dict): storedMcUpgrades = {}
    mcUpgradesVal = dict(storedMcUpgrades)
    for upgId in ALL_MC_UPGRADES:
        mcUpgradesVal[upgId] = MAX_UPGRADE_LEVEL
    mcUpgradesChanged = mcUpgradesVal != storedMcUpgrades

    if pId and (mcRankVal != storedMcRank or carRankVal != storedCarRank
                or mcTrophiesVal != storedMcTrophies or carTrophiesVal != storedCarTrophies
                or trailsChanged or charVisChanged or hatsChanged
                or carUpgradesChanged or mcUpgradesChanged or carVisChanged or mcVisChanged):
        conn = getDbConnection()
        conn.cursor().execute(
            "UPDATE players SET mcRank = ?, carRank = ?, mcTrophies = ?, carTrophies = ?, trails = ?, "
            "characterVisual = ?, purchasedHats = ?, offroadCarUpgrades = ?, motorcycleUpgrades = ?, "
            "offroadCarVisual = ?, motorcycleVisual = ? WHERE id = ?",
            (mcRankVal, carRankVal, mcTrophiesVal, carTrophiesVal, json.dumps(trails),
             json.dumps(charVis), json.dumps(hats), json.dumps(carUpgradesVal), json.dumps(mcUpgradesVal),
             json.dumps(carVisVal), json.dumps(mcVisVal), pId))
        conn.commit(); conn.close()

    # Every one of these gets an isinstance fallback, same as trails/charVis/carVis/
    # mcVis/hats/carUpgrades/mcUpgrades above - not just belt-and-suspenders. Confirmed
    # against the decompiled client that a wrong-shaped value here is NOT just silently
    # ignored: ClientTools.ParsePlayerData's ParsePlayerUpgrades(_dictionary["upgrades"]
    # as Dictionary<string,object>) does an UNGUARDED `foreach (_dictionary.Keys)` with
    # no null check, and claimedTutorials does `(_dictionary["claimedTutorials"] as
    # List<object>).ToArray()` - calling .ToArray() on the null result of a failed `as`
    # cast - so a stray non-dict "upgrades" or non-list "claimedTutorials"/"bundles" (the
    # admin GUI's generic "More..." row editor accepts any text for these JSON columns,
    # no shape validation) throws an unhandled NullReferenceException at the next login,
    # crashing the client before it ever reaches the main menu.
    upgrades    = safeJsonLoads(rowGet(playerRow, ["upgrades"], "{}"), {})
    if not isinstance(upgrades, dict): upgrades = {}
    upgRes      = safeJsonLoads(rowGet(playerRow, ["upgradesResources"], "{}"), {})
    if not isinstance(upgRes, dict): upgRes = {}
    carVis      = carVisVal
    mcVis       = mcVisVal
    chestSlots  = safeJsonLoads(rowGet(playerRow, ["chest"], "[]"), [])
    if not isinstance(chestSlots, list): chestSlots = []
    bundles     = safeJsonLoads(rowGet(playerRow, ["bundles", "bundlesPurchased"], "[]"), [])
    if not isinstance(bundles, list): bundles = []
    chests      = safeJsonLoads(rowGet(playerRow, ["pendingChests"], "[]"), [])
    if not isinstance(chests, list): chests = []
    editorRes   = safeJsonLoads(rowGet(playerRow, ["editorResources"], "{}"), {})
    if not isinstance(editorRes, dict): editorRes = {}
    tutorials   = safeJsonLoads(rowGet(playerRow, ["claimedTutorials"], "[]"), [])
    if not isinstance(tutorials, list): tutorials = []
    dataKv      = safeJsonLoads(rowGet(playerRow, ["data", "customData"], "{}"), {})
    if not isinstance(dataKv, dict): dataKv = {}
    savedPaths  = safeJsonLoads(rowGet(playerRow, ["progressionPaths"], None), None)
    if isinstance(savedPaths, list):
        # The "Shared" planet is a client-only virtual container for floating nodes
        # (events/tournaments/gifts/Fresh&Free) - PsFloaters.AddFloaters() rebuilds it
        # fresh from live floater data every session (PlanetTools.ChangePlanet, right
        # after the loop below). It has no InitialData/unlock graph of its own, so if we
        # echo a persisted "planet":"Shared" path back, PlanetTools.ChangePlanet's loop
        # over every known planet calls PsMetagameData.GetNextUnlock("Shared", ...),
        # which finds no entry, logs "No planet with identifier: Shared", and returns
        # null - then CreateInitialLevelsIfNeeded dereferences nextUnlock.m_name and the
        # client crashes with a NullReferenceException right as the main menu loads.
        savedPaths = [p for p in savedPaths if not (isinstance(p, dict) and p.get("planet") == "Shared")]

    currentMs = nowEpochMs()
    availablePlanets = getAvailablePlanets()
    if not availablePlanets:
        availablePlanets = [
            {"planet": "AdventureOffroadCar", "version": 1},
            {"planet": "AdventureMotorcycle", "version": 1},
            {"planet": "RacingOffroadCar", "version": 1},
            {"planet": "RacingMotorcycle", "version": 1},
        ]

    # Computed once up front: both "eventList" (feeds the News Feed screen, gifts and
    # tournaments) and "eventMessage" (the actual login popup/floating-node trigger -
    # see _selectLoginEventMessage) are built from the same underlying event set.
    eventMessages = getAllEventMessages()
    payload = {
        "id": pId,
        "playerId": pId,
        "name": pName,
        "tag": pTag,
        "sessionId": safeStr(rowGet(playerRow, ["sessionId"], "")),
        "coins": safeInt(rowGet(playerRow, ["coins"], 2000000000)),
        "copper": safeInt(rowGet(playerRow, ["copper"], 90)),
        "diamonds": safeInt(rowGet(playerRow, ["diamonds"], 200000000)),
        "shards": safeInt(rowGet(playerRow, ["shards"], 0)),
        "stars": safeInt(rowGet(playerRow, ["stars"], 0)),
        "level": safeInt(rowGet(playerRow, ["level"], 1)),
        "mcBoosters": safeInt(rowGet(playerRow, ["mcBoosters"], 50)),
        "maxMcBoosters": safeInt(rowGet(playerRow, ["maxMcBoosters"], 99)),
        "carBoosters": safeInt(rowGet(playerRow, ["carBoosters"], 50)),
        "maxCarBoosters": safeInt(rowGet(playerRow, ["maxCarBoosters"], 99)),
        "tournamentBoosters": safeInt(rowGet(playerRow, ["tournamentBoosters"], 10)),
        "itemLevel": safeInt(rowGet(playerRow, ["itemLevel"], 1)),
        "cups": safeInt(rowGet(playerRow, ["cups"], 0)),
        "mcRank": mcRankVal,
        "carRank": carRankVal,
        "mcTrophies": mcTrophiesVal,
        "carTrophies": carTrophiesVal,
        "bigBangPoints": safeInt(rowGet(playerRow, ["bigBangPoints"], 0)),
        "completedAdventures": safeInt(rowGet(playerRow, ["completedAdventures", "adventureLevelsCompleted"], 0)),
        "racesWon": safeInt(rowGet(playerRow, ["racesWon"], 0)),
        # ClientTools.ParsePlayerData reads totalLikes/totalSuperLikes straight off the
        # LOGIN response too (Server/LoginFlow.cs -> PsMetagameManager.SetPlayer ->
        # m_playerStats.likesEarned = totalLikes) - before this, only /v2/minigame/own
        # (the "My Levels"/Create screen) ever sent it, so likesEarned stayed stuck at
        # its C# default (0) from a cold app launch/resume until that screen was
        # visited, making editor items that unlock at a like-count threshold show
        # greyed out ("earn N more likes") even though the player already has plenty -
        # visiting "My Levels" (or leaving/re-entering, which happens to trigger the
        # same refetch) was the only thing that fixed it for the rest of that session.
        "totalLikes": 10000000, "totalSuperLikes": 0,
        "goodOrBadLevelsRated": safeInt(rowGet(playerRow, ["goodOrBadLevelsRated", "newLevelsRated"], 0)),
        "xp": safeInt(rowGet(playerRow, ["xp"], 0)),
        "gender": safeStr(rowGet(playerRow, ["gender"], "male")),
        "ageGroup": safeStr(rowGet(playerRow, ["ageGroup"], "all")),
        "mcHandicap": float(rowGet(playerRow, ["mcHandicap"], 1.0) or 1.0),
        "carHandicap": float(rowGet(playerRow, ["carHandicap"], 1.0) or 1.0),
        "fbClaimed": bool(rowGet(playerRow, ["fbClaimed"], 0)),
        "igClaimed": bool(rowGet(playerRow, ["igClaimed"], 0)),
        "forumClaimed": bool(rowGet(playerRow, ["forumClaimed"], 0)),
        "cardPurchases": sanitizeCardPurchases(rowGet(playerRow, ["cardPurchases"], "")),
        "gachaData": sanitizeGachaData(rowGet(playerRow, ["gachaData"], "")),
        "upgrades": upgrades,
        "OffroadCarUpgrades": carUpgradesVal,
        "MotorcycleUpgrades": mcUpgradesVal,
        "UpgradesResources": upgRes,
        "OffroadCarVisual": carVis,
        "MotorcycleVisual": mcVis,
        "CharacterVisual": charVis,
        "chest": chestSlots,
        "acceptNotifications": bool(rowGet(playerRow, ["acceptNotifications"], 1)),
        "locale": safeStr(rowGet(playerRow, ["locale"], "en")),
        "facebookId": safeStr(rowGet(playerRow, ["facebookId"], "")),
        "gameCenterId": safeStr(rowGet(playerRow, ["gameCenterId"], "")),
        "ninjaCreationTimestamp": safeStr(rowGet(playerRow, ["ninjaCreationTimestamp"], "")),
        "countryCode": safeStr(rowGet(playerRow, ["countryCode"], "US")),
        "itemDbVersion": safeInt(rowGet(playerRow, ["itemDbVersion"], 1)),
        "teamId": safeStr(rowGet(playerRow, ["teamId"], "")),
        "teamName": safeStr(rowGet(playerRow, ["teamName"], "")),
        "teamRole": safeStr(rowGet(playerRow, ["teamRole"], "Member")),
        "hasJoinedTeam": bool(rowGet(playerRow, ["hasJoinedTeam"], 0)),
        "teamKickReason": safeStr(rowGet(playerRow, ["teamKickReason"], "")),
        "lastSeasonEndCarTrophies": safeInt(rowGet(playerRow, ["lastSeasonEndCarTrophies"], 0)),
        "lastSeasonEndMcTrophies": safeInt(rowGet(playerRow, ["lastSeasonEndMcTrophies"], 0)),
        "reward": safeInt(rowGet(playerRow, ["reward", "seasonReward"], 0)),
        "racesThisSeason": safeInt(rowGet(playerRow, ["racesThisSeason"], 0)),
        "youtuber": safeStr(rowGet(playerRow, ["youtuber", "youtubeName"], "")),
        "youtuberId": safeStr(rowGet(playerRow, ["youtuberId", "youtubeId"], "")),
        "youtubeSubscriberCount": safeInt(rowGet(playerRow, ["youtubeSubscriberCount"], 0)),
        "coinDoubler": bool(rowGet(playerRow, ["coinDoubler"], 0)),
        "dirtBikeBundle": bool(rowGet(playerRow, ["dirtBikeBundle"], 0)),
        "bundles": bundles,
        "trails": trails,
        "purchasedHats": hats,
        "pendingChests": chests,
        "nameChangesDone": safeInt(rowGet(playerRow, ["nameChangesDone"], 0)),
        "editorResources": editorRes,
        "claimedTutorials": tutorials,
        "data": dataKv,
        "clientVersion": MIN_BUILD_VERSION,
        "previousLoginClientVersion": "371 IPhonePlayer",
        "versionInfo": "Your client is up to date.",
        "ratingStatus": 0, "newCommentCount": 0, "unclaimedLevels": 0,
        "epochDays": 1, "daySecondsLeft": 86400,
        "firstSeen": {"$date": currentMs},
        "lastLogin": {"$date": currentMs},
        "sessionExpiration": False, "lastPathSync": "0",
        "cheater": False, "developer": False, "completedSurvey": False,
        "clientConfig": {
            "triesForAd": 3, "triesForGems": 5, "triesGemPrice": 15,
            "carRefreshMinutes": 6, "superLikeRefreshHours": 360,
            "freshFreeInterval": 15, "fbConnectRewardAmount": 20,
            "dailyGemAmount": 10, "videoAdCount": 2, "videoAdCoolDown": 3600,
            "freshFreeCount": 3, "freshFreeCoolDown": 1800,
            "inRaceDiamondSpawnProbability": 25, "offerCooldownMinutes": 4320,
            "offerDurationMinutes": 60, "minimumTournamentNitros": 5,
            "tournamentYoutuberFollowNitros": 5, "minimumRentPrice": 10,
            "rentDiamondMultiplier": 1.0, "versusChallengeTryAmount": 3,
            "versusTokenMaxCount": 5, "versusRankCap": 100, "gemShopEnabled": True
        },
        "playerConfig": {"coins": 1000, "diamonds": 50, "bolts": 0, "keys": 5},
        "mcBoosterRefreshEnd": {"$date": currentMs},
        "carBoosterRefreshEnd": {"$date": currentMs},
        "superLikeRefreshEnd": {"$date": currentMs},
        "paths": savedPaths if savedPaths else DEFAULT_PATHS,
        "planetVersions": availablePlanets,
        # tournamentId here MUST match the eventType="Tournament" entry in eventList
        # below - LoginFlow.cs finds the tournament EventMessage by this id and
        # stamps room/time/claimed onto it. See getTournamentConfig().
        # "tournamentTime" here is NOT a room/matchmaking timer despite the name - it's
        # this player's own current best tournament time, in the same raw score units
        # scores.time already uses (PsGameLoopTournament.StartLoop: tournament.time != 0
        # -> m_timeScoreBest = tournament.time, i.e. it seeds "your personal best" before
        # the real leaderboard has even loaded). A hardcoded 3600 here always rendered as
        # a fixed, wrong "00.060" (HighScores.TimeScoreToTime: 3600/1000/60 = 0.06) and
        # could never move no matter what the player actually ran.
        "activeTournament": {
            "tournamentId": safeStr(getTournamentConfig().get("tournamentId"), "tour_main"),
            "tournamentRoom": 1, "tournamentTime": _getPlayerTournamentBestTime(pId),
            "superFuelBought": False,
            "claimed": True, "youtubeNitrosClaimed": True
        },
        "tournamentRewardShares": DEFAULT_TOURNAMENT_SHARES,
        "eventList": eventMessages, "eventMessage": _selectLoginEventMessage(eventMessages), "patchNotes": None,
        "lastClaimedGiftId": 0, "adsConfig": [],
        "seasonConfig": {"seasonNumber": 1, "endTime": nowIso()},
        # ClientTools.ParseSeasonEndData reads these two straight off the login
        # response root (LoginFlow.cs) into the static PsMetagameManager.m_seasonEndData.
        # Without "currentSeason" that field just stays null forever, and every screen
        # that touches it unguarded (PsUICenterTopTeams/PsUICenterPlayerLeaderboards'
        # CreateSeasonTop(), which reads m_seasonEndData.currentSeason.number
        # synchronously in their constructor) crashes the instant it's opened - this is
        # the "Meilleures/Meilleurs" crash. currentSeason.number == latestSeason.number
        # keeps SeasonEndData.hasSeasonEnded() false so no "season just ended" flow
        # fires unexpectedly.
        "currentSeason": {"number": 1, "timeLeft": 2592000},
        "latestSeason": {"number": 1, "timeLeft": 2592000},
        "seasonTeamReward": 0,
        "teamEligibleForRewards": True,
        "iapConfig": {
            "products": [
                {"productId": "gems_pack_small", "price": 0.99, "gems": 100, "coins": 0},
                {"productId": "coins_pack_small", "price": 0.99, "gems": 0, "coins": 5000}
            ]
        },
        "gemPriceConfig": {"skipTimerCost": 1, "convertCoinsMultiplier": 10},
        "editorConfig": {"complexityLimit": 1500, "customItemLimits": {}},
        "bossBattleConfig": {"startHandicap": 1.0, "handicapAlterStep": 0.1},
        "achievements": [],
        # ClientTools.ParseFollowRewadData (Server/LoginFlow.cs:322) parses this ONCE at
        # login into PsMetagameManager.m_followRewardData - following one of these ids
        # in-game unlocks the paired hat and shows the "Hat found!" popup, client-side,
        # the next time FollowCreator() runs (no further server involvement needed; see
        # FOLLOW_REWARD_USERS above).
        "followRewardUsers": [
            {"id": fruId, "followRewards": [hatId]}
            for fruId, _fruName, _fruTag, hatId in FOLLOW_REWARD_USERS
        ],
    }

    resourceStr = (
        f"{payload['coins']}{payload['diamonds']}{payload['maxMcBoosters']}"
        f"{payload['level']}{payload['copper']}{payload['stars']}{payload['itemLevel']}"
        f"{payload['cups']}{payload['mcRank']}{payload['carRank']}{payload['mcTrophies']}"
        f"{payload['carTrophies']}{payload['xp']}"
    )
    payload["hash"] = generatePlayHash("/v4/player/login", resourceStr)
    return payload

def rebindPlayerId(conn, oldId: str, newId: str):
    """
    Move an existing player row from oldId to newId, repointing every
    foreign-key-like reference to it. Used when a device shows up with a new
    UDID (e.g. after an app reinstall) but we've matched it to an existing
    account by name, so we don't want to silently create a fresh, empty
    profile and orphan the player's real progress.
    """
    c = conn.cursor()

    # Drop any of newId's own rows that would become duplicates once
    # repointed onto oldId's data (newId is expected to be a brand new,
    # essentially empty profile at this point).
    c.execute("SELECT followeeId FROM follows WHERE followerId = ?", (oldId,))
    oldFollowees = {r["followeeId"] for r in c.fetchall()}
    c.execute("SELECT followeeId FROM follows WHERE followerId = ?", (newId,))
    for r in c.fetchall():
        if r["followeeId"] in oldFollowees:
            c.execute("DELETE FROM follows WHERE followerId = ? AND followeeId = ?", (newId, r["followeeId"]))

    c.execute("SELECT followerId FROM follows WHERE followeeId = ?", (oldId,))
    oldFollowers = {r["followerId"] for r in c.fetchall()}
    c.execute("SELECT followerId FROM follows WHERE followeeId = ?", (newId,))
    for r in c.fetchall():
        if r["followerId"] in oldFollowers:
            c.execute("DELETE FROM follows WHERE followerId = ? AND followeeId = ?", (r["followerId"], newId))

    # levelRatings is keyed on (gameId, playerId) together, so a straight UPDATE could
    # collide with a rating newId already has on the same level (newId is expected to be
    # an essentially empty profile, but drop any such duplicates defensively first,
    # same idea as the follows cleanup above).
    c.execute("SELECT gameId FROM levelRatings WHERE playerId = ?", (oldId,))
    oldRatedGames = {r["gameId"] for r in c.fetchall()}
    c.execute("SELECT gameId FROM levelRatings WHERE playerId = ?", (newId,))
    for r in c.fetchall():
        if r["gameId"] in oldRatedGames:
            c.execute("DELETE FROM levelRatings WHERE gameId = ? AND playerId = ?", (r["gameId"], newId))

    for table, col in [
        ("minigames", "creatorId"),
        ("scores", "playerId"),
        ("ghosts", "playerId"),
        ("chatMessages", "playerId"),
        ("comments", "playerId"),
        ("follows", "followerId"),
        ("follows", "followeeId"),
        ("teams", "ownerId"),
        ("levelRatings", "playerId"),
    ]:
        c.execute(f"UPDATE {table} SET {col} = ? WHERE {col} = ?", (newId, oldId))

    c.execute("DELETE FROM players WHERE id = ?", (newId,))
    c.execute("UPDATE players SET id = ?, playerId = ? WHERE id = ?", (newId, newId, oldId))
    conn.commit()
    print(f"[DB] Rebound existing player {oldId} -> new UDID {newId} (matched by name)")


def getOrCreatePlayer(name: str, requestedId: str = None) -> dict:
    conn = getDbConnection()
    c = conn.cursor()
    name = safeStr(name, "Player").strip() or "Player"
    requestedId = safeStr(requestedId).strip() if requestedId else None

    row = None
    if requestedId:
        c.execute("SELECT * FROM players WHERE id = ?", (requestedId,))
        row = c.fetchone()

    if not row and requestedId and name and name != "Player":
        # New/unknown UDID (e.g. after a reinstall), but we know the name:
        # try to recover the existing account instead of creating a fresh,
        # empty one and silently orphaning the player's progress.
        c.execute("SELECT * FROM players WHERE name = ? COLLATE NOCASE", (name,))
        candidate = c.fetchone()
        if candidate and candidate["id"] != requestedId:
            oldId = candidate["id"]
            rebindPlayerId(conn, oldId, requestedId)
            c.execute("SELECT * FROM players WHERE id = ?", (requestedId,))
            row = c.fetchone()
            print(f"[DB] requestedId '{requestedId}' not found, but matched existing player '{name}' (was {oldId}) by name")

    if row:
        existingTag = safeStr(rowGet(row, ["tag"], ""))
        if not existingTag:
            newTag = genTag()
            c.execute("UPDATE players SET tag = ? WHERE id = ?", (newTag, row["id"]))
            conn.commit()
            c.execute("SELECT * FROM players WHERE id = ?", (row["id"],))
            row = c.fetchone()
        payload = getPlayerPayload(row)
        print(f"[DB] Logged in existing player: {row['name']} ({row['id']})")
    else:
        pId = requestedId if requestedId else genOid()
        sId = genSid()
        pTag = genTag()
        c.execute("INSERT INTO players (id, playerId, sessionId, name, tag) VALUES (?,?,?,?,?)",
                  (pId, pId, sId, name, pTag))
        conn.commit()
        if requestedId:
            print(f"[DB] requestedId '{requestedId}' not found -> Registered new account: {name} ({pId}) tag={pTag}")
        else:
            print(f"[DB] Created brand new profile: {name} ({pId}) tag={pTag}")
        c.execute("SELECT * FROM players WHERE id = ?", (pId,))
        payload = getPlayerPayload(c.fetchone())

    conn.close()
    return payload

# ---------------------------------------------------------------------
# Player Persistence
# ---------------------------------------------------------------------
def updatePlayerResources(playerId: str, resources: dict):
    if not resources: return
    conn = getDbConnection()
    c = conn.cursor()
    fields = [
        "coins", "copper", "diamonds", "shards", "stars", "level",
        "mcBoosters", "carBoosters", "tournamentBoosters", "cups",
        "mcRank", "carRank", "mcTrophies", "carTrophies", "xp",
        "mcHandicap", "carHandicap", "cardPurchases", "gachaData", "itemLevel"
    ]
    updateParts, values = [], []
    for k in fields:
        if k in resources:
            val = resources[k]
            if isinstance(val, (dict, list)): val = json.dumps(val)
            updateParts.append(f"{k} = ?")
            values.append(val)
    if "upgrades" in resources:
        updateParts.append("upgrades = ?")
        values.append(json.dumps(resources["upgrades"]))
    if updateParts:
        values.append(playerId)
        c.execute(f"UPDATE players SET {', '.join(updateParts)} WHERE id = ?", tuple(values))
        conn.commit()
    conn.close()

def updatePlayerExtra(playerId: str, setData: dict):
    conn = getDbConnection()
    c = conn.cursor()
    updateParts, values = [], []
    for key in ("chest", "editorResources"):
        if key in setData:
            updateParts.append(f"{key} = ?")
            values.append(json.dumps(setData[key]))
    if updateParts:
        values.append(playerId)
        c.execute(f"UPDATE players SET {', '.join(updateParts)} WHERE id = ?", tuple(values))
        conn.commit()
    conn.close()

def updatePlayerCustomisation(playerId: str, customisation: dict):
    if not isinstance(customisation, dict) or not playerId: return
    conn = getDbConnection()
    c = conn.cursor()
    updateParts, values = [], []
    for srcKey in ("CharacterVisual", "OffroadCarVisual", "MotorcycleVisual",
                   "OffroadCarUpgrades", "MotorcycleUpgrades", "UpgradesResources"):
        if srcKey in customisation:
            targetCol = srcKey[0].lower() + srcKey[1:]
            updateParts.append(f"{targetCol} = ?")
            values.append(json.dumps(customisation[srcKey]))
    for levelKey in ("offroadCarLevel", "motorcycleLevel"):
        if levelKey in customisation:
            updateParts.append(f"{levelKey} = ?")
            values.append(safeInt(customisation[levelKey], 0))
    if updateParts:
        values.append(playerId)
        c.execute(f"UPDATE players SET {', '.join(updateParts)} WHERE id = ?", tuple(values))
        conn.commit()
    conn.close()

def applySetdataBody(playerId: str, top: dict):
    if not isinstance(top, dict) or not playerId: return
    updateBlock = top.get("update") or {}
    if isinstance(updateBlock, dict):
        resources = updateBlock.get("Resources")
        if isinstance(resources, dict):
            updatePlayerResources(playerId, resources)
    updatePlayerExtra(playerId, top)
    customisation = top.get("customisation")
    if isinstance(customisation, dict):
        updatePlayerCustomisation(playerId, customisation)
    progression = top.get("progression")
    if isinstance(progression, dict) and "paths" in progression:
        updatePlayerProgression(playerId, progression["paths"])

def updatePlayerProgression(playerId: str, paths):
    if not isinstance(paths, list) or not paths: return
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT progressionPaths FROM players WHERE id = ?", (playerId,))
    row = c.fetchone()
    existing = safeJsonLoads(rowGet(row, "progressionPaths", "[]"), []) if row else []
    if not isinstance(existing, list): existing = []

    existingByKey = {(p.get("planet"), p.get("name")): p for p in existing if isinstance(p, dict)}

    for incomingPath in paths:
        if not isinstance(incomingPath, dict): continue
        if incomingPath.get("planet") == "Shared": continue  # see getPlayerPayload - never persisted, client rebuilds it each session
        key = (incomingPath.get("planet"), incomingPath.get("name"))
        current = existingByKey.get(key)
        if current is None:
            existingByKey[key] = incomingPath
            continue
        for scalarKey in ("currentNode", "lane", "startNode", "overwrite", "type"):
            if scalarKey in incomingPath:
                current[scalarKey] = incomingPath[scalarKey]
        incomingNodes = incomingPath.get("nodes")
        if isinstance(incomingNodes, list):
            currentNodes = current.get("nodes")
            if not isinstance(currentNodes, list): currentNodes = []
            nodesById = {n.get("id"): n for n in currentNodes if isinstance(n, dict)}
            for n in incomingNodes:
                if isinstance(n, dict): nodesById[n.get("id")] = n
            current["nodes"] = list(nodesById.values())
        existingByKey[key] = current

    merged = list(existingByKey.values())
    c.execute("UPDATE players SET progressionPaths = ? WHERE id = ?",
              (json.dumps(merged), playerId))
    conn.commit()
    conn.close()

# ---------------------------------------------------------------------
# Signature System
# ---------------------------------------------------------------------
def generatePlayHash(uri: str, body) -> str:
    secret = gpw(HPW)
    if isinstance(body, bytes):
        return hashlib.sha256(body + (uri + secret).encode("utf-8")).hexdigest()
    return hashlib.sha256((uri + body + secret).encode("utf-8")).hexdigest()

# ---------------------------------------------------------------------
# Route Registration
# ---------------------------------------------------------------------
ROUTES = {}

def route(*paths):
    def decorator(func):
        for p in paths:
            ROUTES[p.lower()] = func
        return func
    return decorator

# =====================================================================
#  ROUTE HANDLERS
# =====================================================================

PRELOAD_ASSETS = {
    "challengemusic":  {"name": "ChallengeMusic",  "type": "audio", "version": 1},
    "puzzlemusic1":    {"name": "PuzzleMusic1",    "type": "audio", "version": 1},
    "racingmusic1":    {"name": "RacingMusic1",    "type": "audio", "version": 1},
    "puzzlemusic2":    {"name": "PuzzleMusic2",    "type": "audio", "version": 1},
    "bossmusic":       {"name": "BossMusic",       "type": "audio", "version": 1},
}

@route("/v1/preload/checkfile")
def hCheckFile(params, body):
    requestedName = params.get("name", [""])[0]
    lookup = requestedName.lower()
    if lookup in PRELOAD_ASSETS:
        canonical = PRELOAD_ASSETS[lookup]["name"]
        atype = PRELOAD_ASSETS[lookup]["type"]
        ver = PRELOAD_ASSETS[lookup]["version"]
    else:
        canonical, atype, ver = requestedName, "audio", 1
    bankFile = f"{canonical}.bank"
    local = os.path.join(SERVER_DATA_DIR, "Music", bankFile)
    if os.path.isfile(local):
        url = f"http://{localIp()}:{HTTP_PORT}/ServerData/Music/{bankFile}"
    else:
        url = ""
    return {"name": canonical, "type": atype, "path": url, "version": ver}

@route("/v1/preload/checkversion")
def hCheckVersion(params, body):
    raw = params.get("version", [""])[0]
    ok = isVersionSupported(raw)
    if ok: return {"version": "upToDate"}
    return {"version": "3.7.1", "versionMessage": "Please update to 3.7.1."}

@route("/v1/path/db/find")
def hPathDbFind(params, body):
    planet = params.get("planet", [""])[0]
    txtPath = resolvePlanetTxtPath(planet)
    if not txtPath:
        rawBytes = json.dumps({"nodes": [], "edges": []}).encode("utf-8")
        return {"_binary": filepackerZipBytes(rawBytes), "_content_type": "application/octet-stream"}
    with open(txtPath, "r", encoding="utf-8") as f:
        rawJson = f.read().strip()
    if rawJson.startswith("\"") and rawJson.endswith("\""):
        try:
            unwrapped = json.loads(rawJson)
            if isinstance(unwrapped, str): rawJson = unwrapped
            else: rawJson = json.dumps(unwrapped, separators=(",", ":"))
        except Exception: pass
    return {"_binary": filepackerZipBytes(rawJson.encode("utf-8")), "_content_type": "application/octet-stream"}

@route("/v4/player/login")
def hLogin(params, body):
    name = "Player"
    requestedId = None
    try:
        parsed = json.loads(body.decode("utf-8"))
        if isinstance(parsed, dict):
            rawName = parsed.get("name", name)
            if isinstance(rawName, str) and rawName.strip(): name = rawName.strip()
            rawId = parsed.get("id")
            if rawId is not None and str(rawId).strip(): requestedId = str(rawId).strip()
    except Exception as e:
        print(f"[Login] Parse error: {e!r}")
    print(f"[Login] name='{name}' requestedId='{requestedId}'")
    return getOrCreatePlayer(name, requestedId)

@route("/v2/player/data/change")
def hPlayerDataChange(params, body):
    try:
        top = json.loads(body.decode("utf-8"))
    except Exception:
        return {"status": "ERROR"}
    if not isinstance(top, dict): return {"status": "ERROR"}
    playerId = params.get("PLAYER_ID", [""])[0]
    if not playerId: return {"status": "OK", "lastPathSync": nowIso()}
    applySetdataBody(playerId, top)
    res = {"status": "OK", "lastPathSync": nowIso()}
    return injectWalletData(res, playerId)

@route("/v1/player/get/social")
def hGetPlayerSocial(params, body):
    # Server.Player.GetPlayerProfile - among other things, this is how PsGameLoop
    # fetches a LEVEL'S CREATOR profile before the race-loading screen can finish
    # (GhostsLoaded -> PlayerDataLoaded -> ExtrasLoaded on PsGameLoopTournament
    # specifically waits on a non-empty playerId before ever calling LevelLoaded()).
    # A bare {"status":"ERROR"} - correct for "there is genuinely no such player" in
    # most other contexts - leaves that playerId empty and the tournament loading
    # screen stuck on "Building level..." forever for any level whose creator isn't
    # a real row in `players` (i.e. every imported/external level). So instead of
    # erroring out, fall back to a minimal-but-valid profile using whatever creator
    # info the level itself carries (creatorName/countryCode on `minigames`), still
    # keyed by the requested id so playerId is never empty.
    playerId = params.get("playerId", [""])[0]
    if not playerId: return {"status": "ERROR"}
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM players WHERE id = ?", (playerId,))
    row = c.fetchone()
    if row:
        conn.close()
        return getFollowPlayerDict(row)
    c.execute("SELECT creatorName, countryCode FROM minigames WHERE creatorId = ? LIMIT 1", (playerId,))
    fallback = c.fetchone()
    conn.close()
    return {
        "id": playerId, "playerId": playerId,
        "name": safeStr(fallback["creatorName"], "Player") if fallback else "Player",
        "tag": "", "level": 1, "mcRank": 1, "carRank": 1, "mcTrophies": 0, "carTrophies": 0,
        "facebookId": "", "gameCenterId": "",
        "countryCode": safeStr(fallback["countryCode"], "US") if fallback else "US",
        "youtuber": "", "youtubeName": "", "youtuberId": "", "youtubeId": "",
        "youtubeSubscriberCount": 0, "publishedMinigameCount": 0,
    }

@route("/v1/player/data/find")
def hPlayerDataFind(params, body):
    return {"data": [], "results": []}

@route("/v1/player/data/remove")
def hPlayerDataRemove(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    fieldsRaw = params.get("fields", [""])[0]
    if playerId and fieldsRaw:
        fields = [f.strip() for f in fieldsRaw.split(",") if f.strip()]
        conn = getDbConnection()
        c = conn.cursor()
        safeFields = {"upgrades", "offroadCarUpgrades", "motorcycleUpgrades",
                      "upgradesResources", "chest", "editorResources", "progressionPaths"}
        for field in fields:
            if field in safeFields:
                c.execute(f"UPDATE players SET {field} = '' WHERE id = ?", (playerId,))
        conn.commit()
        conn.close()
    return {"status": "OK"}

@route("/v1/player/skip")
def hSkipLevel(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        applySetdataBody(playerId, top)
    return {"status": "OK"}

@route("/v1/player/settings")
def hPlayerSettings(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        parsed = json.loads(body.decode("utf-8"))
    except Exception:
        parsed = {}
    if playerId and isinstance(parsed, dict):
        locale = safeStr(parsed.get("locale"), "en")
        acceptNotifications = 1 if parsed.get("acceptNotifications") else 0
        conn = getDbConnection()
        conn.cursor().execute("UPDATE players SET locale = ?, acceptNotifications = ? WHERE id = ?",
                              (locale, acceptNotifications, playerId))
        conn.commit()
        conn.close()
    return {"status": "OK"}

@route("/v1/player/follow/add")
def hFollowAdd(params, body):
    followerId = params.get("PLAYER_ID", [""])[0]
    targetId = params.get("followeeId", [""])[0]
    if followerId and targetId and followerId != targetId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("INSERT OR IGNORE INTO follows (followerId, followeeId) VALUES (?, ?)", (followerId, targetId))
        conn.commit()
        conn.close()
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if followerId and isinstance(top, dict) and "customisation" in top:
        updatePlayerCustomisation(followerId, top["customisation"])
    return {"status": "OK"}

@route("/v1/player/follow/remove")
def hFollowRemove(params, body):
    followerId = params.get("followerId", [""])[0] or params.get("PLAYER_ID", [""])[0]
    targetId = params.get("followeeId", [""])[0]
    if followerId and targetId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("DELETE FROM follows WHERE followerId = ? AND followeeId = ?", (followerId, targetId))
        conn.commit()
        conn.close()
    return {"status": "OK"}

@route("/v2/player/friends")
def hFriendsList(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    followees, followers, mutualFriends = [], [], []
    if playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT p.* FROM players p JOIN follows f ON p.id = f.followeeId WHERE f.followerId = ?", (playerId,))
        followees = [getFollowPlayerDict(r) for r in c.fetchall()]
        followeeIds = {f["id"] for f in followees}
        c.execute("SELECT p.* FROM players p JOIN follows f ON p.id = f.followerId WHERE f.followeeId = ?", (playerId,))
        followers = [getFollowPlayerDict(r) for r in c.fetchall()]
        mutualFriends = [f for f in followers if f["id"] in followeeIds]
        conn.close()
    return {"followees": followees, "friends": mutualFriends, "followers": followers}

@route("/v1/player/follow/followees")
def hFolloweesList(params, body):
    playerId = params.get("followerId", [""])[0] or params.get("PLAYER_ID", [""])[0]
    data = []
    if playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT p.* FROM players p JOIN follows f ON p.id = f.followeeId WHERE f.followerId = ?", (playerId,))
        data = [getFollowPlayerDict(r) for r in c.fetchall()]
        conn.close()
    return {"data": data}

@route("/v1/player/follow/followers")
def hFollowersList(params, body):
    playerId = params.get("followeeId", [""])[0] or params.get("PLAYER_ID", [""])[0]
    data = []
    if playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT p.* FROM players p JOIN follows f ON p.id = f.followerId WHERE f.followeeId = ?", (playerId,))
        data = [getFollowPlayerDict(r) for r in c.fetchall()]
        conn.close()
    return {"data": data}

@route("/v2/player/changename")
def hChangeName(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    rawNewName = params.get("newName", [""])[0] or params.get("name", [""])[0]
    if not rawNewName and body:
        try:
            parsed = json.loads(body.decode("utf-8"))
            if isinstance(parsed, dict):
                rawNewName = parsed.get("newName") or parsed.get("name") or ""
        except Exception: pass
    newName = safeStr(unquote_plus(rawNewName)).strip()[:20]
    nameChangesDone = 0
    if newName and playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT nameChangesDone FROM players WHERE id = ?", (playerId,))
        row = c.fetchone()
        nameChangesDone = (safeInt(rowGet(row, "nameChangesDone", 0), 0) + 1)
        c.execute("UPDATE players SET name = ?, nameChangesDone = ? WHERE id = ?",
                  (newName, nameChangesDone, playerId))
        c.execute("UPDATE minigames SET creatorName = ? WHERE creatorId = ?", (newName, playerId))
        conn.commit()
        conn.close()
        print(f"[Player] {playerId} -> '{newName}' (changes: {nameChangesDone})")
    return {"status": "OK", "name": newName or "Player", "nameChangesDone": nameChangesDone}

@route("/v1/player/changeyoutuber")
def hChangeYoutuber(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    youtuber = safeStr(unquote_plus(params.get("youtuber", [""])[0])).strip()
    youtuberId = safeStr(unquote_plus(params.get("youtuberId", [""])[0])).strip()
    subscriberCount = safeInt(params.get("subscriberCount", ["0"])[0], 0)
    if playerId:
        conn = getDbConnection()
        conn.cursor().execute(
            "UPDATE players SET youtuber = ?, youtuberId = ?, youtubeSubscriberCount = ? WHERE id = ?",
            (youtuber, youtuberId, subscriberCount, playerId))
        conn.commit()
        conn.close()
    return {"status": "OK"}

@route("/v1/player/info")
def hPlayerInfo(params, body): return {"status": "OK"}

@route("/v1/player/stats/find", "/v1/player/stats/set", "/v1/player/stats/change")
def hPlayerStats(params, body):
    return {
        "versusPlays": 0, "versusWins": 0, "versusLosses": 0,
        "mcVersusStats": {"totalPlays": 0, "wins": 0, "losses": 0},
        "carVersusStats": {"totalPlays": 0, "wins": 0, "losses": 0}
    }

@route("/v1/player/remove")
def hRemovePlayer(params, body): return {"status": "OK"}

@route("/v1/player/switch")
def hSwitchPlayer(params, body): return getOrCreatePlayer("Player")

@route("/v1/player/skiptimeleft")
def hSkipTimeLeft(params, body): return {"timeLeft": 0}

@route("/v1/player/resetskiptimer")
def hResetSkipTimer(params, body): return {"status": "OK"}

@route("/v1/player/resetlevel")
def hResetLevel(params, body): return {"status": "OK"}

@route("/v1/player/rent")
def hVehicleRent(params, body): return {"status": "OK", "rentedUntil": nowIso()}

@route("/v1/player/openchest")
def hOpenChest(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    chestId = params.get("id", [""])[0]
    chestType = params.get("chestType", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        applySetdataBody(playerId, top)
    print(f"[Chest] {playerId} opened id={chestId!r} type={chestType!r}")
    return {"status": "OK", "rewards": []}

@route("/v1/player/specialoffer", "/v1/player/specialoffer/start", "/v1/player/specialoffer/claim")
def hSpecialOffer(params, body): return {"status": "OK", "data": [], "offers": []}

@route("/v2/player/join/gamecenter", "/v2/player/check/gamecenter",
       "/v2/player/join/facebook", "/v1/player/join/ninja",
       "/v1/player/check/social", "/v1/player/solve/social", "/v1/player/remove/social",
       "/v1/player/follow/social")
def hSocial(params, body): return {"status": "OK", "linked": False}

@route("/v1/abuse/report")
def hAbuseReport(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    targetId = params.get("targetId", [""])[0]
    message = unquote_plus(params.get("text", [""])[0])
    print(f"[Abuse] Report from {playerId} against {targetId}: {message!r}")
    return {"status": "OK"}

@route("/v1/player/tester/setmax", "/v1/player/tester/use", "/v1/player/tester/purchase")
def hTester(params, body): return {"status": "OK"}

@route("/v1/customisation/add")
def hCustomisation(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        keyToColumn = {
            "OffroadCarVisual": "offroadCarVisual", "OffroadCarUpgrade": "offroadCarUpgrades",
            "MotorcycleVisual": "motorcycleVisual", "MotorcycleUpgrade": "motorcycleUpgrades",
        }
        updateParts, values = [], []
        for srcKey, column in keyToColumn.items():
            if srcKey in top:
                updateParts.append(f"{column} = ?")
                values.append(json.dumps(top[srcKey]))
        if updateParts:
            values.append(playerId)
            conn = getDbConnection()
            conn.cursor().execute(f"UPDATE players SET {', '.join(updateParts)} WHERE id = ?", tuple(values))
            conn.commit()
            conn.close()
    return {"status": "OK"}

@route("/v1/achievement/upsert")
def hAchievement(params, body): return {"status": "OK"}

# --- Search Routes ---

@route("/v1/search/gameandplayer")
def hSearch(params, body):
    query = params.get("query", [""])[0] or params.get("search", [""])[0] or params.get("name", [""])[0]
    query = unquote_plus(query).strip()
    limit = max(1, min(safeInt(params.get("limit", ["20"])[0], 20), 50))

    if not query:
        return {"games": [], "players": [], "tag": [], "data": {"games": [], "players": []}, "results": []}

    # PsUICenterProfilePopup renders tags as "Name @tag" (the "@" is display-only, never
    # stored) - a player copying/typing what they see on screen naturally searches
    # "@c8nop", not "c8nop". Strip both "@" and "#" so all three forms work the same.
    cleanTag = query.lstrip("@#").strip().upper()

    conn = getDbConnection()
    c = conn.cursor()

    # tag comparison is case-insensitive (COLLATE NOCASE) since stored tags aren't all
    # uppercase - some (e.g. the follow-reward NPC accounts) keep their real lowercase
    # display tag, and typing it back should still find them by exact tag.
    c.execute("""SELECT * FROM players
                 WHERE name LIKE ? OR tag = ? COLLATE NOCASE
                 ORDER BY mcTrophies + carTrophies DESC LIMIT ?""",
              (f"%{query}%", cleanTag, limit))
    playerRows = c.fetchall()
    playersData = [getFollowPlayerDict(r) for r in playerRows]
    conn.close()

    tagMatches = [p for p in playersData if p["tag"].upper() == cleanTag] if cleanTag else []
    gamesData = queryMinigames(searchStr=query, state="public", limit=limit)

    print(f"[Search] Query '{query}' -> Found {len(gamesData)} level(s), {len(playersData)} player(s)")

    return {
        "games": gamesData, "players": playersData, "tag": tagMatches,
        "data": {"games": gamesData, "players": playersData},
        "results": gamesData
    }

@route("/v2/minigame/meta/search")
def hMinigameMetaSearch(params, body):
    items = params.get("items", [None])[0]
    gameMode = params.get("gameMode", [None])[0]
    playerUnit = params.get("playerUnit", [None])[0]
    difficulty = params.get("difficulty", [None])[0]
    query = params.get("query", [None])[0] or params.get("search", [None])[0]
    limit = safeInt(params.get("limit", ["10"])[0], 10)
    playerId = params.get("PLAYER_ID", [""])[0]

    data = queryMinigames(gameMode=gameMode, playerUnit=playerUnit,
                          difficulty=difficulty, searchStr=query, items=items,
                          state="public", limit=limit, playerId=playerId)
    return {"data": data, "results": data}

@route("/v1/minigame/meta/finditems")
def hMinigameFinditems(params, body):
    items = params.get("items", [""])[0]
    limit = safeInt(params.get("limit", ["20"])[0], 20)
    data = queryMinigames(items=items, state="public", limit=limit)
    return {"data": data, "results": data}

# --- Minigame Routes ---

@route("/v1/minigame/meta/find")
def hMinigameMetaFind(params, body):
    # Server.MiniGame.Get - this is how the client loads a level's metadata right
    # before playing it, so "rating" here must be THIS player's own past thumbs
    # up/down (PsGameLoop.GetRating()), not the level-wide aggregate.
    minigameId = params.get("id", [""])[0]
    playerId = params.get("PLAYER_ID", [""])[0]
    row = getMinigameRow(minigameId)
    meta = minigameRowToMetaDict(row) if row is not None else buildMinigameMeta(minigameId)
    meta["rating"] = getPlayerRatingForLevel(minigameId, playerId)
    return meta

@route("/v1/minigame/onefresh")
def hMinigameFresh(params, body):
    playerUnit = params.get("playerUnit", ["Any"])[0]
    gameMode = params.get("gameMode", ["Race"])[0]
    playerId = params.get("PLAYER_ID", [""])[0]
    candidates = queryMinigames(gameMode=gameMode, playerUnit=playerUnit, state="public",
                                orderBy="RANDOM()", limit=1, playerId=playerId)
    return candidates[0] if candidates else buildMinigameMeta(genOid(), playerUnit, gameMode)

@route("/v1/minigame/trend/find")
def hMinigameTrend(params, body):
    data = queryMinigames(state="public", orderBy="timesPlayed DESC, createdAt DESC",
                          limit=safeInt(params.get("limit", ["20"])[0], 20),
                          playerId=params.get("PLAYER_ID", [""])[0])
    return {"data": data, "results": data}

@route("/v1/minigame/popular/find")
def hMinigamePopular(params, body):
    data = queryMinigames(state="public", orderBy="upThumbs DESC, timesLiked DESC",
                          limit=safeInt(params.get("limit", ["20"])[0], 20),
                          playerId=params.get("PLAYER_ID", [""])[0])
    return {"data": data, "results": data}

@route("/v1/minigame/unrated/find")
def hMinigameUnrated(params, body):
    data = queryMinigames(state="public", orderBy="timesRated ASC, createdAt DESC",
                          limit=safeInt(params.get("limit", ["20"])[0], 20),
                          playerId=params.get("PLAYER_ID", [""])[0])
    return {"data": data, "results": data}

@route("/v1/minigame/subgenre/find")
def hMinigameSubgenre(params, body):
    data = queryMinigames(gameMode=params.get("gameMode", [None])[0],
                          playerUnit=params.get("playerUnit", [None])[0], state="public",
                          limit=safeInt(params.get("limit", ["20"])[0], 20),
                          playerId=params.get("PLAYER_ID", [""])[0])
    return {"data": data, "results": data}

@route("/v1/minigame/followee/find")
def hMinigameFolloweeFind(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    limit = safeInt(params.get("limit", ["50"])[0], 50)
    data = []
    if playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("""SELECT m.* FROM minigames m
                     JOIN follows f ON f.followeeId = m.creatorId
                     WHERE f.followerId = ? AND m.state = 'public'
                     ORDER BY m.createdAt DESC LIMIT ?""", (playerId, limit))
        data = [minigameRowToMetaDict(r) for r in c.fetchall()]
        conn.close()
    return {"data": data, "results": data}

@route("/v1/minigame/followee/published")
def hMinigameFolloweePublished(params, body):
    targetPlayerId = params.get("playerId", [""])[0] or params.get("PLAYER_ID", [""])[0]
    limit = safeInt(params.get("limit", ["50"])[0], 50)
    data = []
    if targetPlayerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("""SELECT * FROM minigames 
                     WHERE creatorId = ? AND state = 'public'
                     ORDER BY createdAt DESC LIMIT ?""", (targetPlayerId, limit))
        data = [minigameRowToMetaDict(r) for r in c.fetchall()]
        conn.close()
    return {"data": data, "results": data}

@route("/v1/minigame/history")
def hMinigameHistory(params, body):
    data = queryMinigames(state="public", limit=safeInt(params.get("limit", ["20"])[0], 20))
    return {"data": data, "results": data}

@route("/v1/minigame/hidden")
def hMinigameHidden(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    data = queryMinigames(creatorId=playerId or None, state="hidden",
                          limit=safeInt(params.get("limit", ["10"])[0], 10))
    return {"data": data, "results": data}

@route("/v1/minigame/own/published")
def hMinigameOwnPublished(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    data = queryMinigames(creatorId=playerId or None, state="public",
                          limit=safeInt(params.get("limit", ["50"])[0], 50))
    return {"data": data, "results": data}

@route("/v1/minigame/own/saved")
def hMinigameOwnSaved(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    data = queryMinigames(creatorId=playerId or None, state="saved",
                          limit=safeInt(params.get("limit", ["50"])[0], 50))
    return {"data": data, "results": data}

@route("/v2/minigame/own")
def hMinigameOwn(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    data = queryMinigames(creatorId=playerId or None,
                          limit=safeInt(params.get("limit", ["50"])[0], 50))
    publishedCount = sum(1 for d in data if d.get("state") == "public")
    # Le vrai serveur donnait des likes/gains/abonnes en fonction de
    # l'engagement des autres joueurs sur les niveaux publies -- impossible
    # a reproduire sans vrais joueurs en face. Valeurs fixees tres haut
    # a la demande du joueur, en compensation.
    #
    # totalLikes doit rester <= creatorRank6 (10 000 000, cf clientConfig du
    # login) et likesSeen == totalLikes : PsUICenterOwnLevels.DataSUCCEED
    # calcule m_creatorRank a partir de likesSeen (paliers creatorRank1..6),
    # puis Step() anime une barre de progression de likesSeen vers
    # totalLikes en affichant le popup "Rank Up!" a CHAQUE palier franchi
    # pendant l'anim. Avec totalLikes a 2 milliards et likesSeen a 0, cette
    # animation (et donc le popup) rejouait en entier a chaque ouverture de
    # l'ecran Create, puisque rien ne persiste jamais "likesSeen". En gardant
    # les deux valeurs egales et plafonnees au palier max, m_likesToAnimate
    # vaut toujours 0 : rang max affiche direct, sans animation ni popup.
    maxLikes = 10000000
    return {"data": data, "results": data,
            "publishedMinigameCount": publishedCount,
            "followerCount": 2000000000,
            "totalCoinsEarned": 2000000000,
            "totalLikes": maxLikes,
            "totalSuperLikes": 0, "likesSeen": maxLikes}

@route("/v1/minigame/data/find")
def hMinigameDataFind(params, body):
    minigameId = params.get("id", [""])[0]
    row = getMinigameRow(minigameId)
    data = bytes(row["levelData"]) if (row is not None and row["levelData"]) else b""
    if data:
        print(f"[Minigame] data/find: serving {len(data)} bytes for '{minigameId}'")
    else:
        print(f"[Minigame] data/find: no levelData for '{minigameId}', serving empty")
    return {"_binary": data, "_content_type": "application/octet-stream"}

def _classifyAndApplyTrailingSegment(minigameId: str, playerId: str, segment: bytes):
    if not segment: return
    try:
        parsed = json.loads(segment.decode("utf-8"))
        if isinstance(parsed, dict):
            if "update" in parsed and playerId:
                applySetdataBody(playerId, parsed)
            elif "editorResources" in parsed:
                upsertMinigame(minigameId, {"editorMeta": json.dumps(parsed)})
            return
    except Exception:
        pass
    row = getMinigameRow(minigameId)
    if row is not None and not row["screenshot"]:
        conn = getDbConnection()
        conn.cursor().execute("UPDATE minigames SET screenshot = ? WHERE id = ?", (segment, minigameId))
        conn.commit(); conn.close()
    else:
        conn = getDbConnection()
        conn.cursor().execute("UPDATE minigames SET creatorGhost = ? WHERE id = ?", (segment, minigameId))
        conn.commit(); conn.close()

def _handleMinigameSaveVariant(params, body, targetState: str):
    playerId = params.get("PLAYER_ID", [""])[0]
    fileSizes = params.get("FILE_SIZES", [""])[0]
    existingId = params.get("id", [None])[0]
    segments = splitFileSizesBody(fileSizes, body)

    if not segments:
        minigameId = existingId or genOid()
        upsertMinigame(minigameId, {"state": targetState}, levelData=None)
    else:
        minigameId = upsertMinigameFromMetaSegment(segments[0], existingId)
        # Same rule as /v1/minigame/backtosaved: the client's `published` flag is
        # derived purely from the presence of publishTime (ParseMinigameMetaData),
        # not from `state`. Only "public" should carry one - clear it on every other
        # transition (save/hide) or a level that leaves the public state stays stuck
        # looking published.
        fields = {"state": targetState, "publishTime": nowIso() if targetState == "public" else ""}
        levelBytes = segments[1] if len(segments) > 1 else None
        upsertMinigame(minigameId, fields, levelData=levelBytes if levelBytes else None)
        for seg in segments[2:]:
            _classifyAndApplyTrailingSegment(minigameId, playerId, seg)

    # The level's own creator metadata never includes a "countryCode" (the editor
    # doesn't send one - confirmed empty in editorMeta), so a newly-created level's
    # minigames row was always stuck at the players table's 'US' column default,
    # regardless of where the creator actually is - showing the wrong flag on the
    # post-race rating screen for the creator's own levels. Stamped from the
    # creator's own current country every save, same as any other creator field.
    if playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT countryCode FROM players WHERE id = ?", (playerId,))
        creatorRow = c.fetchone()
        conn.close()
        if creatorRow is not None:
            upsertMinigame(minigameId, {"countryCode": safeStr(creatorRow["countryCode"], "US")})

    print(f"[Minigame] {targetState}: id={minigameId} by player={playerId} "
          f"({len(segments)} segments, {len(segments[1]) if len(segments) > 1 else 0} level bytes)")

    row = getMinigameRow(minigameId)
    result = minigameRowToMetaDict(row) if row is not None else buildMinigameMeta(minigameId)
    injectWalletData(result, playerId)
    result["lastPathSync"] = nowIso()
    return result

@route("/v2/minigame/save")
def hMinigameSave(params, body):
    return _handleMinigameSaveVariant(params, body, "saved")

@route("/v1/minigame/hide")
def hMinigameHide(params, body):
    return _handleMinigameSaveVariant(params, body, "hidden")

@route("/v4/minigame/publish")
def hMinigamePublish(params, body):
    return _handleMinigameSaveVariant(params, body, "public")

@route("/v1/minigame/backtosaved")
def hMinigameBacktosaved(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    fileSizes = params.get("FILE_SIZES", [""])[0]
    existingId = params.get("id", [None])[0]
    segments = splitFileSizesBody(fileSizes, body)
    if segments:
        minigameId = upsertMinigameFromMetaSegment(segments[0], existingId)
        # The client's "back to saved" meta (type=1 in CreateMinigameMetaDataHashtable)
        # never carries a publishTime key, so upsertMinigameFromMetaSegment above leaves
        # the old one in place. ParseMinigameMetaData derives `published` purely from the
        # presence of publishTime (not from `state`), so it must be cleared here or the
        # level stays stuck in the client's "Live Levels" list forever.
        upsertMinigame(minigameId, {"state": "saved", "publishTime": ""})
        if len(segments) > 1:
            try:
                updateBody = json.loads(segments[1].decode("utf-8"))
                if isinstance(updateBody, dict) and playerId:
                    applySetdataBody(playerId, updateBody)
            except Exception:
                pass
    result = {"status": "OK", "lastPathSync": nowIso()}
    injectWalletData(result, playerId)
    return result

@route("/v1/minigame/delete")
def hMinigameDelete(params, body):
    minigameId = params.get("id", [""])[0]
    playerId = params.get("PLAYER_ID", [""])[0]
    if minigameId:
        deleteMinigameSafely(minigameId)
        print(f"[Minigame] Deleted {minigameId} (requested by {playerId})")
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
        if isinstance(top, dict) and playerId:
            applySetdataBody(playerId, top)
    except Exception:
        pass
    result = {"status": "OK", "lastPathSync": nowIso()}
    injectWalletData(result, playerId)
    return result

@route("/v1/minigame/data/save")
def hMinigameDataSave(params, body):
    minigameId = params.get("id", [""])[0]
    if minigameId and body:
        upsertMinigame(minigameId, {}, levelData=body)
        print(f"[Minigame] data/save (override): {minigameId} <- {len(body)} bytes")
    return {"status": "OK"}

@route("/v1/minigame/like/save", "/v1/minigame/level/update", "/v1/minigame/start")
def hMinigameUnusedStub(params, body): return {"status": "OK"}

@route("/v1/minigame/claim", "/v1/minigame/claimall")
def hMinigameClaim(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        applySetdataBody(playerId, top)
    result = {"status": "OK", "rewards": [], "lastPathSync": nowIso()}
    injectWalletData(result, playerId)
    return result

@route("/v1/minigame/screenshot/save")
def hScreenshotSave(params, body):
    gameId = params.get("gameId", [""])[0]
    if gameId and body:
        upsertMinigame(gameId, {})
        conn = getDbConnection()
        conn.cursor().execute("UPDATE minigames SET screenshot = ? WHERE id = ?", (body, gameId))
        conn.commit(); conn.close()
        print(f"[Screenshot] Saved {len(body)} bytes for {gameId}")
    return {"status": "OK"}

@route("/v1/minigame/screenshot/find")
def hScreenshotFind(params, body):
    gameId = params.get("gameId", [""])[0]
    row = getMinigameRow(gameId)
    data = bytes(row["screenshot"]) if (row is not None and row["screenshot"]) else b""
    return {"_binary": data, "_content_type": "application/octet-stream"}

_VALID_LEVEL_RATINGS = {"Elated", "Rejecting", "Positive", "Neutral", "Negative", "Unrated", "SuperLike"}

def getPlayerRatingForLevel(gameId: str, playerId: str) -> str:
    if not gameId or not playerId:
        return "Unrated"
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT rating FROM levelRatings WHERE gameId = ? AND playerId = ?", (gameId, playerId))
    row = c.fetchone()
    conn.close()
    return row["rating"] if row is not None else "Unrated"

def setPlayerRatingForLevel(gameId: str, playerId: str, rating: str):
    if not gameId or not playerId or rating not in _VALID_LEVEL_RATINGS:
        return
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""INSERT INTO levelRatings (gameId, playerId, rating, updatedAt)
                 VALUES (?, ?, ?, CURRENT_TIMESTAMP)
                 ON CONFLICT(gameId, playerId) DO UPDATE SET rating = excluded.rating,
                     updatedAt = excluded.updatedAt""", (gameId, playerId, rating))
    # upThumbs/downThumbs/timesLiked/timesSuperLiked/timesRated (all shown when
    # browsing levels - timesLiked/timesSuperLiked feed the "Popular" sort order too,
    # see queryMinigames' ORDER BY) are recomputed from scratch here rather than
    # incremented/decremented, so a player changing their mind (or re-rating on a
    # replay) can never drift the counts out of sync - each is just "how many players'
    # CURRENT rating is X" since levelRatings only keeps one row per (gameId,
    # playerId), no history. Note upThumbs/downThumbs count distinct RATERS, not
    # "rating events" - a single tester picking different positive rating types on the
    # same level will always see upThumbs stay at 1 (it's still only one person), by
    # design, not a bug.
    c.execute("SELECT COUNT(*) AS n FROM levelRatings WHERE gameId = ? AND rating IN ('Positive','Elated','SuperLike')", (gameId,))
    upCount = c.fetchone()["n"]
    c.execute("SELECT COUNT(*) AS n FROM levelRatings WHERE gameId = ? AND rating IN ('Negative','Rejecting')", (gameId,))
    downCount = c.fetchone()["n"]
    c.execute("SELECT COUNT(*) AS n FROM levelRatings WHERE gameId = ? AND rating IN ('Positive','Elated')", (gameId,))
    likedCount = c.fetchone()["n"]
    c.execute("SELECT COUNT(*) AS n FROM levelRatings WHERE gameId = ? AND rating = 'SuperLike'", (gameId,))
    superLikedCount = c.fetchone()["n"]
    c.execute("SELECT COUNT(*) AS n FROM levelRatings WHERE gameId = ? AND rating != 'Unrated'", (gameId,))
    ratedCount = c.fetchone()["n"]
    c.execute("""UPDATE minigames SET upThumbs = ?, downThumbs = ?, timesLiked = ?,
                 timesSuperLiked = ?, timesRated = ? WHERE id = ?""",
              (upCount, downCount, likedCount, superLikedCount, ratedCount, gameId))
    conn.commit()
    conn.close()

def _findComments(gameId: str, limit: int = 50) -> list:
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM comments WHERE gameId = ? ORDER BY id DESC LIMIT ?", (gameId, limit))
    rows = c.fetchall()
    conn.close()
    data = []
    for row in rows:
        data.append({
            "playerId": safeStr(row["playerId"]), "name": safeStr(row["name"], "Player"),
            "comment": safeStr(row["comment"]), "tag": safeStr(row["tag"]),
            "facebookId": safeStr(row["facebookId"]), "gameCenterId": safeStr(row["gameCenterId"]),
            "admin": bool(row["admin"]),
        })
    return data

@route("/v2/minigame/comment/save")
def hMinigameCommentSave(params, body):
    # Comment.Save (client) - used for both level comments and, with gameId set
    # to PsMetagameManager.m_team.id, team chat (PsUICenterTeamChat.cs).
    playerId = params.get("PLAYER_ID", [""])[0]
    gameId = params.get("gameId", [""])[0]
    tag = safeStr(params.get("tag", [""])[0])
    message = unquote_plus(params.get("comment", [""])[0]).strip()[:500]
    if gameId and playerId and message:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT name, tag, facebookId, gameCenterId FROM players WHERE id = ?", (playerId,))
        row = c.fetchone()
        name = safeStr(row["name"], "Player") if row else "Player"
        playerTag = safeStr(row["tag"]) if row else ""
        facebookId = safeStr(row["facebookId"]) if row else ""
        gameCenterId = safeStr(row["gameCenterId"]) if row else ""
        c.execute("""INSERT INTO comments
                     (gameId, playerId, name, facebookId, gameCenterId, tag, comment, timestamp, admin)
                     VALUES (?, ?, ?, ?, ?, ?, ?, ?, 0)""",
                  (gameId, playerId, name, facebookId, gameCenterId, tag or playerTag, message, nowEpochMs()))
        conn.commit(); conn.close()
        print(f"[Comment] {name} on gameId={gameId!r}: {message!r}")
    data = _findComments(gameId, 50) if gameId else []
    return {"status": "OK", "data": data, "results": data}

@route("/v2/minigame/comment/find")
def hMinigameCommentFind(params, body):
    gameId = params.get("gameId", [""])[0]
    limit = max(1, min(safeInt(params.get("limit", ["50"])[0], 50), 100))
    data = _findComments(gameId, limit) if gameId else []
    return {"status": "OK", "data": data, "results": data}

@route("/v1/challenge/daily/find")
def hChallengeDaily(params, body):
    return {"data": [], "dailyChallenge": None, "status": "OK"}

@route("/v4/versus/create")
def hVersusCreate(params, body):
    return {"objectId": genOid(), "status": "OK", "matchId": genOid(), "createdAt": nowIso()}

@route("/v2/versus/score/overwrite", "/v1/versus/score/quit",
       "/v1/versus/win", "/v1/versus/forfeit",
       "/v1/versus/tries/set", "/v1/versus/claim", "/v1/versus/claimandsave")
def hVersusAction(params, body): return {"status": "OK", "rewards": []}

@route("/v1/friendly/create")
def hFriendlyCreate(params, body):
    return {"objectId": genOid(), "status": "OK", "matchId": genOid(), "createdAt": nowIso()}

@route("/v1/friendly/join", "/v1/friendly/decline",
       "/v1/friendly/score/overwrite", "/v1/friendly/score/quit",
       "/v1/friendly/win", "/v1/friendly/forfeit",
       "/v1/friendly/tries/set", "/v1/friendly/claim", "/v1/friendly/claimandsave")
def hFriendlyAction(params, body): return {"status": "OK", "rewards": []}

# =====================================================================
#  DYNAMIC GHOST & HIGH SCORE HANDLERS
# =====================================================================

# Shared SELECT fragment for every "scores JOIN players" query that feeds a ghost
# binary response (packageGhostListResponse/_buildGhostMetaDict). A ghost row's own
# ghostCountryCode/ghostFacebookId/ghostGameCenterId/ghostTeamId/ghostTeamName/
# ghostTrophies (set on import from a real ghosts/<stem>.header - see
# _syncLevelGhostsFolder) take priority over the LEFT JOINed player's own values,
# which is what a live-submitted score (a real, currently-registered local player)
# still falls back to untouched, since those columns are empty/0 by default. Without
# this, a ghost imported from a player that was never registered on THIS server (an
# old-client dump, or another server's export) had nowhere to keep its own real
# country/team/trophies, and always silently fell back to the LEFT JOIN's NULLs (US
# flag, no team) even though the export it came from carried the real values.
_GHOST_ROW_SELECT_EXTRA = """
    COALESCE(NULLIF(s.ghostCountryCode, ''), p.countryCode) AS countryCode,
    COALESCE(NULLIF(s.ghostFacebookId, ''), p.facebookId) AS facebookId,
    COALESCE(NULLIF(s.ghostGameCenterId, ''), p.gameCenterId) AS gameCenterId,
    COALESCE(NULLIF(s.ghostTeamId, ''), p.teamId) AS teamId,
    COALESCE(NULLIF(s.ghostTeamName, ''), p.teamName) AS teamName,
    NULLIF(s.ghostTrophies, 0) AS trophies,
    p.mcTrophies, p.carTrophies
"""

def _buildGhostMetaDict(row, playerUnit: str = "Any", trophyWin: int = 1) -> dict:
    """The full ghost metadata shape ClientTools.ParseGhostDatas actually reads (all
    15 keys: playerId/name/time/trophyWin/trophyLose/ghostWin/ghostLose/ghostId/
    trophies/facebookId/gameCenterId/countryCode/teamId/teamName/version) - shared by
    every place that builds a ghost's metadata segment (live ghost-list responses via
    packageGhostListResponse, and the Levels tab's "Extract to ZIP" export) so they
    can never drift out of sync with each other or with what the client expects.
    `row` needs playerId/name-ish/time-ish fields at minimum; countryCode/facebookId/
    gameCenterId/teamId/teamName/trophies are all optional and default to "no data"
    values (which is what silently produces things like the client always falling
    back to the US flag for a ghost missing countryCode - a real, visible effect of
    skipping these fields, not just unused metadata)."""
    country = safeStr(rowGet(row, "countryCode", "US"))
    if not country or country.strip() == "":
        country = "US"

    trophies = safeInt(rowGet(row, "trophies", 0))
    if trophies <= 0:
        if playerUnit == "Motorcycle":
            trophies = safeInt(rowGet(row, "mcTrophies", 0))
        else:
            trophies = safeInt(rowGet(row, "carTrophies", 0))

    return {
        "playerId": safeStr(rowGet(row, "playerId", "")),
        # "name" covers hTrophyGhostsByTime/hTrophyGhostsByTrophies, which alias
        # "m.creatorName as name" when padding a short leaderboard with the creator's
        # own run - without it, that row's real name is never found here and this
        # always falls through to "Rival" even though the client did send a real name.
        "name": safeStr(rowGet(row, ["playerName", "creatorName", "name"], "Rival")),
        "time": safeInt(rowGet(row, ["time", "bestTime"], 0)),
        "trophyWin": trophyWin,
        "trophyLose": 0,
        "ghostWin": 1,
        "ghostLose": 0,
        "ghostId": safeStr(rowGet(row, "id", "")),
        "trophies": trophies,
        "facebookId": safeStr(rowGet(row, "facebookId", "")),
        "gameCenterId": safeStr(rowGet(row, "gameCenterId", "")),
        "countryCode": country,
        "teamId": safeStr(rowGet(row, "teamId", "")),
        "teamName": safeStr(rowGet(row, "teamName", "")),
        "version": 3,
    }

def packageGhostListResponse(rows: list, playerUnit: str = "Any") -> dict:
    """Packages database rows into the exact two-segment-per-ghost structure
    expected by ClientTools.ParseGhostDatas."""
    segments = []
    for idx, row in enumerate(rows):
        meta = _buildGhostMetaDict(row, playerUnit, trophyWin=idx + 1)
        metaBytes = json.dumps(meta, separators=(",", ":")).encode("utf-8")
        ghostRaw = rowGet(row, ["ghostData", "creatorGhost"], b"")
        ghostBytes = bytes(ghostRaw) if ghostRaw else b""
        segments.append(metaBytes)
        segments.append(ghostBytes)

    bodyBytes, fileSizes = filepackerCombine(segments)
    return {
        "_binary": bodyBytes,
        "_content_type": "application/octet-stream",
        "_headers": {"FILE_SIZES": fileSizes}
    }

def handleFallbackCreatorGhost(gameId: str, playerUnit: str) -> dict:
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""SELECT m.id, m.id as id, m.creatorId as playerId, m.creatorName, 
                        m.bestTime, m.countryCode, m.creatorGhost,
                        CASE WHEN ? = 'Motorcycle' THEN p.mcTrophies ELSE p.carTrophies END AS trophies
                 FROM minigames m
                 LEFT JOIN players p ON m.creatorId = p.id
                 WHERE m.id = ? LIMIT 1""", (playerUnit, gameId))
    row = c.fetchone()
    conn.close()
    
    if row and row["creatorGhost"]:
        return packageGhostListResponse([row], playerUnit)
    return buildSingleFakeGhostResponse(0, "Rival")

@route("/v1/ghost/versus/get", "/v1/ghost/friendly/get")
def hGhostSingle(params, body): return {"data": "", "results": []}

@route("/v1/ghost/creator/get")
def hGhostCreatorGet(params, body):
    gameId = params.get("gameId", [""])[0]
    creatorId = params.get("creatorId", [""])[0] or params.get("playerId", [""])[0]
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT creatorName, bestTime, creatorGhost FROM minigames WHERE id = ? AND creatorId = ?", 
              (gameId, creatorId))
    row = c.fetchone()
    if row and row["creatorGhost"]:
        ghostBytes = bytes(row["creatorGhost"])
        timeScore = safeInt(row["bestTime"])
        # GHOST_NAME travels as an HTTP header, which is Latin-1 only - a raw name with
        # non-Latin-1 characters (emoji, symbols like (tm)/checkmarks, etc.) would crash
        # send_header with UnicodeEncodeError. ClientTools.cs:568 confirms the client
        # expects this percent-encoded (WWW.UnEscapeURL(..., Encoding.UTF8) on read), the
        # same convention WWW.EscapeURL uses everywhere else in the client - so encode,
        # don't decode.
        nameEncoded = quote_plus(safeStr(row["creatorName"], "Creator"))
        conn.close()
    else:
        c.execute("""SELECT playerName, time, ghostData FROM scores
                     WHERE gameId = ? AND playerId = ?
                     ORDER BY time ASC LIMIT 1""", (gameId, creatorId))
        row = c.fetchone()
        conn.close()
        if row and row["ghostData"]:
            ghostBytes = bytes(row["ghostData"])
            timeScore = safeInt(row["time"])
            nameEncoded = quote_plus(safeStr(row["playerName"], "Creator"))
        else:
            ghostBytes = b""
            timeScore = 0
            nameEncoded = "Creator"
    return {
        "_binary": ghostBytes,
        "_content_type": "application/octet-stream",
        "_headers": {"GHOST_TIME": timeScore, "GHOST_NAME": nameEncoded}
    }

@route("/v1/trophy/ghostsbyids")
def hTrophyGhostsByIds(params, body):
    ghostIds = params.get("ghostIds", [""])[0]
    gameId = params.get("gameId", [""])[0]
    playerUnit = params.get("playerUnit", ["Any"])[0]

    idList = [gId.strip() for gId in ghostIds.split(",") if gId.strip()]

    conn = getDbConnection()
    c = conn.cursor()
    rows = []

    # 1. Fetch any specific ghost IDs requested by the client
    if idList:
        placeholders = ",".join(["?"] * len(idList))
        c.execute(f"""SELECT s.*, {_GHOST_ROW_SELECT_EXTRA}
                      FROM scores s
                      LEFT JOIN players p ON s.playerId = p.id
                      WHERE (s.id IN ({placeholders}) OR s.playerId IN ({placeholders}))
                        AND s.ghostData IS NOT NULL AND length(s.ghostData) > 0""", idList + idList)
        rows = list(c.fetchall())

    # 2. If fewer than 3 ghosts were found, pull the remaining ghosts from this level's scores
    if len(rows) < 3:
        existingIds = {rowGet(r, "id") for r in rows}

        if not gameId and rows:
            gameId = rowGet(rows[0], "gameId", "")

        if gameId:
            c.execute(f"""SELECT s.*, {_GHOST_ROW_SELECT_EXTRA}
                         FROM scores s
                         LEFT JOIN players p ON s.playerId = p.id
                         WHERE s.gameId = ? AND s.ghostData IS NOT NULL AND length(s.ghostData) > 0
                         ORDER BY s.time ASC""", (gameId,))
            for g in c.fetchall():
                if rowGet(g, "id") not in existingIds:
                    rows.append(g)
                    existingIds.add(rowGet(g, "id"))
                if len(rows) >= 3:
                    break

    conn.close()

    if not rows:
        return buildSingleFakeGhostResponse(0, "Rival")

    # 3. Deduplicate
    seen = set()
    unique_rows = []
    for r in rows:
        r_id = rowGet(r, "id")
        if r_id not in seen:
            seen.add(r_id)
            unique_rows.append(r)

    # 4. Sort fastest time (lowest ms) to index 0 (Top card / Gold Target)
    def ghostSortKey(r):
        t = safeInt(rowGet(r, "time", 0))
        return (0 if t > 0 else 1, t)

    unique_rows.sort(key=ghostSortKey)

    return packageGhostListResponse(unique_rows[:3], playerUnit)

@route("/v1/trophy/ghostsbytrophies")
def hTrophyGhostsByTrophies(params, body):
    gameId = params.get("gameId", [""])[0]
    playerUnit = params.get("playerUnit", ["Any"])[0]

    conn = getDbConnection()
    c = conn.cursor()
    c.execute(f"""SELECT s.*, {_GHOST_ROW_SELECT_EXTRA}
                 FROM scores s
                 LEFT JOIN players p ON s.playerId = p.id
                 WHERE s.gameId = ? AND s.ghostData IS NOT NULL AND length(s.ghostData) > 0
                 ORDER BY s.time ASC LIMIT 3""", (gameId,))
    rows = list(c.fetchall())
    conn.close()

    if not rows:
        return handleFallbackCreatorGhost(gameId, playerUnit)

    def ghostSortKey(r):
        t = safeInt(rowGet(r, "time", 0))
        return (0 if t > 0 else 1, t)

    rows.sort(key=ghostSortKey)
    return packageGhostListResponse(rows, playerUnit)


@route("/v1/trophy/ghostsbytime")
def hTrophyGhostsByTime(params, body):
    gameId = params.get("gameId", [""])[0]
    playerUnit = params.get("playerUnit", ["Any"])[0]

    conn = getDbConnection()
    c = conn.cursor()
    c.execute(f"""SELECT s.*, {_GHOST_ROW_SELECT_EXTRA}
                 FROM scores s
                 LEFT JOIN players p ON s.playerId = p.id
                 WHERE s.gameId = ? AND s.ghostData IS NOT NULL AND length(s.ghostData) > 0
                 ORDER BY s.time ASC LIMIT 3""", (gameId,))
    rows = list(c.fetchall())
    conn.close()

    if not rows:
        return handleFallbackCreatorGhost(gameId, playerUnit)

    def ghostSortKey(r):
        t = safeInt(rowGet(r, "time", 0))
        return (0 if t > 0 else 1, t)

    rows.sort(key=ghostSortKey)
    return packageGhostListResponse(rows, playerUnit)

@route("/v1/ghost/bossbattle/get")
def hGhostBossbattle(params, body):
    return buildSingleFakeGhostResponse(0, "Boss")

@route("/v1/trophy/win", "/v1/trophy/lose")
def hTrophyAction(params, body): return {"status": "OK"}

@route("/v1/trophy/score/send")
def hTrophyScoreSend(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    fileSizes = params.get("FILE_SIZES", [""])[0]
    segments = splitFileSizesBody(fileSizes, body)
    if segments:
        try:
            meta = json.loads(segments[0].decode("utf-8"))
            gameId = safeStr(meta.get("gameId"))
            timeScore = safeInt(meta.get("time"))
            playerUnit = safeStr(meta.get("playerUnit", "Any"))
            applySetdataBody(playerId, meta)
            ghostBytes = segments[1] if len(segments) > 1 else b""
            
            if timeScore > 0 and gameId and playerId:
                conn = getDbConnection()
                c = conn.cursor()
                
                # Fetch player name
                c.execute("SELECT name FROM players WHERE id = ?", (playerId,))
                pRow = c.fetchone()
                pName = pRow["name"] if pRow else "Rival"
                
                # Unconditionally save the ghost record
                newGhostId = genOid()
                c.execute("""INSERT INTO scores 
                             (id, gameId, playerId, playerName, playerUnit, time, ghostData) 
                             VALUES (?,?,?,?,?,?,?)""",
                          (newGhostId, gameId, playerId, pName, playerUnit, timeScore, ghostBytes))
                
                # Update track best time and total play count
                c.execute("""UPDATE minigames SET 
                             bestTime = CASE WHEN bestTime <= 0 OR ? < bestTime THEN ? ELSE bestTime END,
                             timesPlayed = timesPlayed + 1
                             WHERE id = ?""", (timeScore, timeScore, gameId))
                conn.commit()
                conn.close()
                print(f"[Trophy] Ghost SAVED: {pName} on '{gameId}' -> {timeScore}ms ({len(ghostBytes)} bytes ghost, ID: {newGhostId})")
                
        except Exception as e:
            print(f"[Trophy] Error parsing trophy submission: {e}")
            
    result = {"status": "OK"}
    injectWalletData(result, playerId)
    return result


# ---------------------------------------------------------------------
# Race Highscores & Replay Uploads
# ---------------------------------------------------------------------

@route("/v5/highscore/send")
def hHighscoreSend(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    gameId = params.get("gameId", [""])[0]
    starts = safeInt(params.get("starts", ["1"])[0], 1)
    timeScore = safeInt(params.get("time", ["0"])[0], 0)
    stars = safeInt(params.get("stars", ["0"])[0], 0)
    playerName = safeStr(unquote_plus(params.get("name", ["Player"])[0])).strip()
    playerUnit = params.get("playerUnit", ["Any"])[0]
    mainPath = params.get("mainPath", ["false"])[0]
    boost = params.get("boost", ["false"])[0]
    upgradeSum = safeInt(params.get("upgradeSum", ["0"])[0], 0)
    deathCount = safeInt(params.get("deathCount", ["0"])[0], 0)

    if timeScore > 0 and gameId and playerId:
        conn = getDbConnection()
        c = conn.cursor()
        
        # Unconditionally save the race run and ghost binary
        newGhostId = genOid()
        c.execute("""INSERT INTO scores 
                     (id, gameId, playerId, playerName, playerUnit, time, stars, boost, upgradeSum, deathCount, starts, mainPath, ghostData) 
                     VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                  (newGhostId, gameId, playerId, playerName, playerUnit, timeScore, stars, boost, upgradeSum, deathCount, starts, mainPath, body if body else b""))
        
        # Update track best time and total play count
        c.execute("""UPDATE minigames SET 
                     bestTime = CASE WHEN bestTime <= 0 OR ? < bestTime THEN ? ELSE bestTime END,
                     timesPlayed = timesPlayed + 1
                     WHERE id = ?""", (timeScore, timeScore, gameId))
        conn.commit()
        conn.close()
        print(f"[Race] Highscore SAVED: {playerName} on '{gameId}' -> {timeScore}ms ({len(body) if body else 0} bytes ghost, ID: {newGhostId})")

    return {"status": "OK", "rank": 1, "results": []}

@route("/v2/highscore/quit", "/v1/versus/score/quit", "/v1/friendly/score/quit")
def hHighscoreQuit(params, body):
    return {"status": "OK"}

# ---------------------------------------------------------------------
# Leaderboards & Charts
# ---------------------------------------------------------------------
@route("/v2/highscore/find", "/v1/highscore/next")
def hHighscoreFind(params, body):
    gameId = params.get("gameId", [""])[0]
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""SELECT * FROM scores WHERE gameId = ? 
                 ORDER BY time ASC LIMIT 50""", (gameId,))
    rows = c.fetchall()
    conn.close()
    leaderboardList = []
    for idx, r in enumerate(rows):
        leaderboardList.append({
            "playerId": safeStr(r["playerId"]),
            "name": safeStr(r["playerName"], "Rider"),
            "time": safeInt(r["time"]),
            "rank": idx + 1,
            "stars": safeInt(r["stars"]),
            "playerUnit": safeStr(r["playerUnit"]),
        })
    return {"status": "OK", "data": leaderboardList, "results": leaderboardList}

@route("/v1/trophy/leaderboardbygame")
def hTrophyLeaderboardByGame(params, body):
    gameId = params.get("gameId", [""])[0]
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""SELECT s.*, p.countryCode, p.mcTrophies, p.carTrophies
                 FROM scores s
                 LEFT JOIN players p ON s.playerId = p.id
                 WHERE s.gameId = ? 
                 ORDER BY s.time ASC LIMIT 50""", (gameId,))
    rows = c.fetchall()
    conn.close()
    leaderboardList = []
    for r in rows:
        leaderboardList.append({
            "playerId": safeStr(r["playerId"]),
            "name": safeStr(r["playerName"], "Rider"),
            "time": safeInt(r["time"]),
            "carTrophies": safeInt(rowGet(r, "carTrophies", 0)),
            "mcTrophies": safeInt(rowGet(r, "mcTrophies", 0)),
            "countryCode": safeStr(rowGet(r, "countryCode", "US"))
        })
    return {"status": "OK", "data": leaderboardList}

@route("/v1/trophy/leaderboard")
def hTrophyLeaderboard(params, body):
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""SELECT id, name, mcTrophies, carTrophies, countryCode FROM players 
                 ORDER BY (mcTrophies + carTrophies) DESC LIMIT 100""")
    rows = c.fetchall()
    conn.close()
    standings = []
    for r in rows:
        standings.append({
            "playerId": safeStr(r["id"]),
            "name": safeStr(r["name"]),
            "trophies": safeInt(r["mcTrophies"]) + safeInt(r["carTrophies"]),
            "mcTrophies": safeInt(r["mcTrophies"]),
            "carTrophies": safeInt(r["carTrophies"]),
            "countryCode": safeStr(rowGet(r, "countryCode", "US"))
        })
    return {"global": standings, "local": standings, "friend": []}

@route("/v1/creator/top")
def hCreatorTop(params, body):
    # Only creators that are real registered players - imported/external levels carry
    # their original real-backend creatorId verbatim (see _importSubfolderLevel/
    # _importFlatLevel), which never matches a row in `players`, and grouping by it
    # unfiltered used to surface that dangling id as a "top creator" with no profile
    # behind it. Excluding those rows entirely (rather than reassigning them to a
    # placeholder account) keeps this leaderboard free of ghost identities without
    # needing any visible extra player.
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""SELECT creatorId, creatorName, SUM(upThumbs) as popularity
                 FROM minigames WHERE creatorId IN (SELECT id FROM players)
                 GROUP BY creatorId
                 ORDER BY popularity DESC LIMIT 50""")
    rows = c.fetchall()
    conn.close()
    creatorsList = []
    for r in rows:
        creatorsList.append({
            "playerId": safeStr(r["creatorId"]),
            "name": safeStr(r["creatorName"]),
            "level": 1,
            "countryCode": "US"
        })
    wrappedData = [
        {"offset": 0, "leaderboard": creatorsList},
        {"offset": 1, "leaderboard": creatorsList}
    ]
    return {"data": wrappedData}

# Server.StarCollect.Win/Lose (client) - the adventure-map "collect N pieces" game
# mode (PsGameMode.StarCollect), which also covers the purple "Fresh & Free" bonus
# node (PsGameLoopFresh/PsGameModeAdventureFresh - a pure client-side cosmetic reskin
# of ordinary StarCollect where the 3 pickups render as diamonds and reward shards/
# diamonds instead of the usual map-piece unlock; no separate game mode or endpoint,
# same wire format). Both calls carry the same envelope shape as every other win/claim
# handler in this file (FILE_SIZES-optional JSON meta with "update"/"progression"
# keys, see StarCollect.cs) - this used to be a stub that discarded the body entirely,
# so finishing ANY adventure/star-collect level (including the diamond node) never
# actually persisted its coins/diamonds/shards reward or adventure-path progress.
def _handleStarcollectResult(params, body, isWin: bool):
    playerId = params.get("PLAYER_ID", [""])[0]
    fileSizes = params.get("FILE_SIZES", [""])[0]
    segments = splitFileSizesBody(fileSizes, body)
    metaSeg = segments[0] if segments else body
    try:
        meta = json.loads(metaSeg.decode("utf-8")) if metaSeg else {}
    except Exception:
        meta = {}
    if playerId and isinstance(meta, dict):
        applySetdataBody(playerId, meta)
    if isWin:
        gameId = safeStr(meta.get("gameId"))
        timeScore = safeInt(meta.get("time", 0), 0)
        if gameId and timeScore > 0:
            conn = getDbConnection()
            conn.cursor().execute(
                """UPDATE minigames SET
                   bestTime = CASE WHEN bestTime <= 0 OR ? < bestTime THEN ? ELSE bestTime END,
                   timesPlayed = timesPlayed + 1 WHERE id = ?""",
                (timeScore, timeScore, gameId))
            conn.commit(); conn.close()
    result = {"status": "OK"}
    injectWalletData(result, playerId)
    return result

@route("/v1/starcollect/win")
def hStarcollectWin(params, body):
    return _handleStarcollectResult(params, body, True)

@route("/v1/starcollect/lose")
def hStarcollectLose(params, body):
    return _handleStarcollectResult(params, body, False)

@route("/v1/bossbattle/new")
def hBossBattle(params, body):
    # AdventureBattle.SearchMinigame (client) expects a real ClientTools.ParseMinigameList
    # payload here - an empty list just means "no boss battle available" (safe, no crash),
    # but Boss Battle mode then has nothing to load. Hand back a real published level so the
    # mode is actually playable; fall back to any level at all (any state) if nothing is
    # published yet, so a fresh install with only local drafts still works.
    playerUnit = params.get("playerUnit", ["Any"])[0]
    data = queryMinigames(playerUnit=playerUnit, state="public", orderBy="RANDOM()", limit=1)
    if not data:
        data = queryMinigames(playerUnit=playerUnit, orderBy="RANDOM()", limit=1)
    if not data:
        data = queryMinigames(orderBy="RANDOM()", limit=1)
    return {"data": data, "results": data}

@route("/v1/rating/save")
def hRating(params, body):
    # Server.Rating.Save (client) - sent when the player picks thumbs up/down on the
    # post-race screen. "rating" arrives as the PsRating enum's name (e.g. "Positive"),
    # matching what ClientTools.ParseRating expects back in the level's own metadata.
    gameId = params.get("gameId", [""])[0]
    playerId = params.get("PLAYER_ID", [""])[0]
    rating = params.get("rating", [""])[0]
    setPlayerRatingForLevel(gameId, playerId, rating)
    return {"status": "OK"}

@route("/v1/push/token/save")
def hPushToken(params, body): return {"status": "OK"}

@route("/v1/notification/find")
def hNotifications(params, body): return {"data": [], "results": []}

@route("/v1/notification/count")
def hNotificationCount(params, body): return {"count": 0}

@route("/v1/planet/current/find")
def hPlanet(params, body):
    return {"data": [], "results": [], "planet": {"id": genOid(), "name": "Home", "level": 1}, "status": "OK"}

@route("/v1/reward/claim")
def hRewardClaim(params, body): return {"status": "OK", "rewards": []}

@route("/v1/metagame/gettimed")
def hTimedEvent(params, body): return {"data": [], "results": [], "events": []}

@route("/v1/ads/config")
def hAdsConfig(params, body): return {"enabled": False, "config": {}}

@route("/v1/analytics/trackpurchase", "/v1/analytics/trackevent")
def hAnalytics(params, body): return {"status": "OK"}

@route("/v1/iap/config")
def hIapConfig(params, body): return {"products": [], "config": {}}

@route("/v1/iap/purchase", "/v1/iap/nonce")
def hIapAction(params, body): return {"status": "OK", "nonce": genOid()}

def parseTeamBody(body):
    try:
        parsed = json.loads(body.decode("utf-8")) if body else {}
        return parsed if isinstance(parsed, dict) else {}
    except Exception:
        return {}

def buildTeamDict(conn, teamRow) -> dict:
    c = conn.cursor()
    teamId = safeStr(rowGet(teamRow, "id", ""))
    c.execute(
        "SELECT id, name, tag, teamRole, carTrophies, mcTrophies, countryCode, "
        "facebookId, gameCenterId FROM players WHERE teamId = ? "
        "ORDER BY (carTrophies + mcTrophies) DESC",
        (teamId,),
    )
    members = []
    memberList = []
    totalTrophies = 0
    for m in c.fetchall():
        mTrophies = safeInt(m["carTrophies"]) + safeInt(m["mcTrophies"])
        totalTrophies += mTrophies
        members.append({
            "id": safeStr(m["id"]),
            "playerId": safeStr(m["id"]),
            "name": safeStr(m["name"]),
            "tag": safeStr(m["tag"]),
            "role": safeStr(m["teamRole"], "Member"),
            "trophies": mTrophies,
            "countryCode": safeStr(m["countryCode"], "US"),
        })
        # ClientTools.ParseTeam() -> TeamData(dict) reads "memberList" (NOT
        # "members") into PlayerData[] via ClientTools.ParsePlayerList(), and
        # every PsUITeamProfileBanner rendered for a team's roster (the member
        # rows shown when a team popup is opened, or on the "My Team" screen)
        # is built straight from one of these PlayerData entries. We were
        # never sending "memberList" at all, so TeamData.memberList stayed
        # null on the client - CreateBatch() (which actually draws the member
        # rows) is properly null-guarded so this didn't crash by itself, but
        # it did mean the member roster silently never rendered. Send full
        # PlayerData-shaped entries here too so the roster actually shows up.
        memberList.append({
            "id": safeStr(m["id"]),
            "playerId": safeStr(m["id"]),
            "name": safeStr(m["name"]),
            "tag": safeStr(m["tag"]),
            "teamRole": safeStr(m["teamRole"], "Member"),
            "mcTrophies": safeInt(m["mcTrophies"]),
            "carTrophies": safeInt(m["carTrophies"]),
            "countryCode": safeStr(m["countryCode"], "US"),
            "facebookId": safeStr(m["facebookId"]),
            "gameCenterId": safeStr(m["gameCenterId"]),
        })
    return {
        # NOTE: the client's TeamData(Dictionary) constructor
        # (ClientTools.ParseTeam) reads these exact keys straight off the
        # TOP LEVEL of the response - "id", "name", "description",
        # "joinType", "requiredTrophies", "members"/"memberList", "score"
        # (not "trophies"!), "teamRole". A field it doesn't find just stays
        # at its C# default, which for the string fields ("id"/"name"/
        # "description") is NULL, not "" - and a null string handed to the
        # UI text widgets is exactly what crashes the game the moment a
        # team screen tries to render. So every key below has to exist and
        # be a real string/number here, never omitted.
        "id": teamId,
        "teamId": teamId,
        "name": safeStr(rowGet(teamRow, "name", "")),
        "teamName": safeStr(rowGet(teamRow, "name", "")),
        "tag": safeStr(rowGet(teamRow, "tag", "")),
        "description": safeStr(rowGet(teamRow, "description", "")),
        "joinType": "Open",
        "requiredTrophies": 0,
        "countryCode": safeStr(rowGet(teamRow, "countryCode", "US")),
        "ownerId": safeStr(rowGet(teamRow, "ownerId", "")),
        "memberCount": len(members),
        "score": totalTrophies,
        "trophies": totalTrophies,
        "members": members,
        "memberList": memberList,
        "createdAt": safeStr(rowGet(teamRow, "createdAt", "")),
    }

@route("/v1/team/get", "/v1/team/search", "/v1/team/suggest")
def hTeamGet(params, body):
    conn = getDbConnection()
    c = conn.cursor()
    playerId = safeStr(params.get("PLAYER_ID", [""])[0])
    top = parseTeamBody(body)
    print(f"[Team] get/search/suggest from {playerId}: params={dict(params)} body={top}")
    teamId = safeStr(top.get("id", top.get("teamId", params.get("id", params.get("teamId", [""]))[0])))
    nameQuery = safeStr(top.get("name", top.get("query", params.get("name", params.get("query", [""]))[0])))

    if not teamId and playerId:
        c.execute("SELECT teamId FROM players WHERE id = ?", (playerId,))
        row = c.fetchone()
        if row and row["teamId"]:
            teamId = row["teamId"]

    if teamId:
        c.execute("SELECT * FROM teams WHERE id = ?", (teamId,))
        row = c.fetchone()
        if row:
            team = buildTeamDict(conn, row)
            # /v1/team/get is deserialized straight into a TeamData from
            # the TOP LEVEL of this response (ClientTools.ParseTeam) - it
            # does NOT look inside a "team" key. Spread the flat team dict
            # at top level (keep "data"/"results" too, harmless extras).
            viewerRole = ""
            if playerId:
                c.execute("SELECT teamRole FROM players WHERE id = ? AND teamId = ?", (playerId, teamId))
                pr = c.fetchone()
                if pr:
                    viewerRole = safeStr(pr["teamRole"], "Member")
            resp = {**team, "status": "OK", "data": [team], "results": [team]}
            if viewerRole:
                resp["teamRole"] = viewerRole
            conn.close()
            return resp
        conn.close()
        # Still a flat (but id-less) TeamData so the client doesn't choke -
        # callers check string.IsNullOrEmpty(id) themselves.
        return {"status": "OK", "id": "", "name": "", "description": "", "joinType": "Open",
                "requiredTrophies": 0, "members": [], "memberCount": 0, "score": 0,
                "data": [], "results": []}

    # No specific team requested (search/suggest/list): return every team.
    if nameQuery:
        c.execute("SELECT * FROM teams WHERE name LIKE ? ORDER BY createdAt DESC", (f"%{nameQuery}%",))
    else:
        c.execute("SELECT * FROM teams ORDER BY createdAt DESC")
    teamList = [buildTeamDict(conn, r) for r in c.fetchall()]
    conn.close()
    return {"status": "OK", "data": teamList, "results": teamList}

@route("/v1/team/update")
def hTeamUpdate(params, body):
    playerId = safeStr(params.get("PLAYER_ID", [""])[0])
    top = parseTeamBody(body)
    print(f"[Team] update body from {playerId}: {top}")
    if not playerId:
        return {"status": "ERROR"}

    name = safeStr(top.get("name", top.get("teamName", ""))).strip()
    tag = safeStr(top.get("tag", "")).strip()
    description = safeStr(top.get("description", top.get("desc", ""))).strip()

    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM players WHERE id = ?", (playerId,))
    player = c.fetchone()
    if not player:
        conn.close()
        return {"status": "ERROR"}

    currentTeamId = safeStr(rowGet(player, "teamId", ""))

    if currentTeamId:
        # Player is already in a team: treat this as an edit. Only the
        # owner/an admin may rename/redescribe the team.
        role = safeStr(rowGet(player, "teamRole", "Member"))
        c.execute("SELECT * FROM teams WHERE id = ?", (currentTeamId,))
        team = c.fetchone()
        if not team:
            # Player's teamId pointed nowhere (stale data) -> fall through to create below.
            currentTeamId = ""
        elif role != "Creator":
            conn.close()
            return {"status": "ERROR", "message": "Only the team owner can edit the team."}
        else:
            if name:
                c.execute("UPDATE teams SET name = ? WHERE id = ?", (name, currentTeamId))
                c.execute("UPDATE players SET teamName = ? WHERE teamId = ?", (name, currentTeamId))
            if tag:
                c.execute("UPDATE teams SET tag = ? WHERE id = ?", (tag, currentTeamId))
            if "description" in top or "desc" in top:
                c.execute("UPDATE teams SET description = ? WHERE id = ?", (description, currentTeamId))
            conn.commit()
            c.execute("SELECT * FROM teams WHERE id = ?", (currentTeamId,))
            teamDict = buildTeamDict(conn, c.fetchone())
            conn.close()
            # Flat at top level, not nested under "team" - see buildTeamDict's note.
            return {**teamDict, "status": "OK", "teamRole": role, "hasJoinedTeam": True}

    if not name:
        conn.close()
        return {"status": "ERROR", "message": "Team name is required."}

    newId = genOid()
    countryCode = safeStr(rowGet(player, "countryCode", "US"))
    c.execute(
        "INSERT INTO teams (id, name, tag, description, countryCode, ownerId) VALUES (?,?,?,?,?,?)",
        (newId, name, tag, description, countryCode, playerId),
    )
    c.execute(
        "UPDATE players SET teamId = ?, teamName = ?, teamRole = 'Creator', hasJoinedTeam = 1 WHERE id = ?",
        (newId, name, playerId),
    )
    conn.commit()
    c.execute("SELECT * FROM teams WHERE id = ?", (newId,))
    teamDict = buildTeamDict(conn, c.fetchone())
    conn.close()
    print(f"[Team] Created team '{name}' ({newId}) owned by {playerId}")
    # Flat at top level, not nested under "team" - see buildTeamDict's note.
    return {**teamDict, "status": "OK", "teamRole": "Creator", "hasJoinedTeam": True}

@route("/v1/team/join")
def hTeamJoin(params, body):
    playerId = safeStr(params.get("PLAYER_ID", [""])[0])
    top = parseTeamBody(body)
    print(f"[Team] join body from {playerId}: {top}")
    targetTeamId = safeStr(top.get("id", top.get("teamId", ""))).strip()
    if not playerId or not targetTeamId:
        return {"status": "ERROR"}

    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM teams WHERE id = ?", (targetTeamId,))
    team = c.fetchone()
    if not team:
        conn.close()
        return {"status": "ERROR", "message": "Team not found."}

    c.execute(
        "UPDATE players SET teamId = ?, teamName = ?, teamRole = 'Member', hasJoinedTeam = 1 WHERE id = ?",
        (targetTeamId, safeStr(team["name"]), playerId),
    )
    conn.commit()
    teamDict = buildTeamDict(conn, team)
    conn.close()
    # Flat at top level, not nested under "team" - see buildTeamDict's note.
    return {**teamDict, "status": "OK", "teamRole": "Member", "hasJoinedTeam": True}

@route("/v1/team/leave")
def hTeamLeave(params, body):
    playerId = safeStr(params.get("PLAYER_ID", [""])[0])
    if not playerId:
        return {"status": "ERROR"}

    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT teamId, teamRole FROM players WHERE id = ?", (playerId,))
    player = c.fetchone()
    teamId = safeStr(rowGet(player, "teamId", "")) if player else ""
    role = safeStr(rowGet(player, "teamRole", "")) if player else ""

    c.execute(
        "UPDATE players SET teamId = '', teamName = '', teamRole = 'Member', hasJoinedTeam = 0 WHERE id = ?",
        (playerId,),
    )

    if teamId and role == "Creator":
        c.execute("SELECT id FROM players WHERE teamId = ? ORDER BY createdAt ASC LIMIT 1", (teamId,))
        successor = c.fetchone()
        if successor:
            c.execute("UPDATE players SET teamRole = 'Creator' WHERE id = ?", (successor["id"],))
            c.execute("UPDATE teams SET ownerId = ? WHERE id = ?", (successor["id"], teamId))
        else:
            c.execute("DELETE FROM teams WHERE id = ?", (teamId,))

    conn.commit()
    conn.close()
    return {"status": "OK", "teamId": "", "teamName": "", "teamRole": "Member", "hasJoinedTeam": False}

@route("/v1/team/kick")
def hTeamKick(params, body):
    playerId = safeStr(params.get("PLAYER_ID", [""])[0])
    top = parseTeamBody(body)
    print(f"[Team] kick body from {playerId}: {top}")
    targetId = safeStr(top.get("playerId", top.get("id", top.get("targetId", "")))).strip()
    if not playerId or not targetId:
        return {"status": "ERROR"}

    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT teamId, teamRole FROM players WHERE id = ?", (playerId,))
    requester = c.fetchone()
    c.execute("SELECT teamId FROM players WHERE id = ?", (targetId,))
    target = c.fetchone()

    if not requester or not target or not requester["teamId"] or requester["teamId"] != target["teamId"]:
        conn.close()
        return {"status": "ERROR", "message": "Not in the same team."}
    if safeStr(requester["teamRole"]) != "Creator":
        conn.close()
        return {"status": "ERROR", "message": "Only the team owner can kick."}
    # PsUICenterProfilePopup only ever shows the Kick button when
    # `this.m_user.playerId != PlayerPrefsX.GetUserId()` - the real client never lets
    # a Creator target themselves - but nothing stops a raw request from doing it. If
    # it ever happened, this handler alone would leave the team ownerless (no
    # teamRole='Creator' left, unlike /v1/team/leave which promotes a successor or
    # deletes an empty team), permanently blocking every future kick for that team
    # (the Creator-only check above would then reject everyone, forever).
    if targetId == playerId:
        conn.close()
        return {"status": "ERROR", "message": "Cannot kick yourself - use leave instead."}

    c.execute(
        "UPDATE players SET teamId = '', teamName = '', teamRole = 'Member', hasJoinedTeam = 0, teamKickReason = ? WHERE id = ?",
        ("Kicked from the team", targetId),
    )
    conn.commit()
    conn.close()
    return {"status": "OK"}

@route("/v1/team/kick/claim")
def hTeamKickClaim(params, body):
    playerId = safeStr(params.get("PLAYER_ID", [""])[0])
    if not playerId:
        return {"status": "ERROR"}
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT teamKickReason FROM players WHERE id = ?", (playerId,))
    row = c.fetchone()
    reason = safeStr(rowGet(row, "teamKickReason", "")) if row else ""
    c.execute("UPDATE players SET teamKickReason = '' WHERE id = ?", (playerId,))
    conn.commit()
    conn.close()
    return {"status": "OK", "reason": reason, "teamKickReason": reason}

@route("/v1/team/leaderboard")
def hTeamLeaderboard(params, body):
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM teams")
    teamList = [buildTeamDict(conn, r) for r in c.fetchall()]
    conn.close()
    teamList.sort(key=lambda t: t["trophies"], reverse=True)
    return {"status": "OK", "data": teamList, "results": teamList}

@route("/v1/season/claim")
def hSeasonClaim(params, body): return {"status": "OK", "rewards": []}

@route("/v1/season/previous")
def hSeasonPrevious(params, body): return {"data": [], "results": []}

@route("/v2/gif/save", "/v1/gif/save")
def hGif(params, body):
    # PsUICenterDeathShare.gifSendOk builds the shared message as literally just
    # this "url" (prefixed with "#bigbangracing\n") and hands it to
    # Share.ShareTextOnPlatform - it was NEVER going to AirDrop the gif itself, the
    # real game always shared a TEXT message containing a link to the uploaded gif.
    # Returning "" here (the old stub) meant that link was empty, so recipients
    # opening the shared text just saw a bare text snippet - not a crash, but not a
    # gif either. Saving the actual posted bytes and handing back a real, fetchable
    # URL is what makes that shared link resolve to the real gif.
    if not body:
        return {"status": "OK", "url": ""}
    os.makedirs(GIFS_DIR, exist_ok=True)
    gifId = genOid()
    with open(os.path.join(GIFS_DIR, gifId + ".gif"), "wb") as f:
        f.write(body)
    url = f"http://{localIp()}:{HTTP_PORT}/v1/gif/get?id={gifId}"
    return {"status": "OK", "url": url}

@route("/v1/gif/get")
def hGifGet(params, body):
    gifId = params.get("id", [""])[0]
    safeId = re.sub(r"[^A-Za-z0-9_-]", "", gifId)
    path = os.path.join(GIFS_DIR, safeId + ".gif")
    if safeId and os.path.isfile(path):
        with open(path, "rb") as f:
            return {"_binary": f.read(), "_content_type": "image/gif"}
    return {"_binary": b"", "_content_type": "image/gif"}

@route("/v1/youtube/getchannels")
def hYoutube(params, body): return {"data": [], "results": [], "channels": []}

@route("/v2/event/claim")
def hEventClaim(params, body):
    # Event.Claim/ClaimPatchNotes/ClaimGift - id + optional type as URL params,
    # ClaimGift additionally posts a SetData body. No per-gift-type reward
    # modeling (out of scope - the admin GUI's events are simple announcements,
    # not itemized gift contents), just apply whatever SetData came along.
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        applySetdataBody(playerId, top)
    result = {"status": "OK", "rewards": []}
    injectWalletData(result, playerId)
    return result

@route("/v1/event/feed")
def hEventFeed(params, body):
    # PsUICenterNewsPopup.DataSUCCEED reads {"data": [EventMessage, ...]} - fully
    # ContainsKey-guarded client-side, so an empty list here (no events configured
    # yet) is perfectly safe, same as before.
    data = getAllEventMessages()
    return {"data": data, "results": data}

# ---------------------------------------------------------------------
# Tournament
# ---------------------------------------------------------------------
# Server.Tournament (client) is a real, reachable single-player-ish score-attack
# mode (PsGameLoopTournament/PsGameModeTournament/PsUITournamentLeaderboard) -
# unlike Versus/Friendly/TimedEvents (dead code, nothing ever calls
# Server.TimedEvents.Initialize or Versus/Friendly.Create in this client build,
# confirmed by grepping for callers). The login payload advertises a single
# persistent tournament (activeTournament + an eventType="Tournament" entry in
# eventList - see getAllEventMessages()/buildTournamentEventMessage() below),
# configured via the admin GUI in the `tournamentConfig` singleton row. Runs
# are tracked for real in the `scores` table under a synthetic gameId
# ("tournament:<tournamentId>") that can never collide with a real level id
# (those are hex ObjectIds).
def getTournamentConfig() -> dict:
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM tournamentConfig WHERE id = 1")
    row = c.fetchone()
    if row is None:
        c.execute("INSERT INTO tournamentConfig (id) VALUES (1)")
        conn.commit()
        c.execute("SELECT * FROM tournamentConfig WHERE id = 1")
        row = c.fetchone()
    conn.close()
    return dict(row)

def setTournamentConfig(fields: dict):
    getTournamentConfig()  # ensure the singleton row exists before updating it
    fields = dict(fields or {})
    if not fields: return
    conn = getDbConnection()
    c = conn.cursor()
    setParts = [f"{k} = ?" for k in fields.keys()]
    values = list(fields.values()) + [1]
    c.execute(f"UPDATE tournamentConfig SET {', '.join(setParts)} WHERE id = ?", values)
    conn.commit()
    conn.close()

def tournamentGameId() -> str:
    """The tournament's actual score/ghost storage key - MUST be the tournament LEVEL's
    own real minigameId, matching exactly what the real client sends when submitting a
    run (PsGameModeTournament.cs: `new Tournament.TournamentSendScoreData(
    PsState.m_activeGameLoop.m_minigameId, ...)` - the level's id, not some separate
    abstract "tournament id"). This used to return a synthetic "tournament:<tournamentId>"
    key instead - since admins don't normally change tournamentId when switching which
    level is the tournament (it stays "tour_main"), every tournament level that was ever
    configured kept sharing that ONE key forever: switching the tournament to a new level
    never started a fresh leaderboard/ghost pool, so the personal-best time and the ghost
    shown in-game kept being whatever was last submitted for a completely different map."""
    return safeStr(getTournamentConfig().get("minigameId"))

def _getPlayerTournamentBestTime(playerId: str) -> int:
    """This player's own best submitted time for the current tournament, in the same
    raw score units as scores.time - 0 when they haven't submitted one yet (which
    PsGameLoopTournament.StartLoop treats as "no personal best" and falls back to
    int.MaxValue, exactly like a real empty tournament record)."""
    if not playerId:
        return 0
    conn = getDbConnection()
    row = conn.cursor().execute(
        "SELECT time FROM scores WHERE gameId = ? AND playerId = ?",
        (tournamentGameId(), playerId)).fetchone()
    conn.close()
    return safeInt(row["time"], 0) if row else 0

def _buildTournamentEventMessage():
    """The tournament's minigameId/prizeCoins/etc. only reach the client through
    an eventType="Tournament" entry in eventList (LoginFlow.cs:460-484,
    ClientTools.ParseEventMessageFromDict) - NOT through "activeTournament"
    (that's just a per-player status overlay keyed by tournamentId, already
    handled correctly elsewhere in hLogin). Returns None if no level has been
    picked yet (admin GUI hasn't configured a tournament), same as before."""
    cfg = getTournamentConfig()
    minigameId = safeStr(cfg.get("minigameId"))
    if not minigameId:
        return None
    # PsUITournamentLeaderboard's "host" row/catch-up logic keys off eventData.ownerId
    # matching a real player id (PsUITournamentLeaderboard.cs:234-242) - hardcoding ""
    # here left that permanently unresolvable. The tournament level's own creator is
    # the natural "owner" in this single-tournament model. ownerName is resolved the
    # same way (from the level's own creatorName) rather than a manually-typed admin
    # field, so it can never drift out of sync with whichever level is actually picked.
    levelRow = getMinigameRow(minigameId)
    if levelRow is None:
        # The configured level no longer exists (deleteMinigameSafely disables the
        # tournament when its own level is deleted through the server, but this stays
        # as a second line of defense - e.g. a restored/edited DB). Advertising a
        # tournament whose level can't be loaded is exactly what makes
        # PsGameLoopTournament crash on entry, so don't advertise one at all.
        print(f"[Tournament] Configured level {minigameId} no longer exists - hiding the tournament")
        return None
    ownerId = safeStr(levelRow["creatorId"])
    ownerName = safeStr(levelRow["creatorName"])
    msg = {
        "eventName": "Tournament", "eventType": "Tournament", "id": 1,
        "header": safeStr(cfg.get("header")), "message": safeStr(cfg.get("message")),
        "label": "", "popup": False, "floatingNode": bool(cfg.get("floatingNode", 0)), "newsFeed": False,
        "startTime": safeInt(cfg.get("startTime"), 0),
        "uris": [],
        "eventData": {
            "minigameId": minigameId,
            "tournamentId": safeStr(cfg.get("tournamentId"), "tour_main"),
            "ccCap": float(cfg.get("ccCap", -1.0) or -1.0),
            "prizeCoins": safeInt(cfg.get("prizeCoins"), 500),
            "acceptingNewScores": bool(cfg.get("acceptingNewScores", 1)),
            "ownerId": ownerId, "ownerName": ownerName,
            "ownerFacebookId": "", "youtuber": "", "youtubeSubscriberCount": 0, "youtuberId": "",
            "playerUnit": safeStr(cfg.get("playerUnit"), "Any"),
            "useCreatorUpgrades": bool(cfg.get("useCreatorUpgrades", 0)),
        },
    }
    # ParseEventMessageFromDict does an UNGUARDED (long) cast on endTime when the
    # key is present at all - only include it when it's a real, large ms value.
    endTime = safeInt(cfg.get("endTime"), 0)
    if endTime > 0:
        msg["endTime"] = endTime
    # PsUITournamentHeader/PsUICenterTournament compute m_timeLeft from
    # m_activeTournament.localEndTime, which ParseEventMessageFromDict ONLY sets when
    # "secondsLeft" is present on the event (separately from "endTime"/"startTime"
    # above) - localEndTime = now + secondsLeft. Without it, localEndTime stays at its
    # default of 0 (way in the past), so m_timeLeft is always negative and the client
    # shows "This Tournament is over!" no matter what endTime/duration is configured.
    # A duration of 0 ("unlimited" in the admin GUI) has no literal "never" to send
    # here since this is a plain countdown, so it's approximated with a very large
    # number of seconds (10 years) instead.
    if endTime > 0:
        secondsLeft = max(0, (endTime - nowMs()) // 1000)
    else:
        secondsLeft = 315360000
    msg["secondsLeft"] = secondsLeft
    return msg

def _eventRowToDict(row) -> dict:
    msg = {
        "eventName": safeStr(row["eventName"]), "eventType": safeStr(row["eventType"], "Event"),
        "id": safeInt(row["id"], 0),
        "header": safeStr(row["header"]), "message": safeStr(row["message"]),
        "label": safeStr(row["label"]),
        "popup": bool(row["popup"]), "floatingNode": bool(row["floatingNode"]), "newsFeed": bool(row["newsFeed"]),
        "startTime": safeInt(row["startTime"], 0),
        "uris": [], "eventData": {},
    }
    endTime = safeInt(row["endTime"], 0)
    if endTime > 0:
        msg["endTime"] = endTime
    # ClientTools.ParseEventMessageFromDict ONLY sets EventMessage.localEndTime when a
    # "secondsLeft" key is present (separately from "endTime"/"startTime" above) -
    # localEndTime = now + secondsLeft. Without it localEndTime stays at its C# default
    # of 0 (always in the past), and PsMainMenuState's popup/floating-node gate requires
    # localEndTime >= now - so a regular news/gift event with no secondsLeft can never
    # actually show, exactly the same bug the tournament event had (see
    # _buildTournamentEventMessage). A duration of 0 ("no end configured") is
    # approximated with a very large number of seconds (10 years), same convention.
    if endTime > 0:
        msg["secondsLeft"] = max(0, (endTime - nowMs()) // 1000)
    else:
        msg["secondsLeft"] = 315360000
    # ClientTools.ParseEventGiftComponent dispatches on eventData["type"] into one of
    # upgradeItem/editorItem/chest/resource/hat/trail/timed (EventGift*.cs) - without a
    # populated eventData, a "Gift" event falls into the unrecognized-type branch and
    # giftContent stays null, so claiming it computes no reward at all.
    giftType = safeStr(rowGet(row, "giftType", ""))
    if safeStr(row["eventType"]) == "Gift" and giftType:
        eventData = {"type": giftType, "identifier": safeStr(rowGet(row, "giftIdentifier", ""))}
        giftAmount = safeInt(rowGet(row, "giftAmount", 0), 0)
        if giftAmount > 0:
            eventData["amount"] = giftAmount
        giftTexture = safeInt(rowGet(row, "giftTexture", -1), -1)
        if giftTexture >= 0:
            eventData["texture"] = giftTexture
        msg["eventData"] = eventData
    return msg

def getAllEventMessages() -> list:
    """Combined eventList used by both the login payload and /v1/event/feed -
    every row in `events` plus the synthesized Tournament entry, if configured."""
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM events ORDER BY id DESC")
    rows = c.fetchall()
    conn.close()
    messages = [_eventRowToDict(r) for r in rows]
    tournamentMsg = _buildTournamentEventMessage()
    if tournamentMsg:
        messages.append(tournamentMsg)
    return messages

def _selectLoginEventMessage(messages: list) -> dict:
    """LoginFlow.cs only ever shows the login popup/floating-news-node from the
    login response's OWN top-level "eventMessage" key (Server/LoginFlow.cs:485-490) -
    NOT from anything in "eventList" (that only feeds the News Feed screen, gifts and
    tournaments, see getAllEventMessages()'s docstring). Picks the most recent (highest
    id, since `messages` is already DESC-ordered) event with popup=True that's within
    its own active time window (mirroring the client's own localStartTime/localEndTime
    gate in PsMainMenuState so an expired/not-yet-started event is never sent), or None
    if there isn't one."""
    now = nowMs()
    for msg in messages:
        if not msg.get("popup"):
            continue
        startTime = msg.get("startTime", 0)
        if startTime and startTime > now:
            continue
        endTime = msg.get("endTime", 0)
        if endTime and endTime < now:
            continue
        return msg
    return None

@route("/v1/tournament/join")
def hTournamentJoin(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        applySetdataBody(playerId, top)
    result = {"status": "OK", "tournamentId": getTournamentConfig()["tournamentId"]}
    injectWalletData(result, playerId)
    return result

@route("/v1/tournament/score/send")
def hTournamentScoreSend(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    fileSizes = params.get("FILE_SIZES", [""])[0]
    segments = splitFileSizesBody(fileSizes, body)
    metaSeg = segments[0] if segments else body
    ghostBytes = segments[1] if len(segments) > 1 else b""
    try:
        meta = json.loads(metaSeg.decode("utf-8")) if metaSeg else {}
    except Exception:
        meta = {}
    timeScore = safeInt(meta.get("time", 0), 0)
    playerUnit = safeStr(meta.get("playerUnit", "Any"), "Any")
    if playerId and timeScore > 0:
        # Trust the client's own "gameId" (the real level id - Tournament.SendScore
        # always sends PsState.m_activeGameLoop.m_minigameId here) over re-deriving it
        # from the admin's current tournament config, in case the two are momentarily
        # out of sync (e.g. the admin is mid-edit of which level is active).
        gameId = safeStr(meta.get("gameId")) or tournamentGameId()
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT name FROM players WHERE id = ?", (playerId,))
        pRow = c.fetchone()
        playerName = safeStr(pRow["name"], "Player") if pRow else "Player"
        # ORDER BY time ASC + LIMIT 1 (not a plain fetchone(), which returns whichever
        # row SQLite happens to return first when several already exist for this
        # player) - always finds the player's real best, and the cleanup right after
        # merges away any other duplicate rows so they can never keep accumulating.
        c.execute("SELECT id, time FROM scores WHERE gameId = ? AND playerId = ? ORDER BY time ASC LIMIT 1",
                   (gameId, playerId))
        existing = c.fetchone()
        c.execute("DELETE FROM scores WHERE gameId = ? AND playerId = ? AND id != ?",
                   (gameId, playerId, existing["id"] if existing else ""))
        if existing:
            # Only a new personal best overwrites the stored run/ghost, same as a real leaderboard.
            if timeScore < safeInt(existing["time"], 2**31 - 1):
                # ghostData is only included in the SET clause when this submission
                # actually carries ghost bytes - PsGameModeRace.KeepBestGhost can send a
                # genuinely-faster time with an unfinished/empty ghost segment (recording
                # ghost not yet finalized), and blindly overwriting with that would wipe
                # out a previously-good ghost even though the time itself is legitimate.
                if ghostBytes:
                    c.execute("""UPDATE scores SET time = ?, playerName = ?, playerUnit = ?, ghostData = ?
                                 WHERE id = ?""",
                              (timeScore, playerName, playerUnit, ghostBytes, existing["id"]))
                else:
                    c.execute("""UPDATE scores SET time = ?, playerName = ?, playerUnit = ?
                                 WHERE id = ?""",
                              (timeScore, playerName, playerUnit, existing["id"]))
        else:
            c.execute("""INSERT INTO scores (id, gameId, playerId, playerName, playerUnit, time, ghostData)
                         VALUES (?,?,?,?,?,?,?)""",
                      (genOid(), gameId, playerId, playerName, playerUnit, timeScore,
                       ghostBytes if ghostBytes else None))
        conn.commit()
        conn.close()
        print(f"[Tournament] Score: {playerName} -> {timeScore}ms ({len(ghostBytes)} bytes ghost)")
    # meta itself is the envelope applySetdataBody expects (it reads meta["update"]["Resources"]
    # internally) - passing meta["update"] here instead used to double-unwrap one level too many,
    # so the coins/diamonds/shards patch a tournament run computes was silently never applied.
    if playerId and isinstance(meta, dict):
        applySetdataBody(playerId, meta)
    result = {"status": "OK"}
    injectWalletData(result, playerId)
    return result

def _buildTournamentLeaderboard(playerId: str) -> dict:
    # Tournament.ParseTournamentLeaderboard reads globalParticipants/acceptingNewScores/
    # globalNitroPot/roomNitroPot/ownerTime/room/roomCount at the top level (all
    # ContainsKey-guarded with sane fallbacks client-side), then feeds the whole
    # response into HighScores.ParseDataEntriesJSON for the "data" list - which
    # needs the short-key HighscoreDataEntry shape (n/t/s/fb/gc/p/countryCode),
    # NOT the long-form keys used elsewhere in this file.
    conn = getDbConnection()
    c = conn.cursor()
    # PsUITournamentLeaderboard.CreateLeaderboardEntries builds a Dictionary keyed by
    # playerId (m_entryDictionary.Add(...)) while walking this "data" list - Dictionary.Add
    # throws (an unhandled ArgumentException, crashing the client the instant it opens the
    # tournament screen) if the SAME playerId appears twice. `scores` legitimately keeps
    # multiple rows per player for a level (normal-race ghost history), but a tournament
    # leaderboard needs at most one row per player - the inner correlated subquery keeps
    # only each player's single best (lowest-time) row for this gameId.
    c.execute("""SELECT s.*, p.countryCode, p.facebookId, p.gameCenterId
                 FROM scores s LEFT JOIN players p ON s.playerId = p.id
                 WHERE s.gameId = ? AND s.time > 0
                 AND s.id = (SELECT s2.id FROM scores s2
                             WHERE s2.gameId = s.gameId AND s2.playerId = s.playerId
                             ORDER BY s2.time ASC, s2.id ASC LIMIT 1)
                 ORDER BY s.time ASC LIMIT 50""", (tournamentGameId(),))
    rows = c.fetchall()
    # PsUITournamentLeaderboard.SetTournamentData reads ownerTime as the HOST's own
    # time (m_hostTime), which it then inserts as a distinct leaderboard row
    # (GetHostHighscoreDataEntry) - it's the tournament level's own published creator
    # run, not whichever tournament participant currently happens to be fastest.
    levelRow = getMinigameRow(tournamentGameId())
    ownerTime = safeInt(levelRow["bestTime"], 0) if levelRow is not None else 0
    ownerId = safeStr(levelRow["creatorId"]) if levelRow is not None else ""
    conn.close()
    entries = []
    for r in rows:
        # PsUITournamentLeaderboard.SetTournamentData ALWAYS injects its own "host" row
        # for ownerId (using ownerTime, above) into this same list - if the host also has
        # a normal entry here (because they submitted their own real tournament run, e.g.
        # the level's creator playing their own tournament), their playerId ends up in the
        # list twice, and CreateLeaderboardEntries' Dictionary.Add(playerId, ...) throws on
        # the second occurrence, crashing the client the instant it opens the tournament
        # screen. The host is only ever meant to appear via that separate injected row.
        if ownerId and safeStr(r["playerId"]) == ownerId:
            continue
        entries.append({
            "n": safeStr(r["playerName"], "Rider"),
            "t": safeInt(r["time"], 0),
            "s": 0,
            "p": safeStr(r["playerId"]),
            "fb": safeStr(rowGet(r, "facebookId", "")),
            "gc": safeStr(rowGet(r, "gameCenterId", "")),
            "countryCode": safeStr(rowGet(r, "countryCode", "US")),
        })
    return {
        "data": entries, "results": entries,
        "globalParticipants": len(entries),
        "acceptingNewScores": True,
        "globalNitroPot": 0, "roomNitroPot": 0,
        "ownerTime": ownerTime,
        "room": 1, "roomCount": 1,
    }

@route("/v1/tournament/score/get", "/v1/tournament/ownerroomchange")
def hTournamentScoreGet(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    return _buildTournamentLeaderboard(playerId)

@route("/v1/tournament/claim")
def hTournamentClaim(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    try:
        top = json.loads(body.decode("utf-8")) if body else {}
    except Exception:
        top = {}
    if playerId and isinstance(top, dict):
        applySetdataBody(playerId, top)
    # No other real racers to be "ranked against" - a flat, always-available
    # completion reward beats fabricating a fake competitive placement.
    if playerId:
        conn = getDbConnection()
        conn.cursor().execute("UPDATE players SET coins = coins + 500 WHERE id = ?", (playerId,))
        conn.commit(); conn.close()
    result = {"status": "OK", "rewards": [{"type": "coins", "amount": 500}]}
    injectWalletData(result, playerId)
    return result

@route("/v1/tournament/claimyoutubernitros", "/v1/tournament/setsuperfuel")
def hTournamentAction(params, body): return {"status": "OK"}

@route("/v1/tournament/tournamentnitro")
def hTournamentBooster(params, body): return {"nitro": 3, "status": "OK"}

@route("/v1/tournament/ghosts", "/v1/tournament/ghost", "/v1/tournament/ghosts/latest")
def hTournamentGhosts(params, body):
    # ClientTools.ParseGhostDatas reads a binary body + FILE_SIZES response header,
    # not JSON - same wire format as the trophy ghost endpoints (packageGhostListResponse).
    # Tournament.GetGhostsByIds hits /v1/tournament/ghost (singular) with a "playerIds"
    # (comma-separated) param when the player taps ONE specific leaderboard entry to
    # spectate - previously ignored, always returning the top-3 regardless, so spectating
    # anyone outside the top 3 silently showed the wrong ghost.
    playerIdsRaw = params.get("playerIds", [""])[0]
    playerIdList = [pId.strip() for pId in playerIdsRaw.split(",") if pId.strip()]
    gameId = tournamentGameId()
    conn = getDbConnection()
    c = conn.cursor()
    # A player can have several `scores` rows for the same level (normal-race ghost
    # history) - the correlated subquery below keeps only each player's single best
    # (lowest-time) row, same reasoning as _buildTournamentLeaderboard: the top-3
    # fallback should show 3 DIFFERENT players, and the by-id lookup should return
    # exactly one ghost per requested player.
    if playerIdList:
        placeholders = ",".join(["?"] * len(playerIdList))
        c.execute(f"""SELECT s.*, {_GHOST_ROW_SELECT_EXTRA}
                     FROM scores s LEFT JOIN players p ON s.playerId = p.id
                     WHERE s.gameId = ? AND s.playerId IN ({placeholders})
                     AND s.id = (SELECT s2.id FROM scores s2
                                 WHERE s2.gameId = s.gameId AND s2.playerId = s.playerId
                                 ORDER BY s2.time ASC, s2.id ASC LIMIT 1)""",
                  [gameId] + playerIdList)
    else:
        c.execute(f"""SELECT s.*, {_GHOST_ROW_SELECT_EXTRA}
                     FROM scores s LEFT JOIN players p ON s.playerId = p.id
                     WHERE s.gameId = ? AND s.time > 0
                     AND s.id = (SELECT s2.id FROM scores s2
                                 WHERE s2.gameId = s.gameId AND s2.playerId = s.playerId
                                 ORDER BY s2.time ASC, s2.id ASC LIMIT 1)
                     ORDER BY s.time ASC LIMIT 3""", (tournamentGameId(),))
    rows = list(c.fetchall())
    # The host/owner (the level's own creator - see _buildTournamentEventMessage) is
    # spectatable via PsUITournamentLeaderboard's injected host row even if they never
    # actually submitted a tournament run themselves - in that case there's no `scores`
    # row for them at all, so fall back to the level's own published creator ghost,
    # same pattern as hTrophyGhostsByTime padding a short leaderboard with it.
    if not playerIdList or any(pId not in {safeStr(r["playerId"]) for r in rows} for pId in playerIdList):
        levelRow = getMinigameRow(gameId)
        if levelRow is not None and levelRow["creatorGhost"] and (
                not playerIdList or safeStr(levelRow["creatorId"]) in playerIdList):
            creatorDict = {
                "id": safeStr(levelRow["id"]), "playerId": safeStr(levelRow["creatorId"]),
                "playerName": safeStr(levelRow["creatorName"], "Creator"),
                "time": safeInt(levelRow["bestTime"], 0), "ghostData": levelRow["creatorGhost"],
                "countryCode": safeStr(rowGet(levelRow, "countryCode", "US")),
                "facebookId": "", "gameCenterId": "", "teamId": "", "teamName": "",
            }
            if not any(safeStr(r["playerId"]) == creatorDict["playerId"] for r in rows):
                rows.append(creatorDict)
    conn.close()
    if not rows:
        return buildSingleFakeGhostResponse(0, "Rival")
    return packageGhostListResponse(rows, params.get("playerUnit", ["Any"])[0])

@route("/v1/tournament/comment/save")
def hTournamentCommentSave(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    message = unquote_plus(params.get("comment", [""])[0]).strip()[:500]
    if message and playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT name, tag, facebookId, gameCenterId, teamName FROM players WHERE id = ?", (playerId,))
        row = c.fetchone()
        name = safeStr(row["name"], "Player") if row else "Player"
        tag = safeStr(row["tag"]) if row else ""
        facebookId = safeStr(row["facebookId"]) if row else ""
        gameCenterId = safeStr(row["gameCenterId"]) if row else ""
        teamName = safeStr(row["teamName"]) if row else ""
        c.execute("""INSERT INTO chatMessages
                     (playerId, name, facebookId, gameCenterId, tag, comment, timestamp, type, teamName, admin, customData)
                     VALUES (?, ?, ?, ?, ?, ?, ?, 'tournament', ?, 0, '{}')""",
                  (playerId, name, facebookId, gameCenterId, tag, message, nowEpochMs(), teamName))
        conn.commit(); conn.close()
    return hTournamentCommentGet(params, body)

@route("/v1/tournament/comment/get")
def hTournamentCommentGet(params, body):
    limit = max(1, min(safeInt(params.get("limit", ["50"])[0], 50), 100))
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("SELECT * FROM chatMessages WHERE type = 'tournament' ORDER BY id DESC LIMIT ?", (limit,))
    rows = c.fetchall()
    conn.close()
    data = []
    for row in rows:
        data.append({
            "playerId": safeStr(row["playerId"]), "name": safeStr(row["name"], "Player"),
            "comment": safeStr(row["comment"]), "tag": safeStr(row["tag"]),
            "facebookId": safeStr(row["facebookId"]), "gameCenterId": safeStr(row["gameCenterId"]),
            "admin": bool(row["admin"]),
        })
    return {"status": "OK", "data": data, "results": data}

@route("/v1/global/chat/find")
def hGlobalChat(params, body):
    limit = max(1, min(safeInt(params.get("limit", ["50"])[0], 50), 100))
    conn = getDbConnection()
    c = conn.cursor()
    # type IS NULL: keep tournament chat (type='tournament') out of global chat.
    c.execute("SELECT * FROM chatMessages WHERE type IS NULL ORDER BY id DESC LIMIT ?", (limit,))
    rows = c.fetchall()
    conn.close()
    data = []
    for row in rows:
        custom = safeJsonLoads(row["customData"], {})
        data.append({
            "playerId": safeStr(row["playerId"]),
            "name": safeStr(row["name"], "Player"),
            "facebookId": safeStr(row["facebookId"]),
            "gameCenterId": safeStr(row["gameCenterId"]),
            "tag": safeStr(row["tag"]),
            "comment": safeStr(row["comment"]),
            "timestamp": safeInt(row["timestamp"]),
            "type": None,
            "teamName": safeStr(row["teamName"]),
            "admin": bool(row["admin"]),
            "customData": custom if isinstance(custom, dict) else {},
        })
    return {"comments": data, "data": data, "results": data, "status": "OK"}

@route("/v1/global/chat/save")
def hGlobalChatSave(params, body):
    playerId = params.get("PLAYER_ID", [""])[0]
    message = params.get("message", [""])[0]
    if not message and body:
        try:
            parsed = json.loads(body.decode("utf-8"))
            if isinstance(parsed, dict):
                message = parsed.get("message") or parsed.get("comment") or parsed.get("text") or ""
        except Exception:
            pass
    if not message or not message.strip():
        return hGlobalChat(params, body)
    message = message.strip()[:500]
    name, tag, facebookId, gameCenterId, teamName, admin = "Player", "", "", "", "", 0
    if playerId:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT name, tag, facebookId, gameCenterId, teamName FROM players WHERE id = ?", (playerId,))
        row = c.fetchone()
        if row:
            name = safeStr(row["name"], "Player")
            tag = safeStr(row["tag"])
            facebookId = safeStr(row["facebookId"])
            gameCenterId = safeStr(row["gameCenterId"])
            teamName = safeStr(row["teamName"])
        conn.close()
    ts = nowEpochMs()
    conn = getDbConnection()
    c = conn.cursor()
    c.execute("""INSERT INTO chatMessages
                 (playerId, name, facebookId, gameCenterId, tag, comment, timestamp, type, teamName, admin, customData)
                 VALUES (?, ?, ?, ?, ?, ?, ?, NULL, ?, ?, '{}')""",
              (playerId, name, facebookId, gameCenterId, tag, message, ts, teamName, admin))
    conn.commit()
    c.execute("SELECT COUNT(*) as cnt FROM chatMessages")
    count = c.fetchone()["cnt"]
    if count > 500:
        c.execute("DELETE FROM chatMessages WHERE id IN (SELECT id FROM chatMessages ORDER BY id ASC LIMIT ?)", (count - 500,))
        conn.commit()
    conn.close()
    return hGlobalChat(params, body)

@route("/v1/test/player/update")
def hTestUpdate(params, body): return {"status": "OK"}

# ---------------------------------------------------------------------
# Root CA download (not a game endpoint - lets the device install/trust
# this server's HTTPS certificate directly from Safari, e.g.
# http://<PC IP>:4451/rootca.pem, so DNS spoofing alone works without a
# Charles Proxy relay: iOS recognizes application/x-x509-ca-cert and offers
# to install it as a profile straight away).
# ---------------------------------------------------------------------
ROOT_CA_FILE = os.path.join(SCRIPT_DIR, "BigBangRacing_RootCA.pem")
ROOT_CA_KEY_FILE = os.path.join(SCRIPT_DIR, "BigBangRacing_RootCA.key")

@route("/rootca.pem", "/rootca")
def hRootCa(params, body):
    if not os.path.isfile(ROOT_CA_FILE):
        return {"error": "Root CA file not found on server", "path": ROOT_CA_FILE}
    with open(ROOT_CA_FILE, "rb") as f:
        data = f.read()
    return {"_binary": data, "_content_type": "application/x-x509-ca-cert",
            "_headers": {"Content-Disposition": 'attachment; filename="BigBangRacing_RootCA.pem"'}}

def certCoversHost(hostname: str) -> bool:
    """Cheap SAN check: a certificate's Subject Alternative Name list is stored as
    literal ASCII hostname bytes inside the DER-encoded certificate, so once the PEM's
    base64 is decoded back to raw DER, a plain substring search is enough to tell
    whether a hostname is covered - no need to actually parse ASN.1/X.509 for this.
    CERT_FILE is cert+key concatenated (see its own top-of-file comment), so this
    extracts just the "-----BEGIN CERTIFICATE-----...-----END CERTIFICATE-----" block
    first - ssl.PEM_cert_to_DER_cert requires the string to end right after that
    marker, which it never does in the combined file otherwise. Used to detect whether
    server.pem needs regenerating to add graph.facebook.com before the custom-profile-
    picture feature can work."""
    if not os.path.isfile(CERT_FILE):
        return False
    with open(CERT_FILE, "r", encoding="ascii", errors="ignore") as f:
        pemText = f.read()
    start = pemText.find("-----BEGIN CERTIFICATE-----")
    end = pemText.find("-----END CERTIFICATE-----")
    if start == -1 or end == -1:
        return False
    certPem = pemText[start:end] + "-----END CERTIFICATE-----\n"
    try:
        certBytes = ssl.PEM_cert_to_DER_cert(certPem)
    except Exception:
        return False
    return hostname.encode("ascii") in certBytes

def findOpenssl() -> str:
    """shutil.which("openssl") only checks THIS process's own PATH - and a GUI app
    launched by double-clicking BBRServer.bat/a desktop shortcut doesn't necessarily
    inherit the same PATH a terminal window has, even when Git for Windows (which
    bundles openssl.exe) is genuinely installed - confirmed live: a terminal-launched
    check found it, the actual admin GUI's own click-triggered call didn't. Falls back
    to the handful of locations Git for Windows/a standalone OpenSSL installer
    actually put it at, so this works regardless of how the GUI itself was launched."""
    found = shutil.which("openssl")
    if found:
        return found
    candidates = [
        r"C:\Program Files\Git\mingw64\bin\openssl.exe",
        r"C:\Program Files\Git\usr\bin\openssl.exe",
        r"C:\Program Files (x86)\Git\mingw64\bin\openssl.exe",
        r"C:\Program Files (x86)\Git\usr\bin\openssl.exe",
        r"C:\Program Files\OpenSSL-Win64\bin\openssl.exe",
        r"C:\Program Files\OpenSSL-Win32\bin\openssl.exe",
        r"C:\Program Files\OpenSSL\bin\openssl.exe",
    ]
    for path in candidates:
        if os.path.isfile(path):
            return path
    return ""

def ensureServerDataExtracted():
    """Ships in the repo as ServerData.zip instead of thousands of loose files
    (levels, music, initial data). The first time the server runs, this unpacks
    it into ServerData/ next to the script and deletes the zip - after that it
    behaves exactly like any other install. Never raises; if extraction fails
    the zip is left in place so the user can unzip it by hand."""
    if not os.path.isfile(SERVER_DATA_ZIP):
        return
    try:
        with zipfile.ZipFile(SERVER_DATA_ZIP) as zf:
            zf.extractall(SCRIPT_DIR)
        os.remove(SERVER_DATA_ZIP)
        print(f"[Setup] Extracted ServerData.zip into {SERVER_DATA_DIR}/ and removed the zip.")
    except Exception as e:
        print(f"[Setup] Could not extract ServerData.zip ({e}) - "
              f"unzip it into a 'ServerData' folder next to the script yourself.")

def ensureRootCaExists() -> tuple:
    """Generates a fresh, self-signed Root CA (BigBangRacing_RootCA.pem + .key) the
    first time this server runs on a given machine, if one doesn't already exist.
    This project is meant to be cloned from a public repo, and a Root CA's PRIVATE
    KEY must never be something two different installs share - anyone holding it can
    mint a certificate for ANY hostname that every device trusting that CA will
    silently accept, which is exactly the capability this project's own DNS-redirect
    + HTTPS setup depends on being limited to each install's own devices. So this is
    never committed to the repo and never downloaded from anywhere - each install
    generates its own the first time it starts, exactly once, entirely locally.
    Returns (success: bool, messageKey: str, detail: str), same convention as
    regenerateHttpsCertificate - never raises."""
    if os.path.isfile(ROOT_CA_FILE) and os.path.isfile(ROOT_CA_KEY_FILE):
        return True, "", ""
    opensslPath = findOpenssl()
    if not opensslPath:
        return False, "cert_err_no_openssl", ""
    try:
        genCa = subprocess.run(
            [opensslPath, "req", "-x509", "-newkey", "rsa:2048", "-nodes",
             "-keyout", ROOT_CA_KEY_FILE, "-out", ROOT_CA_FILE,
             "-days", "3650", "-subj", "/CN=BigBangRacing Offline Root CA"],
            capture_output=True, text=True)
        if genCa.returncode != 0:
            return False, "cert_err_csr_failed", genCa.stderr.strip()
        print(f"[Setup] Generated a new local Root CA ({ROOT_CA_FILE}) - this device's own, "
              f"never shared with or downloaded from anywhere else.")
        return True, "", ""
    except Exception as e:
        return False, "cert_err_unexpected", str(e)

def regenerateHttpsCertificate() -> tuple:
    """Regenerates server.pem (the combined HTTPS leaf cert+key this server's HTTPS
    listener loads) to cover every host in TARGET_HOSTS as a Subject Alternative Name,
    signed by the SAME already-installed BigBangRacing_RootCA - so nothing needs
    reinstalling on the device, only this one file changes. Runs openssl as a
    subprocess (bundled with Git for Windows, already confirmed on PATH) so the user
    never has to type a command themselves - this is meant to be called from a GUI
    button (see _linkFacebookFake's auto-prompt) after a new TARGET_HOSTS entry like
    graph.facebook.com is added. Returns (success: bool, messageKey: str, detail: str) -
    messageKey is a t()-translatable key (cert_err_*), detail is either empty or a
    dynamic value (a file path, or openssl's own untranslatable stderr text) meant to
    be formatted into that key's "{0}" placeholder - never raises, every failure mode
    (missing openssl, missing root CA files, a failed openssl invocation) is caught and
    reported back this way instead, since this runs from a GUI button click with no
    console the user would otherwise see errors on."""
    opensslPath = findOpenssl()
    if not opensslPath:
        return False, "cert_err_no_openssl", ""
    if not os.path.isfile(ROOT_CA_FILE) or not os.path.isfile(ROOT_CA_KEY_FILE):
        return False, "cert_err_no_root_ca", f"{ROOT_CA_FILE}, {ROOT_CA_KEY_FILE}"

    tmpDir = tempfile.mkdtemp(prefix="bbr_cert_")
    try:
        keyPath = os.path.join(tmpDir, "leaf.key")
        csrPath = os.path.join(tmpDir, "leaf.csr")
        crtPath = os.path.join(tmpDir, "leaf.crt")
        sanArg = "subjectAltName=" + ",".join(f"DNS:{h}" for h in sorted(TARGET_HOSTS))

        genReq = subprocess.run(
            [opensslPath, "req", "-newkey", "rsa:2048", "-nodes",
             "-keyout", keyPath, "-out", csrPath,
             "-subj", "/CN=woeprod.traplightgames.com", "-addext", sanArg],
            capture_output=True, text=True)
        if genReq.returncode != 0:
            return False, "cert_err_csr_failed", genReq.stderr.strip()

        signReq = subprocess.run(
            [opensslPath, "x509", "-req", "-in", csrPath,
             "-CA", ROOT_CA_FILE, "-CAkey", ROOT_CA_KEY_FILE, "-CAcreateserial",
             "-out", crtPath, "-days", "800", "-copy_extensions", "copy"],
            capture_output=True, text=True)
        if signReq.returncode != 0:
            return False, "cert_err_sign_failed", signReq.stderr.strip()

        with open(crtPath, "rb") as f:
            crtBytes = f.read()
        with open(keyPath, "rb") as f:
            keyBytes = f.read()
        with open(CERT_FILE, "wb") as f:
            f.write(crtBytes)
            f.write(keyBytes)
        return True, "", ""
    except Exception as e:
        return False, "cert_err_unexpected", str(e)
    finally:
        shutil.rmtree(tmpDir, ignore_errors=True)

# ---------------------------------------------------------------------
# Connection Processing Engine
# ---------------------------------------------------------------------
def genericFallback(path):
    return {"id": genOid(), "data": [], "results": [], "status": "OK"}

# ---------------------------------------------------------------------
# Request log - read by the admin GUI (bbr_admin_gui.py), never by the
# game client. Bounded so it can't grow forever; thread-safe since
# ThreadingHTTPServer runs each request on its own thread.
# ---------------------------------------------------------------------
REQUEST_LOG = collections.deque(maxlen=500)
_requestLogLock = threading.Lock()
_requestIdCounter = itertools.count(1)

def _previewBytes(data: bytes, limit: int = 4000) -> str:
    if not data:
        return ""
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return f"<{len(data)} bytes binary>"
    try:
        text = json.dumps(json.loads(text), indent=2, ensure_ascii=False)
    except Exception:
        pass
    if len(text) > limit:
        text = text[:limit] + f"\n... [{len(data)} bytes total]"
    return text

def _logRequest(method, path, query, playerId, sessionId, bodyBytes, responsePreview, status=200):
    entry = {
        "id": next(_requestIdCounter),
        "time": datetime.now(timezone.utc).strftime("%H:%M:%S"),
        "method": method, "path": path,
        "query": {k: v for k, v in query.items() if k not in ("SESSION_ID", "PLAYER_ID", "FILE_SIZES")},
        "playerId": playerId, "sessionId": sessionId,
        "body": _previewBytes(bodyBytes),
        "response": responsePreview,
        "status": status,
    }
    with _requestLogLock:
        REQUEST_LOG.append(entry)

def getRequestLog() -> list:
    with _requestLogLock:
        return list(REQUEST_LOG)

class FakeApiHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def _handle(self):
        parsedUrl = urlparse(self.path)
        cleanPath = parsedUrl.path
        queryParams = parse_qs(parsedUrl.query)
        if cleanPath.lower().startswith("/serverdata/"):
            self._serveStaticFile(cleanPath)
            return
        # graph.facebook.com is DNS-redirected to us (see TARGET_HOSTS/handleDns) so we
        # can serve a self-hosted picture for ANY facebookId, including private profiles
        # the real Facebook API refuses to serve without OAuth - the Host header is what
        # tells us the client thinks it's talking to Facebook rather than the real BBR
        # backend, since both now resolve to this same server/port.
        hostHeader = self.headers.get("Host", "").split(":")[0].lower()
        if hostHeader == "graph.facebook.com":
            self._serveProfilePicture(cleanPath)
            return
        length = int(self.headers.get("Content-Length", 0) or 0)
        body = self.rfile.read(length) if length else b""
        clientSession = self.headers.get("SESSION_ID", "N/A")
        clientPlayerId = self.headers.get("PLAYER_ID", "N/A")
        queryParams["SESSION_ID"] = [clientSession]
        queryParams["PLAYER_ID"] = [clientPlayerId]
        queryParams["FILE_SIZES"] = [self.headers.get("FILE_SIZES", "")]
        print(f"\n{'='*70}")
        print(f"[HTTP] {self.command} {cleanPath}")
        print(f"  Session: {clientSession} | Player: {clientPlayerId}")
        # The Console tab is meant to work as a live server log on its own (without
        # switching to the separate Requests tab for every lookup) - a short one-line
        # summary of the actual query params and any body is enough to follow activity
        # (e.g. "gameId=... rating=Positive") without the full detail the Requests tab
        # keeps for click-to-inspect.
        shownQuery = {k: v for k, v in queryParams.items()
                      if k not in ("SESSION_ID", "PLAYER_ID", "FILE_SIZES") and v and v[0]}
        if shownQuery:
            queryPreview = " ".join(f"{k}={v[0]}" for k, v in shownQuery.items())
            print(f"  Query: {_previewBytes(queryPreview.encode('utf-8', 'replace'), 300)}")
        if body:
            print(f"  Body ({len(body)} bytes): {_previewBytes(body, 300)}")
        lookup = cleanPath.lower()
        if lookup in ROUTES:
            try:
                payload = ROUTES[lookup](queryParams, body)
            except Exception:
                import traceback
                print(f"[HTTP] Handler error for {cleanPath}:")
                traceback.print_exc()
                payload = genericFallback(cleanPath)
        else:
            payload = genericFallback(cleanPath)
        try:
            if isinstance(payload, dict) and "_binary" in payload:
                data = payload["_binary"]
                if not isinstance(data, (bytes, bytearray)):
                    raise TypeError(f"_binary payload for {cleanPath} was {type(data)!r}, not bytes")
                ctype = payload.get("_content_type", "application/octet-stream")
                extraHeaders = payload.get("_headers") or {}
                playHash = generatePlayHash(self.path, bytes(data))
                self.send_response(200)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Length", str(len(data)))
                self.send_header("PLAY_STATUS", "OK")
                self.send_header("PLAY_HASH", playHash)
                for hk, hv in extraHeaders.items():
                    if hv is not None:
                        self.send_header(hk, str(hv))
                # Without this, iOS's URL loading system can cache a GET response by
                # URL+query even with no explicit cache headers at all - endpoints meant
                # to return something fresh/random each call (like /v1/minigame/oneFresh)
                # then keep silently replaying their very first response forever, since
                # the request looks identical every time.
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(data)
                self.close_connection = True
                _logRequest(self.command, cleanPath, queryParams, clientPlayerId, clientSession,
                            body, f"<binary {ctype}, {len(data)} bytes>")
                return
            dataStr = json.dumps(payload, separators=(',', ':'))
        except Exception:
            import traceback
            print(f"[HTTP] Response-building error for {cleanPath}:")
            traceback.print_exc()
            payload = genericFallback(cleanPath)
            dataStr = json.dumps(payload, separators=(',', ':'))
        data = dataStr.encode("utf-8")
        playHash = generatePlayHash(self.path, dataStr)
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("PLAY_STATUS", "OK")
        self.send_header("PLAY_HASH", playHash)
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(data)
        self.close_connection = True
        _logRequest(self.command, cleanPath, queryParams, clientPlayerId, clientSession,
                    body, _previewBytes(data))

    def _serveStaticFile(self, urlPath):
        safePath = os.path.normpath(urlPath.lstrip("/"))
        if safePath.startswith("..") or os.path.isabs(safePath):
            self.send_response(403)
            self.end_headers()
            return
        fullPath = os.path.join(SCRIPT_DIR, safePath)
        if not os.path.isfile(fullPath):
            self.send_response(404)
            self.end_headers()
            return
        ext = os.path.splitext(fullPath)[1].lower()
        ct = {".bank": "application/octet-stream", ".bundle": "application/octet-stream",
              ".json": "application/json", ".png": "application/octet-stream"}.get(ext, "application/octet-stream")
        with open(fullPath, "rb") as f:
            data = f.read()
        self.send_response(200)
        self.send_header("Content-Type", ct)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(data)
        self.close_connection = True

    def _serveProfilePicture(self, urlPath):
        # Matches FacebookManager.GetPicture's exact request shape:
        # "https://graph.facebook.com/<facebookId>/picture?width=W&height=H" - the
        # width/height query params only ask for a size, never change which image, so
        # they're ignored; we always return whatever was uploaded for this facebookId
        # via the Players tab's "Link Facebook" button (see _linkFacebookFake).
        facebookId = urlPath.strip("/").split("/")[0] if urlPath.strip("/") else ""
        data = None
        if facebookId:
            conn = getDbConnection()
            c = conn.cursor()
            c.execute("SELECT customProfilePicture FROM players WHERE facebookId = ?", (facebookId,))
            row = c.fetchone()
            conn.close()
            if row is not None:
                data = row["customProfilePicture"]
        if not data:
            self.send_response(404)
            self.send_header("Content-Length", "0")
            self.send_header("Connection", "close")
            self.end_headers()
            self.close_connection = True
            return
        contentType = "image/png" if data[:8] == b"\x89PNG\r\n\x1a\n" else "image/jpeg"
        self.send_response(200)
        self.send_header("Content-Type", contentType)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(data)
        self.close_connection = True

    def do_GET(self): self._handle()
    def do_POST(self): self._handle()
    def do_PUT(self): self._handle()
    def do_DELETE(self): self._handle()
    def log_message(self, fmt, *args): pass

# ---------------------------------------------------------------------
# Listeners & Start
# ---------------------------------------------------------------------
def runHttpServer():
    try:
        server = ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), FakeApiHandler)
        _serverState["http"] = server
        print(f"[HTTP] Listening on port {HTTP_PORT}")
        server.serve_forever()
    except OSError as e:
        print(f"[HTTP] Error: {e}")

def runHttpsServer():
    if not os.path.isfile(CERT_FILE): return
    try:
        server = ThreadingHTTPServer(("0.0.0.0", HTTPS_PORT), FakeApiHandler)
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.load_cert_chain(certfile=CERT_FILE)
        server.socket = ctx.wrap_socket(server.socket, server_side=True)
        _serverState["https"] = server
        print(f"[HTTPS] Listening on port {HTTPS_PORT}")
        server.serve_forever()
    except Exception as e:
        print(f"[HTTPS] Error: {e}")

# ---------------------------------------------------------------------
# DNS Engine (Fixed)
# ---------------------------------------------------------------------
def parseQname(data, offset):
    labels = []
    while True:
        l = data[offset]
        if l == 0: offset += 1; break
        offset += 1
        labels.append(data[offset:offset+l].decode("ascii", errors="replace"))
        offset += l
    return ".".join(labels), offset

def buildFakeAnswer(req, qend, ip):
    return (req[0:2] + struct.pack("!H", 0x8180) + struct.pack("!HHHH", 1,1,0,0)
            + req[12:qend] + struct.pack("!H", 0xC00C) + struct.pack("!HH", 1,1)
            + struct.pack("!I", 60) + struct.pack("!H", 4) + socket.inet_aton(ip))

def buildEmptyAnswer(req, qend):
    return (req[0:2] + struct.pack("!H", 0x8180) + struct.pack("!HHHH", 1,0,0,0) + req[12:qend])

def buildNxdomainAnswer(req, qend):
    return (req[0:2] + struct.pack("!H", 0x8183) + struct.pack("!HHHH", 1,0,0,0) + req[12:qend])

BLOCKED_PATTERNS = [
    "facebook.com", "fbcdn.net",
    "app-measurement.com", "firebaseinstallations.googleapis.com",
    "firebaseremoteconfig.googleapis.com", "fcm.googleapis.com",
    "firebase.googleapis.com", "crashlytics.com",
]

def isBlocked(qname: str) -> bool:
    return any(p in qname for p in BLOCKED_PATTERNS)

def handleDns(sock, data, addr, fakeIp):
    try:
        qname, nend = parseQname(data, 12)
        qtype, _ = struct.unpack("!HH", data[nend:nend+4])
        qend = nend + 4
        name = qname.lower().rstrip(".")

        # TARGET_HOSTS takes priority over the blocklist below: graph.facebook.com is
        # both "facebook.com" (would otherwise match BLOCKED_PATTERNS, meant for
        # Facebook's SDK telemetry/tracking hosts) AND a TARGET_HOST (redirected to us
        # so we can serve a self-hosted profile picture instead - see
        # _servesGraphFacebookPicture). Every other facebook.com/fbcdn.net subdomain
        # stays blocked exactly as before.
        if name in TARGET_HOSTS and qtype == 1:
            sock.sendto(buildFakeAnswer(data, qend, fakeIp), addr)
        elif name in TARGET_HOSTS and qtype in (28, 65):
            sock.sendto(buildEmptyAnswer(data, qend), addr)
        elif isBlocked(name):
            print(f"[DNS] BLOCKED (Facebook/Firebase): {qname}")
            sock.sendto(buildNxdomainAnswer(data, qend), addr)
        else:
            u = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            u.settimeout(3)
            try:
                u.sendto(data, UPSTREAM_DNS)
                r, _ = u.recvfrom(512)
                sock.sendto(r, addr)
            except (socket.timeout, ConnectionResetError, OSError):
                pass
            finally:
                u.close()
    except Exception:
        pass

def runDns(fakeIp, stopEvent=None):
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.bind(("0.0.0.0", DNS_PORT))
        if hasattr(socket, "SIO_UDP_CONNRESET"):
            s.ioctl(socket.SIO_UDP_CONNRESET, False)
        s.settimeout(1.0)  # lets the loop below notice stopEvent without blocking forever
        _serverState["dns"] = s
        print(f"[DNS] Listening on port {DNS_PORT}")
    except (PermissionError, OSError) as e:
        print(f"[DNS] Port {DNS_PORT} error: {e}")
        return
    while stopEvent is None or not stopEvent.is_set():
        try:
            data, addr = s.recvfrom(512)
        except socket.timeout:
            continue
        except (ConnectionResetError, OSError):
            if stopEvent is not None and stopEvent.is_set():
                break
            continue
        threading.Thread(target=handleDns, args=(s, data, addr, fakeIp), daemon=True).start()
    try:
        s.close()
    except OSError:
        pass

def localIp():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]; s.close(); return ip
    except Exception: return "127.0.0.1"

# ---------------------------------------------------------------------
# Server lifecycle - used by the admin GUI (bbr_admin_gui.py) to start/stop
# the DNS+HTTP+HTTPS listeners on demand, and by __main__ below for the
# unchanged plain-CLI usage (`python bbr_fake_server.py`).
# ---------------------------------------------------------------------
_serverState = {"http": None, "https": None, "dns": None}
_dnsStopEvent = threading.Event()
_dnsThread = None
_httpThread = None
_httpsThread = None

def isServerRunning() -> bool:
    return _serverState["http"] is not None

_startLock = threading.Lock()
_starting = False

def startServer():
    # Re-entrancy guard: isServerRunning() only turns True once HTTP has bound,
    # near the end of this function - without this, a second call arriving
    # while the first is still mid-startup (e.g. two quick clicks of the GUI's
    # Start button, or a click right after the CLI's own startup) would race
    # to bind the same DNS/HTTP/HTTPS ports a second time and fail.
    global _starting
    with _startLock:
        if isServerRunning() or _starting:
            print("[Server] Already running or already starting.")
            return
        _starting = True
    try:
        global _dnsThread, _httpThread, _httpsThread

        # First run on this machine (or a fresh clone that only has ServerData.zip):
        # unpack it into ServerData/ before anything below tries to read from it.
        ensureServerDataExtracted()

        initDb()

        # First run on this machine (or a fresh clone with no cert files at all,
        # e.g. right after `git clone`): generate this install's own Root CA and a
        # matching leaf certificate automatically, so nothing needs to be typed into
        # a terminal and no shared secret ever needs to travel with the repo. Also
        # covers TARGET_HOSTS growing since the cert was last generated (e.g. an
        # older install that predates graph.facebook.com support).
        caOk, caErrKey, caErrDetail = ensureRootCaExists()
        if not caOk:
            print(f"[Setup] Could not generate a Root CA ({caErrKey}: {caErrDetail}) - "
                  f"HTTPS will not start. Install OpenSSL (it ships with Git for Windows) and restart.")
        elif not os.path.isfile(CERT_FILE) or not all(certCoversHost(h) for h in TARGET_HOSTS):
            certOk, certErrKey, certErrDetail = regenerateHttpsCertificate()
            if not certOk:
                print(f"[Setup] Could not generate the HTTPS certificate ({certErrKey}: {certErrDetail}) - "
                      f"HTTPS will not start.")

        ip = localIp()
        print(f"PC IP: {ip}")

        planets = getAvailablePlanets()
        if planets: print(f"[InitData] Advertising planets: {[p['planet'] for p in planets]}")
        else: print(f"[InitData] No planet files in {INITIAL_DATA_DIR}/ yet.")

        levelCount = importLevelsFromFolder()
        if levelCount: print(f"[LevelImport] Imported {levelCount} new level(s) from {LEVELS_DIR}/")
        elif os.path.isdir(LEVELS_DIR): print(f"[LevelImport] {LEVELS_DIR}/ has no new levels to import")
        else: print(f"[LevelImport] No {LEVELS_DIR}/ folder yet.")

        _dnsStopEvent.clear()
        _dnsThread = threading.Thread(target=runDns, args=(ip, _dnsStopEvent), daemon=True)
        _dnsThread.start()
        _httpThread = threading.Thread(target=runHttpServer, daemon=True)
        _httpThread.start()
        _httpsThread = threading.Thread(target=runHttpsServer, daemon=True)
        _httpsThread.start()
        # Give the listener threads a moment to either bind (and populate
        # _serverState) or fail, so isServerRunning() is meaningful right after this call.
        for _ in range(20):
            if _serverState["http"] is not None:
                break
            time.sleep(0.1)
    finally:
        _starting = False

def stopServer():
    if not isServerRunning():
        print("[Server] Not running.")
        return
    _dnsStopEvent.set()
    if _serverState["http"] is not None:
        _serverState["http"].shutdown()
        _serverState["http"].server_close()
        _serverState["http"] = None
    if _serverState["https"] is not None:
        _serverState["https"].shutdown()
        _serverState["https"].server_close()
        _serverState["https"] = None
    _serverState["dns"] = None
    print("[Server] Stopped.")


# =======================================================================
# Admin GUI (Tkinter/ttk, stdlib only) - a control panel that starts/stops
# the server above, shows its console output and request history, and edits
# the SQLite database directly through the same functions/tables the server
# itself uses (getDbConnection(), getTournamentConfig(), etc.). One single
# script: running this file opens the GUI, and the GUI is what starts the
# actual server.
# =======================================================================
class _StreamTee:
    """Redirects stdout/stderr into a Queue so the Console tab can show every
    print() the server makes, including from its own background threads -
    Tkinter isn't thread-safe, so the GUI drains the queue via .after() on
    the main thread instead of writing to the Text widget directly.
    Queue-only (no write-through to the original stream): the GUI Console tab
    is meant to be the only place logs show up, and under pythonw.exe (the
    normal way to launch this without a console window) sys.stdout/stderr are
    None anyway, so writing through would crash."""
    def __init__(self, original, lineQueue):
        self._original = original
        self._queue = lineQueue

    def write(self, text):
        if text:
            self._queue.put(text)

    def flush(self):
        pass


# -- small UI helpers reused by every CRUD panel -------------------------
# ---------------------------------------------------------------------
# GUI localization - covers the admin GUI only (never sent to the game
# client, which has its own separate locale system driven by players.locale).
# ---------------------------------------------------------------------
LANGUAGES = [
    ("en", "English", "GB"),
    ("fr", "Français", "FR"),
    ("it", "Italiano", "IT"),
    ("es", "Español", "ES"),
    ("sv", "Svenska", "SE"),
    ("pt", "Português", "PT"),
]

TRANSLATIONS = {
    "en": {
        "nav_dashboard": "Dashboard", "nav_console": "Console", "nav_requests": "Requests",
        "nav_players": "Players", "nav_levels": "Levels", "nav_teams": "Teams",
        "nav_ghosts": "Ghosts", "nav_tournament": "Tournament", "nav_news": "News Feed",
        "nav_gifs": "Gifs", "col_size": "Size", "col_created": "Created",
        "btn_export_gif": "Extract", "gif_preview_unavailable": "Preview unavailable",
        "btn_extract_level": "Extract to ZIP",
        "msg_gif_missing": "This gif file no longer exists on disk.",
        "msg_gif_exported_fmt": "Exported to {0}", "word_gif": "gif",
        "quit_title": "Quit", "quit_message": "The server is still running. Stop the server and quit?",
        "quit_dont_ask_again": "Don't ask me again",
        "language_button": "Language", "language_picker_title": "Choose language",
        "btn_start_server": "Start Server", "btn_stop_server": "Stop Server",
        "service_status_frame": "Service Status", "port_label": "port",
        "information_frame": "Information", "local_ip_label": "Local IP: {0}",
        "database_label": "Database: {0}",
        "btn_refresh": "Refresh", "details_frame": "Details",
        "confirm_delete_title": "Confirm Delete", "confirm_delete_message": "Delete {0}? This cannot be undone.",
        "btn_clear": "Clear",
        "request_body_label": "Request Body", "response_label": "Response",
        "empty_placeholder": "(empty)",
        "col_time": "Time", "col_method": "Method", "col_path": "Path",
        "col_player": "Player", "col_status": "Status",
        "name": "Name", "tag": "Tag", "coins": "Coins", "diamonds": "Diamonds",
        "country": "Country", "description": "Description", "state": "State",
        "game_mode": "Game Mode", "difficulty": "Difficulty",
        "save": "Save", "delete": "Delete", "more": "More...", "close": "Close", "add": "Add",
        "word_yes": "Yes", "word_no": "No", "word_ok": "OK",
        "id_word": "ID", "error_fmt": "Error: {0}",
        "col_teamid": "Team ID", "col_mctrophies": "MC Trophies", "col_cartrophies": "Car Trophies",
        "btn_link_facebook": "Set Profile Picture", "btn_unlink_facebook": "Remove Profile Picture",
        "msg_select_player_first": "Select a player from the list first.",
        "word_player": "player", "word_level": "level", "word_team": "team",
        "word_ghost_run": "this ghost/run", "word_event": "this event",
        "link_facebook_prompt_title": "Choose a profile picture",
        "link_facebook_done_msg": "Done. The picture will show in-game on next login.",
        "cert_update_needed_title": "Certificate Update Needed",
        "cert_update_needed_msg": "To add a profile picture, the server needs to run an update. Run it now?",
        "cert_update_failed_msg": "Certificate update failed: {0}",
        "cert_update_done_msg": "Certificate updated. If the server is currently running, stop and start it "
                                 "again for this to take effect.",
        "cert_err_no_openssl": "OpenSSL was not found. It ships with Git for Windows, but this admin GUI's own "
                                "process doesn't always see it on PATH even when Git is installed - the usual "
                                "install locations were checked too, with no luck. Install Git for Windows (or "
                                "OpenSSL directly) if it's genuinely missing.",
        "cert_err_no_root_ca": "Root CA files not found next to the server ({0}).",
        "cert_err_csr_failed": "Could not generate a certificate request: {0}",
        "cert_err_sign_failed": "Could not sign the certificate: {0}",
        "cert_err_unexpected": "Unexpected error: {0}",
        "cert_update_wait_title": "Please Wait",
        "cert_update_wait_msg": "Updating the certificate...",
        "col_creatorname": "Creator Name", "col_timesplayed": "Times Played",
        "col_upthumbs": "Up Thumbs", "col_downthumbs": "Down Thumbs",
        "lbl_state_hint": "State (public/saved/hidden)", "lbl_gamemode_hint": "Game Mode (Race/StarCollect)",
        "reward_coins": "Reward (coins)", "msg_select_level_first": "Select a level from the list first.",
        "level_size_info": "level: {0} | screenshot: {1} | ghost: {2}",
        "col_ownerid": "Owner ID", "col_members": "Members",
        "btn_delete_team": "Delete (and remove members)",
        "msg_select_team_first": "Select a team from the list first.",
        "ghosts_heading": "Ghosts (recorded runs)", "col_gameid": "Game ID",
        "col_playername": "Player Name", "col_playerunit": "Player Unit", "col_time_ms": "Time (ms)",
        "col_ghost": "Ghost", "btn_delete_selected": "Delete Selected",
        "msg_select_row_first_list": "Select a row from the list first.",
        "msg_select_row_first": "Select a row first.",
        "tournament_config_heading": "Tournament Configuration",
        "lbl_tournament_level": "Tournament Level",
        "tour_search_hint": "Type to search by name or id - click a result to select it",
        "tour_level_not_found": "(level not found)",
        "btn_choose_level": "Choose Level", "level_picker_title": "Choose a level",
        "btn_disable_tournament": "Disable Tournament",
        "lbl_tournament_id": "Tournament ID", "lbl_cc_cap": "CC Cap (-1 = unlimited)",
        "lbl_use_creator_upgrades": "Use Creator's Upgrades",
        "lbl_accepting_scores": "Accepting New Scores", "lbl_floating_node": "Floating Node (show on map)",
        "lbl_title_header": "Title (header)", "message": "Message",
        "lbl_duration_unlimited": "Duration (days, 0 = unlimited)",
        "tour_saved_at_fmt": "Saved at {0}.", "msg_invalid_numeric_fmt": "Invalid numeric value: {0}",
        "col_eventname": "Event Name", "col_eventtype": "Event Type", "col_headercol": "Header",
        "col_active_until": "Active Until", "val_unlimited": "unlimited", "add_event_frame": "Add Event",
        "lbl_title_ingame": "Title (shown in-game)", "lbl_message_ingame": "Message (shown in-game)",
        "type_word": "Type", "lbl_label_button": "Label (button)",
        "lbl_internal_name": "Internal name (optional, not shown to players)",
        "lbl_duration_short": "Duration (days, 0=unlimited)", "lbl_popup_login": "Popup at Login",
        "lbl_visible_newsfeed": "Visible in News Feed",
        "gift_details_frame": "Gift details (only used when Type = Gift)",
        "lbl_gift_type": "Gift Type", "lbl_identifier": "Identifier", "lbl_amount": "Amount",
        "lbl_texture_optional": "Texture (optional)", "msg_title_required": "Title is required.",
        "msg_invalid_duration": "Invalid duration.",
        "msg_invalid_gift_numbers": "Gift amount/texture must be numbers.",
        "country_picker_title": "Choose country",
        "row_details_title_fmt": "{0} details - {1}",
        "row_not_found_msg": "Row not found (it may have been deleted).",
        "blob_not_editable_fmt": "<{0} bytes - not editable here>", "status_saved": "Saved.",
        "save_failed_fmt": "Save failed: {0}", "numeric_expected_fmt": "'{0}' expects a numeric value, got {1!r}.",
    },
    "fr": {
        "nav_dashboard": "Tableau de bord", "nav_console": "Console", "nav_requests": "Requêtes",
        "nav_players": "Joueurs", "nav_levels": "Niveaux", "nav_teams": "Équipes",
        "nav_ghosts": "Fantômes", "nav_tournament": "Tournoi", "nav_news": "Actualités",
        "nav_gifs": "Gifs", "col_size": "Taille", "col_created": "Créé le",
        "btn_export_gif": "Extraire", "gif_preview_unavailable": "Aperçu indisponible",
        "btn_extract_level": "Extraire en ZIP",
        "msg_gif_missing": "Ce fichier gif n'existe plus sur le disque.",
        "msg_gif_exported_fmt": "Exporté vers {0}", "word_gif": "gif",
        "quit_title": "Quitter",
        "quit_message": "Le serveur est encore en cours d'exécution. Arrêter le serveur et quitter ?",
        "quit_dont_ask_again": "Ne plus me demander",
        "language_button": "Langue", "language_picker_title": "Choisir la langue",
        "btn_start_server": "Démarrer le serveur", "btn_stop_server": "Arrêter le serveur",
        "service_status_frame": "État des services", "port_label": "port",
        "information_frame": "Informations", "local_ip_label": "IP locale : {0}",
        "database_label": "Base de données : {0}",
        "btn_refresh": "Actualiser", "details_frame": "Détails",
        "confirm_delete_title": "Confirmer la suppression",
        "confirm_delete_message": "Supprimer {0} ? Cette action est irréversible.",
        "btn_clear": "Effacer",
        "request_body_label": "Corps de la requête", "response_label": "Réponse",
        "empty_placeholder": "(vide)",
        "col_time": "Heure", "col_method": "Méthode", "col_path": "Chemin",
        "col_player": "Joueur", "col_status": "Statut",
        "name": "Nom", "tag": "Tag", "coins": "Pièces", "diamonds": "Diamants",
        "country": "Pays", "description": "Description", "state": "État",
        "game_mode": "Mode de jeu", "difficulty": "Difficulté",
        "save": "Enregistrer", "delete": "Supprimer", "more": "Plus...", "close": "Fermer", "add": "Ajouter",
        "word_yes": "Oui", "word_no": "Non", "word_ok": "OK",
        "id_word": "ID", "error_fmt": "Erreur : {0}",
        "col_teamid": "ID d'équipe", "col_mctrophies": "Trophées Moto", "col_cartrophies": "Trophées Voiture",
        "btn_link_facebook": "Définir la photo de profil", "btn_unlink_facebook": "Supprimer la photo de profil",
        "msg_select_player_first": "Sélectionnez d'abord un joueur dans la liste.",
        "word_player": "le joueur", "word_level": "le niveau", "word_team": "l'équipe",
        "word_ghost_run": "ce fantôme/run", "word_event": "cet événement",
        "link_facebook_prompt_title": "Choisir une photo de profil",
        "link_facebook_done_msg": "Terminé. La photo s'affichera en jeu à la prochaine connexion.",
        "cert_update_needed_title": "Mise à jour du certificat nécessaire",
        "cert_update_needed_msg": "Pour ajouter une photo de profil, le serveur doit effectuer une mise à jour. "
                                   "L'effectuer maintenant ?",
        "cert_update_failed_msg": "Échec de la mise à jour du certificat : {0}",
        "cert_update_done_msg": "Certificat mis à jour. Si le serveur tourne actuellement, arrête-le puis "
                                 "relance-le pour que ça prenne effet.",
        "cert_err_no_openssl": "OpenSSL est introuvable. Il est fourni avec Git pour Windows, mais ce GUI ne le "
                                "voit pas toujours dans son PATH même quand Git est installé - les emplacements "
                                "habituels ont aussi été vérifiés, sans succès. Installe Git pour Windows (ou "
                                "OpenSSL directement) s'il manque vraiment.",
        "cert_err_no_root_ca": "Fichiers de l'autorité racine introuvables à côté du serveur ({0}).",
        "cert_err_csr_failed": "Impossible de générer la demande de certificat : {0}",
        "cert_err_sign_failed": "Impossible de signer le certificat : {0}",
        "cert_err_unexpected": "Erreur inattendue : {0}",
        "cert_update_wait_title": "Patienter",
        "cert_update_wait_msg": "Mise à jour du certificat en cours...",
        "col_creatorname": "Nom du créateur", "col_timesplayed": "Fois jouées",
        "col_upthumbs": "Pouces levés", "col_downthumbs": "Pouces baissés",
        "lbl_state_hint": "État (public/saved/hidden)", "lbl_gamemode_hint": "Mode de jeu (Race/StarCollect)",
        "reward_coins": "Récompense (pièces)",
        "msg_select_level_first": "Sélectionnez d'abord un niveau dans la liste.",
        "level_size_info": "niveau : {0} | capture d'écran : {1} | ghost : {2}",
        "col_ownerid": "ID du propriétaire", "col_members": "Membres",
        "btn_delete_team": "Supprimer (et retirer les membres)",
        "msg_select_team_first": "Sélectionnez d'abord une équipe dans la liste.",
        "ghosts_heading": "Fantômes (courses enregistrées)", "col_gameid": "ID de niveau",
        "col_playername": "Nom du joueur", "col_playerunit": "Véhicule", "col_time_ms": "Temps (ms)",
        "col_ghost": "Ghost", "btn_delete_selected": "Supprimer la sélection",
        "msg_select_row_first_list": "Sélectionnez d'abord une ligne dans la liste.",
        "msg_select_row_first": "Sélectionnez d'abord une ligne.",
        "tournament_config_heading": "Configuration du tournoi",
        "lbl_tournament_level": "Niveau du tournoi",
        "tour_search_hint": "Tapez pour rechercher par nom ou id - cliquez sur un résultat pour le "
                             "sélectionner",
        "tour_level_not_found": "(niveau introuvable)",
        "btn_choose_level": "Choisir un niveau", "level_picker_title": "Choisir un niveau",
        "btn_disable_tournament": "Désactiver le tournoi",
        "lbl_tournament_id": "ID du tournoi", "lbl_cc_cap": "Plafond CC (-1 = illimité)",
        "lbl_use_creator_upgrades": "Utiliser les améliorations du "
                                     "créateur",
        "lbl_accepting_scores": "Accepter les nouveaux scores",
        "lbl_floating_node": "Nœud flottant (afficher sur la carte)",
        "lbl_title_header": "Titre (en-tête)", "message": "Message",
        "lbl_duration_unlimited": "Durée (jours, 0 = illimité)",
        "tour_saved_at_fmt": "Enregistré à {0}.", "msg_invalid_numeric_fmt": "Valeur numérique invalide : {0}",
        "col_eventname": "Nom de l'événement", "col_eventtype": "Type d'événement", "col_headercol": "En-tête",
        "col_active_until": "Actif jusqu'à", "val_unlimited": "illimité", "add_event_frame": "Ajouter un "
                                                                                              "événement",
        "lbl_title_ingame": "Titre (affiché en jeu)", "lbl_message_ingame": "Message (affiché en jeu)",
        "type_word": "Type", "lbl_label_button": "Libellé (bouton)",
        "lbl_internal_name": "Nom interne (facultatif, non visible des joueurs)",
        "lbl_duration_short": "Durée (jours, 0=illimité)", "lbl_popup_login": "Popup à la connexion",
        "lbl_visible_newsfeed": "Visible dans les actualités",
        "gift_details_frame": "Détails du cadeau (utilisé seulement si Type = Gift)",
        "lbl_gift_type": "Type de cadeau", "lbl_identifier": "Identifiant", "lbl_amount": "Quantité",
        "lbl_texture_optional": "Texture (facultatif)", "msg_title_required": "Le titre est obligatoire.",
        "msg_invalid_duration": "Durée invalide.",
        "msg_invalid_gift_numbers": "La quantité/texture du cadeau doit être un nombre.",
        "country_picker_title": "Choisir le pays",
        "row_details_title_fmt": "Détails de {0} - {1}",
        "row_not_found_msg": "Ligne introuvable (elle a peut-être été supprimée).",
        "blob_not_editable_fmt": "<{0} octets - non modifiable ici>", "status_saved": "Enregistré.",
        "save_failed_fmt": "Échec de l'enregistrement : {0}",
        "numeric_expected_fmt": "'{0}' attend une valeur numérique, reçu {1!r}.",
    },
    "it": {
        "nav_dashboard": "Pannello di controllo", "nav_console": "Console", "nav_requests": "Richieste",
        "nav_players": "Giocatori", "nav_levels": "Livelli", "nav_teams": "Squadre",
        "nav_ghosts": "Fantasmi", "nav_tournament": "Torneo", "nav_news": "Notizie",
        "nav_gifs": "Gif", "col_size": "Dimensione", "col_created": "Creato il",
        "btn_export_gif": "Estrai", "gif_preview_unavailable": "Anteprima non disponibile",
        "btn_extract_level": "Estrai in ZIP",
        "msg_gif_missing": "Questo file gif non esiste più sul disco.",
        "msg_gif_exported_fmt": "Esportato in {0}", "word_gif": "gif",
        "quit_title": "Esci",
        "quit_message": "Il server è ancora in esecuzione. Arrestare il server e uscire?",
        "quit_dont_ask_again": "Non chiedermelo più",
        "language_button": "Lingua", "language_picker_title": "Scegli la lingua",
        "btn_start_server": "Avvia server", "btn_stop_server": "Arresta server",
        "service_status_frame": "Stato dei servizi", "port_label": "porta",
        "information_frame": "Informazioni", "local_ip_label": "IP locale: {0}",
        "database_label": "Database: {0}",
        "btn_refresh": "Aggiorna", "details_frame": "Dettagli",
        "confirm_delete_title": "Conferma eliminazione",
        "confirm_delete_message": "Eliminare {0}? Questa azione non può essere annullata.",
        "btn_clear": "Cancella",
        "request_body_label": "Corpo della richiesta", "response_label": "Risposta",
        "empty_placeholder": "(vuoto)",
        "col_time": "Ora", "col_method": "Metodo", "col_path": "Percorso",
        "col_player": "Giocatore", "col_status": "Stato",
        "name": "Nome", "tag": "Tag", "coins": "Monete", "diamonds": "Diamanti",
        "country": "Paese", "description": "Descrizione", "state": "Stato",
        "game_mode": "Modalità di gioco", "difficulty": "Difficoltà",
        "save": "Salva", "delete": "Elimina", "more": "Altro...", "close": "Chiudi", "add": "Aggiungi",
        "word_yes": "Sì", "word_no": "No", "word_ok": "OK",
        "id_word": "ID", "error_fmt": "Errore: {0}",
        "col_teamid": "ID squadra", "col_mctrophies": "Trofei Moto", "col_cartrophies": "Trofei Auto",
        "btn_link_facebook": "Imposta foto profilo", "btn_unlink_facebook": "Rimuovi foto profilo",
        "msg_select_player_first": "Seleziona prima un giocatore dall'elenco.",
        "word_player": "il giocatore", "word_level": "il livello", "word_team": "la squadra",
        "word_ghost_run": "questo fantasma/run", "word_event": "questo evento",
        "link_facebook_prompt_title": "Scegli una foto profilo",
        "link_facebook_done_msg": "Fatto. La foto apparirà in gioco al prossimo accesso.",
        "cert_update_needed_title": "Aggiornamento certificato necessario",
        "cert_update_needed_msg": "Per aggiungere una foto profilo, il server deve eseguire un aggiornamento. "
                                   "Eseguirlo ora?",
        "cert_update_failed_msg": "Aggiornamento del certificato non riuscito: {0}",
        "cert_update_done_msg": "Certificato aggiornato. Se il server è attualmente in esecuzione, fermalo e "
                                 "riavvialo perché abbia effetto.",
        "cert_err_no_openssl": "OpenSSL non trovato. È incluso con Git per Windows, ma questa GUI non lo vede "
                                "sempre nel suo PATH anche quando Git è installato - controllati anche i "
                                "percorsi di installazione abituali, senza successo. Installa Git per Windows "
                                "(o OpenSSL direttamente) se manca davvero.",
        "cert_err_no_root_ca": "File della CA radice non trovati accanto al server ({0}).",
        "cert_err_csr_failed": "Impossibile generare la richiesta di certificato: {0}",
        "cert_err_sign_failed": "Impossibile firmare il certificato: {0}",
        "cert_err_unexpected": "Errore imprevisto: {0}",
        "cert_update_wait_title": "Attendere",
        "cert_update_wait_msg": "Aggiornamento del certificato in corso...",
        "col_creatorname": "Nome creatore", "col_timesplayed": "Volte giocato",
        "col_upthumbs": "Pollici in su", "col_downthumbs": "Pollici in giù",
        "lbl_state_hint": "Stato (public/saved/hidden)",
        "lbl_gamemode_hint": "Modalità di gioco (Race/StarCollect)",
        "reward_coins": "Ricompensa (monete)",
        "msg_select_level_first": "Seleziona prima un livello dall'elenco.",
        "level_size_info": "livello: {0} | screenshot: {1} | ghost: {2}",
        "col_ownerid": "ID proprietario", "col_members": "Membri",
        "btn_delete_team": "Elimina (e rimuovi i membri)",
        "msg_select_team_first": "Seleziona prima una squadra dall'elenco.",
        "ghosts_heading": "Fantasmi (corse registrate)", "col_gameid": "ID livello",
        "col_playername": "Nome giocatore", "col_playerunit": "Veicolo", "col_time_ms": "Tempo (ms)",
        "col_ghost": "Ghost", "btn_delete_selected": "Elimina selezionato",
        "msg_select_row_first_list": "Seleziona prima una riga dall'elenco.",
        "msg_select_row_first": "Seleziona prima una riga.",
        "tournament_config_heading": "Configurazione torneo",
        "lbl_tournament_level": "Livello del torneo",
        "tour_search_hint": "Digita per cercare per nome o id - clicca su un risultato per selezionarlo",
        "tour_level_not_found": "(livello non trovato)",
        "btn_choose_level": "Scegli un livello", "level_picker_title": "Scegli un livello",
        "btn_disable_tournament": "Disattiva torneo",
        "lbl_tournament_id": "ID torneo", "lbl_cc_cap": "Limite CC (-1 = illimitato)",
        "lbl_use_creator_upgrades": "Usa i potenziamenti del creatore",
        "lbl_accepting_scores": "Accetta nuovi punteggi",
        "lbl_floating_node": "Nodo fluttuante (mostra sulla mappa)",
        "lbl_title_header": "Titolo (intestazione)", "message": "Messaggio",
        "lbl_duration_unlimited": "Durata (giorni, 0 = illimitato)",
        "tour_saved_at_fmt": "Salvato alle {0}.", "msg_invalid_numeric_fmt": "Valore numerico non valido: {0}",
        "col_eventname": "Nome evento", "col_eventtype": "Tipo di evento", "col_headercol": "Intestazione",
        "col_active_until": "Attivo fino a", "val_unlimited": "illimitato", "add_event_frame": "Aggiungi evento",
        "lbl_title_ingame": "Titolo (mostrato in gioco)", "lbl_message_ingame": "Messaggio (mostrato in gioco)",
        "type_word": "Tipo", "lbl_label_button": "Etichetta (pulsante)",
        "lbl_internal_name": "Nome interno (facoltativo, non visibile ai giocatori)",
        "lbl_duration_short": "Durata (giorni, 0=illimitato)", "lbl_popup_login": "Popup all'accesso",
        "lbl_visible_newsfeed": "Visibile nelle notizie",
        "gift_details_frame": "Dettagli del regalo (usato solo se Tipo = Gift)",
        "lbl_gift_type": "Tipo di regalo", "lbl_identifier": "Identificatore", "lbl_amount": "Quantità",
        "lbl_texture_optional": "Texture (facoltativo)", "msg_title_required": "Il titolo è obbligatorio.",
        "msg_invalid_duration": "Durata non valida.",
        "msg_invalid_gift_numbers": "La quantità/texture del regalo deve essere un numero.",
        "country_picker_title": "Scegli il paese",
        "row_details_title_fmt": "Dettagli di {0} - {1}",
        "row_not_found_msg": "Riga non trovata (potrebbe essere stata eliminata).",
        "blob_not_editable_fmt": "<{0} byte - non modificabile qui>", "status_saved": "Salvato.",
        "save_failed_fmt": "Salvataggio non riuscito: {0}",
        "numeric_expected_fmt": "'{0}' richiede un valore numerico, ricevuto {1!r}.",
    },
    "es": {
        "nav_dashboard": "Panel de control", "nav_console": "Consola", "nav_requests": "Solicitudes",
        "nav_players": "Jugadores", "nav_levels": "Niveles", "nav_teams": "Equipos",
        "nav_ghosts": "Fantasmas", "nav_tournament": "Torneo", "nav_news": "Noticias",
        "nav_gifs": "Gifs", "col_size": "Tamaño", "col_created": "Creado el",
        "btn_export_gif": "Extraer", "gif_preview_unavailable": "Vista previa no disponible",
        "btn_extract_level": "Extraer a ZIP",
        "msg_gif_missing": "Este archivo gif ya no existe en el disco.",
        "msg_gif_exported_fmt": "Exportado a {0}", "word_gif": "gif",
        "quit_title": "Salir",
        "quit_message": "El servidor todavía está en ejecución. ¿Detener el servidor y salir?",
        "quit_dont_ask_again": "No volver a preguntar",
        "language_button": "Idioma", "language_picker_title": "Elegir idioma",
        "btn_start_server": "Iniciar servidor", "btn_stop_server": "Detener servidor",
        "service_status_frame": "Estado de los servicios", "port_label": "puerto",
        "information_frame": "Información", "local_ip_label": "IP local: {0}",
        "database_label": "Base de datos: {0}",
        "btn_refresh": "Actualizar", "details_frame": "Detalles",
        "confirm_delete_title": "Confirmar eliminación",
        "confirm_delete_message": "¿Eliminar {0}? Esta acción no se puede deshacer.",
        "btn_clear": "Borrar",
        "request_body_label": "Cuerpo de la solicitud", "response_label": "Respuesta",
        "empty_placeholder": "(vacío)",
        "col_time": "Hora", "col_method": "Método", "col_path": "Ruta",
        "col_player": "Jugador", "col_status": "Estado",
        "name": "Nombre", "tag": "Etiqueta", "coins": "Monedas", "diamonds": "Diamantes",
        "country": "País", "description": "Descripción", "state": "Estado",
        "game_mode": "Modo de juego", "difficulty": "Dificultad",
        "save": "Guardar", "delete": "Eliminar", "more": "Más...", "close": "Cerrar", "add": "Añadir",
        "word_yes": "Sí", "word_no": "No", "word_ok": "OK",
        "id_word": "ID", "error_fmt": "Error: {0}",
        "col_teamid": "ID de equipo", "col_mctrophies": "Trofeos Moto", "col_cartrophies": "Trofeos Coche",
        "btn_link_facebook": "Definir foto de perfil", "btn_unlink_facebook": "Quitar foto de perfil",
        "msg_select_player_first": "Selecciona primero un jugador de la lista.",
        "word_player": "el jugador", "word_level": "el nivel", "word_team": "el equipo",
        "word_ghost_run": "este fantasma/run", "word_event": "este evento",
        "link_facebook_prompt_title": "Elegir una foto de perfil",
        "link_facebook_done_msg": "Listo. La foto aparecerá en el juego en el próximo inicio de sesión.",
        "cert_update_needed_title": "Actualización de certificado necesaria",
        "cert_update_needed_msg": "Para añadir una foto de perfil, el servidor debe realizar una actualización. "
                                   "¿Hacerlo ahora?",
        "cert_update_failed_msg": "Error al actualizar el certificado: {0}",
        "cert_update_done_msg": "Certificado actualizado. Si el servidor está en ejecución, detenlo y vuelve a "
                                 "iniciarlo para que surta efecto.",
        "cert_err_no_openssl": "No se encontró OpenSSL. Viene incluido con Git para Windows, pero esta interfaz "
                                "no siempre lo ve en su PATH aunque Git esté instalado - también se revisaron "
                                "las ubicaciones habituales, sin éxito. Instala Git para Windows (u OpenSSL "
                                "directamente) si realmente falta.",
        "cert_err_no_root_ca": "No se encontraron los archivos de la CA raíz junto al servidor ({0}).",
        "cert_err_csr_failed": "No se pudo generar la solicitud de certificado: {0}",
        "cert_err_sign_failed": "No se pudo firmar el certificado: {0}",
        "cert_err_unexpected": "Error inesperado: {0}",
        "cert_update_wait_title": "Espere",
        "cert_update_wait_msg": "Actualizando el certificado...",
        "col_creatorname": "Nombre del creador", "col_timesplayed": "Veces jugado",
        "col_upthumbs": "Pulgares arriba", "col_downthumbs": "Pulgares abajo",
        "lbl_state_hint": "Estado (public/saved/hidden)",
        "lbl_gamemode_hint": "Modo de juego (Race/StarCollect)",
        "reward_coins": "Recompensa (monedas)",
        "msg_select_level_first": "Selecciona primero un nivel de la lista.",
        "level_size_info": "nivel: {0} | captura: {1} | ghost: {2}",
        "col_ownerid": "ID del propietario", "col_members": "Miembros",
        "btn_delete_team": "Eliminar (y quitar los miembros)",
        "msg_select_team_first": "Selecciona primero un equipo de la lista.",
        "ghosts_heading": "Fantasmas (carreras grabadas)", "col_gameid": "ID de nivel",
        "col_playername": "Nombre del jugador", "col_playerunit": "Vehículo", "col_time_ms": "Tiempo (ms)",
        "col_ghost": "Ghost", "btn_delete_selected": "Eliminar seleccionado",
        "msg_select_row_first_list": "Selecciona primero una fila de la lista.",
        "msg_select_row_first": "Selecciona primero una fila.",
        "tournament_config_heading": "Configuración del torneo",
        "lbl_tournament_level": "Nivel del torneo",
        "tour_search_hint": "Escribe para buscar por nombre o id - haz clic en un resultado para "
                             "seleccionarlo",
        "tour_level_not_found": "(nivel no encontrado)",
        "btn_choose_level": "Elegir un nivel", "level_picker_title": "Elegir un nivel",
        "btn_disable_tournament": "Desactivar torneo",
        "lbl_tournament_id": "ID del torneo", "lbl_cc_cap": "Límite CC (-1 = ilimitado)",
        "lbl_use_creator_upgrades": "Usar las mejoras del creador",
        "lbl_accepting_scores": "Aceptar nuevas puntuaciones",
        "lbl_floating_node": "Nodo flotante (mostrar en el mapa)",
        "lbl_title_header": "Título (encabezado)", "message": "Mensaje",
        "lbl_duration_unlimited": "Duración (días, 0 = ilimitado)",
        "tour_saved_at_fmt": "Guardado a las {0}.",
        "msg_invalid_numeric_fmt": "Valor numérico no válido: {0}",
        "col_eventname": "Nombre del evento", "col_eventtype": "Tipo de evento", "col_headercol": "Encabezado",
        "col_active_until": "Activo hasta", "val_unlimited": "ilimitado", "add_event_frame": "Añadir evento",
        "lbl_title_ingame": "Título (mostrado en el juego)",
        "lbl_message_ingame": "Mensaje (mostrado en el juego)",
        "type_word": "Tipo", "lbl_label_button": "Etiqueta (botón)",
        "lbl_internal_name": "Nombre interno (opcional, no visible para los jugadores)",
        "lbl_duration_short": "Duración (días, 0=ilimitado)",
        "lbl_popup_login": "Ventana emergente al iniciar sesión",
        "lbl_visible_newsfeed": "Visible en las noticias",
        "gift_details_frame": "Detalles del regalo (usado solo si Tipo = Gift)",
        "lbl_gift_type": "Tipo de regalo", "lbl_identifier": "Identificador", "lbl_amount": "Cantidad",
        "lbl_texture_optional": "Textura (opcional)", "msg_title_required": "El título es obligatorio.",
        "msg_invalid_duration": "Duración no válida.",
        "msg_invalid_gift_numbers": "La cantidad/textura del regalo debe ser un número.",
        "country_picker_title": "Elegir el país",
        "row_details_title_fmt": "Detalles de {0} - {1}",
        "row_not_found_msg": "Fila no encontrada (puede que haya sido eliminada).",
        "blob_not_editable_fmt": "<{0} bytes - no editable aquí>", "status_saved": "Guardado.",
        "save_failed_fmt": "Error al guardar: {0}",
        "numeric_expected_fmt": "'{0}' espera un valor numérico, se recibió {1!r}.",
    },
    "sv": {
        "nav_dashboard": "Instrumentpanel", "nav_console": "Konsol", "nav_requests": "Förfrågningar",
        "nav_players": "Spelare", "nav_levels": "Nivåer", "nav_teams": "Lag",
        "nav_ghosts": "Spöken", "nav_tournament": "Turnering", "nav_news": "Nyheter",
        "nav_gifs": "Gifs", "col_size": "Storlek", "col_created": "Skapad",
        "btn_export_gif": "Extrahera", "gif_preview_unavailable": "Förhandsgranskning ej tillgänglig",
        "btn_extract_level": "Extrahera till ZIP",
        "msg_gif_missing": "Den här gif-filen finns inte längre på disken.",
        "msg_gif_exported_fmt": "Exporterad till {0}", "word_gif": "gif",
        "quit_title": "Avsluta",
        "quit_message": "Servern körs fortfarande. Stoppa servern och avsluta?",
        "quit_dont_ask_again": "Fråga mig inte igen",
        "language_button": "Språk", "language_picker_title": "Välj språk",
        "btn_start_server": "Starta server", "btn_stop_server": "Stoppa server",
        "service_status_frame": "Tjänststatus", "port_label": "port",
        "information_frame": "Information", "local_ip_label": "Lokal IP: {0}",
        "database_label": "Databas: {0}",
        "btn_refresh": "Uppdatera", "details_frame": "Detaljer",
        "confirm_delete_title": "Bekräfta borttagning",
        "confirm_delete_message": "Ta bort {0}? Detta kan inte ångras.",
        "btn_clear": "Rensa",
        "request_body_label": "Begärandekropp", "response_label": "Svar",
        "empty_placeholder": "(tomt)",
        "col_time": "Tid", "col_method": "Metod", "col_path": "Sökväg",
        "col_player": "Spelare", "col_status": "Status",
        "name": "Namn", "tag": "Tagg", "coins": "Mynt", "diamonds": "Diamanter",
        "country": "Land", "description": "Beskrivning", "state": "Status",
        "game_mode": "Spelläge", "difficulty": "Svårighetsgrad",
        "save": "Spara", "delete": "Ta bort", "more": "Mer...", "close": "Stäng", "add": "Lägg till",
        "word_yes": "Ja", "word_no": "Nej", "word_ok": "OK",
        "id_word": "ID", "error_fmt": "Fel: {0}",
        "col_teamid": "Lag-ID", "col_mctrophies": "MC-troféer", "col_cartrophies": "Bil-troféer",
        "btn_link_facebook": "Ange profilbild", "btn_unlink_facebook": "Ta bort profilbild",
        "msg_select_player_first": "Välj en spelare i listan först.",
        "word_player": "spelaren", "word_level": "nivån", "word_team": "laget",
        "word_ghost_run": "denna ghost/körning", "word_event": "denna händelse",
        "link_facebook_prompt_title": "Välj en profilbild",
        "link_facebook_done_msg": "Klart. Bilden visas i spelet vid nästa inloggning.",
        "cert_update_needed_title": "Certifikatuppdatering krävs",
        "cert_update_needed_msg": "För att lägga till en profilbild måste servern köra en uppdatering. Köra "
                                   "den nu?",
        "cert_update_failed_msg": "Certifikatuppdateringen misslyckades: {0}",
        "cert_update_done_msg": "Certifikatet har uppdaterats. Om servern körs just nu, stoppa och starta den "
                                 "igen för att detta ska gälla.",
        "cert_err_no_openssl": "OpenSSL hittades inte. Det följer med Git för Windows, men detta gränssnitt ser "
                                "det inte alltid i sin PATH även när Git är installerat - de vanliga "
                                "installationsplatserna kontrollerades också, utan resultat. Installera Git för "
                                "Windows (eller OpenSSL direkt) om det verkligen saknas.",
        "cert_err_no_root_ca": "CA-rotfiler hittades inte bredvid servern ({0}).",
        "cert_err_csr_failed": "Kunde inte skapa certifikatbegäran: {0}",
        "cert_err_sign_failed": "Kunde inte signera certifikatet: {0}",
        "cert_err_unexpected": "Oväntat fel: {0}",
        "cert_update_wait_title": "Vänta",
        "cert_update_wait_msg": "Uppdaterar certifikatet...",
        "col_creatorname": "Skaparens namn", "col_timesplayed": "Antal spelade gånger",
        "col_upthumbs": "Tummar upp", "col_downthumbs": "Tummar ner",
        "lbl_state_hint": "Status (public/saved/hidden)", "lbl_gamemode_hint": "Spelläge (Race/StarCollect)",
        "reward_coins": "Belöning (mynt)",
        "msg_select_level_first": "Välj en nivå i listan först.",
        "level_size_info": "nivå: {0} | skärmbild: {1} | ghost: {2}",
        "col_ownerid": "Ägar-ID", "col_members": "Medlemmar",
        "btn_delete_team": "Ta bort (och ta bort medlemmar)",
        "msg_select_team_first": "Välj ett lag i listan först.",
        "ghosts_heading": "Spöken (inspelade lopp)", "col_gameid": "Nivå-ID",
        "col_playername": "Spelarnamn", "col_playerunit": "Fordon", "col_time_ms": "Tid (ms)",
        "col_ghost": "Ghost", "btn_delete_selected": "Ta bort markerad",
        "msg_select_row_first_list": "Välj en rad i listan först.",
        "msg_select_row_first": "Välj en rad först.",
        "tournament_config_heading": "Turneringsinställningar",
        "lbl_tournament_level": "Turneringsnivå",
        "tour_search_hint": "Skriv för att söka efter namn eller id - klicka på ett resultat för att välja "
                             "det",
        "tour_level_not_found": "(nivån hittades inte)",
        "btn_choose_level": "Välj nivå", "level_picker_title": "Välj en nivå",
        "btn_disable_tournament": "Inaktivera turnering",
        "lbl_tournament_id": "Turnerings-ID", "lbl_cc_cap": "CC-tak (-1 = obegränsat)",
        "lbl_use_creator_upgrades": "Använd skaparens uppgraderingar",
        "lbl_accepting_scores": "Acceptera nya resultat",
        "lbl_floating_node": "Flytande nod (visa på kartan)",
        "lbl_title_header": "Titel (rubrik)", "message": "Meddelande",
        "lbl_duration_unlimited": "Varaktighet (dagar, 0 = obegränsat)",
        "tour_saved_at_fmt": "Sparat kl. {0}.", "msg_invalid_numeric_fmt": "Ogiltigt numeriskt värde: {0}",
        "col_eventname": "Händelsenamn", "col_eventtype": "Händelsetyp", "col_headercol": "Rubrik",
        "col_active_until": "Aktiv till", "val_unlimited": "obegränsat",
        "add_event_frame": "Lägg till händelse",
        "lbl_title_ingame": "Titel (visas i spelet)", "lbl_message_ingame": "Meddelande (visas i spelet)",
        "type_word": "Typ", "lbl_label_button": "Etikett (knapp)",
        "lbl_internal_name": "Internt namn (valfritt, visas inte för spelare)",
        "lbl_duration_short": "Varaktighet (dagar, 0=obegränsat)", "lbl_popup_login": "Popup vid inloggning",
        "lbl_visible_newsfeed": "Synlig i nyhetsflödet",
        "gift_details_frame": "Presentdetaljer (används endast om Typ = Gift)",
        "lbl_gift_type": "Presenttyp", "lbl_identifier": "Identifierare", "lbl_amount": "Mängd",
        "lbl_texture_optional": "Textur (valfritt)", "msg_title_required": "Titel krävs.",
        "msg_invalid_duration": "Ogiltig varaktighet.",
        "msg_invalid_gift_numbers": "Presentens mängd/textur måste vara siffror.",
        "country_picker_title": "Välj land",
        "row_details_title_fmt": "Detaljer för {0} - {1}",
        "row_not_found_msg": "Raden hittades inte (den kan ha tagits bort).",
        "blob_not_editable_fmt": "<{0} byte - ej redigerbart här>", "status_saved": "Sparat.",
        "save_failed_fmt": "Det gick inte att spara: {0}",
        "numeric_expected_fmt": "'{0}' förväntar sig ett numeriskt värde, fick {1!r}.",
    },
    "pt": {
        "nav_dashboard": "Painel de controle", "nav_console": "Console", "nav_requests": "Solicitações",
        "nav_players": "Jogadores", "nav_levels": "Níveis", "nav_teams": "Equipes",
        "nav_ghosts": "Fantasmas", "nav_tournament": "Torneio", "nav_news": "Notícias",
        "nav_gifs": "Gifs", "col_size": "Tamanho", "col_created": "Criado em",
        "btn_export_gif": "Extrair", "gif_preview_unavailable": "Pré-visualização indisponível",
        "btn_extract_level": "Extrair para ZIP",
        "msg_gif_missing": "Este arquivo gif não existe mais no disco.",
        "msg_gif_exported_fmt": "Exportado para {0}", "word_gif": "gif",
        "quit_title": "Sair",
        "quit_message": "O servidor ainda está em execução. Parar o servidor e sair?",
        "quit_dont_ask_again": "Não perguntar novamente",
        "language_button": "Idioma", "language_picker_title": "Escolher idioma",
        "btn_start_server": "Iniciar servidor", "btn_stop_server": "Parar servidor",
        "service_status_frame": "Status dos serviços", "port_label": "porta",
        "information_frame": "Informações", "local_ip_label": "IP local: {0}",
        "database_label": "Banco de dados: {0}",
        "btn_refresh": "Atualizar", "details_frame": "Detalhes",
        "confirm_delete_title": "Confirmar exclusão",
        "confirm_delete_message": "Excluir {0}? Esta ação não pode ser desfeita.",
        "btn_clear": "Limpar",
        "request_body_label": "Corpo da solicitação", "response_label": "Resposta",
        "empty_placeholder": "(vazio)",
        "col_time": "Hora", "col_method": "Método", "col_path": "Caminho",
        "col_player": "Jogador", "col_status": "Status",
        "name": "Nome", "tag": "Tag", "coins": "Moedas", "diamonds": "Diamantes",
        "country": "País", "description": "Descrição", "state": "Estado",
        "game_mode": "Modo de jogo", "difficulty": "Dificuldade",
        "save": "Salvar", "delete": "Excluir", "more": "Mais...", "close": "Fechar", "add": "Adicionar",
        "word_yes": "Sim", "word_no": "Não", "word_ok": "OK",
        "id_word": "ID", "error_fmt": "Erro: {0}",
        "col_teamid": "ID da equipe", "col_mctrophies": "Troféus de Moto", "col_cartrophies": "Troféus de "
                                                                                                "Carro",
        "btn_link_facebook": "Definir foto de perfil", "btn_unlink_facebook": "Remover foto de perfil",
        "msg_select_player_first": "Selecione um jogador da lista primeiro.",
        "word_player": "o jogador", "word_level": "o nível", "word_team": "a equipe",
        "word_ghost_run": "este fantasma/execução", "word_event": "este evento",
        "link_facebook_prompt_title": "Escolher uma foto de perfil",
        "link_facebook_done_msg": "Pronto. A foto aparecerá no jogo no próximo login.",
        "cert_update_needed_title": "Atualização de certificado necessária",
        "cert_update_needed_msg": "Para adicionar uma foto de perfil, o servidor precisa executar uma "
                                   "atualização. Executar agora?",
        "cert_update_failed_msg": "Falha ao atualizar o certificado: {0}",
        "cert_update_done_msg": "Certificado atualizado. Se o servidor estiver em execução, pare-o e inicie-o "
                                 "novamente para que isso tenha efeito.",
        "cert_err_no_openssl": "OpenSSL não foi encontrado. Ele vem com o Git para Windows, mas esta interface "
                                "nem sempre o vê no PATH mesmo quando o Git está instalado - os locais de "
                                "instalação habituais também foram verificados, sem sucesso. Instale o Git "
                                "para Windows (ou o OpenSSL diretamente) se realmente estiver faltando.",
        "cert_err_no_root_ca": "Arquivos da CA raiz não encontrados ao lado do servidor ({0}).",
        "cert_err_csr_failed": "Não foi possível gerar a solicitação de certificado: {0}",
        "cert_err_sign_failed": "Não foi possível assinar o certificado: {0}",
        "cert_err_unexpected": "Erro inesperado: {0}",
        "cert_update_wait_title": "Aguarde",
        "cert_update_wait_msg": "Atualizando o certificado...",
        "col_creatorname": "Nome do criador", "col_timesplayed": "Vezes jogado",
        "col_upthumbs": "Curtidas positivas", "col_downthumbs": "Curtidas negativas",
        "lbl_state_hint": "Estado (public/saved/hidden)", "lbl_gamemode_hint": "Modo de jogo "
                                                                                "(Race/StarCollect)",
        "reward_coins": "Recompensa (moedas)",
        "msg_select_level_first": "Selecione um nível da lista primeiro.",
        "level_size_info": "nível: {0} | captura de tela: {1} | ghost: {2}",
        "col_ownerid": "ID do proprietário", "col_members": "Membros",
        "btn_delete_team": "Excluir (e remover os membros)",
        "msg_select_team_first": "Selecione uma equipe da lista primeiro.",
        "ghosts_heading": "Fantasmas (corridas gravadas)", "col_gameid": "ID do nível",
        "col_playername": "Nome do jogador", "col_playerunit": "Veículo", "col_time_ms": "Tempo (ms)",
        "col_ghost": "Ghost", "btn_delete_selected": "Excluir selecionado",
        "msg_select_row_first_list": "Selecione uma linha da lista primeiro.",
        "msg_select_row_first": "Selecione uma linha primeiro.",
        "tournament_config_heading": "Configuração do torneio",
        "lbl_tournament_level": "Nível do torneio",
        "tour_search_hint": "Digite para pesquisar por nome ou id - clique em um resultado para selecioná-lo",
        "tour_level_not_found": "(nível não encontrado)",
        "btn_choose_level": "Escolher um nível", "level_picker_title": "Escolher um nível",
        "btn_disable_tournament": "Desativar torneio",
        "lbl_tournament_id": "ID do torneio", "lbl_cc_cap": "Limite CC (-1 = ilimitado)",
        "lbl_use_creator_upgrades": "Usar os upgrades do criador",
        "lbl_accepting_scores": "Aceitar novas pontuações",
        "lbl_floating_node": "Nó flutuante (mostrar no mapa)",
        "lbl_title_header": "Título (cabeçalho)", "message": "Mensagem",
        "lbl_duration_unlimited": "Duração (dias, 0 = ilimitado)",
        "tour_saved_at_fmt": "Salvo às {0}.", "msg_invalid_numeric_fmt": "Valor numérico inválido: {0}",
        "col_eventname": "Nome do evento", "col_eventtype": "Tipo de evento", "col_headercol": "Cabeçalho",
        "col_active_until": "Ativo até", "val_unlimited": "ilimitado", "add_event_frame": "Adicionar evento",
        "lbl_title_ingame": "Título (mostrado no jogo)", "lbl_message_ingame": "Mensagem (mostrada no jogo)",
        "type_word": "Tipo", "lbl_label_button": "Rótulo (botão)",
        "lbl_internal_name": "Nome interno (opcional, não visível aos jogadores)",
        "lbl_duration_short": "Duração (dias, 0=ilimitado)", "lbl_popup_login": "Pop-up ao fazer login",
        "lbl_visible_newsfeed": "Visível nas notícias",
        "gift_details_frame": "Detalhes do presente (usado apenas se Tipo = Gift)",
        "lbl_gift_type": "Tipo de presente", "lbl_identifier": "Identificador", "lbl_amount": "Quantidade",
        "lbl_texture_optional": "Textura (opcional)", "msg_title_required": "O título é obrigatório.",
        "msg_invalid_duration": "Duração inválida.",
        "msg_invalid_gift_numbers": "A quantidade/textura do presente deve ser um número.",
        "country_picker_title": "Escolher o país",
        "row_details_title_fmt": "Detalhes de {0} - {1}",
        "row_not_found_msg": "Linha não encontrada (pode ter sido excluída).",
        "blob_not_editable_fmt": "<{0} bytes - não editável aqui>", "status_saved": "Salvo.",
        "save_failed_fmt": "Falha ao salvar: {0}",
        "numeric_expected_fmt": "'{0}' espera um valor numérico, recebeu {1!r}.",
    },
}

_currentLang = "en"
_skipQuitConfirm = False

def _loadGuiSettings() -> dict:
    """Reads admin-GUI preferences (language, dialog 'don't ask again' flags, etc.)
    from the guiSettings DB table. Also transparently imports a legacy gui_lang.json
    left over from older versions of this project (one file back to the DB, then
    removed), so this doesn't need its own file on disk."""
    legacyFile = os.path.join(SCRIPT_DIR, "gui_lang.json")
    if os.path.isfile(legacyFile):
        try:
            with open(legacyFile, "r", encoding="utf-8") as f:
                legacy = json.load(f)
            _saveGuiSettings(legacy)
            os.remove(legacyFile)
        except Exception:
            pass
    try:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("CREATE TABLE IF NOT EXISTS guiSettings (key TEXT PRIMARY KEY, value TEXT)")
        c.execute("SELECT key, value FROM guiSettings")
        rows = {r["key"]: safeJsonLoads(r["value"], None) for r in c.fetchall()}
        conn.close()
        return rows
    except Exception:
        return {}

def _saveGuiSettings(updates: dict):
    try:
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("CREATE TABLE IF NOT EXISTS guiSettings (key TEXT PRIMARY KEY, value TEXT)")
        for key, value in updates.items():
            c.execute(
                "INSERT INTO guiSettings (key, value) VALUES (?, ?) "
                "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
                (key, json.dumps(value)))
        conn.commit()
        conn.close()
    except Exception:
        pass

def loadSavedLang() -> str:
    global _currentLang
    saved = _loadGuiSettings().get("lang", "en")
    if saved in TRANSLATIONS:
        _currentLang = saved
    return _currentLang

def setLang(lang: str):
    global _currentLang
    if lang not in TRANSLATIONS:
        return
    _currentLang = lang
    _saveGuiSettings({"lang": lang})

def loadSkipQuitConfirm() -> bool:
    global _skipQuitConfirm
    _skipQuitConfirm = bool(_loadGuiSettings().get("skipQuitConfirm", False))
    return _skipQuitConfirm

def setSkipQuitConfirm(value: bool):
    global _skipQuitConfirm
    _skipQuitConfirm = bool(value)
    _saveGuiSettings({"skipQuitConfirm": _skipQuitConfirm})

def t(key: str) -> str:
    return TRANSLATIONS.get(_currentLang, TRANSLATIONS["en"]).get(key, TRANSLATIONS["en"].get(key, key))


def centerDialog(dlg, parent=None):
    """Centers a Toplevel dialog over its parent window (or the whole screen, if the
    parent isn't in a usable state) instead of wherever Tk drops it by default (the
    screen's top-left-ish corner on Windows, regardless of where the main window
    actually is) - called once a dialog's final size is known, i.e. after its own
    geometry() call for a fixed-size dialog, or after all of its widgets have been
    packed for one that sizes itself to its contents."""
    dlg.update_idletasks()
    w = dlg.winfo_width() or dlg.winfo_reqwidth()
    h = dlg.winfo_height() or dlg.winfo_reqheight()
    sw, sh = dlg.winfo_screenwidth(), dlg.winfo_screenheight()
    x = y = None
    if parent is not None:
        try:
            px, py = parent.winfo_rootx(), parent.winfo_rooty()
            pw, ph = parent.winfo_width(), parent.winfo_height()
            x = px + (pw - w) // 2
            y = py + (ph - h) // 2
            # A parent whose geometry was queried while minimized/off-screen (e.g. the
            # user alt-tabbed away during a multi-second blocking call, like the
            # certificate regeneration this guards) can report stale coordinates far
            # outside the real screen - falling back to plain screen-centering here
            # instead of trusting that blindly is what actually keeps the dialog
            # visible in that case.
            if not (-w < x < sw and -h < y < sh):
                x = y = None
        except tk.TclError:
            x = y = None
    if x is None:
        x = (sw - w) // 2
        y = (sh - h) // 2
    dlg.geometry(f"{w}x{h}+{max(0, x)}+{max(0, y)}")


# Native tk.messagebox dialogs render as unstyled OS windows (white background) that
# ignore the app's dark ttk theme entirely. These are drop-in replacements matching the
# stdlib (title, message, parent=None) signature, so call sites only need renaming.
_APP_ROOT = None


def _darkDialog(kind, title, message, parent, buttons):
    """kind is 'info'/'error'/'question' (only affects which buttons are shown by the
    caller); buttons is a list of (label, value) pairs, first one focused/default.
    Returns the value tied to whichever button was clicked, or the default's value if
    the window is closed via the titlebar X."""
    owner = parent or _APP_ROOT
    dlg = tk.Toplevel(owner) if owner is not None else tk.Toplevel()
    dlg.title(title)
    dlg.configure(bg=UI_BG)
    dlg.resizable(False, False)
    if owner is not None:
        dlg.transient(owner.winfo_toplevel())

    result = {"value": buttons[0][1]}

    body = ttk.Frame(dlg, padding=(20, 16))
    body.pack(fill="both", expand=True)
    ttk.Label(body, text=message, wraplength=360, justify="left").pack(anchor="w")

    btnFrame = ttk.Frame(dlg, padding=(20, 0, 20, 16))
    btnFrame.pack(fill="x")

    def choose(value):
        result["value"] = value
        dlg.destroy()

    firstBtn = None
    for label, value in reversed(buttons):
        b = ttk.Button(btnFrame, text=label, command=lambda v=value: choose(v))
        b.pack(side="right", padx=(6, 0))
        firstBtn = b
    if firstBtn is not None:
        firstBtn.focus_set()

    dlg.protocol("WM_DELETE_WINDOW", lambda: choose(buttons[-1][1]))
    dlg.bind("<Return>", lambda _e: choose(buttons[0][1]))
    dlg.bind("<Escape>", lambda _e: choose(buttons[-1][1]))
    centerDialog(dlg, owner.winfo_toplevel() if owner is not None else None)
    dlg.grab_set()
    dlg.wait_window()
    return result["value"]


def showInfoDark(title, message, parent=None):
    _darkDialog("info", title, message, parent, [(t("word_ok"), True)])


def showErrorDark(title, message, parent=None):
    _darkDialog("error", title, message, parent, [(t("word_ok"), True)])


def askYesNoDark(title, message, parent=None):
    return _darkDialog("question", title, message, parent, [(t("word_yes"), True), (t("word_no"), False)])


def showWaitingDark(title, message, parent=None):
    """Non-blocking sibling of _darkDialog's other callers - no buttons, no grab_set()/
    wait_window(), just shown immediately so it's visible in front of a following
    blocking call (e.g. regenerateHttpsCertificate()'s few seconds of subprocess
    calls) on the SAME thread. Caller is responsible for calling .destroy() on the
    returned Toplevel once that work finishes."""
    owner = parent or _APP_ROOT
    dlg = tk.Toplevel(owner) if owner is not None else tk.Toplevel()
    dlg.title(title)
    dlg.configure(bg=UI_BG)
    dlg.resizable(False, False)
    if owner is not None:
        dlg.transient(owner.winfo_toplevel())

    body = ttk.Frame(dlg, padding=(20, 16))
    body.pack(fill="both", expand=True)
    ttk.Label(body, text=message, wraplength=360, justify="left").pack(anchor="w")

    centerDialog(dlg, owner.winfo_toplevel() if owner is not None else None)
    dlg.update()
    return dlg


def askYesNoDarkWithCheckbox(title, message, checkboxLabel, parent=None):
    """Same as askYesNoDark, but with an extra checkbox row (e.g. 'don't ask again').
    Returns (confirmed, checkboxChecked)."""
    owner = parent or _APP_ROOT
    dlg = tk.Toplevel(owner) if owner is not None else tk.Toplevel()
    dlg.title(title)
    dlg.configure(bg=UI_BG)
    dlg.resizable(False, False)
    if owner is not None:
        dlg.transient(owner.winfo_toplevel())

    result = {"value": False}
    checkVar = tk.BooleanVar(value=False)

    body = ttk.Frame(dlg, padding=(20, 16))
    body.pack(fill="both", expand=True)
    ttk.Label(body, text=message, wraplength=360, justify="left").pack(anchor="w")
    ttk.Checkbutton(body, text=checkboxLabel, variable=checkVar).pack(anchor="w", pady=(12, 0))

    btnFrame = ttk.Frame(dlg, padding=(20, 0, 20, 16))
    btnFrame.pack(fill="x")

    def choose(value):
        result["value"] = value
        dlg.destroy()

    noBtn = ttk.Button(btnFrame, text=t("word_no"), command=lambda: choose(False))
    noBtn.pack(side="right", padx=(6, 0))
    yesBtn = ttk.Button(btnFrame, text=t("word_yes"), command=lambda: choose(True))
    yesBtn.pack(side="right", padx=(6, 0))
    yesBtn.focus_set()

    dlg.protocol("WM_DELETE_WINDOW", lambda: choose(False))
    dlg.bind("<Return>", lambda _e: choose(True))
    dlg.bind("<Escape>", lambda _e: choose(False))
    centerDialog(dlg, owner.winfo_toplevel() if owner is not None else None)
    dlg.grab_set()
    dlg.wait_window()
    return result["value"], checkVar.get()


def confirmDelete(parent, what: str) -> bool:
    return askYesNoDark(t("confirm_delete_title"), t("confirm_delete_message").format(what), parent=parent)


_BLOB_COLUMNS = {"levelData", "screenshot", "creatorGhost", "ghostData"}


def openFullRowEditor(parent, tableName: str, pkColumn: str, rowId, onSaved=None):
    """Generic 'More...' dialog: every column of one row, via PRAGMA table_info, so
    each CRUD panel doesn't need its own hand-written full-detail form. BLOB columns
    are shown read-only (size only - no binary upload from the GUI); the primary key
    is shown read-only too (renaming it would orphan foreign keys elsewhere - teamId,
    creatorId, gameId, etc. - that reference it)."""
    conn = getDbConnection()
    c = conn.cursor()
    c.execute(f"PRAGMA table_info({tableName})")
    columns = [(r["name"], r["type"]) for r in c.fetchall()]
    c.execute(f"SELECT * FROM {tableName} WHERE {pkColumn} = ?", (rowId,))
    row = c.fetchone()
    conn.close()
    if row is None:
        showInfoDark(t("details_frame"), t("row_not_found_msg"), parent=parent)
        return

    dlg = tk.Toplevel(parent)
    dlg.title(t("row_details_title_fmt").format(tableName, rowId))
    dlg.geometry("580x640")
    dlg.transient(parent.winfo_toplevel())
    dlg.configure(bg=UI_BG)
    centerDialog(dlg, parent.winfo_toplevel())

    btnFrame = ttk.Frame(dlg, padding=(12, 8))
    btnFrame.pack(side="bottom", fill="x")
    statusLabel = ttk.Label(btnFrame, text="", foreground=UI_FG)
    statusLabel.pack(side="left", padx=(8, 0))

    canvasFrame = ttk.Frame(dlg)
    canvasFrame.pack(side="top", fill="both", expand=True)
    canvas = tk.Canvas(canvasFrame, borderwidth=0, highlightthickness=0, bg=UI_BG)
    vscroll = ttk.Scrollbar(canvasFrame, orient="vertical", command=canvas.yview)
    canvas.configure(yscrollcommand=vscroll.set)
    vscroll.pack(side="right", fill="y")
    canvas.pack(side="left", fill="both", expand=True)
    inner = ttk.Frame(canvas, padding=12)
    canvasWindow = canvas.create_window((0, 0), window=inner, anchor="nw")
    inner.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.bind("<Configure>", lambda e: canvas.itemconfigure(canvasWindow, width=e.width))

    fieldVars = {}
    for i, (colName, colType) in enumerate(columns):
        ttk.Label(inner, text=colName, font=("Segoe UI", 9, "bold")).grid(
            row=i, column=0, sticky="ne", padx=(0, 8), pady=3)
        value = row[colName]
        if colName in _BLOB_COLUMNS:
            size = len(value) if value else 0
            ttk.Label(inner, text=t("blob_not_editable_fmt").format(size), foreground=UI_MUTED).grid(
                row=i, column=1, sticky="w", pady=3)
        elif colName == pkColumn:
            ttk.Label(inner, text=str(value), foreground=UI_MUTED).grid(row=i, column=1, sticky="w", pady=3)
        else:
            var = tk.StringVar(value="" if value is None else str(value))
            ttk.Entry(inner, textvariable=var, width=48).grid(row=i, column=1, sticky="w", pady=3)
            fieldVars[colName] = (var, colType)
    inner.columnconfigure(1, weight=1)

    def save():
        setParts, values = [], []
        for colName, (var, colType) in fieldVars.items():
            raw = var.get()
            upperType = (colType or "").upper()
            try:
                if raw == "":
                    coerced = None
                elif "INT" in upperType:
                    coerced = int(raw)
                elif any(t in upperType for t in ("REAL", "FLOA", "DOUB")):
                    coerced = float(raw)
                else:
                    coerced = raw
            except ValueError:
                showErrorDark(t("details_frame"), t("numeric_expected_fmt").format(colName, raw), parent=dlg)
                return
            setParts.append(f"{colName} = ?")
            values.append(coerced)
        values.append(rowId)
        conn2 = getDbConnection()
        try:
            conn2.execute(f"UPDATE {tableName} SET {', '.join(setParts)} WHERE {pkColumn} = ?", values)
            conn2.commit()
        except sqlite3.Error as e:
            showErrorDark(t("details_frame"), t("save_failed_fmt").format(e), parent=dlg)
            return
        finally:
            conn2.close()
        if onSaved:
            onSaved()
        statusLabel.configure(text=t("status_saved"))
        dlg.after(600, dlg.destroy)

    ttk.Button(btnFrame, text=t("save"), command=save).pack(side="left")
    ttk.Button(btnFrame, text=t("close"), command=dlg.destroy).pack(side="left", padx=(6, 0))


def labeledEntry(parent, label, row, col, width=22):
    ttk.Label(parent, text=label).grid(row=row, column=col * 2, sticky="e", padx=(8, 2), pady=3)
    var = tk.StringVar()
    ttk.Entry(parent, textvariable=var, width=width).grid(row=row, column=col * 2 + 1, sticky="w", padx=(0, 8), pady=3)
    return var


def labeledCheckbox(parent, label, row, col):
    var = tk.BooleanVar()
    ttk.Checkbutton(parent, text=label, variable=var).grid(row=row, column=col * 2, columnspan=2, sticky="w", padx=8, pady=3)
    return var


# Standard ISO 3166-1 alpha-2 codes - the client looks these up as "flag_<code>" atlas
# frames (PsUIProfileImage.GetCreatorCountryCode() etc.); an unrecognized code just
# renders no flag rather than crashing, so this being a superset is harmless.
_COUNTRY_CODES = sorted([
    "AD","AE","AF","AG","AI","AL","AM","AO","AQ","AR","AS","AT","AU","AW","AX","AZ",
    "BA","BB","BD","BE","BF","BG","BH","BI","BJ","BL","BM","BN","BO","BQ","BR","BS",
    "BT","BV","BW","BY","BZ","CA","CC","CD","CF","CG","CH","CI","CK","CL","CM","CN",
    "CO","CR","CU","CV","CW","CX","CY","CZ","DE","DJ","DK","DM","DO","DZ","EC","EE",
    "EG","EH","ER","ES","ET","FI","FJ","FK","FM","FO","FR","GA","GB","GD","GE","GF",
    "GG","GH","GI","GL","GM","GN","GP","GQ","GR","GS","GT","GU","GW","GY","HK","HM",
    "HN","HR","HT","HU","ID","IE","IL","IM","IN","IO","IQ","IR","IS","IT","JE","JM",
    "JO","JP","KE","KG","KH","KI","KM","KN","KP","KR","KW","KY","KZ","LA","LB","LC",
    "LI","LK","LR","LS","LT","LU","LV","LY","MA","MC","MD","ME","MF","MG","MH","MK",
    "ML","MM","MN","MO","MP","MQ","MR","MS","MT","MU","MV","MW","MX","MY","MZ","NA",
    "NC","NE","NF","NG","NI","NL","NO","NP","NR","NU","NZ","OM","PA","PE","PF","PG",
    "PH","PK","PL","PM","PN","PR","PS","PT","PW","PY","QA","RE","RO","RS","RU","RW",
    "SA","SB","SC","SD","SE","SG","SH","SI","SJ","SK","SL","SM","SN","SO","SR","SS",
    "ST","SV","SX","SY","SZ","TC","TD","TF","TG","TH","TJ","TK","TL","TM","TN","TO",
    "TR","TT","TV","TW","TZ","UA","UG","UM","US","UY","UZ","VA","VC","VE","VG","VI",
    "VN","VU","WF","WS","YE","YT","ZA","ZM","ZW",
])


# Small flag ICONS drawn with plain tkinter.PhotoImage (no Pillow/network/bundled art
# needed - stdlib-only, matching the rest of this file). Tk cannot render real flag
# emoji (it draws each Unicode "regional indicator" letter as its own tiny glyph
# instead of compositing them into a flag - confirmed, that's why an earlier emoji-text
# attempt looked like "ᴬᴰ AD" instead of an actual flag), so this renders a small
# schematic swatch per country instead: real flag colors laid out as horizontal/
# vertical stripes, a Nordic-style cross, a canton block, or a center disc - whichever
# layout best matches that flag's real design. These are simplified/stylized (a flag
# with an intricate emblem, seal, or animal loses that detail down to its base colors)
# rather than pixel-perfect, since there's no real flag image asset anywhere in this
# project or the decompiled client to draw from instead - but every code gets its
# actual national colors in roughly the right arrangement, which reads as "that
# country's flag" far better than a two-letter code ever could.
_FLAG_SPECS = {
    "AD": ("v3", ("#0018A8", "#FEDD00", "#D50032")), "AE": ("h3", ("#00732F", "#FFFFFF", "#000000")),
    "AF": ("v3", ("#000000", "#D32011", "#007A36")), "AG": ("canton", ("#CE1126", "#000000")),
    "AI": ("canton", ("#00247D", "#CF142B")), "AL": ("solid", ("#E41E20",)),
    "AM": ("h3", ("#D90012", "#0033A0", "#F2A800")), "AO": ("h2", ("#CC092F", "#000000")),
    "AQ": ("solid", ("#FFFFFF",)), "AR": ("h3", ("#74ACDF", "#FFFFFF", "#74ACDF")),
    "AS": ("canton", ("#BF0A30", "#002868")), "AT": ("h3", ("#ED2939", "#FFFFFF", "#ED2939")),
    "AU": ("canton", ("#00247D", "#CF142B")), "AW": ("canton", ("#418FDE", "#F9E814")),
    "AX": ("cross", ("#0053A5", "#FFD100")), "AZ": ("h3", ("#00B9E4", "#EF3340", "#509E2F")),
    "BA": ("canton", ("#002395", "#FECB00")), "BB": ("v3", ("#00267F", "#FFC726", "#00267F")),
    "BD": ("circle", ("#006A4E", "#F42A41")), "BE": ("v3", ("#000000", "#FDDA24", "#EF3340")),
    "BF": ("h2", ("#EF2B2D", "#009E49")), "BG": ("h3", ("#FFFFFF", "#00966E", "#D62612")),
    "BH": ("v2", ("#FFFFFF", "#CE1126")), "BI": ("canton", ("#1EB53A", "#CE1126")),
    "BJ": ("v3", ("#008751", "#FCD116", "#E8112D")), "BL": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "BM": ("canton", ("#CF142B", "#00247D")), "BN": ("canton", ("#FFCE00", "#CE1126")),
    "BO": ("h3", ("#D52B1E", "#F9E300", "#007934")), "BQ": ("h3", ("#AE1C28", "#FFFFFF", "#21468B")),
    "BR": ("canton", ("#009739", "#FEDD00")), "BS": ("h3", ("#00778B", "#FFC72C", "#00778B")),
    "BT": ("v2", ("#FFC726", "#FF4E12")), "BV": ("cross", ("#BA0C2F", "#00205B")),
    "BW": ("h3", ("#75AADB", "#000000", "#75AADB")), "BY": ("h2", ("#D22730", "#007A3D")),
    "BZ": ("h3", ("#CE1126", "#003F87", "#CE1126")), "CA": ("v3", ("#FF0000", "#FFFFFF", "#FF0000")),
    "CC": ("solid", ("#007A3D",)), "CD": ("canton", ("#007FFF", "#F7D618")),
    "CF": ("h3", ("#003082", "#FFFFFF", "#289728")), "CG": ("v3", ("#009543", "#FBDE4A", "#DC241F")),
    "CH": ("cross", ("#FF0000", "#FFFFFF")), "CI": ("v3", ("#F77F00", "#FFFFFF", "#009E60")),
    "CK": ("canton", ("#00247D", "#CF142B")), "CL": ("h2", ("#FFFFFF", "#D52B1E")),
    "CM": ("v3", ("#007A5E", "#CE1126", "#FCD116")), "CN": ("canton", ("#DE2910", "#FFDE00")),
    "CO": ("h3", ("#FCD116", "#003893", "#CE1126")), "CR": ("h3", ("#002B7F", "#CE1126", "#002B7F")),
    "CU": ("canton", ("#CB1515", "#002A8F")), "CV": ("h3", ("#003893", "#FFFFFF", "#003893")),
    "CW": ("h2", ("#002B7F", "#F9E814")), "CX": ("v2", ("#006400", "#00008B")),
    "CY": ("canton", ("#FFFFFF", "#D57800")), "CZ": ("h2", ("#FFFFFF", "#D7141A")),
    "DE": ("h3", ("#000000", "#DD0000", "#FFCE00")), "DJ": ("h2", ("#6AB2E7", "#12AD2B")),
    "DK": ("cross", ("#C60C30", "#FFFFFF")), "DM": ("cross", ("#006B3F", "#FCD116")),
    "DO": ("cross", ("#002D62", "#FFFFFF")), "DZ": ("v2", ("#006233", "#FFFFFF")),
    "EC": ("h3", ("#FFDD00", "#034EA2", "#EF3340")), "EE": ("h3", ("#0072CE", "#000000", "#FFFFFF")),
    "EG": ("h3", ("#CE1126", "#FFFFFF", "#000000")), "EH": ("h3", ("#000000", "#FFFFFF", "#007A3D")),
    "ER": ("v2", ("#12AD2B", "#4189DD")), "ES": ("h3", ("#AA151B", "#F1BF00", "#AA151B")),
    "ET": ("h3", ("#078930", "#FCDD09", "#DA121A")), "FI": ("cross", ("#FFFFFF", "#003580")),
    "FJ": ("canton", ("#68BFE5", "#00247D")), "FK": ("canton", ("#00247D", "#CF142B")),
    "FM": ("solid", ("#75B2DD",)), "FO": ("cross", ("#FFFFFF", "#D22730")),
    "FR": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")), "GA": ("h3", ("#009E60", "#FCD116", "#3A75C4")),
    "GB": ("canton", ("#00247D", "#CF142B")), "GD": ("v3", ("#007A5E", "#FCD116", "#CE1126")),
    "GE": ("cross", ("#FFFFFF", "#FF0000")), "GF": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "GG": ("cross", ("#FFFFFF", "#CF142B")), "GH": ("h3", ("#CE1126", "#FCD116", "#006B3F")),
    "GI": ("h2", ("#FFFFFF", "#DA020E")), "GL": ("h2", ("#FFFFFF", "#C60C30")),
    "GM": ("h3", ("#CE1126", "#0C1C8C", "#3A7728")), "GN": ("v3", ("#CE1126", "#FCD116", "#009460")),
    "GP": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")), "GQ": ("h3", ("#3E9A00", "#FFFFFF", "#E32118")),
    "GR": ("h2", ("#0D5EAF", "#FFFFFF")), "GS": ("canton", ("#00247D", "#CF142B")),
    "GT": ("v3", ("#4997D0", "#FFFFFF", "#4997D0")), "GU": ("canton", ("#003876", "#C8102E")),
    "GW": ("v2", ("#CE1126", "#009E49")), "GY": ("canton", ("#009739", "#CE1126")),
    "HK": ("solid", ("#DE2910",)), "HM": ("canton", ("#00247D", "#CF142B")),
    "HN": ("h3", ("#0073CF", "#FFFFFF", "#0073CF")), "HR": ("h3", ("#FF0000", "#FFFFFF", "#171796")),
    "HT": ("h2", ("#00209F", "#D21034")), "HU": ("h3", ("#CE2939", "#FFFFFF", "#477050")),
    "ID": ("h2", ("#FF0000", "#FFFFFF")), "IE": ("v3", ("#169B62", "#FFFFFF", "#FF883E")),
    "IL": ("h3", ("#0038B8", "#FFFFFF", "#0038B8")), "IM": ("solid", ("#CF142B",)),
    "IN": ("h3", ("#FF9933", "#FFFFFF", "#138808")), "IO": ("canton", ("#00247D", "#CF142B")),
    "IQ": ("h3", ("#CE1126", "#FFFFFF", "#000000")), "IR": ("h3", ("#239F40", "#FFFFFF", "#DA0000")),
    "IS": ("cross", ("#02529C", "#DC1E35")), "IT": ("v3", ("#009246", "#FFFFFF", "#CE2B37")),
    "JE": ("cross", ("#FFFFFF", "#CE1126")), "JM": ("v2", ("#009B3A", "#000000")),
    "JO": ("h3", ("#000000", "#FFFFFF", "#007A3D")), "JP": ("circle", ("#FFFFFF", "#BC002D")),
    "KE": ("h3", ("#000000", "#BB0000", "#006600")), "KG": ("circle", ("#E8112D", "#FFEF00")),
    "KH": ("h3", ("#032EA1", "#E00025", "#032EA1")), "KI": ("h2", ("#CE1126", "#003F87")),
    "KM": ("h3", ("#FFC61E", "#FFFFFF", "#CE1126")), "KN": ("v2", ("#009739", "#CE1126")),
    "KP": ("h3", ("#024FA2", "#ED1C27", "#024FA2")), "KR": ("circle", ("#FFFFFF", "#CD2E3A")),
    "KW": ("h3", ("#007A3D", "#FFFFFF", "#CE1126")), "KY": ("canton", ("#00247D", "#CF142B")),
    "KZ": ("solid", ("#00AFCA",)), "LA": ("h3", ("#CE1126", "#002868", "#CE1126")),
    "LB": ("h3", ("#ED1C24", "#FFFFFF", "#ED1C24")), "LC": ("canton", ("#66CCFF", "#000000")),
    "LI": ("h2", ("#002B7F", "#CE1126")), "LK": ("v3", ("#00534E", "#FF9933", "#8D153A")),
    "LR": ("canton", ("#BF0A30", "#002868")), "LS": ("h3", ("#00209F", "#FFFFFF", "#009543")),
    "LT": ("h3", ("#FDB913", "#006A44", "#C1272D")), "LU": ("h3", ("#ED2939", "#FFFFFF", "#00A1DE")),
    "LV": ("h3", ("#9E3039", "#FFFFFF", "#9E3039")), "LY": ("h3", ("#E70013", "#000000", "#239E46")),
    "MA": ("solid", ("#C1272D",)), "MC": ("h2", ("#CE1126", "#FFFFFF")),
    "MD": ("v3", ("#003DA5", "#FFD200", "#CC092F")), "ME": ("solid", ("#C40308",)),
    "MF": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")), "MG": ("v3", ("#FFFFFF", "#FC3D32", "#007E3A")),
    "MH": ("v2", ("#003893", "#DD7500")), "MK": ("circle", ("#D20000", "#FFE600")),
    "ML": ("v3", ("#14B53A", "#FCD116", "#CE1126")), "MM": ("h3", ("#FECB00", "#34B233", "#EA2839")),
    "MN": ("v3", ("#C4272F", "#015197", "#C4272F")), "MO": ("solid", ("#00785E",)),
    "MP": ("circle", ("#0033A0", "#FFFFFF")), "MQ": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "MR": ("h3", ("#D01C1F", "#00A95C", "#D01C1F")), "MS": ("canton", ("#00247D", "#CF142B")),
    "MT": ("v2", ("#FFFFFF", "#CF142B")), "MU": ("h3", ("#EA2839", "#1A206D", "#00A551")),
    "MV": ("canton", ("#D21034", "#007E3A")), "MW": ("h3", ("#000000", "#CE1126", "#339E35")),
    "MX": ("v3", ("#006847", "#FFFFFF", "#CE1126")), "MY": ("canton", ("#CC0001", "#010066")),
    "MZ": ("h3", ("#009739", "#000000", "#FCD116")), "NA": ("v2", ("#003580", "#009543")),
    "NC": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")), "NE": ("h3", ("#E05206", "#FFFFFF", "#0DB02B")),
    "NF": ("h3", ("#046A38", "#FFFFFF", "#046A38")), "NG": ("v3", ("#008751", "#FFFFFF", "#008751")),
    "NI": ("h3", ("#0067C6", "#FFFFFF", "#0067C6")), "NL": ("h3", ("#AE1C28", "#FFFFFF", "#21468B")),
    "NO": ("cross", ("#BA0C2F", "#00205B")), "NP": ("solid", ("#DC143C",)),
    "NR": ("h2", ("#002B7F", "#FFC61E")), "NU": ("canton", ("#FED141", "#00247D")),
    "NZ": ("canton", ("#00247D", "#CF142B")), "OM": ("h3", ("#FFFFFF", "#DB161B", "#008000")),
    "PA": ("v2", ("#005293", "#D21034")), "PE": ("v3", ("#D91023", "#FFFFFF", "#D91023")),
    "PF": ("h3", ("#CE1126", "#FFFFFF", "#CE1126")), "PG": ("v2", ("#000000", "#CE1126")),
    "PH": ("h2", ("#0038A8", "#CE1126")), "PK": ("v2", ("#FFFFFF", "#01411C")),
    "PL": ("h2", ("#FFFFFF", "#DC143C")), "PM": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "PN": ("canton", ("#00247D", "#CF142B")), "PR": ("canton", ("#ED1C24", "#0050F0")),
    "PS": ("h3", ("#000000", "#FFFFFF", "#007A3D")), "PT": ("v2", ("#046A38", "#DA020E")),
    "PW": ("circle", ("#4AADD6", "#FFDE00")), "PY": ("h3", ("#D52B1E", "#FFFFFF", "#0038A8")),
    "QA": ("v2", ("#FFFFFF", "#8D1B3D")), "RE": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "RO": ("v3", ("#002B7F", "#FCD116", "#CE1126")), "RS": ("h3", ("#C6363C", "#0C4076", "#FFFFFF")),
    "RU": ("h3", ("#FFFFFF", "#0039A6", "#D52B1E")), "RW": ("h3", ("#00A1DE", "#FAD201", "#20603D")),
    "SA": ("solid", ("#006C35",)), "SB": ("v2", ("#0051BA", "#215B33")),
    "SC": ("v3", ("#003F87", "#D62828", "#007A3D")), "SD": ("h3", ("#D21034", "#FFFFFF", "#000000")),
    "SE": ("cross", ("#006AA7", "#FECC02")), "SG": ("h2", ("#ED2939", "#FFFFFF")),
    "SH": ("canton", ("#00247D", "#CF142B")), "SI": ("h3", ("#FFFFFF", "#005DA4", "#ED1C24")),
    "SJ": ("cross", ("#BA0C2F", "#00205B")), "SK": ("h3", ("#FFFFFF", "#0B4EA2", "#EE1C25")),
    "SL": ("h3", ("#1EB53A", "#FFFFFF", "#0072C6")), "SM": ("h2", ("#FFFFFF", "#5EB6E4")),
    "SN": ("v3", ("#00853F", "#FDEF42", "#E31B23")), "SO": ("circle", ("#4189DD", "#FFFFFF")),
    "SR": ("h3", ("#377E3F", "#B40A2D", "#377E3F")), "SS": ("h3", ("#000000", "#DA121A", "#078930")),
    "ST": ("h3", ("#12AD2B", "#FFCE00", "#12AD2B")), "SV": ("h3", ("#0047AB", "#FFFFFF", "#0047AB")),
    "SX": ("v2", ("#C41E3A", "#002868")), "SY": ("h3", ("#CE1126", "#FFFFFF", "#000000")),
    "SZ": ("h3", ("#0D009B", "#FFD900", "#B10C0C")), "TC": ("canton", ("#00247D", "#CF142B")),
    "TD": ("v3", ("#002664", "#FECB00", "#C60C30")), "TF": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "TG": ("canton", ("#006A4E", "#D21034")), "TH": ("h3", ("#A51931", "#00247D", "#A51931")),
    "TJ": ("h3", ("#CC0000", "#FFFFFF", "#006600")), "TK": ("canton", ("#FFD100", "#00247D")),
    "TL": ("v2", ("#FFC60B", "#DC241F")), "TM": ("v2", ("#CE1126", "#00843D")),
    "TN": ("circle", ("#E70013", "#FFFFFF")), "TO": ("canton", ("#C10000", "#FFFFFF")),
    "TR": ("circle", ("#E30A17", "#FFFFFF")), "TT": ("v2", ("#CE1126", "#000000")),
    "TV": ("canton", ("#38B6FF", "#00247D")), "TW": ("canton", ("#FE0000", "#000095")),
    "TZ": ("v2", ("#1EB53A", "#00A3DD")), "UA": ("h2", ("#0057B7", "#FFD700")),
    "UG": ("h3", ("#000000", "#FCDC04", "#D90000")), "UM": ("canton", ("#B22234", "#3C3B6E")),
    "US": ("canton", ("#B22234", "#3C3B6E")), "UY": ("canton", ("#FFFFFF", "#0038A8")),
    "UZ": ("h3", ("#0099B5", "#FFFFFF", "#1EB53A")), "VA": ("v2", ("#FFE000", "#FFFFFF")),
    "VC": ("v3", ("#0038A8", "#FCD116", "#009E49")), "VE": ("h3", ("#FFCC00", "#00247D", "#CF142B")),
    "VG": ("canton", ("#00247D", "#CF142B")), "VI": ("canton", ("#FFFFFF", "#0050A4")),
    "VN": ("circle", ("#DA251D", "#FFFF00")), "VU": ("v2", ("#D21034", "#009543")),
    "WF": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")), "WS": ("canton", ("#CE1126", "#002B7F")),
    "YE": ("h3", ("#CE1126", "#FFFFFF", "#000000")), "YT": ("v3", ("#0055A4", "#FFFFFF", "#EF4135")),
    "ZA": ("h3", ("#007A4D", "#FFB612", "#000000")), "ZM": ("canton", ("#198A00", "#DE2010")),
    "ZW": ("h3", ("#006400", "#FFD200", "#D40000")),
}

_FLAG_W, _FLAG_H = 22, 14
_flagImageCache = {}

def getFlagImage(code: str) -> tk.PhotoImage:
    """Builds (and caches) a small PhotoImage flag swatch for a country code. Cached
    in a module-level dict rather than on the calling widget - PhotoImage objects are
    only kept alive by a live Python reference, and without this every image would be
    garbage-collected (and vanish from its button) the moment the local variable that
    created it went out of scope."""
    code = (code or "").strip().upper()
    if code in _flagImageCache:
        return _flagImageCache[code]
    img = tk.PhotoImage(width=_FLAG_W, height=_FLAG_H)
    spec = _FLAG_SPECS.get(code)
    if spec is None:
        img.put("#777777", to=(0, 0, _FLAG_W, _FLAG_H))
    else:
        kind, colors = spec
        if kind == "solid":
            img.put(colors[0], to=(0, 0, _FLAG_W, _FLAG_H))
        elif kind == "h2":
            img.put(colors[0], to=(0, 0, _FLAG_W, _FLAG_H // 2))
            img.put(colors[1], to=(0, _FLAG_H // 2, _FLAG_W, _FLAG_H))
        elif kind == "h3":
            h = _FLAG_H // 3
            img.put(colors[0], to=(0, 0, _FLAG_W, h))
            img.put(colors[1], to=(0, h, _FLAG_W, 2 * h))
            img.put(colors[2], to=(0, 2 * h, _FLAG_W, _FLAG_H))
        elif kind == "v2":
            w = _FLAG_W // 2
            img.put(colors[0], to=(0, 0, w, _FLAG_H))
            img.put(colors[1], to=(w, 0, _FLAG_W, _FLAG_H))
        elif kind == "v3":
            w = _FLAG_W // 3
            img.put(colors[0], to=(0, 0, w, _FLAG_H))
            img.put(colors[1], to=(w, 0, 2 * w, _FLAG_H))
            img.put(colors[2], to=(2 * w, 0, _FLAG_W, _FLAG_H))
        elif kind == "canton":
            img.put(colors[0], to=(0, 0, _FLAG_W, _FLAG_H))
            img.put(colors[1], to=(0, 0, _FLAG_W * 3 // 5, _FLAG_H * 4 // 7))
        elif kind == "cross":
            img.put(colors[0], to=(0, 0, _FLAG_W, _FLAG_H))
            vx = _FLAG_W * 5 // 14
            vw = max(2, _FLAG_W // 8)
            img.put(colors[1], to=(vx, 0, vx + vw, _FLAG_H))
            hy = _FLAG_H // 2 - 1
            hh = max(2, _FLAG_H // 7)
            img.put(colors[1], to=(0, hy, _FLAG_W, hy + hh))
        elif kind == "circle":
            img.put(colors[0], to=(0, 0, _FLAG_W, _FLAG_H))
            cx, cy, r = _FLAG_W / 2, _FLAG_H / 2, min(_FLAG_W, _FLAG_H) / 3
            for y in range(_FLAG_H):
                for x in range(_FLAG_W):
                    if (x + 0.5 - cx) ** 2 + (y + 0.5 - cy) ** 2 <= r * r:
                        img.put(colors[1], to=(x, y, x + 1, y + 1))
        else:
            img.put("#777777", to=(0, 0, _FLAG_W, _FLAG_H))
    _flagImageCache[code] = img
    return img


def labeledCountryButton(parent, label, row, col):
    ttk.Label(parent, text=label).grid(row=row, column=col * 2, sticky="e", padx=(8, 2), pady=3)
    var = tk.StringVar(value="US")
    displayVar = tk.StringVar()
    btn = ttk.Button(parent, textvariable=displayVar, compound="left", width=6,
                      command=lambda: openCountryPicker(parent, var))

    def _syncDisplay(*_args):
        code = var.get()
        btn.configure(image=getFlagImage(code))
        displayVar.set(code)
    var.trace_add("write", _syncDisplay)
    _syncDisplay()

    btn.grid(row=row, column=col * 2 + 1, sticky="w", padx=(0, 8), pady=3)
    return var


def openCountryPicker(parent, var):
    dlg = tk.Toplevel(parent)
    dlg.title(t("country_picker_title"))
    dlg.transient(parent.winfo_toplevel())
    dlg.geometry("480x520")
    dlg.configure(bg=UI_BG)
    centerDialog(dlg, parent.winfo_toplevel())

    canvasFrame = ttk.Frame(dlg)
    canvasFrame.pack(fill="both", expand=True)
    canvas = tk.Canvas(canvasFrame, borderwidth=0, highlightthickness=0, bg=UI_BG)
    vscroll = ttk.Scrollbar(canvasFrame, orient="vertical", command=canvas.yview)
    canvas.configure(yscrollcommand=vscroll.set)
    vscroll.pack(side="right", fill="y")
    canvas.pack(side="left", fill="both", expand=True)
    inner = ttk.Frame(canvas, padding=8)
    canvasWindow = canvas.create_window((0, 0), window=inner, anchor="nw")
    inner.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.bind("<Configure>", lambda e: canvas.itemconfigure(canvasWindow, width=e.width))

    def pick(code):
        var.set(code)
        dlg.destroy()

    columns = 5
    for i, code in enumerate(_COUNTRY_CODES):
        ttk.Button(inner, image=getFlagImage(code), text=code, compound="left", width=6,
                   command=lambda c=code: pick(c)).grid(
            row=i // columns, column=i % columns, padx=2, pady=2)


def openLevelPicker(parent, onPick):
    """Search-as-you-type level picker dialog (used by the Tournament tab's "Choose
    Level" button) - a plain dropdown/listbox loaded with every level up front becomes
    unusable once the level count gets into the hundreds/thousands, so this queries
    `minigames` fresh on every keystroke instead. Any level created after the dialog
    was last opened - including ones made after this whole app started - shows up
    automatically next time it's opened, since nothing here is cached across opens.
    onPick(minigameId, name) is called once the user picks a row; the dialog closes
    itself either way (picking or cancelling)."""
    dlg = tk.Toplevel(parent)
    dlg.title(t("level_picker_title"))
    dlg.transient(parent.winfo_toplevel())
    dlg.geometry("480x520")
    dlg.configure(bg=UI_BG)

    frame = ttk.Frame(dlg, padding=12)
    frame.pack(fill="both", expand=True)

    searchVar = tk.StringVar()
    searchEntry = ttk.Entry(frame, textvariable=searchVar, width=52)
    searchEntry.pack(anchor="w", fill="x")
    ttk.Label(frame, text=t("tour_search_hint"), foreground=UI_MUTED).pack(anchor="w", pady=(2, 6))

    listboxFrame = ttk.Frame(frame)
    listboxFrame.pack(fill="both", expand=True)
    listbox = tk.Listbox(listboxFrame, exportselection=False)
    listbox.pack(side="left", fill="both", expand=True)
    listboxScroll = ttk.Scrollbar(listboxFrame, orient="vertical", command=listbox.yview)
    listboxScroll.pack(side="right", fill="y")
    listbox.configure(yscrollcommand=listboxScroll.set)

    results = []

    def search(*_args):
        query = searchVar.get().strip()
        conn = getDbConnection()
        c = conn.cursor()
        # A tournament run is always a Race-mode PsGameLoopRacing (PsGameModeTournament
        # only ever wraps that mode), and only a published ("public") level is actually
        # reachable/playable by anyone but its own creator - so those are the only
        # levels that make sense to offer here.
        if query:
            like = f"%{query}%"
            c.execute("SELECT id, name FROM minigames WHERE gameMode = 'Race' AND state = 'public' "
                      "AND (name LIKE ? OR id LIKE ?) ORDER BY createdAt DESC LIMIT 100", (like, like))
        else:
            c.execute("SELECT id, name FROM minigames WHERE gameMode = 'Race' AND state = 'public' "
                      "ORDER BY createdAt DESC LIMIT 100")
        results[:] = [(r["id"], r["name"]) for r in c.fetchall()]
        conn.close()
        listbox.delete(0, "end")
        for lid, name in results:
            listbox.insert("end", f"{name}  [{lid}]")
    searchEntry.bind("<KeyRelease>", search)
    search()

    def pick(_event=None):
        sel = listbox.curselection()
        if not sel:
            return
        lid, name = results[sel[0]]
        dlg.destroy()
        onPick(lid, name)
    listbox.bind("<<ListboxSelect>>", pick)

    centerDialog(dlg, parent.winfo_toplevel())
    searchEntry.focus_set()


def formatBytes(n: int) -> str:
    if not n:
        return "0 B"
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


def nowMs() -> int:
    return int(time.time() * 1000)


# Monochrome (black/white/gray) palette applied via ttk.Style below - "clam" is the
# only built-in ttk theme that's fully Tk-drawn rather than native-themed, which is
# what actually lets these colors take effect on Windows (the default "vista" theme
# ignores most style color options for buttons/comboboxes/etc).
UI_BG = "#121212"
UI_PANEL = "#000000"
UI_INPUT = "#262626"
UI_HOVER = "#3a3a3a"
UI_FG = "#f2f2f2"
UI_MUTED = "#a8a8a8"
UI_BORDER = "#3d3d3d"


def applyMonochromeTheme(root: tk.Tk):
    style = ttk.Style(root)
    style.theme_use("clam")
    style.configure(".", background=UI_BG, foreground=UI_FG, fieldbackground=UI_INPUT,
                     bordercolor=UI_BORDER, darkcolor=UI_BG, lightcolor=UI_BG,
                     troughcolor=UI_PANEL, focuscolor=UI_BORDER, font=("Segoe UI", 9))
    style.configure("TFrame", background=UI_BG)
    style.configure("TLabel", background=UI_BG, foreground=UI_FG)
    style.configure("TLabelframe", background=UI_BG, foreground=UI_FG, bordercolor=UI_BORDER)
    style.configure("TLabelframe.Label", background=UI_BG, foreground=UI_FG)
    style.configure("TButton", background=UI_INPUT, foreground=UI_FG, bordercolor=UI_BORDER,
                     focusthickness=0, padding=6)
    style.map("TButton", background=[("active", UI_HOVER), ("pressed", UI_HOVER)],
              foreground=[("disabled", UI_MUTED)])
    style.configure("TEntry", fieldbackground=UI_INPUT, foreground=UI_FG, insertcolor=UI_FG,
                     bordercolor=UI_BORDER)
    style.configure("TCombobox", fieldbackground=UI_INPUT, foreground=UI_FG, background=UI_INPUT,
                     arrowcolor=UI_FG, bordercolor=UI_BORDER)
    style.map("TCombobox", fieldbackground=[("readonly", UI_INPUT), ("disabled", UI_PANEL)],
              foreground=[("readonly", UI_FG)])
    style.configure("TCheckbutton", background=UI_BG, foreground=UI_FG)
    style.map("TCheckbutton", background=[("active", UI_BG)])
    style.configure("Treeview", background=UI_INPUT, fieldbackground=UI_INPUT, foreground=UI_FG,
                     bordercolor=UI_BORDER, rowheight=22)
    style.map("Treeview", background=[("selected", UI_HOVER)], foreground=[("selected", UI_FG)])
    style.configure("Treeview.Heading", background=UI_PANEL, foreground=UI_FG, bordercolor=UI_BORDER)
    style.map("Treeview.Heading", background=[("active", UI_HOVER)])
    style.configure("TScrollbar", background=UI_PANEL, troughcolor=UI_BG, bordercolor=UI_BORDER,
                     arrowcolor=UI_FG)
    style.configure("TPanedwindow", background=UI_BG)
    root.configure(bg=UI_BG)
    # The combobox dropdown list and any plain tk.Listbox are separate Tk windows, not
    # ttk-styled - option_add is the only way to reach their colors.
    root.option_add("*TCombobox*Listbox.background", UI_INPUT)
    root.option_add("*TCombobox*Listbox.foreground", UI_FG)
    root.option_add("*TCombobox*Listbox.selectBackground", UI_HOVER)
    root.option_add("*TCombobox*Listbox.selectForeground", UI_FG)
    root.option_add("*Listbox.background", UI_INPUT)
    root.option_add("*Listbox.foreground", UI_FG)
    root.option_add("*Listbox.selectBackground", UI_HOVER)
    root.option_add("*Listbox.selectForeground", UI_FG)


class AdminApp(tk.Tk):
    SECTIONS = [
        ("dashboard", "nav_dashboard"),
        ("console", "nav_console"),
        ("requests", "nav_requests"),
        ("players", "nav_players"),
        ("levels", "nav_levels"),
        ("teams", "nav_teams"),
        ("ghosts", "nav_ghosts"),
        ("tournament", "nav_tournament"),
        ("gifs", "nav_gifs"),
        ("news", "nav_news"),
    ]

    def __init__(self):
        super().__init__()
        global _APP_ROOT
        _APP_ROOT = self
        self._gifAnimFrames = None
        self._gifAnimJob = None
        self._livePanels = {}
        self._lastPanelRows = {}
        loadSavedLang()
        loadSkipQuitConfirm()
        self.title("Big Bang Racing Server")
        windowW, windowH = 1150, 720
        screenX = (self.winfo_screenwidth() - windowW) // 2
        screenY = (self.winfo_screenheight() - windowH) // 2
        self.geometry(f"{windowW}x{windowH}+{screenX}+{screenY}")
        self.minsize(950, 600)
        applyMonochromeTheme(self)

        self._consoleQueue = queue.Queue()
        sys.stdout = _StreamTee(sys.stdout, self._consoleQueue)
        sys.stderr = _StreamTee(sys.stderr, self._consoleQueue)

        self._buildLayout()
        self._pageBuilders = {
            "dashboard": self._buildDashboard,
            "console": self._buildConsole,
            "requests": self._buildRequests,
            "players": self._buildPlayers,
            "levels": self._buildLevels,
            "teams": self._buildTeams,
            "ghosts": self._buildGhosts,
            "tournament": self._buildTournament,
            "news": self._buildNews,
            "gifs": self._buildGifs,
        }
        self._currentPage = None
        self._sidebarButtons = {}
        self._buildSidebar()
        self.showPage("dashboard")

        self._pollConsole()
        self._pollStatus()

        self.protocol("WM_DELETE_WINDOW", self._onClose)

    # -- skeleton layout ---------------------------------------------------
    def _buildLayout(self):
        self.sidebar = tk.Frame(self, width=170, bg=UI_PANEL)
        self.sidebar.pack(side="left", fill="y")
        self.sidebar.pack_propagate(False)

        self.content = ttk.Frame(self)
        self.content.pack(side="right", fill="both", expand=True)

    def _buildSidebar(self):
        title = tk.Label(self.sidebar, text="BBR Server", bg=UI_PANEL, fg=UI_FG,
                          font=("Segoe UI", 13, "bold"), pady=16)
        title.pack(fill="x")
        for key, labelKey in self.SECTIONS:
            btn = tk.Button(self.sidebar, text=t(labelKey), anchor="w", bd=0, padx=16, pady=10,
                             bg=UI_PANEL, fg=UI_MUTED, activebackground=UI_HOVER,
                             activeforeground=UI_FG, font=("Segoe UI", 10),
                             command=lambda k=key: self.showPage(k))
            btn.pack(fill="x")
            self._sidebarButtons[key] = btn

    def showPage(self, key):
        if self._currentPage == key:
            return
        self._stopGifAnimation()
        for k, btn in self._sidebarButtons.items():
            btn.configure(bg=UI_HOVER if k == key else UI_PANEL)
        for child in self.content.winfo_children():
            child.destroy()
        self._currentPage = key
        self._pageBuilders[key](self.content)

    def _rebuildSidebar(self):
        for child in self.sidebar.winfo_children():
            child.destroy()
        self._sidebarButtons = {}
        self._buildSidebar()
        if self._currentPage in self._sidebarButtons:
            self._sidebarButtons[self._currentPage].configure(bg=UI_HOVER)

    def _applyLanguage(self, lang):
        setLang(lang)
        self._rebuildSidebar()
        current = self._currentPage
        self._currentPage = None
        self.showPage(current or "dashboard")

    def _openLanguagePicker(self):
        dlg = tk.Toplevel(self)
        dlg.title(t("language_picker_title"))
        dlg.transient(self)
        dlg.configure(bg=UI_BG)
        frame = ttk.Frame(dlg, padding=16)
        frame.pack()
        for code, label, flagCode in LANGUAGES:
            ttk.Button(frame, image=getFlagImage(flagCode), text=label, compound="left", width=16,
                       command=lambda c=code, d=dlg: self._pickLanguage(c, d)).pack(pady=4)
        centerDialog(dlg, self)

    def _pickLanguage(self, code, dlg):
        dlg.destroy()
        self._applyLanguage(code)

    def _onClose(self):
        if isServerRunning():
            if not _skipQuitConfirm:
                confirmed, dontAskAgain = askYesNoDarkWithCheckbox(
                    t("quit_title"), t("quit_message"), t("quit_dont_ask_again"))
                if not confirmed:
                    return
                if dontAskAgain:
                    setSkipQuitConfirm(True)
            stopServer()
        self.destroy()

    # -- polling --------------------------------------------------------
    def _pollConsole(self):
        if self._currentPage == "console" and hasattr(self, "_consoleText"):
            drained = False
            try:
                while True:
                    line = self._consoleQueue.get_nowait()
                    self._consoleText.insert("end", line)
                    drained = True
            except queue.Empty:
                pass
            if drained:
                self._consoleText.see("end")
        else:
            # Still drain the queue so it doesn't grow forever while another tab is open.
            try:
                while True:
                    self._consoleQueue.get_nowait()
            except queue.Empty:
                pass
        self.after(200, self._pollConsole)

    def _pollStatus(self):
        if self._currentPage == "dashboard" and hasattr(self, "_statusLabels"):
            self._refreshDashboardStatus()
        if self._currentPage == "requests" and hasattr(self, "_requestsTree"):
            self._refreshRequests()
        self._pollLivePanel(self._currentPage)
        self.after(1000, self._pollStatus)

    # -- Dashboard ------------------------------------------------------
    def _buildDashboard(self, parent):
        frame = ttk.Frame(parent, padding=20)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text=t("nav_dashboard"), font=("Segoe UI", 14, "bold")).pack(anchor="w")

        btnFrame = ttk.Frame(frame)
        btnFrame.pack(anchor="w", pady=(14, 10))
        self._startStopBtn = ttk.Button(btnFrame, text=t("btn_start_server"), command=self._toggleServer)
        self._startStopBtn.pack(side="left")
        ttk.Button(btnFrame, text=t("language_button"), command=self._openLanguagePicker).pack(
            side="left", padx=(8, 0))

        statusFrame = ttk.LabelFrame(frame, text=t("service_status_frame"), padding=12)
        statusFrame.pack(fill="x", pady=10)
        self._statusLabels = {}
        for i, (key, label, port) in enumerate([
            ("http", "HTTP", HTTP_PORT), ("https", "HTTPS", HTTPS_PORT), ("dns", "DNS", DNS_PORT)
        ]):
            row = ttk.Frame(statusFrame)
            row.pack(fill="x", pady=2)
            dot = tk.Label(row, text="○", bg=UI_BG, fg=UI_MUTED, font=("Segoe UI", 12))
            dot.pack(side="left")
            ttk.Label(row, text=f"  {label} ({t('port_label')} {port})", width=22, anchor="w").pack(side="left")
            self._statusLabels[key] = dot

        infoFrame = ttk.LabelFrame(frame, text=t("information_frame"), padding=12)
        infoFrame.pack(fill="x", pady=10)
        ip = localIp()
        ttk.Label(infoFrame, text=t("local_ip_label").format(ip)).pack(anchor="w")
        ttk.Label(infoFrame, text=t("database_label").format(DB_FILE)).pack(anchor="w")

        self._refreshDashboardStatus()

    def _refreshDashboardStatus(self):
        running = isServerRunning()
        self._startStopBtn.configure(text=t("btn_stop_server") if running else t("btn_start_server"))
        self._statusLabels["http"].configure(text="●" if _serverState["http"] else "○",
                                              fg=UI_FG if _serverState["http"] else UI_MUTED)
        self._statusLabels["https"].configure(text="●" if _serverState["https"] else "○",
                                               fg=UI_FG if _serverState["https"] else UI_MUTED)
        self._statusLabels["dns"].configure(text="●" if _serverState["dns"] else "○",
                                             fg=UI_FG if _serverState["dns"] else UI_MUTED)

    def _toggleServer(self):
        if isServerRunning():
            stopServer()
        else:
            threading.Thread(target=startServer, daemon=True).start()
        self.after(400, self._refreshDashboardStatus)

    # -- Console ------------------------------------------------------------
    def _buildConsole(self, parent):
        frame = ttk.Frame(parent, padding=10)
        frame.pack(fill="both", expand=True)
        toolbar = ttk.Frame(frame)
        toolbar.pack(fill="x")
        ttk.Button(toolbar, text=t("btn_clear"), command=lambda: self._consoleText.delete("1.0", "end")).pack(side="left")

        textFrame = ttk.Frame(frame)
        textFrame.pack(fill="both", expand=True, pady=(6, 0))
        self._consoleText = tk.Text(textFrame, bg=UI_PANEL, fg=UI_FG, insertbackground=UI_FG,
                                     font=("Consolas", 9), wrap="word")
        scroll = ttk.Scrollbar(textFrame, command=self._consoleText.yview)
        self._consoleText.configure(yscrollcommand=scroll.set)
        self._consoleText.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

    # -- Requests -------------------------------------------------------
    def _buildRequests(self, parent):
        frame = ttk.Frame(parent, padding=10)
        frame.pack(fill="both", expand=True)

        paned = ttk.PanedWindow(frame, orient="vertical")
        paned.pack(fill="both", expand=True)

        listFrame = ttk.Frame(paned)
        cols = ("time", "method", "path", "player", "status")
        headers = [t("col_time"), t("col_method"), t("col_path"), t("col_player"), t("col_status")]
        self._requestsTree = ttk.Treeview(listFrame, columns=cols, show="headings", height=14)
        for c, h, w in zip(cols, headers, (70, 60, 320, 160, 60)):
            self._requestsTree.heading(c, text=h)
            self._requestsTree.column(c, width=w, anchor="w")
        self._requestsTree.pack(fill="both", expand=True, side="left")
        vs = ttk.Scrollbar(listFrame, command=self._requestsTree.yview)
        self._requestsTree.configure(yscrollcommand=vs.set)
        vs.pack(side="right", fill="y")
        self._requestsTree.bind("<<TreeviewSelect>>", self._onRequestSelected)
        paned.add(listFrame, weight=2)

        detailFrame = ttk.Frame(paned)
        ttk.Label(detailFrame, text=t("request_body_label")).pack(anchor="w")
        self._reqBodyText = tk.Text(detailFrame, height=8, font=("Consolas", 9), wrap="word",
                                     bg=UI_INPUT, fg=UI_FG, insertbackground=UI_FG)
        self._reqBodyText.pack(fill="both", expand=True)
        ttk.Label(detailFrame, text=t("response_label")).pack(anchor="w", pady=(6, 0))
        self._reqRespText = tk.Text(detailFrame, height=8, font=("Consolas", 9), wrap="word",
                                     bg=UI_INPUT, fg=UI_FG, insertbackground=UI_FG)
        self._reqRespText.pack(fill="both", expand=True)
        paned.add(detailFrame, weight=3)

        self._requestRows = {}
        self._lastRequestId = 0
        self._refreshRequests()

    def _refreshRequests(self):
        log = getRequestLog()
        for entry in log:
            if entry["id"] <= self._lastRequestId:
                continue
            self._lastRequestId = entry["id"]
            iid = str(entry["id"])
            self._requestRows[iid] = entry
            self._requestsTree.insert("", "end", iid=iid, values=(
                entry["time"], entry["method"], entry["path"], entry["playerId"], entry["status"]))
        # Cap the displayed list the same way the deque is capped server-side.
        children = self._requestsTree.get_children()
        if len(children) > 500:
            for iid in children[: len(children) - 500]:
                self._requestsTree.delete(iid)
                self._requestRows.pop(iid, None)
        if children:
            self._requestsTree.see(children[-1])

    def _onRequestSelected(self, _event):
        sel = self._requestsTree.selection()
        if not sel:
            return
        entry = self._requestRows.get(sel[0])
        if not entry:
            return
        self._reqBodyText.delete("1.0", "end")
        self._reqBodyText.insert("1.0", entry["body"] or t("empty_placeholder"))
        self._reqRespText.delete("1.0", "end")
        self._reqRespText.insert("1.0", entry["response"] or t("empty_placeholder"))

    # -- generic table + form panel ---------------------------
    def _buildTablePanel(self, parent, title, columns, colWidths, loadRows, onSelect, extraToolbar=None,
                          headers=None, pollKey=None):
        """Builds {tree, formFrame}; onSelect(values) fills the form. If pollKey is
        given, this panel is registered for live auto-refresh: _pollLivePanel() calls
        loadRows() once a second while this tab is open and rebuilds the tree only
        when the rows actually changed, so every list-based tab (players, levels,
        teams, ghosts, news, gifs, ...) stays live without needing to leave and
        come back to the tab - same idea as the Requests tab already had."""
        frame = ttk.Frame(parent, padding=10)
        frame.pack(fill="both", expand=True)
        ttk.Label(frame, text=title, font=("Segoe UI", 13, "bold")).pack(anchor="w")

        toolbar = ttk.Frame(frame)
        toolbar.pack(fill="x", pady=(6, 6))
        refreshBtn = ttk.Button(toolbar, text=t("btn_refresh"))
        refreshBtn.pack(side="left")
        if extraToolbar:
            extraToolbar(toolbar)

        tree = ttk.Treeview(frame, columns=columns, show="headings", height=12)
        headers = headers or columns
        for c, h, w in zip(columns, headers, colWidths):
            tree.heading(c, text=h)
            tree.column(c, width=w, anchor="w")
        tree.pack(fill="both", expand=True)
        vs = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vs.set)

        def refresh(rows=None):
            if rows is None:
                rows = loadRows()
            tree.delete(*tree.get_children())
            for row in rows:
                tree.insert("", "end", values=row)
        refreshBtn.configure(command=refresh)
        initialRows = loadRows()
        refresh(initialRows)

        formFrame = ttk.LabelFrame(frame, text=t("details_frame"), padding=10)
        formFrame.pack(fill="x", pady=(10, 0))

        def _onSelect(_event):
            sel = tree.selection()
            if not sel:
                return
            onSelect(tree.item(sel[0], "values"))
        tree.bind("<<TreeviewSelect>>", _onSelect)

        if pollKey:
            self._livePanels[pollKey] = (tree, loadRows, refresh)
            self._lastPanelRows[pollKey] = initialRows

        return tree, formFrame, refresh

    def _pollLivePanel(self, pageKey):
        panel = self._livePanels.get(pageKey)
        if not panel:
            return
        tree, loadRows, refresh = panel
        try:
            newRows = loadRows()
        except Exception:
            return
        if newRows == self._lastPanelRows.get(pageKey):
            return
        self._lastPanelRows[pageKey] = newRows
        sel = tree.selection()
        selectedId = tree.item(sel[0], "values")[0] if sel else None
        refresh(newRows)
        if selectedId is not None:
            for iid in tree.get_children():
                if tree.item(iid, "values")[0] == selectedId:
                    tree.selection_set(iid)
                    tree.see(iid)
                    break

    def _syncLivePanelCache(self, pageKey):
        """Call after code outside _pollLivePanel already refreshed a live panel
        (e.g. right after a manual save/delete) so the next poll tick doesn't see a
        stale cached snapshot and redundantly rebuild the tree a second time."""
        panel = self._livePanels.get(pageKey)
        if panel:
            _tree, loadRows, _refresh = panel
            self._lastPanelRows[pageKey] = loadRows()

    # -- Players ----------------------------------------------------------
    def _buildPlayers(self, parent):
        columns = ("id", "name", "tag", "teamId", "coins", "diamonds", "mcTrophies", "carTrophies", "countryCode")
        headers = [t("id_word"), t("name"), t("tag"), t("col_teamid"), t("coins"), t("diamonds"),
                   t("col_mctrophies"), t("col_cartrophies"), t("country")]

        def loadRows():
            conn = getDbConnection()
            c = conn.cursor()
            c.execute("SELECT id,name,tag,teamId,coins,diamonds,mcTrophies,carTrophies,countryCode "
                      "FROM players ORDER BY createdAt DESC")
            rows = [tuple(r) for r in c.fetchall()]
            conn.close()
            return rows

        tree, form, refresh = self._buildTablePanel(
            parent, t("nav_players"), columns, (200, 120, 70, 140, 100, 100, 90, 90, 80), loadRows,
            self._onPlayerSelected, headers=headers, pollKey="players")
        self._playersTree, self._playersRefresh = tree, refresh

        self._playerId = None
        self._pName = labeledEntry(form, t("name"), 0, 0)
        self._pTag = labeledEntry(form, t("tag"), 0, 1)
        self._pTeamId = labeledEntry(form, t("col_teamid"), 0, 2)
        self._pCoins = labeledEntry(form, t("coins"), 1, 0)
        self._pDiamonds = labeledEntry(form, t("diamonds"), 1, 1)
        self._pCountry = labeledCountryButton(form, t("country"), 1, 2)
        self._pMcTrophies = labeledEntry(form, t("col_mctrophies"), 2, 0)
        self._pCarTrophies = labeledEntry(form, t("col_cartrophies"), 2, 1)

        btns = ttk.Frame(form)
        btns.grid(row=3, column=0, columnspan=6, sticky="w", pady=(8, 0))
        ttk.Button(btns, text=t("save"), command=self._savePlayer).pack(side="left", padx=(8, 4))
        ttk.Button(btns, text=t("delete"), command=self._deletePlayer).pack(side="left")
        ttk.Button(btns, text=t("btn_link_facebook"), width=22, command=self._linkFacebookFake).pack(side="left", padx=(4, 0))
        ttk.Button(btns, text=t("btn_unlink_facebook"), width=22, command=self._unlinkFacebook).pack(side="left", padx=(4, 0))
        ttk.Button(btns, text=t("more"), command=self._moreOnPlayer).pack(side="left", padx=(4, 0))

    def _onPlayerSelected(self, values):
        self._playerId = values[0]
        self._pName.set(values[1]); self._pTag.set(values[2]); self._pTeamId.set(values[3])
        self._pCoins.set(values[4]); self._pDiamonds.set(values[5])
        self._pMcTrophies.set(values[6]); self._pCarTrophies.set(values[7]); self._pCountry.set(values[8])

    def _savePlayer(self):
        if not self._playerId:
            showInfoDark(t("nav_players"), t("msg_select_player_first"))
            return
        conn = getDbConnection()
        c = conn.cursor()
        try:
            c.execute("""UPDATE players SET name=?, tag=?, teamId=?, coins=?, diamonds=?,
                         mcTrophies=?, carTrophies=?, countryCode=? WHERE id=?""",
                      (self._pName.get(), self._pTag.get(), self._pTeamId.get(),
                       int(self._pCoins.get() or 0), int(self._pDiamonds.get() or 0),
                       int(self._pMcTrophies.get() or 0), int(self._pCarTrophies.get() or 0),
                       self._pCountry.get() or "US", self._playerId))
            conn.commit()
        except (ValueError, sqlite3.Error) as e:
            showErrorDark(t("nav_players"), t("error_fmt").format(e))
        finally:
            conn.close()
        self._playersRefresh()

    def _deletePlayer(self):
        if not self._playerId:
            return
        if not confirmDelete(self, f"{t('word_player')} {self._pName.get()!r}"):
            return
        conn = getDbConnection()
        conn.cursor().execute("DELETE FROM players WHERE id=?", (self._playerId,))
        conn.commit(); conn.close()
        self._playerId = None
        self._playersRefresh()

    def _moreOnPlayer(self):
        if not self._playerId:
            showInfoDark(t("nav_players"), t("msg_select_player_first"))
            return
        openFullRowEditor(self, "players", "id", self._playerId, onSaved=self._playersRefresh)

    def _linkFacebookFake(self):
        # PsUIProfileImage.LoadPicture only attempts a picture at all when facebookId
        # is non-empty (PlayerPrefsX.GetFacebookId(), synced from this column at
        # login - Server/LoginFlow.cs) - it then requests the real, unmodified
        # https://graph.facebook.com/<id>/picture URL. A REAL Facebook id/username only
        # works there for public Pages - Facebook has since locked down the same
        # endpoint for ordinary personal profiles, so a real player's own account
        # can't be used this way anymore. Instead: graph.facebook.com is DNS-redirected
        # to this server (TARGET_HOSTS/handleDns) and its own TLS cert now covers that
        # hostname too, so we can just serve whatever image is uploaded here directly -
        # facebookId is set to this player's own id (guaranteed unique, never a real
        # Facebook identifier) purely as the lookup key _serveProfilePicture uses.
        if not self._playerId:
            showInfoDark(t("nav_players"), t("msg_select_player_first"))
            return
        if not certCoversHost("graph.facebook.com"):
            confirmed = askYesNoDark(t("cert_update_needed_title"), t("cert_update_needed_msg"), parent=self)
            if not confirmed:
                return
            waitDlg = showWaitingDark(t("cert_update_wait_title"), t("cert_update_wait_msg"), parent=self)
            try:
                ok, msgKey, detail = regenerateHttpsCertificate()
            finally:
                waitDlg.destroy()
            if not ok:
                reason = t(msgKey).format(detail) if detail else t(msgKey)
                showErrorDark(t("nav_players"), t("cert_update_failed_msg").format(reason))
                return
            showInfoDark(t("nav_players"), t("cert_update_done_msg"))
        path = filedialog.askopenfilename(
            title=t("link_facebook_prompt_title"),
            filetypes=[("Images", "*.png *.jpg *.jpeg"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, "rb") as f:
                imageBytes = f.read()
        except OSError as e:
            showErrorDark(t("nav_players"), t("error_fmt").format(e))
            return
        conn = getDbConnection()
        conn.cursor().execute(
            "UPDATE players SET facebookId = ?, customProfilePicture = ? WHERE id = ?",
            (self._playerId, imageBytes, self._playerId))
        conn.commit(); conn.close()
        showInfoDark(t("nav_players"), t("link_facebook_done_msg"))
        self._playersRefresh()

    def _unlinkFacebook(self):
        if not self._playerId:
            showInfoDark(t("nav_players"), t("msg_select_player_first"))
            return
        conn = getDbConnection()
        conn.cursor().execute(
            "UPDATE players SET facebookId = '', customProfilePicture = NULL WHERE id = ?", (self._playerId,))
        conn.commit(); conn.close()
        self._playersRefresh()

    # -- Levels ----------------------------------------------------------
    def _buildLevels(self, parent):
        columns = ("id", "name", "creatorName", "gameMode", "state", "timesPlayed", "upThumbs", "downThumbs")
        headers = [t("id_word"), t("name"), t("col_creatorname"), t("game_mode"), t("state"),
                   t("col_timesplayed"), t("col_upthumbs"), t("col_downthumbs")]

        def loadRows():
            conn = getDbConnection()
            c = conn.cursor()
            c.execute("SELECT id,name,creatorName,gameMode,state,timesPlayed,upThumbs,downThumbs "
                      "FROM minigames ORDER BY createdAt DESC")
            rows = [tuple(r) for r in c.fetchall()]
            conn.close()
            return rows

        tree, form, refresh = self._buildTablePanel(
            parent, t("nav_levels"), columns, (200, 180, 140, 90, 80, 90, 80, 90), loadRows,
            self._onLevelSelected, headers=headers, pollKey="levels")
        self._levelsTree, self._levelsRefresh = tree, refresh

        self._levelId = None
        self._lName = labeledEntry(form, t("name"), 0, 0)
        self._lState = labeledEntry(form, t("lbl_state_hint"), 0, 1)
        self._lGameMode = labeledEntry(form, t("lbl_gamemode_hint"), 0, 2)
        self._lDifficulty = labeledEntry(form, t("difficulty"), 1, 0)
        self._lRewardCoins = labeledEntry(form, t("reward_coins"), 1, 1)
        self._lSizeInfo = ttk.Label(form, text="")
        self._lSizeInfo.grid(row=1, column=4, columnspan=2, sticky="w", padx=8)
        self._lDescription = labeledEntry(form, t("description"), 2, 0, width=60)

        btns = ttk.Frame(form)
        btns.grid(row=3, column=0, columnspan=6, sticky="w", pady=(8, 0))
        ttk.Button(btns, text=t("save"), command=self._saveLevel).pack(side="left", padx=(8, 4))
        ttk.Button(btns, text=t("delete"), command=self._deleteLevel).pack(side="left")
        ttk.Button(btns, text=t("btn_extract_level"), command=self._extractLevel).pack(side="left", padx=(4, 0))
        ttk.Button(btns, text=t("more"), command=self._moreOnLevel).pack(side="left", padx=(4, 0))

    def _onLevelSelected(self, values):
        self._levelId = values[0]
        self._lName.set(values[1]); self._lGameMode.set(values[3]); self._lState.set(values[4])
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT description, difficulty, rewardCoins, length(levelData) as ld, "
                  "length(screenshot) as sd, length(creatorGhost) as gd FROM minigames WHERE id=?", (self._levelId,))
        row = c.fetchone()
        conn.close()
        if row:
            self._lDescription.set(row["description"] or "")
            self._lDifficulty.set(row["difficulty"] or "")
            self._lRewardCoins.set(row["rewardCoins"] or 0)
            self._lSizeInfo.configure(text=t("level_size_info").format(
                formatBytes(row['ld'] or 0), formatBytes(row['sd'] or 0), formatBytes(row['gd'] or 0)))

    def _saveLevel(self):
        if not self._levelId:
            showInfoDark(t("nav_levels"), t("msg_select_level_first"))
            return
        conn = getDbConnection()
        c = conn.cursor()
        try:
            c.execute("""UPDATE minigames SET name=?, description=?, state=?, gameMode=?,
                         difficulty=?, rewardCoins=?, updatedAt=CURRENT_TIMESTAMP WHERE id=?""",
                      (self._lName.get(), self._lDescription.get(), self._lState.get() or "public",
                       self._lGameMode.get() or "Race", self._lDifficulty.get() or "New",
                       int(self._lRewardCoins.get() or 0), self._levelId))
            conn.commit()
        except (ValueError, sqlite3.Error) as e:
            showErrorDark(t("nav_levels"), t("error_fmt").format(e))
        finally:
            conn.close()
        self._levelsRefresh()

    def _deleteLevel(self):
        if not self._levelId:
            return
        if not confirmDelete(self, f"{t('word_level')} {self._lName.get()!r}"):
            return
        deleteMinigameSafely(self._levelId)
        self._levelId = None
        self._levelsRefresh()

    def _moreOnLevel(self):
        if not self._levelId:
            showInfoDark(t("nav_levels"), t("msg_select_level_first"))
            return
        openFullRowEditor(self, "minigames", "id", self._levelId, onSaved=self._levelsRefresh)

    def _extractLevel(self):
        """Exports the selected level as a zip in the same LevelData/<id>/{meta.json,
        level.bin,screenshot.bin,ghosts/creatorGhost.bin(+.header),ghosts/<scoreId>.bin
        (+.header)} layout _importSubfolderLevel expects, so the resulting zip is
        directly re-importable later (e.g. to share a level with someone else's copy
        of this server, or just as a backup) with every recorded ghost intact - not
        just the creator's. Every ghost file gets a real FILE_SIZES-style .header
        carrying the FULL metadata shape ClientTools.ParseGhostDatas actually reads
        (see _buildGhostMetaDict/_buildGhostHeaderedBlob) - an earlier version of this
        only wrote playerId/name/time, which is enough for _syncLevelGhostsFolder to
        re-import the ghost at all, but silently dropped every other field the client
        reads once that ghost is actually shown in-game (countryCode missing is why an
        exported ghost always showed the US flag, regardless of the real player's
        country - confirmed by a friend's side-by-side comparison against a real
        legacy-client ghost export, which carries all of these fields)."""
        if not self._levelId:
            showInfoDark(t("nav_levels"), t("msg_select_level_first"))
            return
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT * FROM minigames WHERE id=?", (self._levelId,))
        row = c.fetchone()
        if row is None:
            conn.close()
            return
        c.execute("""SELECT m.creatorId as playerId, m.creatorName as name, m.bestTime as time,
                     m.id as id, p.countryCode, p.facebookId, p.gameCenterId, p.teamId, p.teamName,
                     p.mcTrophies, p.carTrophies
                     FROM minigames m LEFT JOIN players p ON m.creatorId = p.id WHERE m.id=?""",
                  (self._levelId,))
        creatorRow = c.fetchone()
        c.execute("""SELECT s.id, s.playerId, s.playerName as name, s.time, s.ghostData,
                     p.countryCode, p.facebookId, p.gameCenterId, p.teamId, p.teamName,
                     p.mcTrophies, p.carTrophies
                     FROM scores s LEFT JOIN players p ON s.playerId = p.id WHERE s.gameId=?""",
                  (self._levelId,))
        scoreRows = c.fetchall()
        conn.close()
        playerUnit = safeStr(row["playerUnit"], "Any")

        downloadsDir = os.path.join(os.path.expanduser("~"), "Downloads")
        safeName = re.sub(r'[\\/:*?"<>|]', "_", row["name"] or self._levelId).strip() or self._levelId
        destPath = filedialog.asksaveasfilename(
            title=t("btn_extract_level"), defaultextension=".zip",
            initialdir=downloadsDir if os.path.isdir(downloadsDir) else None,
            initialfile=f"{safeName}.zip",
            filetypes=[("ZIP", "*.zip")])
        if not destPath:
            return

        meta = {k: row[k] for k in _VALID_MINIGAME_COLUMNS if row[k] is not None}
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.writestr(f"{self._levelId}/meta.json", json.dumps(meta, indent=2, ensure_ascii=False))
            if row["levelData"]:
                zf.writestr(f"{self._levelId}/level.bin", row["levelData"])
            if row["screenshot"]:
                zf.writestr(f"{self._levelId}/screenshot.bin", row["screenshot"])
            if row["creatorGhost"] and creatorRow is not None:
                ghostBlob, headerText = _buildGhostHeaderedBlob(
                    bytes(row["creatorGhost"]), creatorRow, playerUnit)
                zf.writestr(f"{self._levelId}/ghosts/creatorGhost.bin", ghostBlob)
                zf.writestr(f"{self._levelId}/ghosts/creatorGhost.header", headerText)
            for sRow in scoreRows:
                if not sRow["ghostData"]:
                    continue
                ghostBlob, headerText = _buildGhostHeaderedBlob(
                    bytes(sRow["ghostData"]), sRow, playerUnit)
                zf.writestr(f"{self._levelId}/ghosts/{sRow['id']}.bin", ghostBlob)
                zf.writestr(f"{self._levelId}/ghosts/{sRow['id']}.header", headerText)
        try:
            with open(destPath, "wb") as f:
                f.write(buf.getvalue())
            showInfoDark(t("nav_levels"), t("msg_gif_exported_fmt").format(destPath))
        except OSError as e:
            showErrorDark(t("nav_levels"), t("error_fmt").format(e))

    # -- Teams ----------------------------------------------------------
    def _buildTeams(self, parent):
        columns = ("id", "name", "tag", "ownerId", "members")
        headers = [t("id_word"), t("name"), t("tag"), t("col_ownerid"), t("col_members")]

        def loadRows():
            conn = getDbConnection()
            c = conn.cursor()
            c.execute("""SELECT t.id, t.name, t.tag, t.ownerId,
                         (SELECT COUNT(*) FROM players p WHERE p.teamId = t.id) as memberCount
                         FROM teams t ORDER BY t.createdAt DESC""")
            rows = [tuple(r) for r in c.fetchall()]
            conn.close()
            return rows

        tree, form, refresh = self._buildTablePanel(
            parent, t("nav_teams"), columns, (200, 180, 90, 200, 80), loadRows, self._onTeamSelected,
            headers=headers, pollKey="teams")
        self._teamsTree, self._teamsRefresh = tree, refresh

        self._teamId = None
        self._tName = labeledEntry(form, t("name"), 0, 0)
        self._tTag = labeledEntry(form, t("tag"), 0, 1)
        self._tCountry = labeledCountryButton(form, t("country"), 0, 2)
        self._tDescription = labeledEntry(form, t("description"), 1, 0, width=60)

        btns = ttk.Frame(form)
        btns.grid(row=2, column=0, columnspan=6, sticky="w", pady=(8, 0))
        ttk.Button(btns, text=t("save"), command=self._saveTeam).pack(side="left", padx=(8, 4))
        ttk.Button(btns, text=t("btn_delete_team"), command=self._deleteTeam).pack(side="left")
        ttk.Button(btns, text=t("more"), command=self._moreOnTeam).pack(side="left", padx=(4, 0))

    def _onTeamSelected(self, values):
        self._teamId = values[0]
        self._tName.set(values[1]); self._tTag.set(values[2])
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("SELECT description, countryCode FROM teams WHERE id=?", (self._teamId,))
        row = c.fetchone()
        conn.close()
        if row:
            self._tDescription.set(row["description"] or "")
            self._tCountry.set(row["countryCode"] or "US")

    def _saveTeam(self):
        if not self._teamId:
            showInfoDark(t("nav_teams"), t("msg_select_team_first"))
            return
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("UPDATE teams SET name=?, tag=?, description=?, countryCode=? WHERE id=?",
                  (self._tName.get(), self._tTag.get(), self._tDescription.get(),
                   self._tCountry.get() or "US", self._teamId))
        conn.commit(); conn.close()
        self._teamsRefresh()

    def _deleteTeam(self):
        if not self._teamId:
            return
        if not confirmDelete(self, f"{t('word_team')} {self._tName.get()!r}"):
            return
        conn = getDbConnection()
        c = conn.cursor()
        # Same behavior as /v1/team/kick server-side: a player without a team
        # must go back to teamRole='Member' (the only valid client-side default).
        c.execute("UPDATE players SET teamId='', teamName='', teamRole='Member' WHERE teamId=?", (self._teamId,))
        c.execute("DELETE FROM teams WHERE id=?", (self._teamId,))
        conn.commit(); conn.close()
        self._teamId = None
        self._teamsRefresh()

    def _moreOnTeam(self):
        if not self._teamId:
            showInfoDark(t("nav_teams"), t("msg_select_team_first"))
            return
        openFullRowEditor(self, "teams", "id", self._teamId, onSaved=self._teamsRefresh)

    # -- Ghosts (backed by the `scores` table) -----------------------------------
    def _buildGhosts(self, parent):
        columns = ("id", "gameId", "playerName", "playerUnit", "time (ms)", "ghost")
        headers = [t("id_word"), t("col_gameid"), t("col_playername"), t("col_playerunit"),
                   t("col_time_ms"), t("col_ghost")]

        def loadRows():
            conn = getDbConnection()
            c = conn.cursor()
            c.execute("SELECT id, gameId, playerName, playerUnit, time, length(ghostData) as gd "
                      "FROM scores ORDER BY createdAt DESC LIMIT 300")
            rows = [(r["id"], r["gameId"], r["playerName"], r["playerUnit"], r["time"], formatBytes(r["gd"] or 0))
                    for r in c.fetchall()]
            conn.close()
            return rows

        def toolbar(bar):
            ttk.Button(bar, text=t("btn_delete_selected"), command=self._deleteGhost).pack(side="left", padx=(6, 0))
            ttk.Button(bar, text=t("more"), command=self._moreOnGhost).pack(side="left", padx=(4, 0))

        self._ghostId = None
        tree, _form, refresh = self._buildTablePanel(
            parent, t("ghosts_heading"), columns, (200, 180, 140, 90, 90, 90),
            loadRows, self._onGhostSelected, extraToolbar=toolbar, headers=headers, pollKey="ghosts")
        self._ghostsTree, self._ghostsRefresh = tree, refresh

    def _onGhostSelected(self, values):
        self._ghostId = values[0]

    def _moreOnGhost(self):
        if not self._ghostId:
            showInfoDark(t("nav_ghosts"), t("msg_select_row_first_list"))
            return
        openFullRowEditor(self, "scores", "id", self._ghostId, onSaved=self._ghostsRefresh)

    def _deleteGhost(self):
        sel = self._ghostsTree.selection()
        if not sel:
            showInfoDark(t("nav_ghosts"), t("msg_select_row_first"))
            return
        scoreId = self._ghostsTree.item(sel[0], "values")[0]
        if not confirmDelete(self, t("word_ghost_run")):
            return
        conn = getDbConnection()
        conn.cursor().execute("DELETE FROM scores WHERE id=?", (scoreId,))
        conn.commit(); conn.close()
        self._ghostsRefresh()

    # -- Tournament ------------------------------------------------------------
    def _buildTournament(self, parent):
        frame = ttk.Frame(parent, padding=16)
        frame.pack(fill="both", expand=True)
        ttk.Label(frame, text=t("tournament_config_heading"), font=("Segoe UI", 13, "bold")).pack(anchor="w", pady=(0, 14))

        form = ttk.Frame(frame)
        form.pack(fill="x")

        # Levels are picked via a dialog (openLevelPicker) that queries `minigames`
        # fresh every time it's opened/searched, rather than a dropdown/list built once
        # when this tab loads - so a level created after this tab was opened still
        # shows up the next time the picker is opened, with no extra wiring needed.
        ttk.Label(form, text=t("lbl_tournament_level")).grid(row=0, column=0, sticky="ne", padx=(0, 6), pady=4)
        pickerFrame = ttk.Frame(form)
        pickerFrame.grid(row=0, column=1, columnspan=3, sticky="w", pady=4)

        self._tourSelectedLevelId = ""
        # The button's own label IS the current-selection indicator: it reads "Choose
        # Level" while nothing is picked, and the level's name once one is.
        self._tourLevelBtnText = tk.StringVar(value=t("btn_choose_level"))

        def onLevelPicked(lid, name):
            self._tourSelectedLevelId = lid
            self._tourLevelBtnText.set(name)

        ttk.Button(pickerFrame, textvariable=self._tourLevelBtnText,
                   command=lambda: openLevelPicker(self, onLevelPicked)).pack(anchor="w")
        ttk.Button(pickerFrame, text=t("btn_disable_tournament"),
                   command=self._clearTournamentLevel).pack(anchor="w", pady=(2, 0))

        self._tourTournamentId = labeledEntry(form, t("lbl_tournament_id"), 1, 0)
        self._tourPrizeCoins = labeledEntry(form, t("reward_coins"), 1, 1)
        self._tourCcCap = labeledEntry(form, t("lbl_cc_cap"), 2, 0)

        ttk.Label(form, text=t("col_playerunit")).grid(row=3, column=0, sticky="e", padx=(0, 6), pady=4)
        self._tourPlayerUnit = tk.StringVar()
        ttk.Combobox(form, textvariable=self._tourPlayerUnit, values=["Any", "OffroadCar", "Motorcycle"],
                     width=20, state="readonly").grid(row=3, column=1, sticky="w", pady=4)

        self._tourUseCreatorUpgrades = labeledCheckbox(form, t("lbl_use_creator_upgrades"), 3, 2)
        self._tourAcceptingScores = labeledCheckbox(form, t("lbl_accepting_scores"), 4, 0)
        self._tourFloatingNode = labeledCheckbox(form, t("lbl_floating_node"), 4, 1)

        self._tourHeader = labeledEntry(form, t("lbl_title_header"), 5, 0, width=50)
        self._tourMessage = labeledEntry(form, t("message"), 6, 0, width=50)

        ttk.Label(form, text=t("lbl_duration_unlimited")).grid(row=7, column=0, sticky="e", padx=(0, 6), pady=4)
        self._tourDurationDays = tk.StringVar()
        ttk.Entry(form, textvariable=self._tourDurationDays, width=10).grid(row=7, column=1, sticky="w", pady=4)

        tourBtns = ttk.Frame(frame)
        tourBtns.pack(anchor="w", pady=(14, 0))
        ttk.Button(tourBtns, text=t("save"), command=self._saveTournament).pack(side="left")
        ttk.Button(tourBtns, text=t("more"), command=self._moreOnTournament).pack(side="left", padx=(6, 0))
        self._tourStatusLabel = ttk.Label(frame, text="", foreground=UI_FG)
        self._tourStatusLabel.pack(anchor="w", pady=(6, 0))

        self._loadTournamentForm()

    def _moreOnTournament(self):
        openFullRowEditor(self, "tournamentConfig", "id", 1, onSaved=self._loadTournamentForm)

    def _clearTournamentLevel(self):
        self._tourSelectedLevelId = ""
        self._tourLevelBtnText.set(t("btn_choose_level"))

    def _loadTournamentForm(self):
        cfg = getTournamentConfig()
        currentId = cfg.get("minigameId") or ""
        self._tourSelectedLevelId = currentId
        if currentId:
            row = getMinigameRow(currentId)
            currentName = row["name"] if row is not None else t("tour_level_not_found")
            self._tourLevelBtnText.set(currentName)
        else:
            self._tourLevelBtnText.set(t("btn_choose_level"))
        self._tourTournamentId.set(cfg.get("tournamentId") or "tour_main")
        self._tourPrizeCoins.set(cfg.get("prizeCoins") or 500)
        self._tourCcCap.set(cfg.get("ccCap") if cfg.get("ccCap") is not None else -1.0)
        self._tourPlayerUnit.set(cfg.get("playerUnit") or "Any")
        self._tourUseCreatorUpgrades.set(bool(cfg.get("useCreatorUpgrades")))
        self._tourAcceptingScores.set(bool(cfg.get("acceptingNewScores", 1)))
        self._tourFloatingNode.set(bool(cfg.get("floatingNode", 0)))
        self._tourHeader.set(cfg.get("header") or "")
        self._tourMessage.set(cfg.get("message") or "")
        endTime = cfg.get("endTime") or 0
        startTime = cfg.get("startTime") or 0
        if endTime and endTime > startTime:
            days = max(0, round((endTime - (startTime or nowMs())) / 86400000))
            self._tourDurationDays.set(days)
        else:
            self._tourDurationDays.set(0)

    def _saveTournament(self):
        minigameId = self._tourSelectedLevelId
        try:
            prizeCoins = int(self._tourPrizeCoins.get() or 0)
            ccCap = float(self._tourCcCap.get() or -1.0)
            days = int(self._tourDurationDays.get() or 0)
        except ValueError as e:
            showErrorDark(t("nav_tournament"), t("msg_invalid_numeric_fmt").format(e))
            return
        start = nowMs()
        end = start + days * 86400000 if days > 0 else 0
        setTournamentConfig({
            "minigameId": minigameId,
            "tournamentId": self._tourTournamentId.get() or "tour_main",
            "header": self._tourHeader.get(), "message": self._tourMessage.get(),
            "prizeCoins": prizeCoins, "ccCap": ccCap,
            "playerUnit": self._tourPlayerUnit.get() or "Any",
            "useCreatorUpgrades": 1 if self._tourUseCreatorUpgrades.get() else 0,
            "acceptingNewScores": 1 if self._tourAcceptingScores.get() else 0,
            "floatingNode": 1 if self._tourFloatingNode.get() else 0,
            "startTime": start if minigameId else 0,
            "endTime": end if minigameId else 0,
        })
        self._tourStatusLabel.configure(text=t("tour_saved_at_fmt").format(datetime.now().strftime('%H:%M:%S')))

    # -- News Feed ------------------------------------------------------------
    def _buildNews(self, parent):
        columns = ("id", "eventName", "eventType", "header", "active_until")
        headers = [t("id_word"), t("col_eventname"), t("col_eventtype"), t("col_headercol"),
                   t("col_active_until")]

        def loadRows():
            conn = getDbConnection()
            c = conn.cursor()
            c.execute("SELECT id, eventName, eventType, header, endTime FROM events ORDER BY id DESC")
            rows = []
            for r in c.fetchall():
                until = datetime.fromtimestamp(r["endTime"] / 1000, tz=timezone.utc).strftime("%Y-%m-%d") if r["endTime"] else t("val_unlimited")
                rows.append((r["id"], r["eventName"], r["eventType"], r["header"], until))
            conn.close()
            return rows

        def toolbar(bar):
            ttk.Button(bar, text=t("btn_delete_selected"), command=self._deleteEvent).pack(side="left", padx=(6, 0))
            ttk.Button(bar, text=t("more"), command=self._moreOnEvent).pack(side="left", padx=(4, 0))

        self._newsId = None
        tree, _form, refresh = self._buildTablePanel(
            parent, t("nav_news"), columns, (60, 160, 110, 260, 100), loadRows, self._onNewsSelected,
            extraToolbar=toolbar, headers=headers, pollKey="news")
        self._newsTree, self._newsRefresh = tree, refresh

        addFrame = ttk.LabelFrame(parent, text=t("add_event_frame"), padding=10)
        addFrame.pack(fill="x", padx=10, pady=(0, 10))
        # "Title"/"Message" are the only two fields actually shown to the player
        # in-game (PsUINewsBanner renders _msg.header as the banner text, and the
        # popup opened by tapping it shows _msg.message) - "Name" is purely an
        # internal/metrics label (PsMetrics.NewsOpened(...)) that never appears on
        # screen. Labeled explicitly below since leaving Title blank (easy to do if
        # "Name" reads as the title, like it does on every other tab) silently
        # blocks the save entirely (see the guard in _addEvent).
        self._evHeader = labeledEntry(addFrame, t("lbl_title_ingame"), 0, 0, width=40)
        self._evMessage = labeledEntry(addFrame, t("lbl_message_ingame"), 1, 0, width=40)
        ttk.Label(addFrame, text=t("type_word")).grid(row=0, column=2, sticky="e", padx=(8, 2))
        self._evType = tk.StringVar(value="Event")
        evTypeCombo = ttk.Combobox(addFrame, textvariable=self._evType,
                     values=["Event", "Announcement", "CreatorChallenge", "Gift", "LiveOps"],
                     width=18, state="readonly")
        evTypeCombo.grid(row=0, column=3, sticky="w")
        self._evLabel = labeledEntry(addFrame, t("lbl_label_button"), 1, 1, width=20)
        self._evName = labeledEntry(addFrame, t("lbl_internal_name"), 2, 0, width=40)
        self._evDurationDays = labeledEntry(addFrame, t("lbl_duration_short"), 2, 1, width=8)
        self._evPopup = labeledCheckbox(addFrame, t("lbl_popup_login"), 3, 0)
        self._evNewsFeed = labeledCheckbox(addFrame, t("lbl_visible_newsfeed"), 3, 1)
        self._evNewsFeed.set(True)
        self._evFloatingNode = labeledCheckbox(addFrame, t("lbl_floating_node"), 3, 2)

        # Only meaningful when Type == "Gift" (ClientTools.ParseEventGiftComponent), and
        # only persisted/used by the server in that case too - hidden otherwise so the
        # form doesn't show fields that don't apply to the selected event type.
        giftFrame = ttk.LabelFrame(addFrame, text=t("gift_details_frame"), padding=8)
        giftFrame.grid(row=4, column=0, columnspan=4, sticky="we", pady=(8, 0))
        ttk.Label(giftFrame, text=t("lbl_gift_type")).grid(row=0, column=0, sticky="e", padx=(0, 4))
        self._evGiftType = tk.StringVar(value="resource")
        giftTypeCombo = ttk.Combobox(giftFrame, textvariable=self._evGiftType,
                                      values=["resource", "upgradeItem", "chest", "hat", "trail",
                                              "timed", "editorItem"],
                                      width=14, state="readonly")
        giftTypeCombo.grid(row=0, column=1, sticky="w")
        ttk.Label(giftFrame, text=t("lbl_identifier")).grid(row=0, column=2, sticky="e", padx=(12, 4))
        self._evGiftIdentifier = tk.StringVar()
        self._evGiftIdentifierCombo = ttk.Combobox(giftFrame, textvariable=self._evGiftIdentifier, width=22)
        self._evGiftIdentifierCombo.grid(row=0, column=3, sticky="w")
        ttk.Label(giftFrame, text=t("lbl_amount")).grid(row=1, column=0, sticky="e", padx=(0, 4), pady=(4, 0))
        self._evGiftAmount = tk.StringVar()
        ttk.Entry(giftFrame, textvariable=self._evGiftAmount, width=10).grid(row=1, column=1, sticky="w", pady=(4, 0))
        ttk.Label(giftFrame, text=t("lbl_texture_optional")).grid(row=1, column=2, sticky="e", padx=(12, 4), pady=(4, 0))
        self._evGiftTexture = tk.StringVar()
        ttk.Entry(giftFrame, textvariable=self._evGiftTexture, width=10).grid(row=1, column=3, sticky="w", pady=(4, 0))

        def onGiftTypeChanged(_event=None):
            self._evGiftIdentifierCombo.configure(values=_GIFT_IDENTIFIER_CHOICES.get(self._evGiftType.get(), []))
        giftTypeCombo.bind("<<ComboboxSelected>>", onGiftTypeChanged)
        onGiftTypeChanged()

        def onEventTypeChanged(_event=None):
            if self._evType.get() == "Gift":
                giftFrame.grid()
            else:
                giftFrame.grid_remove()
        evTypeCombo.bind("<<ComboboxSelected>>", onEventTypeChanged)
        onEventTypeChanged()

        ttk.Button(addFrame, text=t("add"), command=self._addEvent).grid(row=5, column=0, sticky="w", pady=(8, 0))

    def _addEvent(self):
        if not self._evHeader.get().strip():
            showInfoDark(t("nav_news"), t("msg_title_required"))
            return
        try:
            days = int(self._evDurationDays.get() or 0)
        except ValueError:
            showErrorDark(t("nav_news"), t("msg_invalid_duration"))
            return
        try:
            giftAmount = int(self._evGiftAmount.get() or 0)
            giftTexture = int(self._evGiftTexture.get()) if self._evGiftTexture.get().strip() else -1
        except ValueError:
            showErrorDark(t("nav_news"), t("msg_invalid_gift_numbers"))
            return
        start = nowMs()
        end = start + days * 86400000 if days > 0 else 0
        conn = getDbConnection()
        c = conn.cursor()
        c.execute("""INSERT INTO events (eventName, eventType, header, message, label, popup, newsFeed,
                     startTime, endTime, floatingNode, giftType, giftIdentifier, giftAmount, giftTexture)
                     VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                  (self._evName.get() or self._evHeader.get(), self._evType.get(),
                   self._evHeader.get(), self._evMessage.get(), self._evLabel.get(),
                   1 if self._evPopup.get() else 0, 1 if self._evNewsFeed.get() else 0, start, end,
                   1 if self._evFloatingNode.get() else 0,
                   self._evGiftType.get(), self._evGiftIdentifier.get(), giftAmount, giftTexture))
        conn.commit(); conn.close()
        self._evName.set(""); self._evHeader.set(""); self._evMessage.set(""); self._evLabel.set("")
        self._evDurationDays.set(""); self._evGiftIdentifier.set(""); self._evGiftAmount.set("")
        self._evGiftTexture.set("")
        self._newsRefresh()

    def _deleteEvent(self):
        sel = self._newsTree.selection()
        if not sel:
            showInfoDark(t("nav_news"), t("msg_select_row_first"))
            return
        eventId = self._newsTree.item(sel[0], "values")[0]
        if not confirmDelete(self, t("word_event")):
            return
        conn = getDbConnection()
        conn.cursor().execute("DELETE FROM events WHERE id=?", (eventId,))
        conn.commit(); conn.close()
        self._newsRefresh()

    def _onNewsSelected(self, values):
        self._newsId = values[0]

    def _moreOnEvent(self):
        if not self._newsId:
            showInfoDark(t("nav_news"), t("msg_select_row_first_list"))
            return
        openFullRowEditor(self, "events", "id", self._newsId, onSaved=self._newsRefresh)

    # -- Gifs ---------------------------------------------------------------
    def _buildGifs(self, parent):
        columns = ("id", "size", "created")
        headers = [t("id_word"), t("col_size"), t("col_created")]

        def loadRows():
            if not os.path.isdir(GIFS_DIR):
                return []
            rows = []
            for filename in os.listdir(GIFS_DIR):
                if not filename.endswith(".gif"):
                    continue
                fullPath = os.path.join(GIFS_DIR, filename)
                try:
                    st = os.stat(fullPath)
                except OSError:
                    continue
                rows.append((filename[:-4], st.st_mtime, formatBytes(st.st_size),
                             datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M:%S")))
            rows.sort(key=lambda r: r[1], reverse=True)
            return [(r[0], r[2], r[3]) for r in rows]

        tree, form, refresh = self._buildTablePanel(
            parent, t("nav_gifs"), columns, (240, 90, 160), loadRows, self._onGifSelected, headers=headers,
            pollKey="gifs")
        self._gifsTree, self._gifsRefresh = tree, refresh
        self._gifId = None

        self._gifPreviewLabel = ttk.Label(form)
        self._gifPreviewLabel.grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 8))
        self._gifPreviewImage = None
        self._gifAnimFrames = None
        self._gifAnimJob = None

        btns = ttk.Frame(form)
        btns.grid(row=1, column=0, columnspan=4, sticky="w")
        ttk.Button(btns, text=t("btn_export_gif"), command=self._exportGif).pack(side="left", padx=(0, 6))
        ttk.Button(btns, text=t("btn_delete_selected"), command=self._deleteGif).pack(side="left")

    def _gifPath(self, gifId):
        return os.path.join(GIFS_DIR, gifId + ".gif")

    def _stopGifAnimation(self):
        if self._gifAnimJob is not None:
            try:
                self._gifPreviewLabel.after_cancel(self._gifAnimJob)
            except Exception:
                pass
            self._gifAnimJob = None
        self._gifAnimFrames = None

    def _onGifSelected(self, values):
        self._stopGifAnimation()
        self._gifId = values[0]
        path = self._gifPath(self._gifId)

        if _PIL_AVAILABLE:
            try:
                frames = []
                im = _PILImage.open(path)
                for frameIndex in range(im.n_frames):
                    im.seek(frameIndex)
                    duration = max(int(im.info.get("duration", 100)), 20)
                    frames.append((_PILImageTk.PhotoImage(im.convert("RGBA")), duration))
                if frames:
                    self._gifAnimFrames = frames
                    self._gifPreviewLabel.configure(text="")
                    self._runGifAnimation(self._gifId, 0)
                    return
            except Exception:
                pass

        try:
            self._gifPreviewImage = tk.PhotoImage(file=path)
            self._gifPreviewLabel.configure(image=self._gifPreviewImage, text="")
        except Exception:
            # tk.PhotoImage only ever decodes the first frame, and can fail outright
            # on some GIF variants - a broken/unsupported preview shouldn't block
            # exporting or deleting the file itself.
            self._gifPreviewImage = None
            self._gifPreviewLabel.configure(image="", text=t("gif_preview_unavailable"))

    def _runGifAnimation(self, gifId, frameIndex):
        # Guard against the tab having been switched (self.content destroyed) or a
        # different gif being selected since this loop was scheduled.
        if self._gifAnimFrames is None or self._gifId != gifId:
            return
        if not self._gifPreviewLabel.winfo_exists():
            self._gifAnimJob = None
            return
        image, duration = self._gifAnimFrames[frameIndex % len(self._gifAnimFrames)]
        self._gifPreviewImage = image
        self._gifPreviewLabel.configure(image=image)
        nextIndex = (frameIndex + 1) % len(self._gifAnimFrames)
        self._gifAnimJob = self._gifPreviewLabel.after(duration, lambda: self._runGifAnimation(gifId, nextIndex))

    def _exportGif(self):
        if not self._gifId:
            showInfoDark(t("nav_gifs"), t("msg_select_row_first"))
            return
        srcPath = self._gifPath(self._gifId)
        if not os.path.isfile(srcPath):
            showErrorDark(t("nav_gifs"), t("msg_gif_missing"))
            return
        destPath = filedialog.asksaveasfilename(
            title=t("btn_export_gif"), defaultextension=".gif",
            initialfile=f"{self._gifId}.gif",
            filetypes=[("GIF", "*.gif")])
        if not destPath:
            return
        try:
            with open(srcPath, "rb") as src, open(destPath, "wb") as dst:
                dst.write(src.read())
            showInfoDark(t("nav_gifs"), t("msg_gif_exported_fmt").format(destPath))
        except OSError as e:
            showErrorDark(t("nav_gifs"), t("error_fmt").format(e))

    def _deleteGif(self):
        if not self._gifId:
            showInfoDark(t("nav_gifs"), t("msg_select_row_first"))
            return
        if not confirmDelete(self, f"{t('word_gif')} {self._gifId!r}"):
            return
        try:
            os.remove(self._gifPath(self._gifId))
        except OSError:
            pass
        self._stopGifAnimation()
        self._gifId = None
        self._gifPreviewImage = None
        self._gifPreviewLabel.configure(image="", text="")
        self._gifsRefresh()
        self._syncLivePanelCache("gifs")


if __name__ == "__main__":
    app = AdminApp()
    app.mainloop()