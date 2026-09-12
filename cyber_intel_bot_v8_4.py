#!/usr/bin/env python3
"""
Cyber Intel + CTF Discord Bot

Features
--------
- Flexible RSS/Atom ingestion:
  built-in security feeds plus category-specific custom feeds (including RSS.app)
  for news, research, India, exploit intelligence, breaches and CTF registration
- Indian cyber alerts:
  CERT-In vulnerability notes/advisories + India-focused Google News RSS
- Official exploitation intelligence:
  CISA Known Exploited Vulnerabilities (KEV), with official GitHub fallback
- PoC monitoring:
  NomiSec PoC-in-GitHub + Trickest CVE Atom feeds
- CVE enrichment:
  CISA KEV, FIRST EPSS, optional NVD CVSS
- Social breach monitoring:
  Optional X API v2 recent-search collector
- CTF registration discovery:
  only future events or current registration-open opportunities; stale/running/closed
  CTF coverage is rejected
- High-signal trust/relevance scoring to suppress fluff and baseless discovery news
- Two-stage AUTO / REVIEW / DROP publication policy for breaking intelligence
- Persistent four-button topic moderation: Publish Now / Publish Later / Drop Publish / Drop Thread
- Per-feed traversal telemetry with visit/fetch counters, newest-item traces and cycle summaries
- Fast RSS mode with conditional-safe per-feed timeout/backoff and trusted-source soft-signal handling
- Separate manual-review dedupe so early weak leads never block later trusted reports
- Persistent SQLite exact + cross-source historical deduplication
- First-run anti-spam
- Separate Discord channel routing
- Common followable Discord Announcement hub (#cyber-alert)
- Persistent, rate-aware crosspost queue for Announcement followers
- Final queue intelligence gate: re-check importance/staleness before public crosspost
- Queue-level incident conflict resolution: merge duplicates, prefer stronger/official sources
- Bot-status dashboard with uptime, collector health, error/recovery alerts and queue metrics

Use only public information and authorized platform APIs.
"""

from __future__ import annotations

import asyncio
import calendar
import hashlib
import html
import math
import json
import logging
import os
import re
import sqlite3
import time
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timezone
from difflib import SequenceMatcher
from typing import Any, Iterable
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit

import aiohttp
import discord
import feedparser
from bs4 import BeautifulSoup
from discord.ext import tasks
from dotenv import load_dotenv


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

load_dotenv()

LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()
logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(message)s",
)
log = logging.getLogger("cyber-intel-bot")


def env_int(name: str, default: int = 0) -> int:
    value = os.getenv(name, "").strip()
    if not value:
        return default
    try:
        return int(value)
    except ValueError:
        raise RuntimeError(f"{name} must be a Discord numeric ID, got: {value!r}")


def env_bool(name: str, default: bool = False) -> bool:
    value = os.getenv(name)
    if value is None:
        return default
    return value.strip().lower() in {"1", "true", "yes", "on"}


def env_id_set(name: str) -> set[int]:
    """Parse comma/space/newline separated Discord IDs from .env."""
    raw = os.getenv(name, "").strip()
    if not raw:
        return set()
    out: set[int] = set()
    for token in re.split(r"[\s,]+", raw):
        token = token.strip()
        if not token:
            continue
        if not token.isdigit():
            raise RuntimeError(f"{name} must contain numeric Discord IDs only, got: {token!r}")
        out.add(int(token))
    return out


def env_feed_list(name: str, default_label: str) -> list[tuple[str, str]]:
    """Parse comma-separated feed URLs from .env.

    Each item may optionally use ``Label|https://...``. The label is useful for
    a single-publisher RSS.app feed because it lets the trust scorer retain the
    real publisher name even when the feed itself is hosted by RSS.app.
    """
    raw = os.getenv(name, "").strip()
    if not raw:
        return []

    feeds: list[tuple[str, str]] = []
    for token in re.split(r"[\n,]+", raw):
        token = token.strip()
        if not token:
            continue
        label = f"{default_label} {len(feeds) + 1}"
        url = token
        if "|" in token:
            possible_label, possible_url = token.split("|", 1)
            if possible_url.strip().startswith(("http://", "https://")):
                label = possible_label.strip() or label
                url = possible_url.strip()
        if not url.startswith(("http://", "https://")):
            log.warning("Ignoring invalid feed in %s: %r", name, token)
            continue
        feeds.append((label, url))
    return feeds


TOKEN = os.getenv("DISCORD_TOKEN", "").strip()
if not TOKEN:
    raise RuntimeError("DISCORD_TOKEN is missing. Put it in your .env file.")

CHANNEL_NEWS = env_int("CHANNEL_NEWS")
if not CHANNEL_NEWS:
    raise RuntimeError("CHANNEL_NEWS is required. Put its channel ID in .env.")

# Optional specialized channels. If omitted, the bot falls back to CHANNEL_NEWS.
CHANNEL_CRITICAL = env_int("CHANNEL_CRITICAL", CHANNEL_NEWS)
CHANNEL_INDIA = env_int("CHANNEL_INDIA", CHANNEL_NEWS)
CHANNEL_RESEARCH = env_int("CHANNEL_RESEARCH", CHANNEL_NEWS)
CHANNEL_POC = env_int("CHANNEL_POC", CHANNEL_NEWS)
CHANNEL_BREACH = env_int("CHANNEL_BREACH", CHANNEL_NEWS)
CHANNEL_CTF = env_int("CHANNEL_CTF", CHANNEL_NEWS)
CHANNEL_BOT_STATUS = env_int("CHANNEL_BOT_STATUS", 0)

# Public Announcement-channel hub. Every categorized alert is mirrored here,
# then queued for Discord crossposting so other servers can Follow it.
CHANNEL_CYBER_ALERT = env_int("CHANNEL_CYBER_ALERT", 0)
AUTO_PUBLISH_CYBER_ALERT = env_bool("AUTO_PUBLISH_CYBER_ALERT", True)
FORWARD_BOT_STATUS = env_bool("FORWARD_BOT_STATUS", False)
# 360 seconds = at most 10 crossposts/hour. The queue is persistent, so bursts
# are delivered gradually instead of being lost to rate limits.
ANNOUNCEMENT_PUBLISH_INTERVAL_SECONDS = int(
    os.getenv("ANNOUNCEMENT_PUBLISH_INTERVAL_SECONDS", "360")
)

# Final public-feed gate. Topic-channel posts are already filtered, but queued
# announcements are checked again immediately before Discord crossposting.
# This lets newer/better intelligence replace weaker queued reporting and drops
# news that became stale while waiting.
ANNOUNCEMENT_FINAL_RECHECK = env_bool("ANNOUNCEMENT_FINAL_RECHECK", True)
ANNOUNCEMENT_QUEUE_DEDUP_THRESHOLD = min(1.0, max(0.60, float(
    os.getenv("ANNOUNCEMENT_QUEUE_DEDUP_THRESHOLD", "0.90")
)))
ANNOUNCEMENT_QUEUE_MAX_CANDIDATES = max(25, int(
    os.getenv("ANNOUNCEMENT_QUEUE_MAX_CANDIDATES", "250")
))
ANNOUNCEMENT_DELETE_REJECTED_MIRRORS = env_bool(
    "ANNOUNCEMENT_DELETE_REJECTED_MIRRORS", True
)

# Bot-status channel. The bot maintains one live dashboard message instead of
# spamming periodic heartbeat messages. Errors/recoveries are posted only when
# a collector changes state.
STATUS_HEARTBEAT_ENABLED = env_bool("STATUS_HEARTBEAT_ENABLED", True)
STATUS_HEARTBEAT_INTERVAL_SECONDS = max(300, int(
    os.getenv("STATUS_HEARTBEAT_INTERVAL_SECONDS", "1800")
))
# Dashboard edits are deliberately coalesced. Discord's message-edit route is
# rate-limited, and several collectors can transition state at nearly the same
# time after startup/reconnect. Debouncing + a minimum edit gap guarantees only
# one in-flight PATCH and prevents a status-update storm.
STATUS_DASHBOARD_DEBOUNCE_SECONDS = max(1, int(
    os.getenv("STATUS_DASHBOARD_DEBOUNCE_SECONDS", "12")
))
STATUS_DASHBOARD_MIN_EDIT_INTERVAL_SECONDS = max(10, int(
    os.getenv("STATUS_DASHBOARD_MIN_EDIT_INTERVAL_SECONDS", "30")
))
STATUS_DASHBOARD_CHANGE_DETECTION = env_bool(
    "STATUS_DASHBOARD_CHANGE_DETECTION", True
)
STATUS_POST_STARTUP = env_bool("STATUS_POST_STARTUP", True)
STATUS_POST_ERRORS = env_bool("STATUS_POST_ERRORS", True)
STATUS_POST_RECOVERY = env_bool("STATUS_POST_RECOVERY", True)
STATUS_DASHBOARD_ENABLED = env_bool("STATUS_DASHBOARD_ENABLED", True)

THREAT_ROLE_ID = env_int("THREAT_ROLE_ID", 0)
CTF_ROLE_ID = env_int("CTF_ROLE_ID", 0)

BACKFILL_ON_FIRST_RUN = env_bool("BACKFILL_ON_FIRST_RUN", False)
CTF_MENTIONS = env_bool("CTF_MENTIONS", True)

ENABLE_X_API = env_bool("ENABLE_X_API", False)
X_BEARER_TOKEN = os.getenv("X_BEARER_TOKEN", "").strip()
X_QUERY_OVERRIDE = os.getenv("X_QUERY", "").strip()
X_WATCH_ACCOUNTS = [
    x.strip().lstrip("@")
    for x in os.getenv("X_WATCH_ACCOUNTS", "").split(",")
    if x.strip()
]
NVD_API_KEY = os.getenv("NVD_API_KEY", "").strip()

DB_PATH = os.getenv("DB_PATH", "threatbot.db")

HTTP_TIMEOUT = aiohttp.ClientTimeout(total=35)
FEED_HTTP_TIMEOUT_SECONDS = max(5, int(os.getenv("FEED_HTTP_TIMEOUT_SECONDS", "12")))
HTTP_DNS_CACHE_SECONDS = max(60, int(os.getenv("HTTP_DNS_CACHE_SECONDS", "300")))
HTTP_MAX_CONNECTIONS = max(5, int(os.getenv("HTTP_MAX_CONNECTIONS", "30")))
HTTP_MAX_CONNECTIONS_PER_HOST = max(1, int(os.getenv("HTTP_MAX_CONNECTIONS_PER_HOST", "4")))
FEED_BACKOFF_BASE_SECONDS = max(15, int(os.getenv("FEED_BACKOFF_BASE_SECONDS", "30")))
FEED_BACKOFF_MAX_SECONDS = max(FEED_BACKOFF_BASE_SECONDS, int(os.getenv("FEED_BACKOFF_MAX_SECONDS", "900")))
FEED_TRAVERSAL_LOGS = env_bool("FEED_TRAVERSAL_LOGS", True)
FEED_TRACE_TITLES = max(0, min(5, int(os.getenv("FEED_TRACE_TITLES", "1"))))
TRUSTED_SOURCE_SOFT_SIGNAL_MODE = env_bool("TRUSTED_SOURCE_SOFT_SIGNAL_MODE", True)
USER_AGENT = os.getenv(
    "USER_AGENT",
    "CyberIntelDiscordBot/1.0 (+public threat intelligence aggregator)",
)

# Polling intervals
RSS_INTERVAL_SECONDS = int(os.getenv("RSS_INTERVAL_SECONDS", "60"))
OFFICIAL_INTERVAL_SECONDS = int(os.getenv("OFFICIAL_INTERVAL_SECONDS", "300"))
X_INTERVAL_SECONDS = int(os.getenv("X_INTERVAL_SECONDS", "300"))
CTF_INTERVAL_SECONDS = int(os.getenv("CTF_INTERVAL_SECONDS", "1200"))

# Persistent cross-source duplicate suppression. Exact source IDs are still
# retained forever in `seen`. The history table adds URL/title/event matching
# across different feeds and survives bot restarts.
DEDUP_ENABLED = env_bool("DEDUP_ENABLED", True)
DEDUP_HISTORY_DAYS = max(1, int(os.getenv("DEDUP_HISTORY_DAYS", "120")))
DEDUP_FUZZY_THRESHOLD = min(1.0, max(0.50, float(os.getenv("DEDUP_FUZZY_THRESHOLD", "0.90"))))
DEDUP_CVE_THRESHOLD = min(1.0, max(0.40, float(os.getenv("DEDUP_CVE_THRESHOLD", "0.72"))))
DEDUP_SAME_CVE_HOURS = max(1, int(os.getenv("DEDUP_SAME_CVE_HOURS", "96")))
DEDUP_FUZZY_CANDIDATES = max(50, int(os.getenv("DEDUP_FUZZY_CANDIDATES", "400")))

# High-signal publication policy. The defaults intentionally favor fewer, better
# alerts over volume so members do not learn to ignore the feed.
HIGH_SIGNAL_ONLY = env_bool("HIGH_SIGNAL_ONLY", True)
NEWS_MIN_QUALITY_SCORE = max(0, min(100, int(os.getenv("NEWS_MIN_QUALITY_SCORE", "70"))))
INDIA_MIN_QUALITY_SCORE = max(0, min(100, int(os.getenv("INDIA_MIN_QUALITY_SCORE", "70"))))
RESEARCH_MIN_QUALITY_SCORE = max(0, min(100, int(os.getenv("RESEARCH_MIN_QUALITY_SCORE", "70"))))
POC_MIN_QUALITY_SCORE = max(0, min(100, int(os.getenv("POC_MIN_QUALITY_SCORE", "70"))))
MAX_SECURITY_ARTICLE_AGE_HOURS = max(1, int(os.getenv("MAX_SECURITY_ARTICLE_AGE_HOURS", "72")))
ENABLE_DISCOVERY_NEWS = env_bool("ENABLE_DISCOVERY_NEWS", False)
ALLOW_UNVERIFIED_SOCIAL = env_bool("ALLOW_UNVERIFIED_SOCIAL", False)
X_REQUIRE_WATCHLIST = env_bool("X_REQUIRE_WATCHLIST", True)
POC_REQUIRE_CVE = env_bool("POC_REQUIRE_CVE", True)

# Two-stage publication policy (v8.2). Relevance decides whether a candidate is
# useful enough for the internal/topic channel; trust/quality decides whether it
# may be automatically crossposted to followers. This keeps breaking-but-early
# breach intelligence visible without treating it as confirmed public reporting.
MANUAL_REVIEW_ENABLED = env_bool("MANUAL_REVIEW_ENABLED", True)
# v8.3: every fresh/high-signal security item below this score is kept in its
# topic channel with four persistent moderator controls instead of being silently
# discarded or automatically syndicated. Tier-4 breach leads still require review
# even when their numeric score is above this threshold.
COMMUNITY_AUTO_PUBLISH_SCORE = max(0, min(100, int(os.getenv("COMMUNITY_AUTO_PUBLISH_SCORE", "70"))))
MANUAL_REVIEW_MIN_SCORE = max(0, min(100, int(os.getenv("MANUAL_REVIEW_MIN_SCORE", "0"))))
MANUAL_REVIEW_BREACH_MIN_SCORE = max(0, min(100, int(os.getenv("MANUAL_REVIEW_BREACH_MIN_SCORE", "0"))))
MANUAL_REVIEW_ALLOW_DISCOVERY_BREACH = env_bool("MANUAL_REVIEW_ALLOW_DISCOVERY_BREACH", True)
MANUAL_REVIEW_ALLOW_UNVERIFIED_SOCIAL = env_bool("MANUAL_REVIEW_ALLOW_UNVERIFIED_SOCIAL", False)
# Low-score items remain in their respective topic channel until a moderator
# chooses Publish Now. Keep this false for the four-button workflow.
MANUAL_REVIEW_MIRROR_TO_CYBER_ALERT = env_bool("MANUAL_REVIEW_MIRROR_TO_CYBER_ALERT", False)
MANUAL_REVIEW_HISTORY_HOURS = max(1, int(os.getenv("MANUAL_REVIEW_HISTORY_HOURS", "48")))

# Persistent moderator controls rendered directly on each low-score topic alert.
REVIEW_CONTROLS_ENABLED = env_bool("REVIEW_CONTROLS_ENABLED", True)
REVIEWER_USER_IDS = env_id_set("REVIEWER_USER_IDS")
REVIEWER_ROLE_IDS = env_id_set("REVIEWER_ROLE_IDS")
REVIEW_ALLOW_MANAGE_MESSAGES = env_bool("REVIEW_ALLOW_MANAGE_MESSAGES", True)
# Strong default: an unverified Tier-4 breach still asks a moderator even at 70+.
# Set false only if you want the rule to be strictly score-based.
TIER4_BREACH_FORCE_REVIEW = env_bool("TIER4_BREACH_FORCE_REVIEW", True)

# CTF policy: publish actionable opportunities, not stale/running/closed event
# coverage. CTFtime entries must be future events; article/search discoveries
# must explicitly advertise registration and be recent.
CTF_UPCOMING_ONLY = env_bool("CTF_UPCOMING_ONLY", True)
CTF_LOOKAHEAD_DAYS = max(1, int(os.getenv("CTF_LOOKAHEAD_DAYS", "120")))
CTF_DISCOVERY_MAX_AGE_DAYS = max(1, int(os.getenv("CTF_DISCOVERY_MAX_AGE_DAYS", "10")))
CTF_REQUIRE_OFFICIAL_URL = env_bool("CTF_REQUIRE_OFFICIAL_URL", True)
CTF_REQUIRE_REGISTRATION_SIGNAL = env_bool("CTF_REQUIRE_REGISTRATION_SIGNAL", True)
CTF_ALLOW_RUNNING_IF_REGISTRATION_OPEN = env_bool("CTF_ALLOW_RUNNING_IF_REGISTRATION_OPEN", True)
CTF_MIN_PRIORITY = os.getenv("CTF_MIN_PRIORITY", "RATED").strip().upper()

# Flexible RSS/Atom input. RSS.app is intentionally treated as a transport/
# discovery provider, not as a trusted publisher. Trust is derived from the
# underlying entry publisher/domain whenever possible.
ENABLE_BUILTIN_RSS = env_bool("ENABLE_BUILTIN_RSS", True)
NEWS_RSS_FEEDS = env_feed_list("NEWS_RSS_FEEDS", "Custom News RSS")
RESEARCH_RSS_FEEDS = env_feed_list("RESEARCH_RSS_FEEDS", "Custom Research RSS")
INDIA_RSS_FEEDS = env_feed_list("INDIA_RSS_FEEDS", "Custom India RSS")
EXPLOIT_RSS_FEEDS = env_feed_list("EXPLOIT_RSS_FEEDS", "Custom Exploit RSS")
BREACH_RSS_FEEDS = env_feed_list("BREACH_RSS_FEEDS", "Custom Breach RSS")
CTF_RSS_FEEDS = env_feed_list("CTF_RSS_FEEDS", "Custom CTF RSS")

# Optional free discovery replacement for social/X monitoring. These Google News
# RSS searches are intentionally OFF by default because discovery feeds are noisy.
# If enabled, candidates still pass the strict cyber relevance + trust gate, and
# Tier-4-only breach leads are never mirrored to the public Announcement feed.
ENABLE_BREACH_DISCOVERY_RSS = env_bool("ENABLE_BREACH_DISCOVERY_RSS", False)


# ---------------------------------------------------------------------------
# Data sources
# ---------------------------------------------------------------------------

BUILTIN_RSS_FEEDS = [
    # Tier 3 — reputable cybersecurity news
    ("BleepingComputer", "https://www.bleepingcomputer.com/feed/", "news"),
    ("The Hacker News", "https://feeds.feedburner.com/TheHackersNews", "news"),
    ("SecurityWeek", "https://www.securityweek.com/feed/", "news"),
    ("KrebsOnSecurity", "https://krebsonsecurity.com/feed/", "news"),
    ("Dark Reading", "https://www.darkreading.com/rss.xml", "news"),

    # Tier 2 — security research / vendor intelligence
    ("PortSwigger Research", "https://portswigger.net/research/rss", "research"),
    ("Unit 42", "https://unit42.paloaltonetworks.com/feed/", "research"),
    ("Cisco Talos", "https://blog.talosintelligence.com/rss/", "research"),
    ("ProjectDiscovery", "https://projectdiscovery.io/rss.xml", "research"),
    ("Hackaday Security", "https://hackaday.com/category/security-hacks/feed/", "research"),

    # India / Asia-focused publishers
    ("Cyble", "https://cyble.com/feed/", "india"),
    ("The Cyber Express", "https://thecyberexpress.com/feed/", "india"),
]

POC_FEEDS = [
    ("NomiSec PoC-in-GitHub", "https://github.com/nomi-sec/PoC-in-GitHub/commits/master.atom"),
    ("Trickest CVE PoCs", "https://github.com/trickest/cve/commits/main.atom"),
]

CERTIN_LIST_URLS = [
    "https://www.cert-in.org.in/s2cMainServlet?pageid=VLNLIST02",
    "https://www.cert-in.org.in/s2cMainServlet?pageid=PUBADVLIST02",
]

CISA_KEV_URLS = [
    # Canonical feed
    "https://www.cisa.gov/sites/default/files/feeds/known_exploited_vulnerabilities.json",
    # Official CISA GitHub mirror fallback
    "https://raw.githubusercontent.com/cisagov/kev-data/develop/known_exploited_vulnerabilities.json",
]

CTFTIME_API = "https://ctftime.org/api/v1/events/"
HTB_EVENTS_URL = "https://www.hackthebox.com/events"
X_RECENT_SEARCH_URL = "https://api.x.com/2/tweets/search/recent"
EPSS_API = "https://api.first.org/data/v1/epss"
NVD_API = "https://services.nvd.nist.gov/rest/json/cves/2.0"


def google_news_rss(query: str, india: bool = False) -> str:
    params = {
        "q": query,
        "hl": "en-IN" if india else "en-US",
        "gl": "IN" if india else "US",
        "ceid": "IN:en" if india else "US:en",
    }
    return "https://news.google.com/rss/search?" + urlencode(params)


# India-specific cyber reporting feeds built from Google News search RSS.
INDIA_NEWS_FEEDS = [
    (
        "India Cyber News",
        google_news_rss(
            'India ("cyber attack" OR ransomware OR "data breach" OR "zero-day" OR "security incident")',
            india=True,
        ),
    ),
    (
        "India Government Cyber",
        google_news_rss(
            '("CERT-In" OR MeitY OR NCIIPC OR "Indian Army") '
            '(cybersecurity OR vulnerability OR "data breach" OR "security incident" OR "cyber attack" OR ransomware)',
            india=True,
        ),
    ),
]

# Google News is a discovery source, not a trusted security-only publisher.
# Items from these feeds must pass a second-stage cybersecurity relevance gate.
DISCOVERY_SECURITY_SOURCES = {
    "India Cyber News",
    "India Government Cyber",
    "Breach Discovery",
    "Ransomware Discovery",
    "India Breach Discovery",
}

# Optional RSS-only discovery to replace social/X monitoring. These are leads,
# not trusted facts. The item publisher is recovered from feed metadata when
# possible, then normal source-tier and significance checks decide whether it
# deserves a topic-channel post or public crosspost.
BREACH_SEARCH_FEEDS = [
    (
        "Breach Discovery",
        google_news_rss(
            '"data breach" OR ransomware OR "security incident" OR '
            '"unauthorized access" OR "customer data stolen" OR "stolen data"'
        ),
    ),
    (
        "Ransomware Discovery",
        google_news_rss('"ransomware attack" company'),
    ),
    (
        "India Breach Discovery",
        google_news_rss(
            'India ("data breach" OR ransomware OR "security incident" OR "unauthorized access")',
            india=True,
        ),
    ),
]

# Search-RSS feeds are intentionally registration-focused. Generic "CTF" news
# queries produce recaps, writeups and already-running event coverage, so the
# search terms below require an actionable registration signal.
CTF_SEARCH_FEEDS = [
    (
        "India CTF Registration Search",
        google_news_rss(
            'India (CTF OR "capture the flag" OR "cyber challenge" OR "cybersecurity competition") '
            '("registration open" OR "registrations open" OR "register now" OR "registration closes" OR "applications open")',
            india=True,
        ),
    ),
    (
        "Indian Government CTF Registration Search",
        google_news_rss(
            '("Indian Army" OR "Territorial Army" OR CERT-In OR MeitY OR DRDO OR NCIIPC OR IIT OR NIT OR IIIT) '
            '(CTF OR "capture the flag" OR "cyber challenge" OR "cybersecurity competition") '
            '("registration open" OR "registrations open" OR "register now" OR "registration closes" OR "applications open")',
            india=True,
        ),
    ),
    (
        "Hack The Box CTF Registration Search",
        google_news_rss(
            '"Hack The Box" (CTF OR "Cyber Apocalypse") '
            '("registration open" OR "register now" OR "sign up")'
        ),
    ),
    (
        "TryHackMe CTF Registration Search",
        google_news_rss(
            'TryHackMe (CTF OR competition OR challenge) '
            '("registration open" OR "register now" OR "sign up")'
        ),
    ),
]

# Backward compatibility with v1-v7. Prefer CTF_RSS_FEEDS in new deployments.
LEGACY_CUSTOM_CTF_RSS = [
    x.strip()
    for x in os.getenv("CUSTOM_CTF_RSS", "").split(",")
    if x.strip()
]


# ---------------------------------------------------------------------------
# Text / classification helpers
# ---------------------------------------------------------------------------

CVE_RE = re.compile(r"\bCVE-\d{4}-\d{4,19}\b", re.I)

CRITICAL_PATTERNS = [
    r"\bactively exploited\b",
    r"\bexploited in the wild\b",
    r"\bzero[- ]day\b",
    r"\b0[- ]day\b",
    r"\bmass exploitation\b",
    r"\bpre[- ]auth(?:entication)?\b",
    r"\bremote code execution\b",
    r"\bRCE\b",
    r"\bauthentication bypass\b",
    r"\bwormable\b",
    r"\bsupply[- ]chain attack\b",
]

HIGH_PATTERNS = [
    r"\bransomware\b",
    r"\bprivilege escalation\b",
    r"\bcommand injection\b",
    r"\bSQL injection\b",
    r"\bSQLi\b",
    r"\barbitrary file upload\b",
    r"\bpath traversal\b",
    r"\bcredential theft\b",
    r"\bmalware campaign\b",
    r"\bbotnet\b",
]

INDIA_PATTERNS = [
    r"\bindia\b",
    r"\bindian\b",
    r"\bCERT[- ]?In\b",
    r"\bMeitY\b",
    r"\bNCIIPC\b",
    r"\bUIDAI\b",
    r"\bAadhaar\b",
    r"\bUPI\b",
    r"\bRBI\b",
    r"\bNPCI\b",
    r"\bDigiLocker\b",
    r"\bIndian Army\b",
    r"\bTerritorial Army\b",
    r"\bMinistry of Defence\b",
    r"\bDRDO\b",
    r"\bCyberPeace\b",
    r"\.gov\.in\b",
]

CTF_PATTERNS = [
    r"\bCTF\b",
    r"\bcapture[\s-]+the[\s-]+flag\b",
    r"\bcyber challenge\b",
    r"\bcybersecurity competition\b",
    r"\bhacking competition\b",
    r"\bjeopardy[- ]style\b",
    r"\battack[- ]defen[cs]e\b",
    r"\bbug hunting (?:challenge|competition)\b",
]

CYBER_CONTEXT_PATTERNS = [
    r"\bcyber\b",
    r"\bhack",
    r"\bsecurity\b",
    r"\bvulnerability\b",
    r"\bforensics\b",
    r"\breverse engineering\b",
    r"\bpwn\b",
    r"\bweb exploitation\b",
]

NATIONAL_CTF_PATTERNS = [
    r"\bIndian Army\b",
    r"\bTerritorial Army\b",
    r"\bMinistry of Defence\b",
    r"\bCERT[- ]?In\b",
    r"\bMeitY\b",
    r"\bNCIIPC\b",
    r"\bDRDO\b",
    r"\bGovernment of India\b",
    r"\bnational[- ]level\b",
]

MAJOR_CTF_PATTERNS = [
    r"\bHack The Box\b",
    r"\bHTB\b",
    r"\bCyber Apocalypse\b",
    r"\bTryHackMe\b",
    r"\bpicoCTF\b",
    r"\bDEF CON\b",
    r"\bGoogle CTF\b",
    r"\bIIT(?:s)?\b",
    r"\bNIT(?:s)?\b",
    r"\bIIIT(?:s)?\b",
    r"\bCyberPeace\b",
]

CTF_REGISTRATION_OPEN_PATTERNS = [
    r"\bregistration(?:s)? (?:is |are )?open\b",
    r"\bregistration(?:s)? (?:has |have )?opened\b",
    r"\bregister now\b",
    r"\bsign[ -]?up(?: now)?\b",
    r"\bapplications? (?:is |are )?open\b",
    r"\bregistration closes?\b",
    r"\bregistration deadline\b",
    r"\bapply now\b",
]

CTF_CLOSED_OR_RECAP_PATTERNS = [
    r"\bregistration(?:s)? (?:is |are )?closed\b",
    r"\bregistration(?:s)? (?:has |have )?closed\b",
    r"\bregistration ended\b",
    r"\bdeadline (?:has )?passed\b",
    r"\bevent (?:has )?(?:ended|concluded)\b",
    r"\bfinal standings\b",
    r"\bwinners? announced\b",
    r"\bwrite[ -]?up\b",
    r"\bpost[- ]event\b",
    r"\brecap\b",
]

LOW_VALUE_NEWS_PATTERNS = [
    r"\bweekly roundup\b", r"\bpodcast\b", r"\bwebinar\b",
    r"\bconference recap\b", r"\bfunding round\b", r"\bacquisition\b",
    r"\bappoints?\b", r"\bpartnership\b", r"\bmarket report\b",
    r"\bcareer(?:s)?\b", r"\bcertification sale\b", r"\bflash sale\b",
    r"\bdiscount\b", r"\bwhat is\b", r"\bbeginner(?:'s)? guide\b",
    r"\btop \d+\b", r"\bblueprint\b", r"\bthought leadership\b",
]

STRONG_SECURITY_SIGNAL_PATTERNS = CRITICAL_PATTERNS + HIGH_PATTERNS + [
    r"\bCVE-\d{4}-\d{4,19}\b", r"\bdata breach\b",
    r"\bbreach notification\b", r"\bmalware\b", r"\bphishing campaign\b",
    r"\bDDoS\b", r"\bcredential leak\b", r"\bcredential dump\b",
    r"\bsecurity flaw\b", r"\bvulnerabilit(?:y|ies)\b",
    r"\brequest smuggling\b", r"\bweb cache poisoning\b",
    r"\bprototype pollution\b", r"\bSSRF\b", r"\bXSS\b",
    r"\bdeserialization\b", r"\bsandbox escape\b",
    r"\bexploit chain\b", r"\bpatch(?:ed|es|ing)?\b",
]

BREACH_ROUTE_PATTERNS = [
    r"\bdata breach\b", r"\bbreach notification\b", r"\bransomware\b",
    r"\bcredential (?:leak|dump|theft)\b", r"\bstolen (?:data|records|credentials)\b",
]

SOURCE_REPUTATION = {
    "CISA KEV": 100,
    "CERT-In": 100,
    "PortSwigger Research": 95,
    "BleepingComputer": 92,
    "ProjectDiscovery": 90,
    "SecurityWeek": 89,
    "KrebsOnSecurity": 91,
    "Dark Reading": 87,
    "The Hacker News": 88,
    "NomiSec PoC-in-GitHub": 87,
    "Trickest CVE PoCs": 87,
    "Cyble": 82,
    "The Cyber Express": 76,
    "Hackaday Security": 72,
    "CTFtime": 94,
    "Hack The Box": 96,
    "TryHackMe": 94,
    "Mandiant": 97,
    "Google Project Zero": 97,
    "Cisco Talos": 95,
    "Unit 42": 95,
    "Microsoft Security Response Center": 96,
    "Cloudflare": 93,
    "Rapid7": 92,
    "Tenable": 90,
}


PUBLISHER_HOST_MAP = {
    "bleepingcomputer.com": "BleepingComputer",
    "thehackernews.com": "The Hacker News",
    "portswigger.net": "PortSwigger Research",
    "projectdiscovery.io": "ProjectDiscovery",
    "securityweek.com": "SecurityWeek",
    "krebsonsecurity.com": "KrebsOnSecurity",
    "darkreading.com": "Dark Reading",
    "hackaday.com": "Hackaday Security",
    "cyble.com": "Cyble",
    "thecyberexpress.com": "The Cyber Express",
    "ctftime.org": "CTFtime",
    "hackthebox.com": "Hack The Box",
    "tryhackme.com": "TryHackMe",
    "cisa.gov": "CISA KEV",
    "cert-in.org.in": "CERT-In",
    "mandiant.com": "Mandiant",
    "googleprojectzero.blogspot.com": "Google Project Zero",
    "talosintelligence.com": "Cisco Talos",
    "unit42.paloaltonetworks.com": "Unit 42",
    "msrc.microsoft.com": "Microsoft Security Response Center",
    "cloudflare.com": "Cloudflare",
    "rapid7.com": "Rapid7",
    "tenable.com": "Tenable",
}

PUBLISHER_NAME_ALIASES = {
    "bleeping computer": "BleepingComputer",
    "bleepingcomputer": "BleepingComputer",
    "the hacker news": "The Hacker News",
    "portswigger": "PortSwigger Research",
    "portswigger research": "PortSwigger Research",
    "projectdiscovery": "ProjectDiscovery",
    "securityweek": "SecurityWeek",
    "krebsonsecurity": "KrebsOnSecurity",
    "krebs on security": "KrebsOnSecurity",
    "dark reading": "Dark Reading",
    "darkreading": "Dark Reading",
    "hackaday": "Hackaday Security",
    "hackaday security": "Hackaday Security",
    "cyble": "Cyble",
    "the cyber express": "The Cyber Express",
    "ctftime": "CTFtime",
    "hack the box": "Hack The Box",
    "tryhackme": "TryHackMe",
    "mandiant": "Mandiant",
    "google project zero": "Google Project Zero",
    "project zero": "Google Project Zero",
    "cisco talos": "Cisco Talos",
    "talos": "Cisco Talos",
    "unit 42": "Unit 42",
    "microsoft security response center": "Microsoft Security Response Center",
    "msrc": "Microsoft Security Response Center",
    "cloudflare": "Cloudflare",
    "rapid7": "Rapid7",
    "tenable": "Tenable",
}


TIER1_SOURCES = {
    "CISA KEV", "CERT-In", "Microsoft Security Response Center",
}

TIER2_SOURCES = {
    "PortSwigger Research", "Unit 42", "Cisco Talos", "ProjectDiscovery",
    "Mandiant", "Google Project Zero", "Cloudflare", "Rapid7", "Tenable",
}

TIER3_SOURCES = {
    "BleepingComputer", "The Hacker News", "SecurityWeek", "KrebsOnSecurity",
    "Dark Reading", "Cyble", "The Cyber Express", "Hackaday Security",
}

def source_tier(item_or_source: dict[str, Any] | str) -> int:
    source = (
        str(item_or_source.get("source", ""))
        if isinstance(item_or_source, dict)
        else str(item_or_source)
    )
    if source in TIER1_SOURCES:
        return 1
    if source in TIER2_SOURCES:
        return 2
    if source in TIER3_SOURCES:
        return 3
    return 4

def source_tier_label(item_or_source: dict[str, Any] | str) -> str:
    tier = source_tier(item_or_source)
    return {
        1: "Tier 1 • Official",
        2: "Tier 2 • Security research",
        3: "Tier 3 • Reputable security news",
        4: "Tier 4 • Discovery / unverified",
    }[tier]

def breach_confidence_label(item: dict[str, Any]) -> str:
    tier = source_tier(item)
    if tier == 1:
        return "🔴 Confirmed / official"
    if tier == 2:
        return "🟠 High-confidence technical reporting"
    if tier == 3:
        return "🟠 Reputable reporting"
    return "⚠️ Developing / unverified"

def public_alert_allowed(item: dict[str, Any], route: str) -> tuple[bool, str]:
    # Discovery-only breach leads are useful internally but should never be
    # syndicated as a confirmed public alert by themselves. A later Tier 1–3
    # report for the same incident will pass, and v7/v8 queue resolution will
    # merge/upgrade the public incident before crosspost.
    if route == "breach" and source_tier(item) >= 4 and TIER4_BREACH_FORCE_REVIEW:
        return False, "Tier-4-only breach lead kept internal until corroborated or moderator-approved"
    return True, "eligible"


def normalize_publisher_name(value: str | None) -> str:
    value = " ".join((value or "").split()).strip()
    if not value:
        return ""
    lowered = value.casefold()
    if lowered in {"rss.app", "rss app", "rss", "feed", "news", "google news"}:
        return ""
    return PUBLISHER_NAME_ALIASES.get(lowered, value)


def publisher_from_url(value: str | None) -> str:
    try:
        host = (urlsplit(value or "").hostname or "").lower().removeprefix("www.")
    except Exception:
        return ""
    if not host or host.endswith("rss.app"):
        return ""
    # Longest suffix first so specific subdomains win.
    for suffix, publisher in sorted(PUBLISHER_HOST_MAP.items(), key=lambda x: len(x[0]), reverse=True):
        if host == suffix or host.endswith("." + suffix):
            return publisher
    return ""


def feed_provider_name(feed_url: str) -> str:
    try:
        host = (urlsplit(feed_url).hostname or "").lower().removeprefix("www.")
    except Exception:
        return "custom RSS"
    if host == "rss.app" or host.endswith(".rss.app"):
        return "RSS.app"
    return host or "custom RSS"


def strip_html(value: str | None) -> str:
    if not value:
        return ""
    return BeautifulSoup(html.unescape(value), "html.parser").get_text(" ", strip=True)


def truncate(text: str, n: int) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= n else text[: n - 1] + "…"


def stable_id(source: str, unique: str) -> str:
    return hashlib.sha256(f"{source}:{unique}".encode("utf-8", "ignore")).hexdigest()


_TRACKING_QUERY_KEYS = {
    "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
    "utm_id", "gclid", "fbclid", "mc_cid", "mc_eid", "ref", "source",
}

# These words add little value when deciding whether two headlines describe the
# same story. They are used only for fuzzy candidate scoring, never for display.
_DEDUP_STOPWORDS = {
    "a", "an", "and", "are", "as", "at", "be", "by", "for", "from", "has",
    "have", "in", "into", "is", "it", "its", "new", "of", "on", "or", "says",
    "that", "the", "their", "this", "to", "with", "after", "over", "about",
    "security", "cybersecurity", "cyber", "update", "updates", "report",
}


def canonicalize_url(value: str | None) -> str:
    """Return a stable URL for duplicate checks.

    Tracking parameters and fragments are removed, host/scheme are normalized,
    and a non-root trailing slash is removed. Non-http(s) values are ignored.
    """
    value = (value or "").strip()
    if not value.startswith(("http://", "https://")):
        return ""
    try:
        parts = urlsplit(value)
        scheme = parts.scheme.lower()
        host = (parts.hostname or "").lower()
        if not host:
            return ""
        # Preserve an explicit non-default port.
        port = parts.port
        netloc = host
        if port and not ((scheme == "http" and port == 80) or (scheme == "https" and port == 443)):
            netloc = f"{host}:{port}"
        path = re.sub(r"/{2,}", "/", parts.path or "/")
        if path != "/":
            path = path.rstrip("/")
        query_pairs = [
            (k, v)
            for k, v in parse_qsl(parts.query, keep_blank_values=True)
            if k.lower() not in _TRACKING_QUERY_KEYS and not k.lower().startswith("utm_")
        ]
        query = urlencode(sorted(query_pairs))
        return urlunsplit((scheme, netloc, path, query, ""))
    except Exception:
        return value.split("#", 1)[0]


def normalize_title(value: str | None) -> str:
    """Normalize a headline without changing its meaning."""
    text = strip_html(value or "")
    text = unicodedata.normalize("NFKC", text).casefold()
    text = re.sub(r"https?://\S+", " ", text)
    # Normalize common typographic separators/punctuation to spaces.
    text = re.sub(r"[^\w\s-]", " ", text, flags=re.UNICODE)
    text = text.replace("_", " ").replace("-", " ")
    return " ".join(text.split())


def _title_tokens(norm_title: str) -> set[str]:
    return {
        tok for tok in norm_title.split()
        if len(tok) >= 3 and tok not in _DEDUP_STOPWORDS
    }


def title_similarity(a: str, b: str) -> float:
    """Similarity tuned for news headlines.

    Sequence similarity catches wording/order; token containment catches the
    common case where one feed appends a publisher or short qualifier.
    """
    if not a or not b:
        return 0.0
    if a == b:
        return 1.0
    seq = SequenceMatcher(None, a, b, autojunk=False).ratio()
    ta, tb = _title_tokens(a), _title_tokens(b)
    if not ta or not tb:
        return seq
    overlap = len(ta & tb)
    union = len(ta | tb)
    jaccard = overlap / union if union else 0.0
    containment = overlap / min(len(ta), len(tb))
    token_score = (0.45 * jaccard) + (0.55 * containment)
    # Strong token containment catches reordered headlines and publisher suffixes.
    # Requiring >=3 shared meaningful tokens keeps short generic headlines from
    # becoming accidental matches.
    if containment >= 0.80 and overlap >= 3:
        token_score = max(token_score, min(0.98, 0.87 + 0.11 * containment))
    return max(seq, token_score)


def cve_key(item: dict[str, Any]) -> str:
    cves = item.get("cves") or []
    if isinstance(cves, str):
        cves = extract_cves(cves)
    return ",".join(sorted({str(c).upper() for c in cves if c}))


def history_fields(item: dict[str, Any]) -> dict[str, str]:
    norm = normalize_title(str(item.get("title", "")))
    url = canonicalize_url(str(item.get("url") or item.get("ctftime_url") or ""))
    title_hash = hashlib.sha256(norm.encode("utf-8", "ignore")).hexdigest() if norm else ""
    return {
        "norm_title": norm,
        "title_hash": title_hash,
        "canonical_url": url,
        "cve_key": cve_key(item),
    }


def development_kind(item: dict[str, Any]) -> str:
    """Coarse development phase used only for queue conflict resolution.

    The phase prevents unsafe over-merging of materially different updates for
    the same CVE (for example, a PoC release versus a patch release), while
    allowing two publishers reporting the same exploitation event to converge.
    """
    if item.get("type") == "CTF":
        return "ctf"
    if item.get("type") == "POC":
        return "poc"

    text = item_text(item)
    source = str(item.get("source", ""))
    if source == "CISA KEV" or item.get("kev") or matches_any(
        [r"\bactively exploited\b", r"\bexploited in the wild\b", r"\bmass exploitation\b"],
        text,
    ):
        return "exploitation"
    if matches_any(BREACH_ROUTE_PATTERNS, text):
        return "breach"
    if matches_any([r"\bpatch(?:ed|es|ing)?\b", r"\bfixed\b", r"\bsecurity update\b"], text):
        return "patch"
    if item.get("route_hint") == "research":
        return "research"
    if cve_key(item):
        # Generic reporting about a CVE/disclosure.
        if re.search(r"\bexploit(?:ed|ation|s)?\b", text, re.I):
            return "exploitation"
        return "vulnerability"
    return "news"


def incident_key(item: dict[str, Any]) -> str:
    """Stable incident/event key for queued, not-yet-crossposted messages."""
    f = history_fields(item)
    if item.get("type") == "CTF":
        start = str(item.get("start") or "")
        event_url = canonicalize_url(
            str(item.get("registration_url") or item.get("url") or item.get("ctftime_url") or "")
        )
        if event_url:
            return "ctf:url:" + hashlib.sha256(event_url.encode()).hexdigest()[:24]
        basis = f"{f['norm_title']}|{start}"
        return "ctf:title:" + hashlib.sha256(basis.encode()).hexdigest()[:24]

    if f["cve_key"]:
        basis = f"{f['cve_key']}|{development_kind(item)}"
        return "cve:" + hashlib.sha256(basis.encode()).hexdigest()[:24]
    if f["canonical_url"]:
        return "url:" + hashlib.sha256(f["canonical_url"].encode()).hexdigest()[:24]
    if f["title_hash"]:
        return "title:" + f["title_hash"][:24]
    return ""


def queue_quality_score(item: dict[str, Any], priority: str) -> int:
    if item.get("type") == "CTF":
        return {"NATIONAL": 100, "MAJOR": 94, "RATED": 86, "COMMUNITY": 70}.get(priority, 70)
    score, _ = security_quality(item)
    return int(score)


def announcement_strength(item: dict[str, Any], priority: str) -> int:
    """Rank competing queued reports; priority dominates, then trust/quality."""
    priority_value = {
        "URGENT": 100, "CRITICAL": 90, "HIGH": 80, "NATIONAL": 78,
        "MAJOR": 72, "RATED": 60, "NEWS": 50, "COMMUNITY": 40,
    }.get(priority, 40)
    source = str(item.get("source", ""))
    reputation = SOURCE_REPUTATION.get(source, 55)
    quality = queue_quality_score(item, priority)
    official_bonus = 12 if source in {"CISA KEV", "CERT-In"} else 0
    return (priority_value * 10000) + ((reputation + official_bonus) * 100) + quality


def queue_item_json(item: dict[str, Any]) -> str:
    """Serialize only public intelligence metadata needed for the final gate."""
    try:
        return json.dumps(item, ensure_ascii=False, default=str, separators=(",", ":"))
    except Exception:
        return "{}"


def extract_cves(text: str) -> list[str]:
    return sorted({m.group(0).upper() for m in CVE_RE.finditer(text or "")})


def matches_any(patterns: Iterable[str], text: str) -> bool:
    return any(re.search(p, text, re.I) for p in patterns)


def is_india_related(item: dict[str, Any]) -> bool:
    if item.get("source") == "CERT-In":
        return True
    text = " ".join(
        str(item.get(k, ""))
        for k in ("title", "summary", "description", "location", "organizer", "source")
    )
    return matches_any(INDIA_PATTERNS, text)


def classify_security(item: dict[str, Any]) -> str:
    if item.get("source") == "CISA KEV" or item.get("kev"):
        return "URGENT"

    severity = str(item.get("official_severity", "")).lower()
    if severity == "critical":
        return "CRITICAL"
    if severity == "high":
        return "HIGH"

    text = f"{item.get('title', '')} {item.get('summary', '')}"
    if matches_any(CRITICAL_PATTERNS, text):
        return "CRITICAL"
    if matches_any(HIGH_PATTERNS, text):
        return "HIGH"
    return "NEWS"


def looks_like_ctf(item: dict[str, Any]) -> bool:
    text = " ".join(
        str(item.get(k, ""))
        for k in ("title", "summary", "description", "organizer", "location", "source")
    )

    # Explicit CTF phrase is enough if the source is a known cyber source.
    has_ctf = matches_any(CTF_PATTERNS, text)
    has_cyber = matches_any(CYBER_CONTEXT_PATTERNS, text)

    known_ctf_source = item.get("source") in {"CTFtime", "Hack The Box", "TryHackMe"}
    return known_ctf_source or (has_ctf and has_cyber) or (
        has_ctf and matches_any(MAJOR_CTF_PATTERNS + NATIONAL_CTF_PATTERNS, text)
    )


def ctf_priority(item: dict[str, Any]) -> str:
    text = " ".join(
        str(item.get(k, ""))
        for k in ("title", "summary", "description", "organizer", "location", "source")
    )
    if matches_any(NATIONAL_CTF_PATTERNS, text):
        return "NATIONAL"
    if matches_any(MAJOR_CTF_PATTERNS, text):
        return "MAJOR"
    try:
        if float(item.get("weight") or 0) > 0:
            return "RATED"
    except (TypeError, ValueError):
        pass
    return "COMMUNITY"


# Strong indicators used to reject false positives from broad discovery/search feeds.
# Intentionally do NOT include ambiguous standalone words such as "breach" or "attack".
SECURITY_RELEVANCE_PATTERNS = [
    r"\bcybersecurity\b",
    r"\bcyber[- ]?(?:attack|threat|incident|crime|espionage|security)\b",
    r"\bCVE-\d{4}-\d{4,19}\b",
    r"\bCERT[- ]?In\b",
    r"\bCISA\b",
    r"\bNCIIPC\b",
    r"\bzero[- ]day\b",
    r"\bransomware\b",
    r"\bmalware\b",
    r"\bphishing\b",
    r"\bbotnet\b",
    r"\bDDoS\b",
    r"\bdata breach\b",
    r"\bsecurity incident\b",
    r"\bvulnerabilit(?:y|ies)\b",
    r"\bremote code execution\b",
    r"\bauthentication bypass\b",
    r"\bprivilege escalation\b",
    r"\bSQL injection\b",
    r"\bcommand injection\b",
    r"\bcredential (?:theft|stealing|leak|dump)\b",
    r"\b(?:hacker|hackers|hacked|hacking)\b",
    r"\bexploit(?:ed|ation)? (?:code|chain|kit|vulnerability|flaw)\b",
]


def is_relevant_security_item(item: dict[str, Any]) -> bool:
    """Second-stage filter for broad search/discovery feeds.

    Dedicated cybersecurity publishers are trusted by source and do not need this
    gate. Search-engine feeds do, because terms like 'breach' and 'attack' are
    common in non-cyber news.
    """
    source = str(item.get("source", ""))
    if source not in DISCOVERY_SECURITY_SOURCES and not item.get("custom_feed"):
        return True

    text = " ".join(
        str(item.get(k, ""))
        for k in ("title", "summary", "description", "source")
    )
    return matches_any(SECURITY_RELEVANCE_PATTERNS, text)


def parse_iso_epoch(value: str | None) -> int | None:
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if not dt.tzinfo:
            dt = dt.replace(tzinfo=timezone.utc)
        return int(dt.timestamp())
    except Exception:
        return None


def item_text(item: dict[str, Any]) -> str:
    return " ".join(
        str(item.get(k, ""))
        for k in ("title", "summary", "description", "source", "organizer", "location")
    )


def article_is_fresh(item: dict[str, Any], max_age_hours: int) -> bool:
    epoch = item.get("published_epoch") or parse_iso_epoch(str(item.get("published", "")))
    if not epoch:
        return True  # Some official/technical feeds omit a machine-readable date.
    return int(time.time()) - int(epoch) <= max_age_hours * 3600


def security_quality(item: dict[str, Any]) -> tuple[int, list[str]]:
    """Score trust + technical significance. This is a relevance gate, not truth proof."""
    source = str(item.get("source", ""))
    text = item_text(item)
    score = SOURCE_REPUTATION.get(source, 55)
    reasons: list[str] = []

    if source in {"CISA KEV", "CERT-In"}:
        reasons.append("official source")
    if item.get("kev") or source == "CISA KEV":
        score += 20; reasons.append("known exploited")
    if item.get("cves") or CVE_RE.search(text):
        score += 10; reasons.append("CVE-backed")
    if matches_any(CRITICAL_PATTERNS, text):
        score += 16; reasons.append("critical exploitation signal")
    elif matches_any(HIGH_PATTERNS, text):
        score += 10; reasons.append("high-impact threat")
    if matches_any(BREACH_ROUTE_PATTERNS, text):
        score += 8; reasons.append("concrete breach/ransomware signal")
    if item.get("official_severity"):
        sev = str(item["official_severity"]).lower()
        if sev == "critical": score += 12
        elif sev == "high": score += 7
    if item.get("route_hint") == "research" and matches_any(STRONG_SECURITY_SIGNAL_PATTERNS, text):
        score += 6; reasons.append("technical research")
    if source in DISCOVERY_SECURITY_SOURCES:
        score -= 25
    if item.get("custom_feed") and source not in SOURCE_REPUTATION:
        score -= 10
        reasons.append("unknown custom-feed publisher")
    if item.get("social_unverified"):
        score -= 40
    if matches_any(LOW_VALUE_NEWS_PATTERNS, text):
        score -= 25; reasons.append("low-value/editorial pattern")

    return max(0, min(100, score)), reasons


def security_publish_decision(item: dict[str, Any]) -> tuple[bool, str, int]:
    source = str(item.get("source", ""))
    text = item_text(item)

    if source in {"CISA KEV", "CERT-In"}:
        score, _ = security_quality(item)
        return True, "official", score

    if item.get("social_unverified"):
        if not ALLOW_UNVERIFIED_SOCIAL:
            return False, "unverified social reports disabled", 0
        if X_REQUIRE_WATCHLIST and not X_WATCH_ACCOUNTS:
            return False, "X watchlist required in high-signal mode", 0

    if item.get("type") == "POC" and POC_REQUIRE_CVE and not (item.get("cves") or CVE_RE.search(text)):
        return False, "PoC/index update has no CVE", 0

    if not article_is_fresh(item, MAX_SECURITY_ARTICLE_AGE_HOURS):
        return False, f"older than {MAX_SECURITY_ARTICLE_AGE_HOURS}h", 0

    if source in DISCOVERY_SECURITY_SOURCES and not ENABLE_DISCOVERY_NEWS:
        return False, "broad discovery news disabled", 0

    strong_signal = matches_any(STRONG_SECURITY_SIGNAL_PATTERNS, text)
    trusted_dedicated_source = source in SOURCE_REPUTATION and source_tier(item) <= 3
    if HIGH_SIGNAL_ONLY and not strong_signal:
        # v8.4: dedicated Tier 1-3 cyber publishers are already curated security
        # sources. Let their numeric trust/quality score decide AUTO vs REVIEW
        # instead of silently dropping a fresh article because a regex did not match.
        if not (TRUSTED_SOURCE_SOFT_SIGNAL_MODE and trusted_dedicated_source):
            return False, "no concrete high-signal security indicator", 0

    if HIGH_SIGNAL_ONLY and matches_any(LOW_VALUE_NEWS_PATTERNS, text):
        return False, "editorial/promotional/low-value headline", 0

    score, reasons = security_quality(item)
    route_hint = str(item.get("route_hint", "news"))
    if item.get("type") == "POC": threshold = POC_MIN_QUALITY_SCORE
    elif route_hint == "research": threshold = RESEARCH_MIN_QUALITY_SCORE
    elif route_hint == "india": threshold = INDIA_MIN_QUALITY_SCORE
    else: threshold = NEWS_MIN_QUALITY_SCORE

    if score < threshold:
        return False, f"quality score {score} below threshold {threshold}", score
    return True, ", ".join(reasons[:3]) or "trusted high-signal source", score


def manual_review_decision(
    item: dict[str, Any],
    filter_reason: str,
    quality_score: int | None,
) -> tuple[bool, str]:
    """Return whether a rejected security item is still useful for human review.

    This is deliberately narrower than simply posting every score failure. Hard
    failures (stale, low-value, non-cyber, CVE-less PoC, unsafe social noise) stay
    dropped. Fresh concrete security/breach signals above a lower review floor are
    posted to the topic channel with Auto Publish=False.
    """
    if not MANUAL_REVIEW_ENABLED:
        return False, "manual-review mode disabled"
    if item.get("type") in {"STATUS", "CTF"}:
        return False, "not a security review candidate"

    text = item_text(item)
    # Recompute the score here because some hard public-gate reasons (for example
    # broad discovery being disabled) return score=0 before normal scoring. The
    # review path still needs the real trust/significance score.
    score = int(security_quality(item)[0])
    is_breach = (
        str(item.get("route_hint", "")) == "breach"
        or matches_any(BREACH_ROUTE_PATTERNS, text)
    )

    # Keep genuinely bad/stale content out of moderator channels.
    if not article_is_fresh(item, MAX_SECURITY_ARTICLE_AGE_HOURS):
        return False, "stale security item"
    if HIGH_SIGNAL_ONLY and matches_any(LOW_VALUE_NEWS_PATTERNS, text):
        return False, "editorial/promotional/low-value item"
    if not is_relevant_security_item(item):
        return False, "not sufficiently cyber-relevant"
    strong_signal = matches_any(STRONG_SECURITY_SIGNAL_PATTERNS, text)
    source = str(item.get("source", ""))
    trusted_dedicated_source = source in SOURCE_REPUTATION and source_tier(item) <= 3
    if HIGH_SIGNAL_ONLY and not strong_signal:
        if not (TRUSTED_SOURCE_SOFT_SIGNAL_MODE and trusted_dedicated_source):
            return False, "no concrete high-signal security indicator"

    if item.get("type") == "POC" and POC_REQUIRE_CVE and not (item.get("cves") or CVE_RE.search(text)):
        return False, "CVE-less PoC remains a hard reject"

    if item.get("social_unverified") and not MANUAL_REVIEW_ALLOW_UNVERIFIED_SOCIAL:
        return False, "unverified social report not allowed into manual-review flow"

    source = str(item.get("source", ""))
    if source in DISCOVERY_SECURITY_SOURCES and not ENABLE_DISCOVERY_NEWS:
        if not (is_breach and MANUAL_REVIEW_ALLOW_DISCOVERY_BREACH):
            return False, "broad discovery item is not an allowed breach review candidate"

    floor = MANUAL_REVIEW_BREACH_MIN_SCORE if is_breach else MANUAL_REVIEW_MIN_SCORE
    if score < floor:
        return False, f"review score {score} below manual-review floor {floor}"

    if is_breach:
        return True, f"breaking breach candidate: score {score} below auto-publish threshold; human verification required"
    return True, f"high-signal candidate: score {score} below auto-publish threshold; human verification required"


_CTF_PRIORITY_RANK = {"COMMUNITY": 0, "RATED": 1, "MAJOR": 2, "NATIONAL": 3}

def ctf_publish_decision(item: dict[str, Any]) -> tuple[bool, str]:
    now = int(time.time())
    text = item_text(item)
    start = parse_iso_epoch(item.get("start"))
    finish = parse_iso_epoch(item.get("finish"))
    reg_open = bool(item.get("registration_open")) or matches_any(CTF_REGISTRATION_OPEN_PATTERNS, text)
    closed = bool(item.get("registration_closed")) or matches_any(CTF_CLOSED_OR_RECAP_PATTERNS, text)

    if closed:
        return False, "registration closed / recap / finished coverage"
    if finish and finish <= now:
        return False, "event already finished"
    if start and start > now + CTF_LOOKAHEAD_DAYS * 86400:
        return False, f"starts more than {CTF_LOOKAHEAD_DAYS} days away"

    if start:
        if start <= now:
            if not (CTF_ALLOW_RUNNING_IF_REGISTRATION_OPEN and reg_open and (not finish or finish > now)):
                return False, "event already running"
            item["registration_status"] = "🟢 Registration appears open while event is running"
        else:
            item["registration_status"] = "🟢 Upcoming" + (" • registration signal found" if reg_open else "")
    else:
        # Search/article discoveries without machine-readable event dates must be
        # both recent and explicitly registration-focused.
        if not article_is_fresh(item, CTF_DISCOVERY_MAX_AGE_DAYS * 24):
            return False, f"registration article older than {CTF_DISCOVERY_MAX_AGE_DAYS} days"
        if CTF_REQUIRE_REGISTRATION_SIGNAL and not reg_open:
            return False, "no current registration signal and no future start date"
        item["registration_status"] = "🟢 Registration announced/open"

    official_url = str(item.get("registration_url") or "")
    if CTF_REQUIRE_OFFICIAL_URL and item.get("source") == "CTFtime" and not official_url:
        return False, "no official event/registration URL"

    pri = ctf_priority(item)
    min_rank = _CTF_PRIORITY_RANK.get(CTF_MIN_PRIORITY, 1)
    if _CTF_PRIORITY_RANK.get(pri, 0) < min_rank:
        return False, f"CTF priority {pri} below configured minimum {CTF_MIN_PRIORITY}"

    return True, item.get("registration_status", "upcoming registration opportunity")


def stream_publish_decision(stream: str, item: dict[str, Any]) -> tuple[bool, str, int | None]:
    if item.get("type") == "STATUS":
        return True, "operational status", 100
    if item.get("type") == "CTF":
        ok, reason = ctf_publish_decision(item)
        return ok, reason, None
    ok, reason, score = security_publish_decision(item)
    return ok, reason, score


# ---------------------------------------------------------------------------
# SQLite storage
# ---------------------------------------------------------------------------

class ThreatDB:
    def __init__(self, path: str):
        self.conn = sqlite3.connect(path)
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS seen (
                item_id TEXT PRIMARY KEY,
                stream TEXT NOT NULL,
                source TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS dedupe_history (
                item_id TEXT PRIMARY KEY,
                stream TEXT NOT NULL,
                source TEXT,
                title TEXT,
                norm_title TEXT,
                title_hash TEXT,
                canonical_url TEXT,
                cve_key TEXT,
                first_seen_epoch INTEGER NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_dedupe_url ON dedupe_history(canonical_url)"
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_dedupe_title_hash ON dedupe_history(title_hash)"
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_dedupe_cve ON dedupe_history(cve_key, first_seen_epoch)"
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_dedupe_time ON dedupe_history(first_seen_epoch)"
        )
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS manual_review_history (
                item_id TEXT PRIMARY KEY,
                stream TEXT NOT NULL,
                source TEXT,
                title TEXT,
                norm_title TEXT,
                title_hash TEXT,
                canonical_url TEXT,
                cve_key TEXT,
                first_seen_epoch INTEGER NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_review_url ON manual_review_history(canonical_url)"
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_review_title_hash ON manual_review_history(title_hash)"
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_review_time ON manual_review_history(first_seen_epoch)"
        )
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS publication_review_queue (
                source_message_id INTEGER PRIMARY KEY,
                source_channel_id INTEGER NOT NULL,
                route TEXT NOT NULL,
                priority_name TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                item_json TEXT NOT NULL,
                hub_message_id INTEGER NOT NULL DEFAULT 0,
                reviewed_by INTEGER NOT NULL DEFAULT 0,
                created_epoch INTEGER NOT NULL,
                updated_epoch INTEGER NOT NULL
            )
            """
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_publication_review_status ON publication_review_queue(status, updated_epoch)"
        )
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS kv (
                key TEXT PRIMARY KEY,
                value TEXT
            )
            """
        )
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS announcement_queue (
                message_id INTEGER PRIMARY KEY,
                channel_id INTEGER NOT NULL,
                priority INTEGER NOT NULL DEFAULT 50,
                category TEXT,
                title TEXT,
                attempts INTEGER NOT NULL DEFAULT 0,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                incident_key TEXT,
                norm_title TEXT,
                canonical_url TEXT,
                cve_key TEXT,
                development_kind TEXT,
                source TEXT,
                quality_score INTEGER NOT NULL DEFAULT 0,
                strength INTEGER NOT NULL DEFAULT 0,
                item_json TEXT,
                corroborators TEXT,
                updated_epoch INTEGER NOT NULL DEFAULT 0
            )
            """
        )

        # In-place migration from v3-v6 databases. SQLite supports ADD COLUMN,
        # allowing users to keep their existing threatbot.db and dedupe history.
        existing_cols = {
            row[1] for row in self.conn.execute("PRAGMA table_info(announcement_queue)").fetchall()
        }
        migration_cols = {
            "incident_key": "TEXT",
            "norm_title": "TEXT",
            "canonical_url": "TEXT",
            "cve_key": "TEXT",
            "development_kind": "TEXT",
            "source": "TEXT",
            "quality_score": "INTEGER NOT NULL DEFAULT 0",
            "strength": "INTEGER NOT NULL DEFAULT 0",
            "item_json": "TEXT",
            "corroborators": "TEXT",
            "updated_epoch": "INTEGER NOT NULL DEFAULT 0",
        }
        for col, ddl in migration_cols.items():
            if col not in existing_cols:
                self.conn.execute(f"ALTER TABLE announcement_queue ADD COLUMN {col} {ddl}")
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_announcement_incident ON announcement_queue(incident_key)"
        )
        self.conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_announcement_cve ON announcement_queue(cve_key, development_kind)"
        )
        self.conn.commit()

    def seen(self, item_id: str) -> bool:
        return (
            self.conn.execute(
                "SELECT 1 FROM seen WHERE item_id=?", (item_id,)
            ).fetchone()
            is not None
        )

    def mark_seen(self, item_id: str, stream: str, source: str = "") -> None:
        self.conn.execute(
            "INSERT OR IGNORE INTO seen(item_id, stream, source) VALUES (?, ?, ?)",
            (item_id, stream, source),
        )
        self.conn.commit()

    def mark_many_seen(self, items: list[dict[str, Any]], stream: str) -> None:
        """Insert many seen items in one SQLite transaction."""
        rows = [
            (item["id"], stream, str(item.get("source", "")))
            for item in items
            if item.get("id")
        ]
        if not rows:
            return
        with self.conn:
            self.conn.executemany(
                "INSERT OR IGNORE INTO seen(item_id, stream, source) VALUES (?, ?, ?)",
                rows,
            )

    def seen_ids(self, item_ids: list[str]) -> set[str]:
        """Return already-seen IDs using chunked set queries instead of N SELECTs."""
        ids = [x for x in item_ids if x]
        if not ids:
            return set()

        found: set[str] = set()
        # Keep safely below SQLite's common host-parameter limit.
        for i in range(0, len(ids), 800):
            chunk = ids[i:i + 800]
            placeholders = ",".join("?" for _ in chunk)
            rows = self.conn.execute(
                f"SELECT item_id FROM seen WHERE item_id IN ({placeholders})",
                chunk,
            ).fetchall()
            found.update(row[0] for row in rows)
        return found

    def record_history(self, item: dict[str, Any], stream: str) -> None:
        """Persist metadata used for cross-source duplicate detection."""
        if not item.get("id"):
            return
        fields = history_fields(item)
        with self.conn:
            self.conn.execute(
                """
                INSERT OR IGNORE INTO dedupe_history(
                    item_id, stream, source, title, norm_title, title_hash,
                    canonical_url, cve_key, first_seen_epoch
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    item["id"],
                    stream,
                    str(item.get("source", "")),
                    str(item.get("title", "")),
                    fields["norm_title"],
                    fields["title_hash"],
                    fields["canonical_url"],
                    fields["cve_key"],
                    int(time.time()),
                ),
            )

    def record_many_history(self, items: list[dict[str, Any]], stream: str) -> None:
        rows = []
        now = int(time.time())
        for item in items:
            if not item.get("id"):
                continue
            fields = history_fields(item)
            rows.append(
                (
                    item["id"], stream, str(item.get("source", "")),
                    str(item.get("title", "")), fields["norm_title"],
                    fields["title_hash"], fields["canonical_url"],
                    fields["cve_key"], now,
                )
            )
        if not rows:
            return
        with self.conn:
            self.conn.executemany(
                """
                INSERT OR IGNORE INTO dedupe_history(
                    item_id, stream, source, title, norm_title, title_hash,
                    canonical_url, cve_key, first_seen_epoch
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                rows,
            )

    def record_review_history(self, item: dict[str, Any], stream: str) -> None:
        """Track internal/manual-review candidates without blocking later trusted reports."""
        if not item.get("id"):
            return
        fields = history_fields(item)
        with self.conn:
            self.conn.execute(
                """
                INSERT OR IGNORE INTO manual_review_history(
                    item_id, stream, source, title, norm_title, title_hash,
                    canonical_url, cve_key, first_seen_epoch
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    item["id"], stream, str(item.get("source", "")),
                    str(item.get("title", "")), fields["norm_title"],
                    fields["title_hash"], fields["canonical_url"],
                    fields["cve_key"], int(time.time()),
                ),
            )
            cutoff = int(time.time()) - MANUAL_REVIEW_HISTORY_HOURS * 3600
            self.conn.execute(
                "DELETE FROM manual_review_history WHERE first_seen_epoch < ?",
                (cutoff,),
            )

    def review_history_count(self) -> int:
        row = self.conn.execute("SELECT COUNT(*) FROM manual_review_history").fetchone()
        return int(row[0]) if row else 0

    def delete_review_history(self, item_id: str) -> None:
        if not item_id:
            return
        with self.conn:
            self.conn.execute(
                "DELETE FROM manual_review_history WHERE item_id=?",
                (item_id,),
            )

    def save_publication_review(
        self,
        source_message_id: int,
        source_channel_id: int,
        route: str,
        priority_name: str,
        item: dict[str, Any],
        status: str = "pending",
    ) -> None:
        now = int(time.time())
        with self.conn:
            self.conn.execute(
                """
                INSERT INTO publication_review_queue(
                    source_message_id, source_channel_id, route, priority_name,
                    status, item_json, hub_message_id, reviewed_by, created_epoch, updated_epoch
                ) VALUES (?, ?, ?, ?, ?, ?, 0, 0, ?, ?)
                ON CONFLICT(source_message_id) DO UPDATE SET
                    source_channel_id=excluded.source_channel_id,
                    route=excluded.route,
                    priority_name=excluded.priority_name,
                    item_json=excluded.item_json,
                    updated_epoch=excluded.updated_epoch
                """,
                (
                    int(source_message_id), int(source_channel_id), route, priority_name,
                    status, queue_item_json(item), now, now,
                ),
            )

    def get_publication_review(self, source_message_id: int) -> dict[str, Any] | None:
        row = self.conn.execute(
            """SELECT source_message_id, source_channel_id, route, priority_name,
                      status, item_json, hub_message_id, reviewed_by, created_epoch, updated_epoch
               FROM publication_review_queue WHERE source_message_id=?""",
            (int(source_message_id),),
        ).fetchone()
        if not row:
            return None
        try:
            item = json.loads(row[5] or "{}")
        except Exception:
            item = {}
        return {
            "source_message_id": int(row[0]),
            "source_channel_id": int(row[1]),
            "route": row[2] or "news",
            "priority_name": row[3] or "NEWS",
            "status": row[4] or "pending",
            "item": item if isinstance(item, dict) else {},
            "hub_message_id": int(row[6] or 0),
            "reviewed_by": int(row[7] or 0),
            "created_epoch": int(row[8] or 0),
            "updated_epoch": int(row[9] or 0),
        }

    def update_publication_review(
        self,
        source_message_id: int,
        *,
        status: str | None = None,
        hub_message_id: int | None = None,
        reviewed_by: int | None = None,
        item: dict[str, Any] | None = None,
    ) -> None:
        current = self.get_publication_review(source_message_id)
        if current is None:
            return
        with self.conn:
            self.conn.execute(
                """UPDATE publication_review_queue
                   SET status=?, hub_message_id=?, reviewed_by=?, item_json=?, updated_epoch=?
                   WHERE source_message_id=?""",
                (
                    status if status is not None else current["status"],
                    int(hub_message_id if hub_message_id is not None else current["hub_message_id"]),
                    int(reviewed_by if reviewed_by is not None else current["reviewed_by"]),
                    queue_item_json(item) if item is not None else queue_item_json(current["item"]),
                    int(time.time()), int(source_message_id),
                ),
            )

    def publication_review_count(self, statuses: tuple[str, ...] = ("pending", "later")) -> int:
        if not statuses:
            return 0
        placeholders = ",".join("?" for _ in statuses)
        row = self.conn.execute(
            f"SELECT COUNT(*) FROM publication_review_queue WHERE status IN ({placeholders})",
            statuses,
        ).fetchone()
        return int(row[0]) if row else 0

    def find_review_duplicate(self, item: dict[str, Any]) -> dict[str, Any] | None:
        """Suppress repeated low-confidence review posts without poisoning trusted history."""
        if not DEDUP_ENABLED or not item.get("id"):
            return None
        f = history_fields(item)
        item_id = item["id"]
        cutoff = int(time.time()) - MANUAL_REVIEW_HISTORY_HOURS * 3600

        def as_match(row, reason: str, score: float = 1.0):
            if not row:
                return None
            return {
                "item_id": row[0],
                "source": row[1] or "",
                "title": row[2] or "",
                "reason": reason,
                "score": score,
            }

        if f["canonical_url"]:
            row = self.conn.execute(
                """SELECT item_id, source, title FROM manual_review_history
                   WHERE canonical_url=? AND item_id<>? AND first_seen_epoch>=?
                   ORDER BY first_seen_epoch DESC LIMIT 1""",
                (f["canonical_url"], item_id, cutoff),
            ).fetchone()
            if row:
                return as_match(row, "same review URL")

        if f["title_hash"]:
            row = self.conn.execute(
                """SELECT item_id, source, title FROM manual_review_history
                   WHERE title_hash=? AND item_id<>? AND first_seen_epoch>=?
                   ORDER BY first_seen_epoch DESC LIMIT 1""",
                (f["title_hash"], item_id, cutoff),
            ).fetchone()
            if row:
                return as_match(row, "same review title")

        norm = f["norm_title"]
        tokens = _title_tokens(norm)
        if not norm or len(tokens) < 3:
            return None
        rows = self.conn.execute(
            """SELECT item_id, source, title, norm_title FROM manual_review_history
               WHERE first_seen_epoch>=? AND item_id<>? AND norm_title<>''
               ORDER BY first_seen_epoch DESC LIMIT ?""",
            (cutoff, item_id, DEDUP_FUZZY_CANDIDATES),
        ).fetchall()
        for row in rows:
            old_norm = row[3] or ""
            old_tokens = _title_tokens(old_norm)
            if not old_tokens:
                continue
            overlap = len(tokens & old_tokens)
            min_tokens = min(len(tokens), len(old_tokens))
            needed = max(3, math.ceil(min_tokens * 0.55))
            if overlap < needed:
                continue
            score = title_similarity(norm, old_norm)
            if score >= DEDUP_FUZZY_THRESHOLD:
                return as_match(row[:3], "similar manual-review headline", score)
        return None

    def history_count(self) -> int:
        row = self.conn.execute("SELECT COUNT(*) FROM dedupe_history").fetchone()
        return int(row[0]) if row else 0

    def find_duplicate(self, item: dict[str, Any]) -> dict[str, Any] | None:
        """Find a previously-published equivalent item across all streams/sources.

        Exact URL/title matches are permanent. Fuzzy title matching is bounded to
        a configurable recent-history window to avoid treating a genuinely new
        development months later as the same story. Same-CVE matching gets its
        own shorter window and a lower threshold, while still requiring headline
        similarity so "PoC released" and "CISA adds to KEV" remain distinct.
        """
        if not DEDUP_ENABLED or not item.get("id"):
            return None

        f = history_fields(item)
        item_id = item["id"]

        def as_match(row, reason: str, score: float = 1.0):
            if not row:
                return None
            return {
                "item_id": row[0],
                "source": row[1] or "",
                "title": row[2] or "",
                "reason": reason,
                "score": score,
            }

        if f["canonical_url"]:
            row = self.conn.execute(
                """
                SELECT item_id, source, title
                FROM dedupe_history
                WHERE canonical_url=? AND item_id<>?
                ORDER BY first_seen_epoch DESC LIMIT 1
                """,
                (f["canonical_url"], item_id),
            ).fetchone()
            if row:
                return as_match(row, "same canonical URL")

        if f["title_hash"]:
            row = self.conn.execute(
                """
                SELECT item_id, source, title
                FROM dedupe_history
                WHERE title_hash=? AND item_id<>?
                ORDER BY first_seen_epoch DESC LIMIT 1
                """,
                (f["title_hash"], item_id),
            ).fetchone()
            if row:
                return as_match(row, "same normalized title")

        norm = f["norm_title"]
        tokens = _title_tokens(norm)
        if not norm or len(tokens) < 3:
            return None

        now = int(time.time())

        # CVE-aware comparison: narrower time window and cheaper candidate set.
        if f["cve_key"]:
            cutoff = now - (DEDUP_SAME_CVE_HOURS * 3600)
            rows = self.conn.execute(
                """
                SELECT item_id, source, title, norm_title
                FROM dedupe_history
                WHERE cve_key=? AND first_seen_epoch>=? AND item_id<>?
                ORDER BY first_seen_epoch DESC
                LIMIT ?
                """,
                (f["cve_key"], cutoff, item_id, DEDUP_FUZZY_CANDIDATES),
            ).fetchall()
            for row in rows:
                score = title_similarity(norm, row[3] or "")
                if score >= DEDUP_CVE_THRESHOLD:
                    return as_match(row[:3], "same CVE + similar headline", score)

        # Generic cross-source fuzzy match against recent history. Exact URL/title
        # checks above remain permanent; only fuzzy similarity has an age window.
        cutoff = now - (DEDUP_HISTORY_DAYS * 86400)
        rows = self.conn.execute(
            """
            SELECT item_id, source, title, norm_title
            FROM dedupe_history
            WHERE first_seen_epoch>=? AND item_id<>? AND norm_title<>''
            ORDER BY first_seen_epoch DESC
            LIMIT ?
            """,
            (cutoff, item_id, DEDUP_FUZZY_CANDIDATES),
        ).fetchall()

        for row in rows:
            old_norm = row[3] or ""
            old_tokens = _title_tokens(old_norm)
            if not old_tokens:
                continue
            overlap = len(tokens & old_tokens)
            # Cheap prefilter before SequenceMatcher. Headlines need at least
            # three meaningful shared tokens and substantial token containment.
            min_tokens = min(len(tokens), len(old_tokens))
            needed = max(3, math.ceil(min_tokens * 0.55))
            if overlap < needed:
                continue
            score = title_similarity(norm, old_norm)
            if score >= DEDUP_FUZZY_THRESHOLD:
                return as_match(row[:3], "similar headline in history", score)

        return None

    @staticmethod
    def _decode_corrob(value: str | None) -> list[str]:
        try:
            data = json.loads(value or "[]")
            return [str(x) for x in data if str(x).strip()] if isinstance(data, list) else []
        except Exception:
            return []

    @staticmethod
    def _queue_row(row) -> dict[str, Any] | None:
        if not row:
            return None
        item = {}
        try:
            parsed = json.loads(row[14] or "{}")
            if isinstance(parsed, dict):
                item = parsed
        except Exception:
            item = {}
        return {
            "message_id": int(row[0]),
            "channel_id": int(row[1]),
            "priority": int(row[2]),
            "category": row[3] or "",
            "title": row[4] or "",
            "attempts": int(row[5] or 0),
            "incident_key": row[6] or "",
            "norm_title": row[7] or "",
            "canonical_url": row[8] or "",
            "cve_key": row[9] or "",
            "development_kind": row[10] or "",
            "source": row[11] or "",
            "quality_score": int(row[12] or 0),
            "strength": int(row[13] or 0),
            "item": item,
            "corroborators": ThreatDB._decode_corrob(row[15]),
            "updated_epoch": int(row[16] or 0),
        }

    def enqueue_announcement(
        self,
        message_id: int,
        channel_id: int,
        priority: int,
        category: str,
        title: str,
        item: dict[str, Any],
        priority_name: str,
        corroborators: list[str] | None = None,
    ) -> None:
        f = history_fields(item)
        source = str(item.get("source", ""))
        quality = queue_quality_score(item, priority_name)
        strength = announcement_strength(item, priority_name)
        corrob = list(dict.fromkeys([x for x in (corroborators or []) if x and x != source]))
        now = int(time.time())
        with self.conn:
            self.conn.execute(
                """
                INSERT OR IGNORE INTO announcement_queue(
                    message_id, channel_id, priority, category, title, incident_key,
                    norm_title, canonical_url, cve_key, development_kind, source,
                    quality_score, strength, item_json, corroborators, updated_epoch
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    message_id, channel_id, priority, category, title, incident_key(item),
                    f["norm_title"], f["canonical_url"], f["cve_key"], development_kind(item),
                    source, quality, strength, queue_item_json(item),
                    json.dumps(corrob, ensure_ascii=False), now,
                ),
            )

    def next_announcement(self) -> dict[str, Any] | None:
        row = self.conn.execute(
            """
            SELECT message_id, channel_id, priority, category, title, attempts,
                   incident_key, norm_title, canonical_url, cve_key, development_kind,
                   source, quality_score, strength, item_json, corroborators, updated_epoch
            FROM announcement_queue
            ORDER BY priority ASC, created_at ASC
            LIMIT 1
            """
        ).fetchone()
        return self._queue_row(row)

    def queued_announcements(self, exclude_message_id: int = 0) -> list[dict[str, Any]]:
        rows = self.conn.execute(
            """
            SELECT message_id, channel_id, priority, category, title, attempts,
                   incident_key, norm_title, canonical_url, cve_key, development_kind,
                   source, quality_score, strength, item_json, corroborators, updated_epoch
            FROM announcement_queue
            WHERE message_id<>?
            ORDER BY priority ASC, created_at ASC
            LIMIT ?
            """,
            (int(exclude_message_id or 0), ANNOUNCEMENT_QUEUE_MAX_CANDIDATES),
        ).fetchall()
        return [x for x in (self._queue_row(row) for row in rows) if x is not None]

    def find_queued_conflicts(
        self, item: dict[str, Any], route: str, exclude_message_id: int = 0
    ) -> list[dict[str, Any]]:
        """Return not-yet-crossposted messages that appear to be the same development."""
        f = history_fields(item)
        ikey = incident_key(item)
        kind = development_kind(item)
        norm = f["norm_title"]
        out: list[dict[str, Any]] = []

        for row in self.queued_announcements(exclude_message_id):
            reason = ""
            score = 0.0
            if ikey and row["incident_key"] == ikey:
                reason, score = "same incident fingerprint", 1.0
            elif f["canonical_url"] and row["canonical_url"] == f["canonical_url"]:
                reason, score = "same canonical URL", 1.0
            elif (
                f["cve_key"] and row["cve_key"] == f["cve_key"]
                and row["development_kind"] == kind
            ):
                reason, score = "same CVE development", 0.99
            elif norm and row["norm_title"] and row["category"] == route:
                sim = title_similarity(norm, row["norm_title"])
                if sim >= ANNOUNCEMENT_QUEUE_DEDUP_THRESHOLD:
                    reason, score = "similar queued headline", sim
            if reason:
                row = dict(row)
                row["match_reason"] = reason
                row["match_score"] = score
                out.append(row)
        return out

    def update_announcement(
        self,
        message_id: int,
        *,
        priority: int | None = None,
        category: str | None = None,
        title: str | None = None,
        item: dict[str, Any] | None = None,
        priority_name: str | None = None,
        corroborators: list[str] | None = None,
    ) -> None:
        current = next((x for x in self.queued_announcements(0) if x["message_id"] == message_id), None)
        if current is None:
            # queued_announcements may be capped; fetch this exact row directly.
            row = self.conn.execute(
                """SELECT message_id, channel_id, priority, category, title, attempts,
                          incident_key, norm_title, canonical_url, cve_key, development_kind,
                          source, quality_score, strength, item_json, corroborators, updated_epoch
                   FROM announcement_queue WHERE message_id=?""",
                (message_id,),
            ).fetchone()
            current = self._queue_row(row)
        if current is None:
            return

        new_item = item or current.get("item") or {}
        pri_name = priority_name or next(
            (name for name, value in ANNOUNCEMENT_PRIORITY.items() if value == (priority if priority is not None else current["priority"])),
            "NEWS",
        )
        f = history_fields(new_item) if new_item else {
            "norm_title": current["norm_title"], "canonical_url": current["canonical_url"],
            "cve_key": current["cve_key"], "title_hash": "",
        }
        source = str(new_item.get("source", current["source"])) if new_item else current["source"]
        corrob = list(dict.fromkeys([
            x for x in (corroborators if corroborators is not None else current["corroborators"])
            if x and x != source
        ]))
        q = queue_quality_score(new_item, pri_name) if new_item else current["quality_score"]
        strength = announcement_strength(new_item, pri_name) if new_item else current["strength"]
        with self.conn:
            self.conn.execute(
                """
                UPDATE announcement_queue SET
                    priority=?, category=?, title=?, incident_key=?, norm_title=?,
                    canonical_url=?, cve_key=?, development_kind=?, source=?,
                    quality_score=?, strength=?, item_json=?, corroborators=?, updated_epoch=?
                WHERE message_id=?
                """,
                (
                    priority if priority is not None else current["priority"],
                    category if category is not None else current["category"],
                    title if title is not None else current["title"],
                    incident_key(new_item) if new_item else current["incident_key"],
                    f["norm_title"], f["canonical_url"], f["cve_key"],
                    development_kind(new_item) if new_item else current["development_kind"],
                    source, q, strength, queue_item_json(new_item) if new_item else json.dumps(current["item"]),
                    json.dumps(corrob, ensure_ascii=False), int(time.time()), message_id,
                ),
            )

    def delete_announcement(self, message_id: int) -> None:
        with self.conn:
            self.conn.execute(
                "DELETE FROM announcement_queue WHERE message_id=?",
                (message_id,),
            )

    def bump_announcement_attempt(self, message_id: int) -> None:
        with self.conn:
            self.conn.execute(
                "UPDATE announcement_queue SET attempts=attempts+1 WHERE message_id=?",
                (message_id,),
            )

    def announcement_queue_size(self) -> int:
        row = self.conn.execute(
            "SELECT COUNT(*) FROM announcement_queue"
        ).fetchone()
        return int(row[0]) if row else 0

    def increment(self, key: str, amount: int = 1) -> int:
        try:
            current = int(self.get(key, "0") or 0)
        except ValueError:
            current = 0
        current += amount
        self.set(key, str(current))
        return current

    def get(self, key: str, default: str | None = None) -> str | None:
        row = self.conn.execute("SELECT value FROM kv WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    def set(self, key: str, value: str) -> None:
        self.conn.execute(
            "INSERT OR REPLACE INTO kv(key, value) VALUES (?, ?)",
            (key, value),
        )
        self.conn.commit()

    def initialized(self, stream: str) -> bool:
        return self.get(f"initialized:{stream}") == "1"

    def set_initialized(self, stream: str) -> None:
        self.set(f"initialized:{stream}", "1")


db = ThreatDB(DB_PATH)

# Runtime-only feed telemetry/backoff. Persistent item/dedupe state remains in SQLite.
FEED_VISIT_COUNTS: dict[str, int] = {}
FEED_FETCH_COUNTS: dict[str, int] = {}
FEED_FAILURE_COUNTS: dict[str, int] = {}
FEED_BACKOFF_UNTIL: dict[str, float] = {}

def _feed_runtime_key(source: str, url: str) -> str:
    return f"{source}|{url}"

def _retry_after_seconds(exc: Exception) -> int | None:
    headers = getattr(exc, "headers", None)
    if not headers:
        return None
    raw = headers.get("Retry-After")
    if not raw:
        return None
    try:
        return max(1, int(float(raw)))
    except Exception:
        return None


# ---------------------------------------------------------------------------
# HTTP helpers
# ---------------------------------------------------------------------------

async def fetch_bytes(session: aiohttp.ClientSession, url: str) -> bytes:
    async with session.get(
        url,
        headers={"User-Agent": USER_AGENT},
        allow_redirects=True,
    ) as response:
        response.raise_for_status()
        return await response.read()


async def fetch_text(session: aiohttp.ClientSession, url: str) -> str:
    async with session.get(
        url,
        headers={"User-Agent": USER_AGENT},
        allow_redirects=True,
    ) as response:
        response.raise_for_status()
        return await response.text(errors="replace")


async def fetch_json(session: aiohttp.ClientSession, url: str, **kwargs) -> dict[str, Any]:
    headers = {"User-Agent": USER_AGENT, "Accept": "application/json"}
    headers.update(kwargs.pop("headers", {}))
    async with session.get(url, headers=headers, allow_redirects=True, **kwargs) as response:
        response.raise_for_status()
        # Some public APIs use imperfect content types.
        return json.loads(await response.text())


# ---------------------------------------------------------------------------
# Generic RSS / Atom collectors
# ---------------------------------------------------------------------------

async def collect_feed(
    session: aiohttp.ClientSession,
    source: str,
    url: str,
    route: str = "news",
    limit: int = 30,
    *,
    custom_feed: bool = False,
    prefer_entry_publisher: bool = False,
) -> list[dict[str, Any]]:
    key = _feed_runtime_key(source, url)
    FEED_VISIT_COUNTS[key] = FEED_VISIT_COUNTS.get(key, 0) + 1
    visit_no = FEED_VISIT_COUNTS[key]
    now_mono = time.monotonic()
    backoff_until = FEED_BACKOFF_UNTIL.get(key, 0.0)
    if backoff_until > now_mono:
        remaining = int(backoff_until - now_mono + 0.999)
        if FEED_TRAVERSAL_LOGS:
            log.info(
                "[feed visit=%d fetch=%d] SKIP backoff source=%s route=%s remaining=%ss",
                visit_no, FEED_FETCH_COUNTS.get(key, 0), source, route, remaining,
            )
        return []

    FEED_FETCH_COUNTS[key] = FEED_FETCH_COUNTS.get(key, 0) + 1
    fetch_no = FEED_FETCH_COUNTS[key]
    started = time.monotonic()
    try:
        raw = await asyncio.wait_for(
            fetch_bytes(session, url), timeout=FEED_HTTP_TIMEOUT_SECONDS
        )
    except Exception as exc:
        failures = FEED_FAILURE_COUNTS.get(key, 0) + 1
        FEED_FAILURE_COUNTS[key] = failures
        retry_after = _retry_after_seconds(exc)
        status = getattr(exc, "status", None)
        if status == 429:
            delay = retry_after or max(300, FEED_BACKOFF_BASE_SECONDS)
        else:
            delay = min(
                FEED_BACKOFF_MAX_SECONDS,
                FEED_BACKOFF_BASE_SECONDS * (2 ** min(failures - 1, 5)),
            )
        FEED_BACKOFF_UNTIL[key] = time.monotonic() + delay
        elapsed = time.monotonic() - started
        log.warning(
            "[feed visit=%d fetch=%d] FAILED source=%s route=%s after=%.2fs backoff=%ss error=%s",
            visit_no, fetch_no, source, route, elapsed, delay, exc,
        )
        return []

    FEED_FAILURE_COUNTS[key] = 0
    FEED_BACKOFF_UNTIL.pop(key, None)
    parsed = feedparser.parse(raw)
    if getattr(parsed, "bozo", False):
        log.debug("Feed parser warning [%s]: %s", source, getattr(parsed, "bozo_exception", ""))

    provider = feed_provider_name(url)
    feed_title = normalize_publisher_name(str(getattr(parsed, "feed", {}).get("title", "")))
    configured_publisher = normalize_publisher_name(source)

    items: list[dict[str, Any]] = []
    for entry in parsed.entries[:limit]:
        title = strip_html(entry.get("title", "Security update"))

        # RSS.app normally exposes the original article URL as entry.link. When a
        # provider/redirect URL is used, also inspect alternate links and anchors
        # embedded in the entry body and prefer a non-RSS.app HTTP(S) target.
        candidate_links: list[str] = []
        if entry.get("link"):
            candidate_links.append(str(entry.get("link")))
        for link_obj in entry.get("links", []) or []:
            href = str((link_obj or {}).get("href", ""))
            if href:
                candidate_links.append(href)
        raw_blobs = [
            str(entry.get("summary", "")),
            str(entry.get("description", "")),
        ]
        for content_obj in entry.get("content", []) or []:
            raw_blobs.append(str((content_obj or {}).get("value", "")))
        for blob in raw_blobs:
            if not blob:
                continue
            try:
                for a in BeautifulSoup(blob, "html.parser").find_all("a", href=True):
                    candidate_links.append(str(a.get("href", "")))
            except Exception:
                pass

        link = ""
        fallback_link = ""
        for candidate in candidate_links:
            if not candidate.startswith(("http://", "https://")):
                continue
            if not fallback_link:
                fallback_link = candidate
            try:
                host = (urlsplit(candidate).hostname or "").lower()
            except Exception:
                host = ""
            if host and not (host == "rss.app" or host.endswith(".rss.app")):
                # Avoid accidentally choosing an image/CDN asset from HTML.
                if not re.search(r"\.(?:png|jpe?g|gif|webp|svg|ico)(?:\?|$)", candidate, re.I):
                    link = candidate
                    break
        link = link or fallback_link or str(entry.get("link", ""))

        summary = strip_html(
            entry.get("summary", "")
            or entry.get("description", "")
            or entry.get("content", [{}])[0].get("value", "")
            if entry.get("content")
            else entry.get("summary", "") or entry.get("description", "")
        )
        unique = entry.get("id") or entry.get("guid") or link or title
        text = f"{title} {summary}"
        parsed_time = entry.get("published_parsed") or entry.get("updated_parsed")
        published_epoch = calendar.timegm(parsed_time) if parsed_time else None

        entry_publisher = ""
        try:
            entry_publisher = normalize_publisher_name(str((entry.get("source") or {}).get("title", "")))
        except Exception:
            entry_publisher = ""
        url_publisher = publisher_from_url(link)

        # For built-in feeds, the configured name remains authoritative. For
        # RSS.app/custom feeds, use the original publisher when detectable. An
        # explicitly configured Name|URL label that matches a known reputation
        # entry is preferred for single-publisher feeds.
        if not prefer_entry_publisher:
            actual_source = configured_publisher or source
        elif configured_publisher in SOURCE_REPUTATION:
            actual_source = configured_publisher
        else:
            actual_source = url_publisher or entry_publisher or feed_title or configured_publisher or source

        items.append(
            {
                "id": stable_id(source, str(unique)),
                "source": actual_source,
                "publisher": entry_publisher or url_publisher,
                "collector_source": source,
                "feed_provider": provider,
                "custom_feed": custom_feed,
                "type": "ARTICLE",
                "route_hint": route,
                "title": title,
                "summary": summary,
                "url": link,
                "published": entry.get("published") or entry.get("updated") or "",
                "published_epoch": published_epoch,
                "cves": extract_cves(text),
            }
        )

    if FEED_TRAVERSAL_LOGS:
        elapsed = time.monotonic() - started
        seen_ids = db.seen_ids([x["id"] for x in items]) if items else set()
        unseen = sum(1 for x in items if x["id"] not in seen_ids)
        newest = items[0] if items else None
        newest_title = truncate(str(newest.get("title", "")), 85) if newest else "(empty feed)"
        published = str(newest.get("published", "")) if newest else ""
        log.info(
            "[feed visit=%d fetch=%d] OK source=%s route=%s entries=%d unseen=%d elapsed=%.2fs provider=%s newest=%s%s",
            visit_no, fetch_no, source, route, len(items), unseen, elapsed, provider, newest_title,
            f" | published={truncate(published, 55)}" if published else "",
        )
        if FEED_TRACE_TITLES > 0 and items:
            for idx, candidate in enumerate(items[:FEED_TRACE_TITLES], start=1):
                state = "SEEN" if candidate["id"] in seen_ids else "NEW"
                try:
                    preview_score = security_quality(candidate)[0]
                except Exception:
                    preview_score = -1
                log.info(
                    "[feed-item %s %d/%d] source=%s score=%s title=%s",
                    state, idx, min(FEED_TRACE_TITLES, len(items)),
                    candidate.get("source", source),
                    preview_score if preview_score >= 0 else "?",
                    truncate(candidate.get("title", ""), 115),
                )
    return items


async def collect_all_standard_rss(session: aiohttp.ClientSession) -> list[dict[str, Any]]:
    builtin_jobs = []
    if ENABLE_BUILTIN_RSS:
        builtin_jobs = [
            collect_feed(session, source, url, route)
            for source, url, route in BUILTIN_RSS_FEEDS
        ]

    custom_specs: list[tuple[str, str, str]] = []
    for label, url in NEWS_RSS_FEEDS:
        custom_specs.append((label, url, "news"))
    for label, url in RESEARCH_RSS_FEEDS:
        custom_specs.append((label, url, "research"))
    for label, url in INDIA_RSS_FEEDS:
        custom_specs.append((label, url, "india"))
    for label, url in BREACH_RSS_FEEDS:
        custom_specs.append((label, url, "breach"))

    custom_jobs = [
        collect_feed(
            session,
            label,
            url,
            route,
            custom_feed=True,
            prefer_entry_publisher=True,
        )
        for label, url, route in custom_specs
    ]

    discovery_jobs = [
        collect_feed(session, source, url, "india", custom_feed=True, prefer_entry_publisher=True)
        for source, url in INDIA_NEWS_FEEDS
    ] if ENABLE_DISCOVERY_NEWS else []

    breach_discovery_jobs = [
        collect_feed(session, source, url, "breach", custom_feed=True, prefer_entry_publisher=True)
        for source, url in BREACH_SEARCH_FEEDS
    ] if ENABLE_BREACH_DISCOVERY_RSS else []

    builtin_results, custom_results, discovery_results, breach_discovery_results = await asyncio.gather(
        asyncio.gather(*builtin_jobs, return_exceptions=True),
        asyncio.gather(*custom_jobs, return_exceptions=True),
        asyncio.gather(*discovery_jobs, return_exceptions=True),
        asyncio.gather(*breach_discovery_jobs, return_exceptions=True),
    )

    output: list[dict[str, Any]] = []
    for group_name, results in (("built-in RSS", builtin_results), ("custom RSS", custom_results)):
        for result in results:
            if isinstance(result, Exception):
                log.warning("%s collector task failed: %s", group_name, result)
                continue
            for item in result:
                # Custom/RSS.app feeds are discovery inputs. They must still pass
                # the cybersecurity relevance gate before the quality scorer.
                if item.get("custom_feed") and not is_relevant_security_item(item):
                    log.debug(
                        "[custom-rss] non-cyber candidate rejected: %s",
                        truncate(item.get("title", ""), 110),
                    )
                    continue
                output.append(item)

    rejected = 0
    for result in discovery_results:
        if isinstance(result, Exception):
            log.warning("Discovery RSS task failed: %s", result)
            continue
        for item in result:
            if is_relevant_security_item(item):
                output.append(item)
            else:
                rejected += 1

    for result in breach_discovery_results:
        if isinstance(result, Exception):
            log.warning("Breach discovery RSS task failed: %s", result)
            continue
        for item in result:
            # Require explicit breach/ransomware semantics, not ambiguous standalone
            # words such as "breach" or "attack". Normal quality scoring follows.
            if is_relevant_security_item(item) and matches_any(BREACH_ROUTE_PATTERNS, item_text(item)):
                output.append(item)
            else:
                rejected += 1

    if rejected:
        log.debug("Filtered %d non-cyber/weak discovery RSS item(s).", rejected)
    return output


async def collect_poc_feeds(session: aiohttp.ClientSession) -> list[dict[str, Any]]:
    jobs = [
        collect_feed(session, source, url, "poc", limit=40)
        for source, url in POC_FEEDS
    ]
    jobs.extend(
        collect_feed(
            session,
            label,
            url,
            "poc",
            limit=40,
            custom_feed=True,
            prefer_entry_publisher=True,
        )
        for label, url in EXPLOIT_RSS_FEEDS
    )

    results = await asyncio.gather(*jobs, return_exceptions=True)
    output: list[dict[str, Any]] = []
    for result in results:
        if isinstance(result, Exception):
            log.warning("PoC feed task failed: %s", result)
            continue
        for item in result:
            item["type"] = "POC"
            item["route_hint"] = "poc"
            # Preserve the original v7 warning for public PoC/index feeds.
            item["poc_warning"] = "Public PoC/index reference; validate independently before use."
            output.append(item)
    return output


# ---------------------------------------------------------------------------
# CERT-In collector
# ---------------------------------------------------------------------------

async def collect_certin_list(
    session: aiohttp.ClientSession, list_url: str
) -> list[dict[str, Any]]:
    try:
        page = await fetch_text(session, list_url)
    except Exception as exc:
        log.warning("CERT-In list failed %s: %s", list_url, exc)
        return []

    soup = BeautifulSoup(page, "html.parser")
    found: dict[str, dict[str, Any]] = {}

    for a in soup.find_all("a", href=True):
        anchor_text = a.get_text(" ", strip=True)
        nearby = a.parent.get_text(" ", strip=True) if a.parent else anchor_text
        combined = f"{anchor_text} {nearby} {a.get('href', '')}"

        m = re.search(r"\b(?:CIVN|CIAD)-\d{4}-\d+\b", combined, re.I)
        if not m:
            continue

        cert_id = m.group(0).upper()
        href = urljoin(list_url, a["href"])
        title = truncate(nearby or anchor_text or cert_id, 300)

        found[cert_id] = {
            "id": stable_id("CERT-In", cert_id),
            "source": "CERT-In",
            "type": "CERTIN",
            "route_hint": "india",
            "cert_id": cert_id,
            "title": title,
            "summary": "",
            "url": href,
            "cves": extract_cves(combined),
        }

    return list(found.values())


async def enrich_certin(
    session: aiohttp.ClientSession, item: dict[str, Any]
) -> dict[str, Any]:
    try:
        page = await fetch_text(session, item["url"])
    except Exception as exc:
        log.warning("CERT-In detail failed %s: %s", item.get("url"), exc)
        return item

    soup = BeautifulSoup(page, "html.parser")
    text = soup.get_text(" ", strip=True)

    severity = re.search(
        r"Severity\s*Rating\s*:?\s*(Critical|High|Medium|Low)",
        text,
        re.I,
    )
    if severity:
        item["official_severity"] = severity.group(1).title()

    cves = extract_cves(text)
    if cves:
        item["cves"] = cves

    # Prefer the Overview / Description region when available.
    overview = re.search(
        r"(?:Overview|Description)\s*:?\s*(.{80,1400}?)(?:Solution|Mitigation|Target Audience|References|References\s*:)",
        text,
        re.I,
    )
    if overview:
        item["summary"] = truncate(overview.group(1), 1200)
    else:
        exploit_context = re.search(
            r"(.{0,220}(?:exploited in the wild|actively exploited|remote code execution|ransomware).{0,500})",
            text,
            re.I,
        )
        item["summary"] = truncate(
            exploit_context.group(1) if exploit_context else text,
            1200,
        )

    return item


async def collect_certin(session: aiohttp.ClientSession) -> list[dict[str, Any]]:
    results = await asyncio.gather(
        *[collect_certin_list(session, url) for url in CERTIN_LIST_URLS],
        return_exceptions=True,
    )
    merged: dict[str, dict[str, Any]] = {}
    for result in results:
        if isinstance(result, Exception):
            log.warning("CERT-In task failed: %s", result)
            continue
        for item in result:
            merged[item["cert_id"]] = item
    return list(merged.values())



# ---------------------------------------------------------------------------
# CISA KEV + CVE enrichment
# ---------------------------------------------------------------------------

async def get_cisa_kev(session: aiohttp.ClientSession) -> dict[str, Any] | None:
    for url in CISA_KEV_URLS:
        try:
            data = await fetch_json(session, url)
            if isinstance(data.get("vulnerabilities"), list):
                return data
        except Exception as exc:
            log.warning("CISA KEV source failed %s: %s", url, exc)
    return None


def cisa_items(data: dict[str, Any]) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for vuln in data.get("vulnerabilities", []):
        cve = str(vuln.get("cveID", "")).upper()
        if not cve:
            continue

        vendor = vuln.get("vendorProject", "")
        product = vuln.get("product", "")
        name = vuln.get("vulnerabilityName", "")
        title = f"{cve} — {vendor} {product}".strip(" —")

        output.append(
            {
                "id": stable_id("CISA KEV", cve),
                "source": "CISA KEV",
                "type": "KEV",
                "route_hint": "critical",
                "title": title,
                "summary": vuln.get("shortDescription", "") or name,
                "url": "https://www.cisa.gov/known-exploited-vulnerabilities-catalog",
                "cves": [cve],
                "cve": cve,
                "kev": True,
                "date_added": vuln.get("dateAdded", ""),
                "due_date": vuln.get("dueDate", ""),
                "required_action": vuln.get("requiredAction", ""),
                "ransomware": vuln.get("knownRansomwareCampaignUse", ""),
            }
        )
    return output


async def fetch_epss(
    session: aiohttp.ClientSession, cve: str
) -> dict[str, Any]:
    try:
        data = await fetch_json(session, EPSS_API, params={"cve": cve})
        rows = data.get("data", [])
        if not rows:
            return {}
        row = rows[0]
        return {
            "epss": float(row.get("epss", 0.0)),
            "epss_percentile": float(row.get("percentile", 0.0)),
        }
    except Exception as exc:
        log.debug("EPSS lookup failed for %s: %s", cve, exc)
        return {}


async def fetch_nvd_cvss(
    session: aiohttp.ClientSession, cve: str
) -> dict[str, Any]:
    headers = {}
    if NVD_API_KEY:
        headers["apiKey"] = NVD_API_KEY

    try:
        data = await fetch_json(
            session,
            NVD_API,
            params={"cveId": cve},
            headers=headers,
        )
        vulns = data.get("vulnerabilities", [])
        if not vulns:
            return {}

        metrics = vulns[0].get("cve", {}).get("metrics", {})
        for metric_key in (
            "cvssMetricV40",
            "cvssMetricV31",
            "cvssMetricV30",
            "cvssMetricV2",
        ):
            candidates = metrics.get(metric_key) or []
            if not candidates:
                continue
            cvss_data = candidates[0].get("cvssData", {})
            score = cvss_data.get("baseScore")
            severity = (
                cvss_data.get("baseSeverity")
                or candidates[0].get("baseSeverity")
            )
            if score is not None:
                return {
                    "cvss": score,
                    "cvss_severity": severity or "",
                    "cvss_version": cvss_data.get("version", ""),
                }
    except Exception as exc:
        log.debug("NVD lookup failed for %s: %s", cve, exc)
    return {}


# ---------------------------------------------------------------------------
# X / Twitter recent breach collector (optional)
# ---------------------------------------------------------------------------

def build_x_query() -> str:
    if X_QUERY_OVERRIDE:
        return X_QUERY_OVERRIDE

    keywords = (
        '("data breach" OR "breach notification" OR ransomware OR '
        '"security incident" OR "cyber attack" OR hacked OR compromised)'
    )

    if X_WATCH_ACCOUNTS:
        accounts = " OR ".join(f"from:{u}" for u in X_WATCH_ACCOUNTS[:10])
        return f"({accounts}) {keywords} -is:retweet lang:en"

    # Broader default; tune X_QUERY in .env if this is too noisy.
    return (
        f"{keywords} "
        '(company OR organization OR customers OR users OR systems OR vendor) '
        "-is:retweet lang:en"
    )


async def collect_x_breaches(
    session: aiohttp.ClientSession,
) -> list[dict[str, Any]]:
    if not X_BEARER_TOKEN:
        return []

    params = {
        "query": build_x_query(),
        "max_results": 100,
        "sort_order": "recency",
        "tweet.fields": "created_at,author_id,public_metrics",
        "expansions": "author_id",
        "user.fields": "username,name,verified",
    }
    headers = {
        "Authorization": f"Bearer {X_BEARER_TOKEN}",
        "User-Agent": USER_AGENT,
    }

    try:
        async with session.get(
            X_RECENT_SEARCH_URL,
            params=params,
            headers=headers,
        ) as response:
            if response.status != 200:
                body = truncate(await response.text(), 500)
                log.warning("X API returned %s: %s", response.status, body)
                return []
            data = json.loads(await response.text())
    except Exception as exc:
        log.warning("X API collection failed: %s", exc)
        return []

    users = {
        str(u.get("id")): u
        for u in data.get("includes", {}).get("users", [])
    }

    output: list[dict[str, Any]] = []
    for post in data.get("data", []):
        post_id = str(post.get("id", ""))
        if not post_id:
            continue

        author = users.get(str(post.get("author_id")), {})
        username = author.get("username", "")
        text = post.get("text", "")

        # Simple noise gate. Every output is still explicitly labeled unverified.
        if not matches_any(HIGH_PATTERNS + CRITICAL_PATTERNS + [
            r"\bdata breach\b",
            r"\bbreach notification\b",
            r"\bsecurity incident\b",
            r"\bcompromised\b",
            r"\bhacked\b",
        ], text):
            continue

        url = (
            f"https://x.com/{username}/status/{post_id}"
            if username
            else f"https://x.com/i/web/status/{post_id}"
        )

        output.append(
            {
                "id": stable_id("X", post_id),
                "source": f"X @{username}" if username else "X",
                "type": "SOCIAL",
                "route_hint": "breach",
                "title": truncate(text, 240),
                "summary": text,
                "url": url,
                "published": post.get("created_at", ""),
                "cves": extract_cves(text),
                "social_unverified": True,
            }
        )
    return output


# ---------------------------------------------------------------------------
# CTF discovery
# ---------------------------------------------------------------------------

async def collect_ctftime(
    session: aiohttp.ClientSession,
) -> list[dict[str, Any]]:
    now = int(time.time())
    finish = now + CTF_LOOKAHEAD_DAYS * 24 * 60 * 60

    try:
        data = await fetch_json(
            session,
            CTFTIME_API,
            params={"limit": 100, "start": now, "finish": finish},
        )
    except Exception as exc:
        log.warning("CTFtime failed: %s", exc)
        return []

    if not isinstance(data, list):
        return []

    output: list[dict[str, Any]] = []
    for event in data:
        event_id = str(event.get("id", ""))
        if not event_id:
            continue

        official_url = event.get("url") or ""
        ctftime_url = event.get("ctftime_url", "")
        candidate = {
            "id": stable_id("CTFtime", event_id),
            "source": "CTFtime",
            "type": "CTF",
            "title": event.get("title", "CTF event"),
            "summary": strip_html(event.get("description", "")),
            "url": official_url or ctftime_url,
            "registration_url": official_url,
            "ctftime_url": ctftime_url,
            "start": event.get("start", ""),
            "finish": event.get("finish", ""),
            "format": event.get("format", ""),
            "location": event.get("location", ""),
            "onsite": bool(event.get("onsite", False)),
            "weight": event.get("weight", 0),
            "organizer": ", ".join(
                t.get("name", "")
                for t in event.get("organizers", [])
                if t.get("name")
            ),
        }
        # CTFtime is authoritative for event timing. Running/finished events are
        # never turned into "new registration" alerts merely because they still
        # appear in the API window.
        start_epoch = parse_iso_epoch(candidate.get("start"))
        if CTF_UPCOMING_ONLY and (not start_epoch or start_epoch <= now):
            continue
        output.append(candidate)
    return output


async def collect_htb_events(
    session: aiohttp.ClientSession,
) -> list[dict[str, Any]]:
    """
    Best-effort scraper of public HTB event cards.
    CTFtime/search RSS remain the primary discovery mechanisms because
    vendor page HTML can change.
    """
    try:
        page = await fetch_text(session, HTB_EVENTS_URL)
    except Exception as exc:
        log.warning("HTB events page failed: %s", exc)
        return []

    soup = BeautifulSoup(page, "html.parser")
    found: dict[str, dict[str, Any]] = {}

    for a in soup.find_all("a", href=True):
        href = a["href"]
        if "/events/" not in href:
            continue

        parent_text = a.parent.get_text(" ", strip=True) if a.parent else ""
        title = a.get_text(" ", strip=True)
        combined = truncate(f"{title} {parent_text}", 800)

        event_url = urljoin(HTB_EVENTS_URL, href)
        candidate = {
            "source": "Hack The Box",
            "title": title or truncate(parent_text, 250),
            "summary": parent_text,
            "organizer": "Hack The Box",
            "url": event_url,
            "registration_url": event_url,
            "type": "CTF",
        }
        if not looks_like_ctf(candidate):
            continue
        combined_text = item_text(candidate)
        if matches_any(CTF_CLOSED_OR_RECAP_PATTERNS, combined_text):
            continue
        # HTB's page markup is not a stable API. Without a machine-readable date,
        # require a registration/open signal so old event cards do not leak in.
        if CTF_REQUIRE_REGISTRATION_SIGNAL and not matches_any(CTF_REGISTRATION_OPEN_PATTERNS, combined_text):
            continue
        candidate["registration_open"] = True

        key = candidate["url"]
        candidate["id"] = stable_id("Hack The Box", key)
        found[key] = candidate

    return list(found.values())


async def collect_ctf_search_rss(
    session: aiohttp.ClientSession,
) -> list[dict[str, Any]]:
    feeds = list(CTF_SEARCH_FEEDS)
    custom_labels = list(CTF_RSS_FEEDS)
    custom_labels += [
        (f"Legacy Custom CTF RSS {i+1}", url)
        for i, url in enumerate(LEGACY_CUSTOM_CTF_RSS)
    ]

    jobs = [
        collect_feed(session, source, url, "ctf", limit=30)
        for source, url in feeds
    ]
    jobs.extend(
        collect_feed(
            session,
            label,
            url,
            "ctf",
            limit=30,
            custom_feed=True,
            prefer_entry_publisher=True,
        )
        for label, url in custom_labels
    )

    results = await asyncio.gather(*jobs, return_exceptions=True)

    output: list[dict[str, Any]] = []
    for result in results:
        if isinstance(result, Exception):
            log.warning("CTF search feed task failed: %s", result)
            continue
        for item in result:
            item["type"] = "CTF"
            if not looks_like_ctf(item):
                continue
            text = item_text(item)
            if matches_any(CTF_CLOSED_OR_RECAP_PATTERNS, text):
                continue
            if CTF_REQUIRE_REGISTRATION_SIGNAL and not matches_any(CTF_REGISTRATION_OPEN_PATTERNS, text):
                continue
            if not article_is_fresh(item, CTF_DISCOVERY_MAX_AGE_DAYS * 24):
                continue
            item["registration_open"] = True
            item["registration_url"] = item.get("url", "")
            output.append(item)
    return output


# ---------------------------------------------------------------------------
# Discord bot
# ---------------------------------------------------------------------------

@dataclass
class ChannelMap:
    news: int = CHANNEL_NEWS
    critical: int = CHANNEL_CRITICAL
    india: int = CHANNEL_INDIA
    research: int = CHANNEL_RESEARCH
    poc: int = CHANNEL_POC
    breach: int = CHANNEL_BREACH
    ctf: int = CHANNEL_CTF


CHANNELS = ChannelMap()


CATEGORY_INFO = {
    "critical": {"emoji": "🚨", "label": "CRITICAL THREATS", "channel": "critical-threats"},
    "india": {"emoji": "🇮🇳", "label": "INDIA CYBER", "channel": "india-cyber"},
    "news": {"emoji": "📰", "label": "CYBER NEWS", "channel": "cyber-news"},
    "research": {"emoji": "🔬", "label": "SECURITY RESEARCH", "channel": "security-research"},
    "poc": {"emoji": "🧪", "label": "EXPLOIT INTEL", "channel": "exploit-intel"},
    "breach": {"emoji": "🐦", "label": "BREACH WATCH", "channel": "breach-watch"},
    "ctf": {"emoji": "🏴", "label": "CTF UPDATES", "channel": "ctf-updates"},
    "status": {"emoji": "🤖", "label": "BOT STATUS", "channel": "bot-status"},
}

# Lower number = earlier in the persistent Announcement queue.
ANNOUNCEMENT_PRIORITY = {
    "URGENT": 0,
    "CRITICAL": 5,
    "HIGH": 10,
    "NATIONAL": 15,
    "MAJOR": 20,
    "RATED": 40,
    "NEWS": 50,
    "COMMUNITY": 60,
}


class PublicationReviewView(discord.ui.View):
    """Persistent four-button moderator controls for one topic alert.

    custom_id values are intentionally identical for every alert. The callback
    resolves the clicked message ID against SQLite, so one persistent view can
    survive restarts and service every pending review item.
    """

    def __init__(self, bot: "CyberIntelBot", status: str = "pending"):
        super().__init__(timeout=None)
        self.bot = bot
        status = status or "pending"
        if status == "later":
            self.publish_later.disabled = True
        elif status in {"drop_publish", "superseded"}:
            self.publish_now.disabled = True
            self.publish_later.disabled = True
            self.drop_publish.disabled = True
        elif status == "published":
            for child in self.children:
                if isinstance(child, discord.ui.Button):
                    child.disabled = True

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if self.bot.is_authorized_reviewer(interaction):
            return True
        if not interaction.response.is_done():
            await interaction.response.send_message(
                "⛔ You are not authorized to control community publication for this alert.",
                ephemeral=True,
            )
        return False

    @discord.ui.button(
        label="Publish Now", emoji="🚀", style=discord.ButtonStyle.success,
        custom_id="cyberintel:review:publish_now", row=0,
    )
    async def publish_now(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self.bot.handle_publication_review_action(interaction, "publish_now")

    @discord.ui.button(
        label="Publish Later", emoji="🕒", style=discord.ButtonStyle.primary,
        custom_id="cyberintel:review:publish_later", row=0,
    )
    async def publish_later(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self.bot.handle_publication_review_action(interaction, "publish_later")

    @discord.ui.button(
        label="Drop Publish", emoji="🚫", style=discord.ButtonStyle.secondary,
        custom_id="cyberintel:review:drop_publish", row=0,
    )
    async def drop_publish(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self.bot.handle_publication_review_action(interaction, "drop_publish")

    @discord.ui.button(
        label="Drop Thread", emoji="🗑️", style=discord.ButtonStyle.danger,
        custom_id="cyberintel:review:drop_thread", row=0,
    )
    async def drop_thread(self, interaction: discord.Interaction, button: discord.ui.Button) -> None:
        await self.bot.handle_publication_review_action(interaction, "drop_thread")


class CyberIntelBot(discord.Client):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.session: aiohttp.ClientSession | None = None
        self.kev_cves: set[str] = set()
        self.enrichment_cache: dict[str, dict[str, Any]] = {}
        # Serializes queue merge/edit decisions while collectors continue fetching
        # concurrently. This closes the race where two sources discover the same
        # incident before either has reached persistent history.
        self.announcement_lock = asyncio.Lock()
        # Moderator button actions are serialized independently from collectors and
        # the Announcement queue. RSS/API collection continues in parallel.
        self.review_action_lock = asyncio.Lock()

        # Bot-status dashboard protection. Several collectors can request a
        # refresh at the same time after startup/reconnect. We coalesce those
        # requests, serialize Discord PATCHes and enforce a minimum gap between
        # edits so discord.py never has a pile of concurrent retries.
        self.status_update_lock = asyncio.Lock()
        self.status_update_task: asyncio.Task[Any] | None = None
        self.status_update_requested_pending = False
        self.status_update_force_pending = False
        self.status_update_force_state_pending: str | None = None
        self.last_status_update_monotonic = 0.0
        self.last_status_semantic_hash: str | None = None
        self._status_message: discord.Message | None = None
        self._closing_status = False

        self._ready_once = False
        self.started_at = int(time.time())
        self.rss_cycle_no = 0
        self.official_cycle_no = 0
        self.ctf_cycle_no = 0
        self.collector_health: dict[str, dict[str, Any]] = {
            "rss": {"state": "starting", "last_success": 0, "last_error": "", "failures": 0, "detail": ""},
            "official": {"state": "starting", "last_success": 0, "last_error": "", "failures": 0, "detail": ""},
            "ctf": {"state": "starting", "last_success": 0, "last_error": "", "failures": 0, "detail": ""},
            "x": {
                "state": "starting" if (ENABLE_X_API and X_BEARER_TOKEN) else "disabled",
                "last_success": 0,
                "last_error": "",
                "failures": 0,
                "detail": "configured" if (ENABLE_X_API and X_BEARER_TOKEN) else ("disabled by ENABLE_X_API=false" if not ENABLE_X_API else "X_BEARER_TOKEN not configured"),
            },
        }

    async def setup_hook(self) -> None:
        connector = aiohttp.TCPConnector(
            limit=HTTP_MAX_CONNECTIONS,
            limit_per_host=HTTP_MAX_CONNECTIONS_PER_HOST,
            ttl_dns_cache=HTTP_DNS_CACHE_SECONDS,
            keepalive_timeout=30,
        )
        self.session = aiohttp.ClientSession(timeout=HTTP_TIMEOUT, connector=connector)

        # Register one global persistent view. Buttons already attached to old
        # review messages remain functional after a bot/Termux/VPS restart.
        if REVIEW_CONTROLS_ENABLED:
            self.add_view(PublicationReviewView(self))

        # Change intervals from environment while retaining tasks.loop.
        self.rss_loop.change_interval(seconds=max(60, RSS_INTERVAL_SECONDS))
        self.official_loop.change_interval(seconds=max(120, OFFICIAL_INTERVAL_SECONDS))
        self.x_loop.change_interval(seconds=max(60, X_INTERVAL_SECONDS))
        self.ctf_loop.change_interval(seconds=max(300, CTF_INTERVAL_SECONDS))
        self.announcement_publish_loop.change_interval(
            seconds=max(60, ANNOUNCEMENT_PUBLISH_INTERVAL_SECONDS)
        )
        self.status_loop.change_interval(
            seconds=STATUS_HEARTBEAT_INTERVAL_SECONDS
        )

        self.rss_loop.start()
        self.official_loop.start()
        self.x_loop.start()
        self.ctf_loop.start()
        if CHANNEL_CYBER_ALERT and AUTO_PUBLISH_CYBER_ALERT:
            self.announcement_publish_loop.start()
        if CHANNEL_BOT_STATUS and STATUS_HEARTBEAT_ENABLED:
            self.status_loop.start()

    async def close(self) -> None:
        self._closing_status = True
        self.status_update_requested_pending = False
        self.status_update_force_pending = False
        self.status_update_force_state_pending = None

        # Best-effort graceful shutdown status. Abrupt process/VPS termination
        # cannot send a Discord message, but the stale dashboard timestamp still
        # makes that visible to moderators.
        if self.status_update_task and not self.status_update_task.done():
            self.status_update_task.cancel()
            try:
                await self.status_update_task
            except asyncio.CancelledError:
                pass
            self.status_update_task = None

        if self.is_ready() and CHANNEL_BOT_STATUS:
            try:
                await self.update_status_dashboard(force_state="OFFLINE", force=True)
                await self.post_status_event(
                    "🔴 Bot shutting down",
                    "InterOneBot is stopping gracefully. Automatic intelligence collection is paused until it starts again.",
                    discord.Color.red(),
                )
            except Exception:
                pass
        if self.session and not self.session.closed:
            await self.session.close()
        await super().close()

    async def on_ready(self) -> None:
        if not self._ready_once:
            log.info("Logged in as %s (ID %s)", self.user, getattr(self.user, "id", "?"))
            log.info("Process PID: %s", os.getpid())
            log.info(
                "Collectors: RSS=%ss Official=%ss X=%ss CTF=%ss",
                max(60, RSS_INTERVAL_SECONDS),
                max(120, OFFICIAL_INTERVAL_SECONDS),
                max(60, X_INTERVAL_SECONDS),
                max(300, CTF_INTERVAL_SECONDS),
            )
            log.info(
                "Feed telemetry: traversal_logs=%s trace_titles=%d feed_timeout=%ss dns_cache=%ss http_limit=%d/%d trusted_soft_signal=%s",
                FEED_TRAVERSAL_LOGS, FEED_TRACE_TITLES, FEED_HTTP_TIMEOUT_SECONDS,
                HTTP_DNS_CACHE_SECONDS, HTTP_MAX_CONNECTIONS, HTTP_MAX_CONNECTIONS_PER_HOST,
                TRUSTED_SOURCE_SOFT_SIGNAL_MODE,
            )
            custom_feed_count = sum(map(len, [
                NEWS_RSS_FEEDS, RESEARCH_RSS_FEEDS, INDIA_RSS_FEEDS,
                EXPLOIT_RSS_FEEDS, BREACH_RSS_FEEDS, CTF_RSS_FEEDS,
            ])) + len(LEGACY_CUSTOM_CTF_RSS)
            rss_app_count = sum(
                1
                for feed_list in [NEWS_RSS_FEEDS, RESEARCH_RSS_FEEDS, INDIA_RSS_FEEDS,
                                  EXPLOIT_RSS_FEEDS, BREACH_RSS_FEEDS, CTF_RSS_FEEDS]
                for _, feed_url in feed_list
                if feed_provider_name(feed_url) == "RSS.app"
            )
            log.info(
                "RSS inputs: built_in=%s custom=%d rss_app=%d (news=%d research=%d india=%d exploit=%d breach=%d ctf=%d)",
                ENABLE_BUILTIN_RSS, custom_feed_count, rss_app_count,
                len(NEWS_RSS_FEEDS), len(RESEARCH_RSS_FEEDS), len(INDIA_RSS_FEEDS),
                len(EXPLOIT_RSS_FEEDS), len(BREACH_RSS_FEEDS), len(CTF_RSS_FEEDS),
            )
            log.info("Free discovery: breach_rss=%s x_api=%s", ENABLE_BREACH_DISCOVERY_RSS, ENABLE_X_API)
            if not ENABLE_X_API:
                log.info("X API monitoring disabled; RSS/Atom breach discovery is preferred.")
            elif not X_BEARER_TOKEN:
                log.info("X_BEARER_TOKEN not configured; X breach monitoring is disabled.")
            log.info(
                "Historical dedupe: enabled=%s history=%d fuzzy=%0.2f window=%dd same_cve=%dh",
                DEDUP_ENABLED,
                db.history_count(),
                DEDUP_FUZZY_THRESHOLD,
                DEDUP_HISTORY_DAYS,
                DEDUP_SAME_CVE_HOURS,
            )
            log.info(
                "High-signal mode: enabled=%s news>=%d india>=%d research>=%d poc>=%d max_age=%dh discovery_news=%s unverified_social=%s",
                HIGH_SIGNAL_ONLY, NEWS_MIN_QUALITY_SCORE, INDIA_MIN_QUALITY_SCORE,
                RESEARCH_MIN_QUALITY_SCORE, POC_MIN_QUALITY_SCORE,
                MAX_SECURITY_ARTICLE_AGE_HOURS, ENABLE_DISCOVERY_NEWS, ALLOW_UNVERIFIED_SOCIAL,
            )
            log.info(
                "Manual-review policy: enabled=%s community_auto_score>=%d general_floor=%d breach_floor=%d controls=%s mirror_draft=%s review_history=%dh pending_actions=%d",
                MANUAL_REVIEW_ENABLED, COMMUNITY_AUTO_PUBLISH_SCORE,
                MANUAL_REVIEW_MIN_SCORE, MANUAL_REVIEW_BREACH_MIN_SCORE,
                REVIEW_CONTROLS_ENABLED, MANUAL_REVIEW_MIRROR_TO_CYBER_ALERT,
                MANUAL_REVIEW_HISTORY_HOURS, db.publication_review_count(),
            )
            log.info(
                "CTF policy: upcoming_only=%s lookahead=%dd min_priority=%s registration_signal=%s max_discovery_age=%dd",
                CTF_UPCOMING_ONLY, CTF_LOOKAHEAD_DAYS, CTF_MIN_PRIORITY,
                CTF_REQUIRE_REGISTRATION_SIGNAL, CTF_DISCOVERY_MAX_AGE_DAYS,
            )
            if CHANNEL_CYBER_ALERT:
                log.info(
                    "Cyber-alert hub enabled: channel=%s auto_publish=%s queue=%d publish_interval=%ss",
                    CHANNEL_CYBER_ALERT,
                    AUTO_PUBLISH_CYBER_ALERT,
                    db.announcement_queue_size(),
                    max(60, ANNOUNCEMENT_PUBLISH_INTERVAL_SECONDS),
                )
                log.info(
                    "Announcement final gate: recheck=%s queue_dedup=%0.2f delete_rejected=%s merged=%s rejected=%s",
                    ANNOUNCEMENT_FINAL_RECHECK, ANNOUNCEMENT_QUEUE_DEDUP_THRESHOLD,
                    ANNOUNCEMENT_DELETE_REJECTED_MIRRORS,
                    db.get("announcement_merged_count", "0"),
                    db.get("announcement_rejected_count", "0"),
                )
            else:
                log.info("CHANNEL_CYBER_ALERT not configured; public Announcement hub is disabled.")

            if CHANNEL_BOT_STATUS:
                log.info(
                    "Bot-status enabled: channel=%s dashboard=%s heartbeat=%ss errors=%s recovery=%s",
                    CHANNEL_BOT_STATUS, STATUS_DASHBOARD_ENABLED,
                    STATUS_HEARTBEAT_INTERVAL_SECONDS, STATUS_POST_ERRORS, STATUS_POST_RECOVERY,
                )
                if STATUS_DASHBOARD_ENABLED:
                    log.info(
                        "Bot-status rate guard: debounce=%ss min_edit_gap=%ss change_detection=%s",
                        STATUS_DASHBOARD_DEBOUNCE_SECONDS,
                        STATUS_DASHBOARD_MIN_EDIT_INTERVAL_SECONDS,
                        STATUS_DASHBOARD_CHANGE_DETECTION,
                    )
            else:
                log.info("CHANNEL_BOT_STATUS not configured; Discord health dashboard is disabled.")

            try:
                await self.change_presence(
                    status=discord.Status.online,
                    activity=discord.Activity(
                        type=discord.ActivityType.watching,
                        name="cyber intelligence",
                    ),
                )
            except Exception as exc:
                log.debug("Unable to set Discord presence: %s", exc)

            self._ready_once = True

            if CHANNEL_BOT_STATUS:
                if STATUS_POST_STARTUP:
                    await self.post_status_event(
                        "🟢 Bot online",
                        "InterOneBot connected successfully. Cyber-intelligence collectors and persistent deduplication are active.",
                        discord.Color.green(),
                    )
                if STATUS_DASHBOARD_ENABLED:
                    # One intentional startup refresh. Collector transitions that
                    # follow are debounced instead of issuing immediate PATCHes.
                    await self.update_status_dashboard(force=True)

    async def on_resumed(self) -> None:
        log.info("Discord gateway session resumed.")
        if CHANNEL_BOT_STATUS and STATUS_DASHBOARD_ENABLED:
            await self.schedule_status_dashboard_update(delay=15)

    async def get_target_channel(self, channel_id: int) -> discord.abc.Messageable:
        channel = self.get_channel(channel_id)
        if channel is not None:
            return channel
        return await self.fetch_channel(channel_id)

    def is_authorized_reviewer(self, interaction: discord.Interaction) -> bool:
        user = interaction.user
        user_id = int(getattr(user, "id", 0) or 0)
        if user_id and user_id in REVIEWER_USER_IDS:
            return True
        roles = getattr(user, "roles", []) or []
        if REVIEWER_ROLE_IDS and any(int(getattr(role, "id", 0) or 0) in REVIEWER_ROLE_IDS for role in roles):
            return True
        if REVIEW_ALLOW_MANAGE_MESSAGES:
            perms = getattr(user, "guild_permissions", None)
            if perms and (getattr(perms, "administrator", False) or getattr(perms, "manage_messages", False)):
                return True
        return False

    @staticmethod
    def _review_status_text(status: str, actor_id: int = 0) -> str:
        actor = f" by <@{actor_id}>" if actor_id else ""
        return {
            "pending": "🟡 Pending moderator decision",
            "later": f"🕒 Publish later selected{actor} — **Publish Now** remains available",
            "drop_publish": f"🚫 Community publication dropped{actor} — kept in this topic only",
            "superseded": "🔁 Publication skipped — a stronger/trusted equivalent is already covered",
            "published": f"✅ Published to the community Announcement channel{actor}",
        }.get(status, status)

    def _review_state_embed(
        self, source_embed: discord.Embed, status: str, actor_id: int = 0, *, for_public: bool = False
    ) -> discord.Embed:
        embed = discord.Embed.from_dict(source_embed.to_dict())
        value = self._review_status_text(status, actor_id)
        if for_public:
            value = f"✅ Moderator approved by <@{actor_id}>" if actor_id else "✅ Moderator approved"
        found = False
        for idx, field in enumerate(embed.fields):
            if field.name in {"Publish", "Publication decision"}:
                embed.set_field_at(idx, name="Publish", value=value, inline=True)
                found = True
                break
        if not found:
            embed.add_field(name="Publish", value=value, inline=True)
        return embed

    async def _fetch_review_source_message(self, row: dict[str, Any]) -> discord.Message:
        channel = await self.get_target_channel(int(row["source_channel_id"]))
        if not hasattr(channel, "fetch_message"):
            raise RuntimeError("Source channel does not support message retrieval")
        return await channel.fetch_message(int(row["source_message_id"]))

    async def handle_publication_review_action(
        self, interaction: discord.Interaction, action: str
    ) -> None:
        if not interaction.response.is_done():
            await interaction.response.defer(ephemeral=True, thinking=True)

        message = interaction.message
        if message is None:
            await interaction.followup.send("⚠️ Unable to resolve the alert message.", ephemeral=True)
            return

        async with self.review_action_lock:
            row = db.get_publication_review(message.id)
            if row is None:
                await interaction.followup.send(
                    "⚠️ This alert has no active publication-review record.", ephemeral=True
                )
                return

            status = row["status"]
            reviewer_id = int(getattr(interaction.user, "id", 0) or 0)

            if action == "publish_later":
                if status == "published":
                    await interaction.followup.send("✅ This alert is already published.", ephemeral=True)
                    return
                if status == "drop_publish":
                    await interaction.followup.send(
                        "🚫 Publication was already dropped for this alert.", ephemeral=True
                    )
                    return
                db.update_publication_review(message.id, status="later", reviewed_by=reviewer_id)
                try:
                    embed = self._review_state_embed(message.embeds[0], "later", reviewer_id) if message.embeds else None
                    await message.edit(embed=embed, view=PublicationReviewView(self, "later"))
                except Exception as exc:
                    log.warning("Unable to update Publish Later controls for %s: %s", message.id, exc)
                await self.schedule_status_dashboard_update(delay=3)
                await interaction.followup.send(
                    "🕒 Saved for later. The alert stays in this topic and **Publish Now** remains available whenever you want it.",
                    ephemeral=True,
                )
                return

            if action == "drop_publish":
                if status == "published":
                    await interaction.followup.send(
                        "⚠️ This alert was already published; dropping the local publication decision cannot retract follower-server copies.",
                        ephemeral=True,
                    )
                    return
                db.update_publication_review(message.id, status="drop_publish", reviewed_by=reviewer_id)
                try:
                    embed = self._review_state_embed(message.embeds[0], "drop_publish", reviewer_id) if message.embeds else None
                    await message.edit(embed=embed, view=PublicationReviewView(self, "drop_publish"))
                except Exception as exc:
                    log.warning("Unable to update Drop Publish controls for %s: %s", message.id, exc)
                await self.schedule_status_dashboard_update(delay=3)
                await interaction.followup.send(
                    "🚫 Community publication dropped. The alert remains in this topic only.", ephemeral=True
                )
                return

            if action == "drop_thread":
                if status == "published":
                    await interaction.followup.send(
                        "⚠️ This alert is already public. The source topic copy was not deleted because follower-server copies cannot be recalled reliably.",
                        ephemeral=True,
                    )
                    return
                db.update_publication_review(message.id, status="dropped_thread", reviewed_by=reviewer_id)
                try:
                    # If the bot alert actually lives inside a Discord Thread, the
                    # moderator explicitly requested "Drop Thread": delete that
                    # thread container. In a normal text/news channel, delete only
                    # the alert message (the practical equivalent of dropping it).
                    source_channel = message.channel
                    if isinstance(source_channel, discord.Thread):
                        await source_channel.delete(reason=f"Cyber intel review dropped by {interaction.user}")
                    else:
                        await message.delete()
                except discord.NotFound:
                    pass
                except Exception as exc:
                    log.warning("Unable to delete dropped review alert/thread %s: %s", message.id, exc)
                    await interaction.followup.send(
                        f"⚠️ Decision saved, but Discord could not delete the topic alert/thread: {exc}", ephemeral=True
                    )
                    return
                await self.schedule_status_dashboard_update(delay=3)
                await interaction.followup.send(
                    "🗑️ Topic alert/thread dropped. Nothing was sent to #cyber-alert.", ephemeral=True
                )
                return

            if action != "publish_now":
                await interaction.followup.send("⚠️ Unknown review action.", ephemeral=True)
                return

            if status == "published":
                await interaction.followup.send("✅ This alert is already published.", ephemeral=True)
                return
            if status == "drop_publish":
                await interaction.followup.send(
                    "🚫 Publication was dropped. Use **Publish Later** instead of Drop Publish when you may want to publish later.",
                    ephemeral=True,
                )
                return
            if status == "dropped_thread":
                await interaction.followup.send("🗑️ This alert was already dropped.", ephemeral=True)
                return

            item = dict(row.get("item") or {})
            item["auto_publish"] = True
            item["manual_review"] = False
            item["manual_review_approved"] = True
            item["manual_review_approved_by"] = reviewer_id
            item["quality_score"] = int(security_quality(item)[0]) if item.get("type") != "CTF" else item.get("quality_score")

            # A Publish-Later item may have been overtaken by a stronger trusted
            # report while waiting. Never create a second public copy in that case.
            covered = db.find_duplicate(item) if item.get("type") != "CTF" else None
            if covered is not None:
                db.update_publication_review(message.id, status="superseded", reviewed_by=reviewer_id)
                try:
                    if message.embeds:
                        embed = self._review_state_embed(message.embeds[0], "superseded", reviewer_id)
                        embed.add_field(
                            name="Already covered by",
                            value=truncate(
                                f"[{covered.get('source') or 'trusted history'}] {covered.get('title') or 'equivalent alert'}",
                                700,
                            ),
                            inline=False,
                        )
                        await message.edit(embed=embed, view=PublicationReviewView(self, "superseded"))
                except Exception as exc:
                    log.warning("Unable to mark review alert %s superseded: %s", message.id, exc)
                await self.schedule_status_dashboard_update(delay=3)
                await interaction.followup.send(
                    "🔁 Not published again: a stronger/trusted equivalent is already in publication history.",
                    ephemeral=True,
                )
                return

            try:
                source_message = await self._fetch_review_source_message(row)
            except Exception as exc:
                await interaction.followup.send(
                    f"⚠️ The source topic alert could not be fetched: {exc}", ephemeral=True
                )
                return

            source_embed = source_message.embeds[0] if source_message.embeds else discord.Embed(
                title=truncate(str(item.get("title", "Cyber intelligence update")), 256)
            )
            public_embed = self._review_state_embed(source_embed, "published", reviewer_id, for_public=True)

            hub_message = None
            hub_id = int(row.get("hub_message_id", 0) or 0)
            if hub_id and CHANNEL_CYBER_ALERT:
                try:
                    hub = await self.get_target_channel(CHANNEL_CYBER_ALERT)
                    if hasattr(hub, "fetch_message"):
                        hub_message = await hub.fetch_message(hub_id)
                        await hub_message.edit(embed=self._build_hub_embed(
                            public_embed, source_message, row["route"], [],
                            "Moderator-approved manual review; published explicitly from the topic-channel controls.",
                        ))
                except Exception:
                    hub_message = None

            if hub_message is None:
                hub_message = await self.mirror_to_cyber_alert(
                    source_message=source_message,
                    source_embed=public_embed,
                    route=row["route"],
                    priority=row["priority_name"],
                    item=item,
                    queue_for_crosspost=False,
                )
                if hub_message is None:
                    await interaction.followup.send(
                        "⚠️ Could not mirror this alert to #cyber-alert. Check CHANNEL_CYBER_ALERT and bot permissions.",
                        ephemeral=True,
                    )
                    return
                db.update_publication_review(
                    message.id, hub_message_id=hub_message.id, reviewed_by=reviewer_id, item=item
                )

            crossposted = False
            if isinstance(hub_message.channel, discord.TextChannel) and hub_message.channel.is_news():
                if not getattr(hub_message.flags, "crossposted", False):
                    try:
                        await hub_message.publish()
                    except Exception as exc:
                        # Keep it retryable with Publish Now and remember the already-created hub copy.
                        db.update_publication_review(
                            message.id, status="later", hub_message_id=hub_message.id,
                            reviewed_by=reviewer_id, item=item,
                        )
                        await interaction.followup.send(
                            f"⚠️ Mirrored to #cyber-alert, but Discord could not crosspost it yet: {exc}. "
                            "It is saved as Publish Later; press Publish Now again to retry.",
                            ephemeral=True,
                        )
                        return
                crossposted = True
            else:
                log.warning("Manual Publish Now mirrored message %s but CHANNEL_CYBER_ALERT is not an Announcement channel", hub_message.id)

            db.update_publication_review(
                message.id, status="published", hub_message_id=hub_message.id,
                reviewed_by=reviewer_id, item=item,
            )
            if item.get("id"):
                db.delete_review_history(str(item["id"]))
                db.record_history(item, "manual-approved")
            db.increment("manual_review_published_count")
            await self.schedule_status_dashboard_update(delay=3)

            try:
                source_public_state = self._review_state_embed(source_embed, "published", reviewer_id)
                await source_message.edit(
                    embed=source_public_state, view=PublicationReviewView(self, "published")
                )
            except Exception as exc:
                log.warning("Unable to mark source alert %s as published: %s", message.id, exc)

            result_text = (
                "🚀 Published now: mirrored to #cyber-alert and crossposted to community followers."
                if crossposted
                else "✅ Mirrored to #cyber-alert. That channel is not currently an Announcement channel, so Discord follower crossposting was not available."
            )
            await interaction.followup.send(result_text, ephemeral=True)

    @staticmethod
    def _relative_timestamp(epoch: int | float | None) -> str:
        if not epoch:
            return "not yet"
        return f"<t:{int(epoch)}:R>"

    def _collector_line(self, name: str, label: str) -> str:
        health = self.collector_health.get(name, {})
        state = health.get("state", "starting")
        if state == "disabled":
            return f"⚪ **{label}** — disabled ({health.get('detail', 'not configured')})"
        if state == "error":
            return (
                f"🔴 **{label}** — error • failures: {health.get('failures', 0)} "
                f"• last success {self._relative_timestamp(health.get('last_success'))}"
            )
        if state == "ok":
            detail = truncate(str(health.get("detail", "")), 80)
            suffix = f" • {detail}" if detail else ""
            return f"🟢 **{label}** — healthy • checked {self._relative_timestamp(health.get('last_success'))}{suffix}"
        return f"🟡 **{label}** — starting / waiting for first check"

    def build_status_embed(self, force_state: str | None = None) -> discord.Embed:
        offline = force_state == "OFFLINE"
        latency_ms = int(self.latency * 1000) if self.latency >= 0 else 0
        now = int(time.time())
        uptime_seconds = max(0, now - self.started_at)
        hours, rem = divmod(uptime_seconds, 3600)
        minutes = rem // 60

        embed = discord.Embed(
            title="🔴 InterOneBot offline" if offline else "🟢 InterOneBot operational",
            description=(
                "Cyber-intelligence collection is stopped." if offline else
                "Live health dashboard for the cybersecurity intelligence pipeline."
            ),
            color=discord.Color.red() if offline else discord.Color.green(),
            timestamp=datetime.now(timezone.utc),
        )
        embed.set_author(name="🤖 CYBER INTELLIGENCE • BOT STATUS")
        embed.add_field(
            name="Runtime",
            value=(
                f"**Uptime:** {hours}h {minutes}m\n"
                f"**Gateway latency:** {latency_ms} ms\n"
                f"**Started:** <t:{self.started_at}:R>"
            ),
            inline=True,
        )
        embed.add_field(
            name="Data state",
            value=(
                f"**Dedup history:** {db.history_count():,}\n"
                f"**Manual-review history:** {db.review_history_count():,}\n"
                f"**Pending publication reviews:** {db.publication_review_count():,}\n"
                f"**Announcement queue:** {db.announcement_queue_size():,}\n"
                f"**Queue merges:** {int(db.get('announcement_merged_count', '0') or 0):,}\n"
                f"**Final-gate drops:** {int(db.get('announcement_rejected_count', '0') or 0):,}\n"
                f"**High-signal mode:** {'ON' if HIGH_SIGNAL_ONLY else 'OFF'}"
            ),
            inline=True,
        )
        embed.add_field(
            name="Collectors",
            value="\n".join([
                self._collector_line("official", "CISA / CERT-In"),
                self._collector_line("rss", "Security RSS / PoC"),
                self._collector_line("ctf", "Upcoming CTF"),
                self._collector_line("x", "X breach watch"),
            ]),
            inline=False,
        )

        errors = []
        for name, health in self.collector_health.items():
            if health.get("state") == "error" and health.get("last_error"):
                errors.append(f"**{name}:** {truncate(str(health['last_error']), 180)}")
        if errors:
            embed.add_field(name="⚠️ Active collector errors", value="\n".join(errors)[:1024], inline=False)

        embed.add_field(
            name="Policy",
            value=(
                f"**CTF:** upcoming/registerable only • minimum {CTF_MIN_PRIORITY}\n"
                f"**Community auto-publish:** ≥{COMMUNITY_AUTO_PUBLISH_SCORE}/100\n"
                f"**Manual review:** {'ON' if MANUAL_REVIEW_ENABLED else 'OFF'} • controls {'ON' if REVIEW_CONTROLS_ENABLED else 'OFF'}\n"
                f"**Tier-4 breach force-review:** {'ON' if TIER4_BREACH_FORCE_REVIEW else 'OFF'}\n"
                f"**Built-in RSS:** {'ON' if ENABLE_BUILTIN_RSS else 'OFF'} • "
                f"**Custom RSS:** {sum(map(len, [NEWS_RSS_FEEDS, RESEARCH_RSS_FEEDS, INDIA_RSS_FEEDS, EXPLOIT_RSS_FEEDS, BREACH_RSS_FEEDS, CTF_RSS_FEEDS]))}\n"
                f"**Persistent duplicate filter:** {'enabled' if DEDUP_ENABLED else 'disabled'}\n"
                f"**Final announcement re-check:** {'enabled' if ANNOUNCEMENT_FINAL_RECHECK else 'disabled'}"
            ),
            inline=False,
        )
        embed.set_footer(
            text=(
                f"Dashboard auto-updates every {STATUS_HEARTBEAT_INTERVAL_SECONDS // 60} min • "
                "bot-status is not public unless FORWARD_BOT_STATUS=true"
            )
        )
        return embed

    def _status_semantic_hash(self, force_state: str | None = None) -> str:
        """Hash only meaningful dashboard state, excluding live clock/latency.

        The rendered embed contains a timestamp, uptime and gateway latency, so
        hashing the raw embed would make every refresh look different. This
        signature intentionally tracks state that should cause an immediate edit.
        Routine clock/latency refreshes are handled by the forced heartbeat.
        """
        collectors: dict[str, dict[str, Any]] = {}
        for name, health in sorted(self.collector_health.items()):
            collectors[name] = {
                "state": health.get("state", "starting"),
                "failures": int(health.get("failures", 0) or 0),
                "last_error": str(health.get("last_error", "")),
                "detail": str(health.get("detail", "")),
            }

        payload = {
            "force_state": force_state or "ONLINE",
            "collectors": collectors,
            "history_count": db.history_count(),
            "review_history_count": db.review_history_count(),
            "publication_review_count": db.publication_review_count(),
            "announcement_queue": db.announcement_queue_size(),
            "announcement_merges": db.get("announcement_merged_count", "0"),
            "announcement_rejected": db.get("announcement_rejected_count", "0"),
            "high_signal": HIGH_SIGNAL_ONLY,
            "manual_review": MANUAL_REVIEW_ENABLED,
            "manual_review_min": MANUAL_REVIEW_MIN_SCORE,
            "manual_review_breach_min": MANUAL_REVIEW_BREACH_MIN_SCORE,
            "community_auto_publish_score": COMMUNITY_AUTO_PUBLISH_SCORE,
            "review_controls": REVIEW_CONTROLS_ENABLED,
            "tier4_breach_force_review": TIER4_BREACH_FORCE_REVIEW,
            "manual_review_mirror": MANUAL_REVIEW_MIRROR_TO_CYBER_ALERT,
            "builtin_rss": ENABLE_BUILTIN_RSS,
            "custom_rss": sum(map(len, [
                NEWS_RSS_FEEDS, RESEARCH_RSS_FEEDS, INDIA_RSS_FEEDS,
                EXPLOIT_RSS_FEEDS, BREACH_RSS_FEEDS, CTF_RSS_FEEDS,
            ])),
            "ctf_min_priority": CTF_MIN_PRIORITY,
            "news_threshold": NEWS_MIN_QUALITY_SCORE,
            "dedupe": DEDUP_ENABLED,
            "announcement_final_recheck": ANNOUNCEMENT_FINAL_RECHECK,
        }
        return hashlib.sha256(
            json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
        ).hexdigest()

    async def update_status_dashboard(
        self,
        force_state: str | None = None,
        *,
        force: bool = False,
    ) -> bool:
        """Create/edit the single status dashboard with rate-limit protection.

        Returns True only when a Discord send/edit was actually performed.
        """
        if not CHANNEL_BOT_STATUS or not STATUS_DASHBOARD_ENABLED:
            return False

        async with self.status_update_lock:
            semantic_hash = self._status_semantic_hash(force_state)
            if (
                STATUS_DASHBOARD_CHANGE_DETECTION
                and not force
                and semantic_hash == self.last_status_semantic_hash
            ):
                log.debug("Bot-status dashboard unchanged; skipping Discord PATCH.")
                return False

            # Enforce a minimum spacing between edits. If discord.py is already
            # waiting on a 429 Retry-After, this lock also prevents another
            # dashboard PATCH from being started concurrently.
            if self.last_status_update_monotonic > 0:
                elapsed = time.monotonic() - self.last_status_update_monotonic
                remaining = STATUS_DASHBOARD_MIN_EDIT_INTERVAL_SECONDS - elapsed
                if remaining > 0:
                    log.debug(
                        "Bot-status edit delayed %.1fs to respect minimum edit gap.",
                        remaining,
                    )
                    await asyncio.sleep(remaining)

            # Collector state may have changed while waiting for the edit gap.
            # Recompute so the stored signature matches the embed we are about
            # to render and another identical request can be skipped.
            semantic_hash = self._status_semantic_hash(force_state)
            if (
                STATUS_DASHBOARD_CHANGE_DETECTION
                and not force
                and semantic_hash == self.last_status_semantic_hash
            ):
                log.debug("Bot-status dashboard unchanged after debounce; skipping PATCH.")
                return False

            try:
                channel = await self.get_target_channel(CHANNEL_BOT_STATUS)
                embed = self.build_status_embed(force_state=force_state)
                message = self._status_message

                if message is None:
                    stored = db.get("bot_status_message_id")
                    if stored:
                        try:
                            message = await channel.fetch_message(int(stored))
                        except (discord.NotFound, discord.Forbidden, ValueError):
                            message = None

                if message is None:
                    message = await channel.send(embed=embed)
                    self._status_message = message
                    db.set("bot_status_message_id", str(message.id))
                    log.info("Created bot-status dashboard message %s", message.id)
                else:
                    try:
                        await message.edit(embed=embed)
                        self._status_message = message
                    except discord.NotFound:
                        # Dashboard was manually deleted. Re-create it once and
                        # update the persisted message ID.
                        message = await channel.send(embed=embed)
                        self._status_message = message
                        db.set("bot_status_message_id", str(message.id))
                        log.info("Re-created bot-status dashboard message %s", message.id)

                self.last_status_update_monotonic = time.monotonic()
                self.last_status_semantic_hash = semantic_hash
                return True
            except Exception as exc:
                log.warning("Unable to update bot-status dashboard: %s", exc)
                return False

    async def schedule_status_dashboard_update(
        self,
        delay: float | None = None,
        *,
        force: bool = False,
        force_state: str | None = None,
    ) -> None:
        """Coalesce many dashboard refresh requests into one future edit."""
        if (
            self._closing_status
            or not CHANNEL_BOT_STATUS
            or not STATUS_DASHBOARD_ENABLED
        ):
            return

        self.status_update_requested_pending = True
        self.status_update_force_pending = self.status_update_force_pending or force
        if force_state is not None:
            self.status_update_force_state_pending = force_state

        if self.status_update_task and not self.status_update_task.done():
            return

        wait_seconds = (
            float(STATUS_DASHBOARD_DEBOUNCE_SECONDS)
            if delay is None
            else max(0.0, float(delay))
        )

        async def delayed_update() -> None:
            try:
                if wait_seconds:
                    await asyncio.sleep(wait_seconds)

                pending_force = self.status_update_force_pending
                pending_state = self.status_update_force_state_pending
                self.status_update_requested_pending = False
                self.status_update_force_pending = False
                self.status_update_force_state_pending = None

                await self.update_status_dashboard(
                    force_state=pending_state,
                    force=pending_force,
                )
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                log.warning("Deferred bot-status dashboard update failed: %s", exc)
            finally:
                self.status_update_task = None

                # A request may have arrived while the previous edit was in
                # flight. Schedule one more coalesced pass instead of dropping it.
                if (
                    self.status_update_requested_pending
                    or self.status_update_force_pending
                    or self.status_update_force_state_pending is not None
                ):
                    await self.schedule_status_dashboard_update()

        self.status_update_task = asyncio.create_task(
            delayed_update(),
            name="bot-status-dashboard-debounce",
        )

    async def post_status_event(
        self,
        title: str,
        description: str,
        color: discord.Color = discord.Color.light_grey(),
    ) -> discord.Message | None:
        if not CHANNEL_BOT_STATUS:
            return None
        try:
            channel = await self.get_target_channel(CHANNEL_BOT_STATUS)
            embed = discord.Embed(
                title=truncate(title, 256),
                description=truncate(description, 1800),
                color=color,
                timestamp=datetime.now(timezone.utc),
            )
            embed.set_author(name="🤖 CYBER INTELLIGENCE • BOT STATUS")
            source_message = await channel.send(embed=embed)
            if FORWARD_BOT_STATUS:
                await self.mirror_to_cyber_alert(
                    source_message=source_message,
                    source_embed=embed,
                    route="status",
                    priority="NEWS",
                    item={
                        "id": stable_id("bot-status", f"{title}:{int(time.time())}"),
                        "type": "STATUS",
                        "source": "InterOneBot",
                        "title": title,
                        "summary": description,
                    },
                )
            return source_message
        except Exception as exc:
            log.warning("Unable to post bot-status event: %s", exc)
            return None

    async def report_status(self, message: str) -> None:
        """Backward-compatible helper for one-off operational messages."""
        log.info(message)
        await self.post_status_event("🤖 Bot status", message)

    async def mark_collector_success(self, name: str, detail: str = "") -> None:
        health = self.collector_health.setdefault(name, {})
        previous = health.get("state")
        previous_error = health.get("last_error", "")
        health.update({
            "state": "ok",
            "last_success": int(time.time()),
            "last_error": "",
            "failures": 0,
            "detail": detail,
        })
        if previous == "error" and STATUS_POST_RECOVERY:
            await self.post_status_event(
                f"🟢 {name.upper()} collector recovered",
                f"The collector is healthy again. Previous error: {truncate(str(previous_error), 500)}",
                discord.Color.green(),
            )
        # The heartbeat loop refreshes routine success timestamps. Update
        # immediately only on a state transition so a 2-minute RSS loop does not
        # generate unnecessary Discord message edits.
        if previous != "ok" and CHANNEL_BOT_STATUS and STATUS_DASHBOARD_ENABLED:
            await self.schedule_status_dashboard_update()

    async def mark_collector_error(self, name: str, exc: Exception) -> None:
        health = self.collector_health.setdefault(name, {})
        previous = health.get("state")
        health["state"] = "error"
        health["last_error"] = str(exc)
        health["failures"] = int(health.get("failures", 0)) + 1
        if previous != "error" and STATUS_POST_ERRORS:
            await self.post_status_event(
                f"🔴 {name.upper()} collector error",
                f"Collector failed and will retry automatically on its next scheduled cycle.\n\n`{truncate(str(exc), 1200)}`",
                discord.Color.red(),
            )
        if previous != "error" and CHANNEL_BOT_STATUS and STATUS_DASHBOARD_ENABLED:
            await self.schedule_status_dashboard_update()

    def _build_hub_embed(
        self,
        source_embed: discord.Embed,
        source_message: discord.Message,
        route: str,
        corroborators: list[str] | None = None,
        resolution_note: str | None = None,
    ) -> discord.Embed:
        info = CATEGORY_INFO.get(
            route,
            {"emoji": "🛰", "label": "CYBER INTELLIGENCE", "channel": route},
        )
        hub_embed = discord.Embed.from_dict(source_embed.to_dict())
        original_title = hub_embed.title or "Cyber intelligence update"
        prefix = f"{info['emoji']} {info['label']} | "
        hub_embed.title = truncate(prefix + original_title, 256)

        # Avoid duplicate queue-resolution fields if an embed is edited repeatedly.
        hub_embed._fields = [
            f for f in hub_embed._fields
            if f.get("name") not in {
                "📂 Intelligence category", "🔗 Categorized source",
                "🧭 Source resolution", "📰 Also reported by",
            }
        ]
        hub_embed.add_field(
            name="📂 Intelligence category",
            value=f"{info['emoji']} #{info['channel']}",
            inline=True,
        )
        hub_embed.add_field(
            name="🔗 Categorized source",
            value=f"[Open original alert]({source_message.jump_url})",
            inline=True,
        )
        if corroborators:
            unique = list(dict.fromkeys(x for x in corroborators if x))
            if unique:
                hub_embed.add_field(
                    name="📰 Also reported by",
                    value=truncate(", ".join(unique[:8]), 500),
                    inline=False,
                )
        if resolution_note:
            hub_embed.add_field(
                name="🧭 Source resolution",
                value=truncate(resolution_note, 600),
                inline=False,
            )
        return hub_embed

    async def _safe_delete_hub_message(self, channel_id: int, message_id: int) -> None:
        if not ANNOUNCEMENT_DELETE_REJECTED_MIRRORS:
            return
        try:
            channel = await self.get_target_channel(channel_id)
            message = await channel.fetch_message(message_id)
            if not getattr(message.flags, "crossposted", False):
                await message.delete()
        except (discord.NotFound, discord.Forbidden):
            pass
        except Exception as exc:
            log.debug("Unable to remove superseded #cyber-alert message %s: %s", message_id, exc)

    async def mirror_to_cyber_alert(
        self,
        source_message: discord.Message,
        source_embed: discord.Embed,
        route: str,
        priority: str,
        item: dict[str, Any] | None = None,
        queue_for_crosspost: bool = True,
    ) -> discord.Message | None:
        """Mirror one categorized alert into the common public hub.

        Before creating a new hub message, compare it with every not-yet-published
        queued incident. Equivalent reports are merged. If the new source has a
        stronger priority/trust score, it replaces the queued primary embed;
        otherwise it is recorded as additional reporting. Topic-channel originals
        remain untouched.
        """
        if not CHANNEL_CYBER_ALERT:
            return None
        if route == "status" and not FORWARD_BOT_STATUS:
            return None
        if source_message.channel.id == CHANNEL_CYBER_ALERT:
            return None

        try:
            hub = await self.get_target_channel(CHANNEL_CYBER_ALERT)
        except Exception as exc:
            log.warning("Unable to resolve CHANNEL_CYBER_ALERT=%s: %s", CHANNEL_CYBER_ALERT, exc)
            return None

        item = dict(item or {})
        item.setdefault("title", source_embed.title or "Cyber intelligence update")
        item.setdefault("source", "Bot status" if route == "status" else "Unknown")
        original_title = source_embed.title or "Cyber intelligence update"

        async with self.announcement_lock:
            if queue_for_crosspost and AUTO_PUBLISH_CYBER_ALERT and isinstance(hub, discord.TextChannel) and hub.is_news():
                conflicts = db.find_queued_conflicts(item, route)
            else:
                conflicts = []

            if conflicts:
                # Pick the strongest existing equivalent. All others are folded into
                # this winner during final reconciliation before crossposting.
                existing = max(conflicts, key=lambda x: x.get("strength", 0))
                new_strength = announcement_strength(item, priority)
                existing_sources = list(existing.get("corroborators", []))
                if existing.get("source"):
                    existing_sources.append(existing["source"])
                new_source = str(item.get("source", ""))

                try:
                    existing_channel = await self.get_target_channel(existing["channel_id"])
                    existing_message = await existing_channel.fetch_message(existing["message_id"])
                except Exception as exc:
                    # Stale queue row: remove it and fall through to creating a fresh hub copy.
                    log.warning("Queued conflict message %s could not be fetched; pruning: %s", existing["message_id"], exc)
                    db.delete_announcement(existing["message_id"])
                    existing = None

                if existing is not None:
                    if new_strength > int(existing.get("strength", 0)):
                        corrob = list(dict.fromkeys(existing_sources))
                        if new_source in corrob:
                            corrob.remove(new_source)
                        hub_embed = self._build_hub_embed(
                            source_embed, source_message, route, corrob,
                            "Upgraded before public crosspost because a higher-priority or more trusted source arrived.",
                        )
                        await existing_message.edit(embed=hub_embed)
                        db.update_announcement(
                            existing["message_id"],
                            priority=ANNOUNCEMENT_PRIORITY.get(priority, 50),
                            category=route,
                            title=original_title,
                            item=item,
                            priority_name=priority,
                            corroborators=corrob,
                        )
                        log.info(
                            "[cyber-alert] queued incident upgraded: [%s] %s -> [%s] %s",
                            existing.get("source", "unknown"), truncate(existing.get("title", ""), 70),
                            new_source or "unknown", truncate(original_title, 70),
                        )
                    else:
                        corrob = list(dict.fromkeys(existing_sources + ([new_source] if new_source else [])))
                        primary = existing.get("source", "")
                        corrob = [x for x in corrob if x != primary]
                        if existing_message.embeds:
                            base = discord.Embed.from_dict(existing_message.embeds[0].to_dict())
                            base._fields = [
                                f for f in base._fields
                                if f.get("name") not in {"📰 Also reported by", "🧭 Source resolution"}
                            ]
                            if corrob:
                                base.add_field(
                                    name="📰 Also reported by",
                                    value=truncate(", ".join(corrob[:8]), 500),
                                    inline=False,
                                )
                            base.add_field(
                                name="🧭 Source resolution",
                                value="Equivalent queued reporting was merged; the stronger existing source remains primary.",
                                inline=False,
                            )
                            await existing_message.edit(embed=base)
                        db.update_announcement(
                            existing["message_id"], corroborators=corrob
                        )
                        log.info(
                            "[cyber-alert] queued duplicate merged (%s %.2f): %s + %s",
                            existing.get("match_reason", "equivalent incident"),
                            float(existing.get("match_score", 1.0)),
                            primary or "existing", new_source or "new source",
                        )
                    db.increment("announcement_merged_count")
                    return existing_message

            hub_embed = self._build_hub_embed(source_embed, source_message, route)
            try:
                hub_message = await hub.send(embed=hub_embed)
            except Exception as exc:
                log.warning("Unable to mirror alert into #cyber-alert: %s", exc)
                return None

            log.info(
                "[cyber-alert] mirrored from #%s: %s",
                CATEGORY_INFO.get(route, {}).get("channel", route),
                truncate(original_title, 100),
            )

            if not queue_for_crosspost:
                log.info(
                    "[cyber-alert] manual-review draft only; not queued for auto crosspost: %s",
                    truncate(original_title, 100),
                )
                return hub_message

            if not AUTO_PUBLISH_CYBER_ALERT:
                return hub_message

            is_announcement = bool(
                isinstance(hub, discord.TextChannel) and hub.is_news()
            )
            if not is_announcement:
                log.warning(
                    "CHANNEL_CYBER_ALERT (%s) is not an Announcement channel. "
                    "Messages are mirrored, but followers cannot receive crossposts.",
                    CHANNEL_CYBER_ALERT,
                )
                return hub_message

            queue_priority = ANNOUNCEMENT_PRIORITY.get(priority, 50)
            db.enqueue_announcement(
                message_id=hub_message.id,
                channel_id=hub_message.channel.id,
                priority=queue_priority,
                category=route,
                title=original_title,
                item=item,
                priority_name=priority,
            )
            log.debug(
                "[cyber-alert] queued for crosspost: %s (queue=%d)",
                truncate(original_title, 100),
                db.announcement_queue_size(),
            )
            return hub_message

    async def _final_queue_reconcile(self, queued: dict[str, Any]) -> bool:
        """Revalidate one queue candidate and collapse any remaining race duplicates.

        Returns True only when `queued` should continue to Discord publish().
        """
        item = queued.get("item") or {}
        message_id = queued["message_id"]

        # Legacy v3-v6 queue rows have no item_json. Preserve them rather than
        # dropping user data during migration; new v7 rows always have metadata.
        if item and ANNOUNCEMENT_FINAL_RECHECK:
            allowed, reason, score = stream_publish_decision("announcement-final", item)
            if not allowed:
                db.delete_announcement(message_id)
                db.increment("announcement_rejected_count")
                await self._safe_delete_hub_message(queued["channel_id"], message_id)
                log.info(
                    "[cyber-alert] final gate dropped: %s | %s",
                    truncate(queued.get("title", ""), 100), reason,
                )
                return False
            if score is not None:
                item["quality_score"] = score

        if not item:
            return True

        # Check again immediately before crosspost. This covers legacy duplicates
        # and any very tight inter-task race that survived pre-mirror merging.
        conflicts = db.find_queued_conflicts(item, queued.get("category", ""), exclude_message_id=message_id)
        if not conflicts:
            return True

        all_candidates = [queued] + conflicts
        winner = max(all_candidates, key=lambda x: int(x.get("strength", 0)))
        sources = list(dict.fromkeys(
            str(x.get("source", ""))
            for x in all_candidates if str(x.get("source", "")).strip()
        ))

        if winner["message_id"] != message_id:
            # Current candidate lost to a stronger equivalent still in queue.
            corrob = list(dict.fromkeys(winner.get("corroborators", []) + sources))
            corrob = [x for x in corrob if x != winner.get("source")]
            db.update_announcement(winner["message_id"], corroborators=corrob)
            db.delete_announcement(message_id)
            db.increment("announcement_merged_count")
            await self._safe_delete_hub_message(queued["channel_id"], message_id)
            log.info(
                "[cyber-alert] final resolver suppressed weaker queued copy: %s; winner=%s",
                truncate(queued.get("title", ""), 90), truncate(winner.get("title", ""), 90),
            )
            return False

        # Current candidate is strongest: prune weaker copies and annotate winner.
        corrob = list(dict.fromkeys(queued.get("corroborators", []) + sources))
        corrob = [x for x in corrob if x != queued.get("source")]
        for other in conflicts:
            db.delete_announcement(other["message_id"])
            await self._safe_delete_hub_message(other["channel_id"], other["message_id"])
            db.increment("announcement_merged_count")
        db.update_announcement(message_id, corroborators=corrob)

        try:
            channel = await self.get_target_channel(queued["channel_id"])
            message = await channel.fetch_message(message_id)
            if message.embeds:
                embed = discord.Embed.from_dict(message.embeds[0].to_dict())
                embed._fields = [
                    f for f in embed._fields
                    if f.get("name") not in {"📰 Also reported by", "🧭 Source resolution"}
                ]
                if corrob:
                    embed.add_field(
                        name="📰 Also reported by",
                        value=truncate(", ".join(corrob[:8]), 500),
                        inline=False,
                    )
                embed.add_field(
                    name="🧭 Source resolution",
                    value="Final pre-publish check merged equivalent queued reports and retained the strongest source.",
                    inline=False,
                )
                await message.edit(embed=embed)
        except Exception as exc:
            log.debug("Could not annotate reconciled queue winner %s: %s", message_id, exc)
        return True

    async def publish_one_announcement(self) -> None:
        async with self.announcement_lock:
            queued = db.next_announcement()
            if not queued:
                return

            message_id = queued["message_id"]
            channel_id = queued["channel_id"]

            if not await self._final_queue_reconcile(queued):
                return

            # Re-read because reconciliation may have updated priority/source metadata.
            queued = db.next_announcement()
            if not queued or queued["message_id"] != message_id:
                # A stronger item may now be at the head. Let the next scheduler tick
                # publish it rather than violating priority order.
                return

            try:
                channel = await self.get_target_channel(channel_id)
                if not isinstance(channel, discord.TextChannel) or not channel.is_news():
                    log.warning(
                        "Dropping queued announcement %s because channel %s is no longer an Announcement channel.",
                        message_id,
                        channel_id,
                    )
                    db.delete_announcement(message_id)
                    return
                message = await channel.fetch_message(message_id)

                if getattr(message.flags, "crossposted", False):
                    db.delete_announcement(message_id)
                    return

                await message.publish()
                db.delete_announcement(message_id)
                log.info(
                    "[cyber-alert] published to followers after final gate: %s (remaining queue=%d)",
                    truncate(queued.get("title", ""), 100),
                    db.announcement_queue_size(),
                )

            except discord.NotFound:
                db.delete_announcement(message_id)
                log.warning("Queued cyber-alert message %s no longer exists; removed from queue.", message_id)
            except discord.Forbidden as exc:
                db.bump_announcement_attempt(message_id)
                log.error(
                    "Cannot publish #cyber-alert announcement (permission/channel type): %s",
                    exc,
                )
            except discord.HTTPException as exc:
                db.bump_announcement_attempt(message_id)
                log.warning(
                    "Announcement crosspost deferred (HTTP %s): %s",
                    getattr(exc, "status", "?"),
                    exc,
                )
            except Exception as exc:
                db.bump_announcement_attempt(message_id)
                log.exception("Unexpected Announcement publish failure: %s", exc)

    async def enrich_cve_item(self, item: dict[str, Any]) -> dict[str, Any]:
        cves = item.get("cves") or extract_cves(
            f"{item.get('title', '')} {item.get('summary', '')}"
        )
        item["cves"] = cves

        if not cves:
            return item

        cve = cves[0]
        item["kev"] = item.get("kev", False) or cve in self.kev_cves

        if cve in self.enrichment_cache:
            item.update(self.enrichment_cache[cve])
            item["kev"] = item.get("kev", False) or cve in self.kev_cves
            return item

        assert self.session is not None

        epss_task = fetch_epss(self.session, cve)

        # NVD's unauthenticated API has a relatively small public rate budget.
        # Use it for high-signal/official/PoC items, or for everything when the
        # operator configured an NVD API key. EPSS remains lightweight for all CVEs.
        base_priority = classify_security(item)
        should_query_nvd = bool(NVD_API_KEY) or (
            base_priority in {"URGENT", "CRITICAL", "HIGH"}
            or item.get("type") == "POC"
            or item.get("source") in {"CERT-In", "CISA KEV"}
        )

        if should_query_nvd:
            epss, nvd = await asyncio.gather(
                epss_task,
                fetch_nvd_cvss(self.session, cve),
            )
        else:
            epss = await epss_task
            nvd = {}

        enrichment = {**epss, **nvd}
        self.enrichment_cache[cve] = enrichment
        item.update(enrichment)
        return item

    def select_route(self, item: dict[str, Any]) -> tuple[str, str]:
        if item.get("type") == "CTF":
            return "ctf", ctf_priority(item)

        if item.get("type") == "POC":
            return "poc", classify_security(item)

        if item.get("type") == "SOCIAL":
            return "breach", classify_security(item)

        priority = classify_security(item)
        if item.get("route_hint") == "breach":
            return "breach", priority
        if matches_any(BREACH_ROUTE_PATTERNS, item_text(item)):
            return "breach", priority
        if priority in {"URGENT", "CRITICAL"}:
            return "critical", priority

        if is_india_related(item) or item.get("route_hint") == "india":
            return "india", priority

        if item.get("route_hint") == "research":
            return "research", priority

        return "news", priority

    async def publish(self, item: dict[str, Any]) -> None:
        item = await self.enrich_cve_item(item)
        route, priority = self.select_route(item)

        # v8.3 final publication threshold is evaluated after CVE enrichment. This
        # ensures the four buttons appear only when the final security score is
        # below COMMUNITY_AUTO_PUBLISH_SCORE. CTF items do not use this score path.
        if item.get("type") != "CTF":
            final_score, _ = security_quality(item)
            item["quality_score"] = int(final_score)
            if int(final_score) < COMMUNITY_AUTO_PUBLISH_SCORE:
                item["auto_publish"] = False
                item["manual_review"] = True
                item["review_reason"] = (
                    f"Signal score {int(final_score)}/100 is below the community auto-publish "
                    f"threshold {COMMUNITY_AUTO_PUBLISH_SCORE}/100; moderator decision required."
                )
            elif not (route == "breach" and source_tier(item) >= 4 and TIER4_BREACH_FORCE_REVIEW):
                # A score >= threshold overrides older per-route score thresholds for
                # community publication, but never overrides hard trust policy.
                item["auto_publish"] = True
                item["manual_review"] = False

        # A Tier-4 breach may have a high urgency/relevance score while still
        # lacking trustworthy confirmation. Keep it in REVIEW state regardless of
        # numeric score so the embed never misleadingly says Publish=True.
        if route == "breach" and source_tier(item) >= 4 and TIER4_BREACH_FORCE_REVIEW and item.get("auto_publish", True):
            item["auto_publish"] = False
            item["manual_review"] = True
            item["review_reason"] = (
                "Tier-4 breach lead requires corroboration or moderator verification "
                "before public syndication."
            )

        channel_id = getattr(CHANNELS, route)
        channel = await self.get_target_channel(channel_id)

        if item.get("type") == "CTF":
            source_message, source_embed = await self.publish_ctf(channel, item, priority)
        else:
            source_message, source_embed = await self.publish_security(
                channel, item, priority, route
            )

        # v8.2 separates internal relevance from automatic public syndication.
        # Manual-review candidates are always visible in their topic channel, but
        # never enter the automatic Announcement queue. Optionally mirror them to
        # #cyber-alert as an unqueued draft so a moderator can manually Publish it.
        if item.get("auto_publish") is False:
            if MANUAL_REVIEW_MIRROR_TO_CYBER_ALERT:
                draft = await self.mirror_to_cyber_alert(
                    source_message=source_message,
                    source_embed=source_embed,
                    route=route,
                    priority=priority,
                    item=item,
                    queue_for_crosspost=False,
                )
                if draft is not None:
                    db.update_publication_review(source_message.id, hub_message_id=draft.id)
            else:
                log.info(
                    "[%s] manual-review only (Publish=false): %s",
                    route, truncate(item.get("title", ""), 100),
                )
            return

        # Every auto-approved categorized alert fans into the public hub. Tier-4
        # breach leads still remain internal unless a trusted/corroborating source
        # qualifies them for automatic syndication.
        public_ok, public_reason = public_alert_allowed(item, route)
        if public_ok:
            await self.mirror_to_cyber_alert(
                source_message=source_message,
                source_embed=source_embed,
                route=route,
                priority=priority,
                item=item,
            )
        else:
            log.info(
                "[%s] not mirrored to #cyber-alert: %s | %s",
                route, truncate(item.get("title", ""), 100), public_reason,
            )

    async def publish_security(
        self,
        channel: discord.abc.Messageable,
        item: dict[str, Any],
        priority: str,
        route: str,
    ) -> tuple[discord.Message, discord.Embed]:
        icon = {
            "URGENT": "🚨",
            "CRITICAL": "🔴",
            "HIGH": "🟠",
            "NEWS": "📰",
        }.get(priority, "📰")

        if item.get("type") == "POC":
            heading = "🧪 PoC / Exploit Intel"
        elif item.get("type") == "SOCIAL":
            heading = "🐦 Unverified Social Report"
        elif item.get("source") == "CERT-In":
            heading = "🇮🇳 CERT-In"
        elif item.get("source") == "CISA KEV":
            heading = "🇺🇸 CISA KEV"
        elif route == "india":
            heading = "🇮🇳 India Cyber"
        elif route == "research":
            heading = "🔬 Security Research"
        else:
            heading = "📰 Cyber Intelligence"

        color = {
            "URGENT": discord.Color.red(),
            "CRITICAL": discord.Color.red(),
            "HIGH": discord.Color.orange(),
            "NEWS": discord.Color.blue(),
        }.get(priority, discord.Color.blue())

        url = item.get("url") or None
        if url and not str(url).startswith(("http://", "https://")):
            url = None

        embed = discord.Embed(
            title=truncate(item.get("title", "Security update"), 256),
            description=truncate(item.get("summary", ""), 1800) or None,
            url=url,
            color=color,
        )
        embed.set_author(name=f"{heading} • {icon} {priority}")

        embed.add_field(name="Source", value=truncate(item.get("source", "Unknown"), 200), inline=True)

        qscore, qreasons = security_quality(item)
        if route == "breach":
            confidence = breach_confidence_label(item)
        elif source_tier(item) == 1:
            confidence = "Official"
        elif source_tier(item) == 2:
            confidence = "Technical research"
        elif source_tier(item) == 3:
            confidence = "High-signal curated"
        else:
            confidence = "Discovery / requires verification"
        embed.add_field(name="Confidence", value=confidence, inline=True)
        embed.add_field(name="Source tier", value=source_tier_label(item), inline=True)
        embed.add_field(name="Signal score", value=f"{qscore}/100", inline=True)
        if item.get("auto_publish") is False:
            embed.add_field(
                name="Publish",
                value="❌ False — manual verification required",
                inline=True,
            )
            if item.get("review_reason"):
                embed.add_field(
                    name="Manual review",
                    value=truncate(str(item["review_reason"]), 700),
                    inline=False,
                )
        else:
            embed.add_field(
                name="Publish",
                value="✅ True — eligible for automatic crosspost",
                inline=True,
            )
        if item.get("review_upgrade_from"):
            embed.add_field(
                name="Review resolution",
                value=truncate(str(item["review_upgrade_from"]), 700),
                inline=False,
            )
        if qreasons:
            embed.add_field(name="Why it matters", value=truncate(", ".join(qreasons[:4]), 350), inline=False)

        if item.get("official_severity"):
            embed.add_field(
                name="Official severity",
                value=str(item["official_severity"]),
                inline=True,
            )

        cves = item.get("cves") or []
        if cves:
            embed.add_field(
                name="CVE",
                value=", ".join(cves[:5]),
                inline=True,
            )

        if cves:
            embed.add_field(
                name="CISA KEV",
                value="✅ Known exploited" if item.get("kev") else "— Not in cached KEV",
                inline=True,
            )

        if item.get("cvss") is not None:
            cvss = str(item["cvss"])
            sev = item.get("cvss_severity", "")
            embed.add_field(
                name="CVSS",
                value=f"{cvss} {sev}".strip(),
                inline=True,
            )

        if item.get("epss") is not None:
            embed.add_field(
                name="EPSS",
                value=f"{float(item['epss']) * 100:.2f}%"
                      f" (pct {float(item.get('epss_percentile', 0)) * 100:.1f})",
                inline=True,
            )

        if item.get("required_action"):
            embed.add_field(
                name="Required action",
                value=truncate(item["required_action"], 900),
                inline=False,
            )

        if item.get("due_date"):
            embed.add_field(name="CISA due date", value=str(item["due_date"]), inline=True)

        if item.get("ransomware"):
            embed.add_field(name="Ransomware use", value=str(item["ransomware"]), inline=True)

        if item.get("social_unverified"):
            embed.add_field(
                name="Verification",
                value="⚠️ Unverified social-media report. Treat as a lead until corroborated by an official/company or reputable security source.",
                inline=False,
            )

        if item.get("type") == "POC":
            embed.add_field(
                name="PoC status",
                value="Public PoC/index update detected. Availability does not prove that the code is reliable or safe.",
                inline=False,
            )

        if item.get("published"):
            embed.set_footer(text=f"Published/updated: {truncate(str(item['published']), 150)}")
        else:
            embed.set_footer(text="Automated public cyber-intelligence feed")

        mention = None
        if item.get("auto_publish") is not False and priority in {"URGENT", "CRITICAL"} and THREAT_ROLE_ID:
            mention = f"<@&{THREAT_ROLE_ID}> {icon} threat alert"

        review_view = None
        if REVIEW_CONTROLS_ENABLED and item.get("auto_publish") is False:
            review_view = PublicationReviewView(self, "pending")

        source_message = await channel.send(
            content=mention,
            embed=embed,
            view=review_view,
            allowed_mentions=discord.AllowedMentions(roles=True, everyone=False, users=False),
        )
        if review_view is not None:
            db.save_publication_review(
                source_message_id=source_message.id,
                source_channel_id=source_message.channel.id,
                route=route,
                priority_name=priority,
                item=item,
                status="pending",
            )
        return source_message, embed

    async def publish_ctf(
        self,
        channel: discord.abc.Messageable,
        item: dict[str, Any],
        priority: str,
    ) -> tuple[discord.Message, discord.Embed]:
        india = is_india_related(item)
        flag = "🇮🇳 " if india else "🌍 "
        level_icon = {
            "NATIONAL": "⭐⭐⭐⭐⭐",
            "MAJOR": "⭐⭐⭐⭐",
            "RATED": "⭐⭐⭐",
            "COMMUNITY": "⭐⭐",
        }.get(priority, "⭐⭐")

        url = item.get("url") or item.get("ctftime_url") or None
        if url and not str(url).startswith(("http://", "https://")):
            url = None

        embed = discord.Embed(
            title=truncate(item.get("title", "CTF event"), 256),
            description=truncate(item.get("summary", ""), 1500) or None,
            url=url,
            color=discord.Color.gold(),
        )
        embed.set_author(name=f"{flag}🏴 CTF REGISTRATION • {priority} {level_icon}")
        embed.add_field(name="Source", value=truncate(item.get("source", "Unknown"), 200), inline=True)
        embed.add_field(name="Status", value=truncate(item.get("registration_status", "🟢 Upcoming"), 250), inline=True)

        registration_url = item.get("registration_url") or item.get("url")
        if registration_url and str(registration_url).startswith(("http://", "https://")):
            embed.add_field(
                name="Registration / Official page",
                value=f"[Open registration information]({registration_url})",
                inline=False,
            )

        if item.get("organizer"):
            embed.add_field(name="Organizer", value=truncate(item["organizer"], 300), inline=True)
        if item.get("format"):
            embed.add_field(name="Format", value=truncate(str(item["format"]), 200), inline=True)
        if item.get("location"):
            embed.add_field(name="Location", value=truncate(str(item["location"]), 300), inline=True)

        start_epoch = parse_iso_epoch(item.get("start"))
        finish_epoch = parse_iso_epoch(item.get("finish"))

        if start_epoch:
            embed.add_field(
                name="Starts",
                value=f"<t:{start_epoch}:F>\n<t:{start_epoch}:R>",
                inline=True,
            )
        if finish_epoch:
            embed.add_field(
                name="Ends",
                value=f"<t:{finish_epoch}:F>\n<t:{finish_epoch}:R>",
                inline=True,
            )

        if item.get("onsite") is not None and item.get("source") == "CTFtime":
            embed.add_field(
                name="Mode",
                value="📍 On-site" if item.get("onsite") else "🌐 Online",
                inline=True,
            )

        if item.get("weight"):
            embed.add_field(name="CTFtime weight", value=str(item["weight"]), inline=True)

        if item.get("ctftime_url"):
            embed.add_field(
                name="CTFtime",
                value=f"[Event page]({item['ctftime_url']})",
                inline=True,
            )

        embed.set_footer(
            text="Only upcoming/currently-registerable opportunities are published. Verify final eligibility, deadline and fees on the official page."
        )

        mention = None
        if CTF_MENTIONS and CTF_ROLE_ID and priority in {"NATIONAL", "MAJOR"}:
            mention = f"<@&{CTF_ROLE_ID}> 🏴 new {priority.lower()} CTF registration opportunity"

        source_message = await channel.send(
            content=mention,
            embed=embed,
            allowed_mentions=discord.AllowedMentions(roles=True, everyone=False, users=False),
        )
        return source_message, embed

    async def process_stream(
        self,
        stream: str,
        items: list[dict[str, Any]],
        pre_publish=None,
    ) -> None:
        # De-duplicate identical collector IDs inside this poll first.
        unique: dict[str, dict[str, Any]] = {x["id"]: x for x in items if x.get("id")}
        items = list(unique.values())

        if not db.initialized(stream) and not BACKFILL_ON_FIRST_RUN:
            # Mark the whole current snapshot seen to avoid startup floods, but
            # seed cross-source duplicate history only with items that satisfy the
            # current high-signal/CTF policy. A weak article should never block a
            # later trusted report of the same incident.
            db.mark_many_seen(items, stream)
            eligible_history = []
            for x in items:
                ok, _, _ = stream_publish_decision(stream, x)
                if ok:
                    eligible_history.append(x)
            db.record_many_history(eligible_history, stream)
            db.set_initialized(stream)
            db.set(f"history_seeded:{stream}", "1")
            log.info(
                "Initialized stream '%s' with %d existing items; no backfill posted; %d high-signal items seeded to history.",
                stream,
                len(items),
                len(eligible_history),
            )
            return

        if not db.initialized(stream):
            db.set_initialized(stream)

        # Fetch exact source-ID history in batched SQL queries.
        already_seen = db.seen_ids([item["id"] for item in items])
        if FEED_TRAVERSAL_LOGS and stream in {"rss", "poc", "ctf-search", "htb-ctf", "ctftime"}:
            source_counts: dict[str, int] = {}
            unseen_source_counts: dict[str, int] = {}
            for candidate in items:
                src = str(candidate.get("source", "Unknown"))
                source_counts[src] = source_counts.get(src, 0) + 1
                if candidate["id"] not in already_seen:
                    unseen_source_counts[src] = unseen_source_counts.get(src, 0) + 1
            log.info(
                "[stream %s] received=%d already_seen=%d unseen=%d sources=%s",
                stream, len(items), len(already_seen), len(items) - len(already_seen),
                ", ".join(
                    f"{src}:{count}/{unseen_source_counts.get(src, 0)}new"
                    for src, count in sorted(source_counts.items())
                ) or "none",
            )

        # Upgrade path from v3: the old DB knows exact item IDs but does not have
        # title/URL metadata. Seed dedupe_history from currently-visible items
        # that v3 had already marked seen. Existing DB history is therefore kept.
        if DEDUP_ENABLED and db.get(f"history_seeded:{stream}") != "1":
            seed_items = [item for item in items if item["id"] in already_seen]
            db.record_many_history(seed_items, stream)
            db.set(f"history_seeded:{stream}", "1")
            log.info(
                "[%s] seeded persistent duplicate history with %d previously seen items.",
                stream,
                len(seed_items),
            )

        # Oldest first where a parsable timestamp exists; otherwise stable source order.
        for item in reversed(items):
            if item["id"] in already_seen:
                continue

            allowed, filter_reason, quality_score = stream_publish_decision(stream, item)
            manual_review = False

            if not allowed:
                review_ok, review_reason = manual_review_decision(
                    item, filter_reason, quality_score
                )
                if review_ok:
                    review_score, _ = security_quality(item)
                    # v8.3 makes 70 the final community threshold even if an old
                    # .env still has legacy per-route values such as NEWS=82. If
                    # the *only* failure is that legacy numeric threshold and the
                    # item already scores >= COMMUNITY_AUTO_PUBLISH_SCORE, treat it
                    # as auto-approved here so review-history dedupe cannot suppress it.
                    legacy_score_only = str(filter_reason).startswith("quality score ")
                    if legacy_score_only and int(review_score) >= COMMUNITY_AUTO_PUBLISH_SCORE:
                        manual_review = False
                        item["auto_publish"] = True
                        item["manual_review"] = False
                        item["quality_score"] = review_score
                        item["quality_reason"] = (
                            f"score {review_score} meets community threshold "
                            f"{COMMUNITY_AUTO_PUBLISH_SCORE}"
                        )
                    else:
                        # Soft failure: useful/relevant enough for the topic channel,
                        # but not trusted enough for automatic public syndication.
                        manual_review = True
                        item["auto_publish"] = False
                        item["manual_review"] = True
                        item["quality_score"] = review_score
                        item["quality_reason"] = filter_reason
                        item["review_reason"] = review_reason
                        log.info(
                            "[%s] manual-review candidate score=%s: %s | %s",
                            stream, review_score, truncate(item.get("title", ""), 105), review_reason,
                        )
                else:
                    # Hard reject: remember the exact source item so stale/noisy
                    # content does not waste work every poll. Do not insert it into
                    # trusted cross-source history.
                    db.mark_seen(item["id"], stream, item.get("source", ""))
                    suffix = f" score={quality_score}" if quality_score is not None else ""
                    log.info(
                        "[%s] filtered%s: %s | %s",
                        stream, suffix, truncate(item.get("title", ""), 105), filter_reason,
                    )
                    continue
            else:
                item["auto_publish"] = True
                item["manual_review"] = False
                item["quality_score"] = quality_score
                item["quality_reason"] = filter_reason

                # Trust gate is independent of the numeric score. A Tier-4 breach
                # can be highly relevant/urgent yet still require corroboration.
                looks_like_breach = (
                    str(item.get("route_hint", "")) == "breach"
                    or matches_any(BREACH_ROUTE_PATTERNS, item_text(item))
                    or item.get("type") == "SOCIAL"
                )
                if looks_like_breach and source_tier(item) >= 4 and TIER4_BREACH_FORCE_REVIEW:
                    manual_review = True
                    item["auto_publish"] = False
                    item["manual_review"] = True
                    item["review_reason"] = (
                        "Tier-4 breach lead requires corroboration or moderator "
                        "verification before public syndication."
                    )

            # Trusted/public history is checked for both states. This prevents a
            # weak review candidate from re-posting after a stronger report already
            # covered the incident. Manual-review history is separate so an early
            # weak lead never blocks a later trusted source from auto-publishing.
            duplicate = db.find_duplicate(item)
            if duplicate is not None:
                db.mark_seen(item["id"], stream, item.get("source", ""))
                if not manual_review:
                    db.record_history(item, stream)
                log.info(
                    "[%s] duplicate skipped (%s, score=%.2f): %s | matches [%s] %s",
                    stream,
                    duplicate["reason"],
                    float(duplicate.get("score", 1.0)),
                    truncate(item.get("title", ""), 100),
                    duplicate.get("source", "history"),
                    truncate(duplicate.get("title", ""), 100),
                )
                continue

            if not manual_review:
                # A trusted report may resolve an earlier REVIEW lead. Do not treat
                # that lead as a duplicate blocker; instead annotate the stronger
                # item and let it auto-publish normally.
                review_match = db.find_review_duplicate(item)
                if review_match is not None:
                    item["review_upgrade_from"] = (
                        f"Earlier manual-review lead from {review_match.get('source') or 'unknown source'} "
                        f"was matched; this stronger report is now eligible for automatic publication."
                    )
                    item["_review_match_id"] = review_match.get("item_id", "")
                    log.info(
                        "[%s] review lead upgraded by trusted report: [%s] %s -> [%s] %s",
                        stream,
                        review_match.get("source", "review"),
                        truncate(review_match.get("title", ""), 75),
                        item.get("source", "trusted"),
                        truncate(item.get("title", ""), 75),
                    )

            if manual_review:
                review_duplicate = db.find_review_duplicate(item)
                if review_duplicate is not None:
                    db.mark_seen(item["id"], stream, item.get("source", ""))
                    db.record_review_history(item, stream)
                    log.info(
                        "[%s] manual-review duplicate skipped (%s, score=%.2f): %s | matches [%s] %s",
                        stream,
                        review_duplicate["reason"],
                        float(review_duplicate.get("score", 1.0)),
                        truncate(item.get("title", ""), 100),
                        review_duplicate.get("source", "review"),
                        truncate(review_duplicate.get("title", ""), 100),
                    )
                    continue

            try:
                if pre_publish is not None:
                    item = await pre_publish(item)
                await self.publish(item)
                # publish() performs the final post-enrichment 70-point community
                # decision, so trust its final state rather than the pre-enrichment
                # local flag used earlier in this loop.
                manual_review = item.get("auto_publish") is False
                db.mark_seen(item["id"], stream, item.get("source", ""))
                if manual_review:
                    db.record_review_history(item, stream)
                    log.info(
                        "[%s] posted for manual review (Publish=false): %s",
                        stream, truncate(item.get("title", ""), 120),
                    )
                else:
                    db.record_history(item, stream)
                    if item.get("_review_match_id"):
                        db.delete_review_history(str(item.get("_review_match_id")))
                    log.info("[%s] posted: %s", stream, truncate(item.get("title", ""), 120))
                await asyncio.sleep(0.8)
            except Exception as exc:
                # Do NOT mark seen/history on publish failure; retry next cycle.
                log.exception("[%s] publish failed for %s: %s", stream, item.get("title"), exc)

    @tasks.loop(seconds=1800)
    async def status_loop(self) -> None:
        """Refresh the single dashboard on the low-frequency heartbeat."""
        if CHANNEL_BOT_STATUS and STATUS_DASHBOARD_ENABLED:
            # Heartbeats intentionally refresh dynamic uptime/latency even when
            # semantic collector state has not changed. The edit lock/min-gap
            # still protects this PATCH from colliding with state transitions.
            await self.update_status_dashboard(force=True)

    @status_loop.before_loop
    async def before_status_loop(self) -> None:
        await self.wait_until_ready()

    @tasks.loop(seconds=360)
    async def announcement_publish_loop(self) -> None:
        """Publish at most one queued hub message per interval.

        Mirroring happens immediately. Crossposting is intentionally paced and
        persistent so a burst of RSS/CISA/CTF items does not hammer Discord's
        Announcement publish endpoint. Urgent/critical items jump ahead of news.
        """
        if not CHANNEL_CYBER_ALERT or not AUTO_PUBLISH_CYBER_ALERT:
            return
        await self.publish_one_announcement()

    @announcement_publish_loop.before_loop
    async def before_announcement_publish_loop(self) -> None:
        await self.wait_until_ready()

    # ------------------------------------------------------------------
    # Periodic loops
    # ------------------------------------------------------------------

    @tasks.loop(seconds=120)
    async def rss_loop(self) -> None:
        assert self.session is not None
        self.rss_cycle_no += 1
        cycle = self.rss_cycle_no
        started = time.monotonic()
        standard_feed_count = (len(BUILTIN_RSS_FEEDS) if ENABLE_BUILTIN_RSS else 0) + sum(map(len, [
            NEWS_RSS_FEEDS, RESEARCH_RSS_FEEDS, INDIA_RSS_FEEDS, BREACH_RSS_FEEDS
        ])) + (len(INDIA_NEWS_FEEDS) if ENABLE_DISCOVERY_NEWS else 0) + (
            len(BREACH_SEARCH_FEEDS) if ENABLE_BREACH_DISCOVERY_RSS else 0
        )
        poc_feed_count = len(POC_FEEDS) + len(EXPLOIT_RSS_FEEDS)
        log.info(
            "[rss-cycle #%d] START standard_feeds=%d poc_feeds=%d interval=%ss",
            cycle, standard_feed_count, poc_feed_count, max(60, RSS_INTERVAL_SECONDS),
        )
        try:
            articles = await collect_all_standard_rss(self.session)
            pocs = await collect_poc_feeds(self.session)
            await self.process_stream("rss", articles)
            await self.process_stream("poc", pocs)
            elapsed = time.monotonic() - started
            log.info(
                "[rss-cycle #%d] END articles=%d pocs=%d elapsed=%.2fs next_in~%ss",
                cycle, len(articles), len(pocs), elapsed, max(60, RSS_INTERVAL_SECONDS),
            )
            await self.mark_collector_success(
                "rss", f"cycle #{cycle}: {len(articles)} articles + {len(pocs)} PoC entries scanned in {elapsed:.1f}s"
            )
        except Exception as exc:
            log.exception("[rss-cycle #%d] FAILED: %s", cycle, exc)
            await self.mark_collector_error("rss", exc)

    @rss_loop.before_loop
    async def before_rss_loop(self) -> None:
        await self.wait_until_ready()

    @tasks.loop(seconds=300)
    async def official_loop(self) -> None:
        assert self.session is not None
        try:
            # CISA KEV
            kev_data = await get_cisa_kev(self.session)
            if kev_data:
                items = cisa_items(kev_data)
                self.kev_cves = {
                    x["cve"] for x in items if x.get("cve")
                }
                await self.process_stream("cisa-kev", items)

            # CERT-In
            cert_items = await collect_certin(self.session)

            async def enrich_new_cert(item):
                return await enrich_certin(self.session, item)

            await self.process_stream("cert-in", cert_items, enrich_new_cert)
            await self.mark_collector_success(
                "official", f"{len(items) if kev_data else 0} CISA KEV + {len(cert_items)} CERT-In entries scanned"
            )
        except Exception as exc:
            log.exception("Official-source loop failed: %s", exc)
            await self.mark_collector_error("official", exc)

    @official_loop.before_loop
    async def before_official_loop(self) -> None:
        await self.wait_until_ready()

    @tasks.loop(seconds=300)
    async def x_loop(self) -> None:
        await self.wait_until_ready()
        if not ENABLE_X_API or not X_BEARER_TOKEN:
            return
        assert self.session is not None
        try:
            items = await collect_x_breaches(self.session)
            await self.process_stream("x-breach", items)
            await self.mark_collector_success("x", f"{len(items)} candidate posts scanned")
        except Exception as exc:
            log.exception("X loop failed: %s", exc)
            await self.mark_collector_error("x", exc)

    @x_loop.before_loop
    async def before_x_loop(self) -> None:
        await self.wait_until_ready()

    @tasks.loop(seconds=1200)
    async def ctf_loop(self) -> None:
        assert self.session is not None
        try:
            ctftime_task = collect_ctftime(self.session)
            htb_task = collect_htb_events(self.session)
            search_task = collect_ctf_search_rss(self.session)

            ctftime_items, htb_items, search_items = await asyncio.gather(
                ctftime_task,
                htb_task,
                search_task,
            )

            # Separate streams keep first-run behavior sane.
            await self.process_stream("ctftime", ctftime_items)
            await self.process_stream("htb-ctf", htb_items)
            await self.process_stream("ctf-search", search_items)
            await self.mark_collector_success(
                "ctf",
                f"{len(ctftime_items)} CTFtime + {len(htb_items)} HTB + {len(search_items)} discovery entries scanned",
            )
        except Exception as exc:
            log.exception("CTF loop failed: %s", exc)
            await self.mark_collector_error("ctf", exc)

    @ctf_loop.before_loop
    async def before_ctf_loop(self) -> None:
        await self.wait_until_ready()


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    intents = discord.Intents.default()
    # This bot only sends notifications and does not need Message Content intent.
    bot = CyberIntelBot(intents=intents)
    bot.run(TOKEN, log_handler=None)


if __name__ == "__main__":
    main()
