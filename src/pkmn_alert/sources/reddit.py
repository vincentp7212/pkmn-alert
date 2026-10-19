"""Reddit source — reads the newest posts across one or more subreddits.

## Two paths: OAuth (preferred) and the public Atom feed (fallback)

Reddit now 403s its anonymous endpoints (both ``/r/xxx/.json`` and, as of
2026, ``/r/xxx/new.rss``) from datacenter/cloud IP ranges — including the
Azure pool GitHub Actions runs on. A descriptive User-Agent no longer
helps: the block is at the IP-reputation layer.

The fix is Reddit's *authenticated* API. When ``REDDIT_CLIENT_ID`` and
``REDDIT_CLIENT_SECRET`` are set (env or sources.yaml options), this source
uses the application-only client-credentials grant to get a bearer token
and reads ``https://oauth.reddit.com/r/a+b+c/new`` (JSON). Authenticated
requests are rate-limited per OAuth client (100 QPM), NOT per IP, so this
works from CI with no proxy. Create a free "script" app at
https://www.reddit.com/prefs/apps to get the id/secret.

Without credentials we fall back to the public Atom feed at
``/r/a+b+c/new.rss`` — still fine from a residential IP or behind a clean
proxy, just not from GitHub's runners.

## Multi-sub combined feed

Reddit supports ``/r/a+b+c/new.rss`` which returns the newest posts across
all named subreddits in a SINGLE HTTP request. This is a huge win vs. the
old per-sub loop:

  * one request => one rate-limit hit (previously N requests => cloud-ASN
    per-second throttle would 429 the 2nd+ request even with 6s spacing).
  * ~4x more subs covered for the same rate-limit budget.
  * simpler code — no ordering / partial-failure gymnastics.

## Signal quality

r/PokemonRestocks and r/PKMNTCGDeals are restock-focused. r/PokeInvesting
and r/pokemongoing are broader but often surface drops from a different
angle (invest hype spikes, casual collector chatter). Combined feed means
we catch signal from all four without paying 4x request cost.
"""

from __future__ import annotations

import logging
import os
import random
import re
from datetime import datetime, timedelta, timezone
from typing import Any

import feedparser
import httpx
from dateutil import parser as dateparser

from ..event import DropEvent
from .base import Source, SourceContext

log = logging.getLogger(__name__)

DEFAULT_SUBREDDITS = [
    "PokemonRestocks",
    "PKMNTCGDeals",
    "PokeInvesting",
    "pokemongoing",
]
DEFAULT_LIMIT = 25

# --- OAuth (authenticated API) ----------------------------------------------
#
# The anonymous .rss / .json endpoints now 403 from datacenter/cloud IP
# ranges (including GitHub Actions' Azure pool). Reddit's *authenticated*
# API is the sanctioned path and is rate-limited per OAuth client (100
# QPM) rather than per IP, so it works from CI without a proxy.
#
# We use the "application-only" client-credentials grant: a confidential
# ("script" or "web app") client needs only a client_id + secret, no user
# password, and gets read access to public listings — exactly what we need.
# Set REDDIT_CLIENT_ID / REDDIT_CLIENT_SECRET (env or sources.yaml options)
# to switch this source onto the OAuth path automatically.
OAUTH_TOKEN_URL = "https://www.reddit.com/api/v1/access_token"
OAUTH_API_BASE = "https://oauth.reddit.com"
# Refresh a little before the real expiry so a token never dies mid-request.
OAUTH_EXPIRY_BUFFER = timedelta(seconds=60)

# Cooldown when Reddit sends us a 429 or 403. Both signal "back off on this
# UA/IP for a while"; 15 min is enough to clear their sliding window.
RATE_LIMIT_COOLDOWN = timedelta(minutes=15)

# Reddit strips HTML tags from feed entries; we keep this regex around to
# defensively clean any residual tags before matching keywords.
_TAG_RE = re.compile(r"<[^>]+>")

# --- Classification patterns -------------------------------------------------
#
# All matchers below use ``\b`` word boundaries because a naive substring
# check produced a real-world false positive: the title
#   "Pokemon Center PSA 10 Special Delivery Bidoof Sells $3500 ..."
# was classified as kind=restock because ``"live" in "delivery"`` is True,
# then paired with retailer=pokemoncenter (title mentions "Pokemon Center"),
# then survived the ``me`` subscriber's filter, then ntfy'd the user's phone
# at 04:49 UTC on 2026-07-20. See tests/test_reddit_parser.py for regressions.
#
# Ordering matters: queue > preorder > restock > deal > news. The first
# pattern that matches wins.
_KIND_MATCHERS: list[tuple[str, re.Pattern[str]]] = [
    ("queue",    re.compile(r"\b(queue|waiting[\s-]?room)\b", re.I)),
    ("preorder", re.compile(r"\bpre[-\s]?orders?\b", re.I)),
    # ``live`` here must be a WORD, not a substring of ``delivery``/``alive``.
    # ``drops?`` and ``dropped`` are separate word forms; ``dropping`` is
    # intentionally NOT included because "price is dropping" is speculation,
    # not a live restock signal.
    ("restock",  re.compile(
        r"\b(restock|back\s+in\s+stock|is\s+live|now\s+live|goes?\s+live"
        r"|live\s+now|just\s+dropped|dropped|drops?\s+now|drops?)\b",
        re.I,
    )),
    ("deal",     re.compile(r"\b(deal|discount|\d+\s*%\s*off|clearance|on\s+sale)\b", re.I)),
]

_RETAILER_MATCHERS: list[tuple[str, re.Pattern[str]]] = [
    ("pokemoncenter", re.compile(r"\b(pok[eé]mon\s+center|pokemoncenter|pokecenter|pkmn\s+center|pkc)\b", re.I)),
    ("target",        re.compile(r"\btarget\b", re.I)),
    ("walmart",       re.compile(r"\bwal[\s-]?mart\b", re.I)),
    ("bestbuy",       re.compile(r"\bbest\s?buy\b", re.I)),
    ("costco",        re.compile(r"\bcostco\b", re.I)),
    ("amazon",        re.compile(r"\bamazon\b", re.I)),
    ("gamestop",      re.compile(r"\bgamestop\b", re.I)),
]

# --- Noise blocklist ---------------------------------------------------------
#
# r/PokeInvesting in particular is full of secondary-market chatter that
# frequently mentions "Pokemon Center" but is NOT a drop announcement.
# We downgrade posts matching any of these patterns to kind=news +
# retailer=unknown so subscriber filters (which reject news / require a
# real retailer) never wake the user up. Keeping these as separate rules
# rather than deleting them entirely so the debug-stdout subscriber still
# logs them for review.
_NOISE_MATCHERS: list[re.Pattern[str]] = [
    # Secondary-market sale posts: "Sells $3500", "Sold for $2850", etc.
    re.compile(r"\bsells?\s+(?:for\s+)?\$", re.I),
    re.compile(r"\bsold\s+(?:for\s+)?\$", re.I),
    # eBay affiliate/promotion posts
    re.compile(r"\bpromotion\s+by\s+ebay\b", re.I),
    re.compile(r"\bebay\s+sales?\b", re.I),
    # Analytics / price-movement posts
    re.compile(r"\bpast\s+(?:year|month|week|day|quarter)\b", re.I),
    re.compile(r"\bup\s+\d+\s*%", re.I),
    re.compile(r"\bdown\s+\d+\s*%", re.I),
]


# --- Proxy pool --------------------------------------------------------------
#
# Reddit 403s datacenter IPs (GitHub's Azure range). A pool of residential
# proxies lets us borrow a trusted IP. The list is supplied via the
# ``PROXY_LIST`` env var (a GitHub Actions secret — never committed), one
# ``host:port:user:pass`` entry per line (newlines, commas or spaces all work).
# Parsed once and cached.
_PROXY_CACHE: list[str] | None = None


def _proxy_urls() -> list[str]:
    global _PROXY_CACHE
    if _PROXY_CACHE is not None:
        return _PROXY_CACHE
    raw = os.environ.get("PROXY_LIST", "")
    urls: list[str] = []
    for entry in re.split(r"[\s,]+", raw.strip()):
        if not entry:
            continue
        parts = entry.split(":")
        if len(parts) != 4:
            continue  # skip malformed lines silently (never echo the value)
        host, port, user, pw = parts
        urls.append(f"http://{user}:{pw}@{host}:{port}")
    _PROXY_CACHE = urls
    return urls


def _is_noise(title: str) -> bool:
    """True if the title looks like secondary-market/analytics chatter that
    should never reach an end-user notification, regardless of what keywords
    it happens to contain."""
    return any(p.search(title) for p in _NOISE_MATCHERS)


class RedditSource(Source):
    def fetch(self, ctx: SourceContext) -> list[DropEvent]:
        subs: list[str] = self.options.get("subreddits") or DEFAULT_SUBREDDITS
        limit: int = int(self.options.get("limit", DEFAULT_LIMIT))
        # No default keyword_hints: the configured subs are restock-focused,
        # so we let every post through and rely on per-subscriber
        # `filters.keywords` for the final cut.
        keyword_hint: list[str] = [
            k.lower() for k in self.options.get("keyword_hints", [])
        ]

        if not subs:
            log.warning("[%s] no subreddits configured; nothing to fetch", self.id)
            return []

        # Reddit's built-in multi-sub feed: /r/a+b+c/... returns the newest
        # posts across all named subs in ONE request. Single-sub setups
        # collapse cleanly to /r/a/...
        combined = "+".join(subs)

        # Prefer the authenticated API when credentials are configured — it's
        # the only path that works from cloud IPs. Fall back to the public
        # Atom feed otherwise (works from residential IPs / behind a proxy).
        if self._oauth_creds():
            return self._fetch_oauth(ctx, combined, limit, keyword_hint)
        return self._fetch_rss(ctx, combined, limit, keyword_hint)

    # --- RSS path (public Atom feed, anonymous) ------------------------------

    def _fetch_rss(
        self, ctx: SourceContext, combined: str, limit: int, keyword_hint: list[str]
    ) -> list[DropEvent]:
        url = f"https://www.reddit.com/r/{combined}/new.rss?limit={limit}"

        resp = self._get(url, ctx)
        if resp is None:
            return []

        if resp.status_code in (429, 403):
            log.warning(
                "[%s] reddit returned HTTP %s on combined feed; cooling down %s",
                self.id, resp.status_code, RATE_LIMIT_COOLDOWN,
            )
            now = datetime.now(tz=timezone.utc)
            ctx.state.set_cooldown(self.id, now + RATE_LIMIT_COOLDOWN)
            return []

        if resp.status_code != 200:
            log.warning(
                "[%s] reddit returned HTTP %s on combined feed",
                self.id, resp.status_code,
            )
            return []

        parsed = feedparser.parse(resp.content)
        if parsed.bozo and not parsed.entries:
            log.warning(
                "[%s] reddit combined feed parse failed: %s",
                self.id, parsed.bozo_exception,
            )
            return []

        # State-side dedupe against the most-recently-seen entry across the
        # combined feed. This is best-effort — the main pipeline's per-event
        # dedupe (state.seen) is the source of truth. This just lets us bail
        # out of the loop early once we hit a known entry, saving a few
        # microseconds of parsing on quiet ticks.
        meta = ctx.state.source_meta.setdefault(self.id, {})
        last_seen_id = meta.get("last_id_combined")
        first_new_id: str | None = None

        events: list[DropEvent] = []
        for entry in parsed.entries:
            entry_id: str = getattr(entry, "id", "") or ""
            if entry_id and entry_id == last_seen_id:
                break
            if first_new_id is None and entry_id:
                first_new_id = entry_id

            title = (getattr(entry, "title", "") or "").strip()
            if not title:
                continue

            if keyword_hint and not any(k in title.lower() for k in keyword_hint):
                continue

            link = getattr(entry, "link", "") or ""
            # Best-effort recover which sub this came from (Reddit stamps
            # the entry.tags with subreddit info in the combined feed).
            sub_name = _extract_subreddit(entry) or ""

            # Secondary-market / analytics chatter gets downgraded to
            # news+unknown so subscriber `kinds` / `retailers` filters
            # naturally exclude it. See _NOISE_MATCHERS for rationale.
            if _is_noise(title):
                kind = "news"
                retailer = "unknown"
            else:
                kind = _infer_kind(title)
                retailer = _infer_retailer(title)

            events.append(
                DropEvent(
                    source=self.id,
                    title=title,
                    url=link,
                    detected_at=_entry_time(entry),
                    kind=kind,
                    region="US",
                    retailer=retailer,
                    raw={"subreddit": sub_name, "id": entry_id},
                )
            )

        if first_new_id:
            meta["last_id_combined"] = first_new_id

        return events

    def _get(self, url: str, ctx: SourceContext) -> httpx.Response | None:
        headers = {
            # Reddit-recommended format. Any unique descriptive string
            # works; do NOT masquerade as a browser (that gets 429'd
            # almost immediately since Reddit expects real browsers
            # to be logged in).
            "User-Agent": ctx.user_agent,
            "Accept": "application/atom+xml, application/rss+xml, application/xml, text/xml",
            "Accept-Language": "en-US,en;q=0.9",
        }

        proxies = _proxy_urls()
        if not proxies:
            # No proxy pool configured — go direct (works from a residential
            # IP; this is the local / Mac-agent path).
            try:
                return httpx.get(url, headers=headers, timeout=ctx.timeout_s, follow_redirects=True)
            except httpx.HTTPError as exc:
                log.warning("[%s] reddit fetch failed: %s", self.id, exc)
                return None

        # Proxy-pool path (cloud): each IP in the pool is a single sticky
        # residential IP that Reddit throttles to ~1 request before 429, but
        # a *fresh* IP returns 200. So rotate through the shuffled pool and
        # retry on 403/429 until one lands clean. We never log the IP/creds —
        # only an attempt counter — because GitHub only masks the exact secret
        # blob, not individual lines printed on their own.
        max_attempts = min(int(self.options.get("proxy_max_attempts", 6)), len(proxies))
        order = random.sample(proxies, len(proxies))
        last: httpx.Response | None = None
        for i in range(max_attempts):
            proxy = order[i]
            try:
                with httpx.Client(
                    proxy=proxy, timeout=ctx.timeout_s, follow_redirects=True, trust_env=False
                ) as client:
                    resp = client.get(url, headers=headers)
            except httpx.HTTPError as exc:
                log.warning("[%s] reddit proxy attempt %d/%d failed: %s",
                            self.id, i + 1, max_attempts, type(exc).__name__)
                continue
            if resp.status_code == 200:
                if i:
                    log.info("[%s] reddit ok via proxy attempt %d/%d", self.id, i + 1, max_attempts)
                return resp
            log.info("[%s] reddit proxy attempt %d/%d got HTTP %s; rotating",
                     self.id, i + 1, max_attempts, resp.status_code)
            last = resp
        log.warning("[%s] all %d proxy attempts failed", self.id, max_attempts)
        return last

    # --- OAuth path (authenticated JSON API) ---------------------------------

    def _oauth_creds(self) -> tuple[str, str] | None:
        """(client_id, client_secret) from sources.yaml options or env, or None.

        Options win over env so a per-source override is possible, but the
        normal case is the two REDDIT_* secrets injected by the workflow."""
        cid = (self.options.get("client_id") or os.environ.get("REDDIT_CLIENT_ID") or "").strip()
        csec = (self.options.get("client_secret") or os.environ.get("REDDIT_CLIENT_SECRET") or "").strip()
        return (cid, csec) if cid and csec else None

    def _get_token(self, ctx: SourceContext) -> str | None:
        """Return a valid app-only bearer token, reusing a cached one from
        state until it nears expiry. Returns None on failure (caller logs)."""
        meta = ctx.state.source_meta.setdefault(self.id, {})
        now = datetime.now(tz=timezone.utc)

        cached = meta.get("oauth_token")
        expiry_raw = meta.get("oauth_expiry")
        if cached and expiry_raw:
            try:
                if dateparser.parse(expiry_raw) > now:
                    return cached
            except (ValueError, TypeError):
                pass  # corrupt expiry -> fetch a fresh token

        creds = self._oauth_creds()
        if not creds:
            return None
        try:
            resp = httpx.post(
                OAUTH_TOKEN_URL,
                auth=creds,  # HTTP Basic (client_id, client_secret)
                data={"grant_type": "client_credentials"},
                headers={"User-Agent": ctx.user_agent},
                timeout=ctx.timeout_s,
            )
        except httpx.HTTPError as exc:
            log.warning("[%s] reddit token request failed: %s", self.id, exc)
            return None

        if resp.status_code != 200:
            log.warning(
                "[%s] reddit token endpoint returned HTTP %s (check client id/secret)",
                self.id, resp.status_code,
            )
            return None

        try:
            payload = resp.json()
        except ValueError:
            log.warning("[%s] reddit token response was not JSON", self.id)
            return None

        token = payload.get("access_token")
        if not token:
            log.warning("[%s] reddit token response had no access_token", self.id)
            return None

        expires_in = int(payload.get("expires_in", 3600))
        meta["oauth_token"] = token
        meta["oauth_expiry"] = (
            now + timedelta(seconds=expires_in) - OAUTH_EXPIRY_BUFFER
        ).isoformat()
        log.info("[%s] obtained reddit app-only token (expires_in=%ss)", self.id, expires_in)
        return token

    def _fetch_oauth(
        self, ctx: SourceContext, combined: str, limit: int, keyword_hint: list[str]
    ) -> list[DropEvent]:
        token = self._get_token(ctx)
        if token is None:
            return []

        url = f"{OAUTH_API_BASE}/r/{combined}/new?limit={limit}&raw_json=1"
        headers = {"User-Agent": ctx.user_agent, "Authorization": f"bearer {token}"}

        try:
            resp = httpx.get(url, headers=headers, timeout=ctx.timeout_s, follow_redirects=True)
            # A 401 means our cached token went stale early — drop it and retry once.
            if resp.status_code == 401:
                ctx.state.source_meta.setdefault(self.id, {}).pop("oauth_token", None)
                token = self._get_token(ctx)
                if token is None:
                    return []
                headers["Authorization"] = f"bearer {token}"
                resp = httpx.get(url, headers=headers, timeout=ctx.timeout_s, follow_redirects=True)
        except httpx.HTTPError as exc:
            log.warning("[%s] reddit oauth fetch failed: %s", self.id, exc)
            return []

        if resp.status_code in (429, 403):
            log.warning(
                "[%s] reddit oauth returned HTTP %s; cooling down %s",
                self.id, resp.status_code, RATE_LIMIT_COOLDOWN,
            )
            ctx.state.set_cooldown(self.id, datetime.now(tz=timezone.utc) + RATE_LIMIT_COOLDOWN)
            return []
        if resp.status_code != 200:
            log.warning("[%s] reddit oauth returned HTTP %s", self.id, resp.status_code)
            return []

        try:
            children = resp.json().get("data", {}).get("children", [])
        except ValueError:
            log.warning("[%s] reddit oauth response was not JSON", self.id)
            return []

        meta = ctx.state.source_meta.setdefault(self.id, {})
        last_seen_id = meta.get("last_id_combined")
        first_new_id: str | None = None

        events: list[DropEvent] = []
        for child in children:
            post = child.get("data", {}) or {}
            entry_id = post.get("name") or ""  # fullname, e.g. t3_abc123
            if entry_id and entry_id == last_seen_id:
                break
            if first_new_id is None and entry_id:
                first_new_id = entry_id

            title = (post.get("title") or "").strip()
            if not title:
                continue
            if keyword_hint and not any(k in title.lower() for k in keyword_hint):
                continue

            permalink = post.get("permalink") or ""
            link = f"https://www.reddit.com{permalink}" if permalink else (post.get("url") or "")
            sub_name = post.get("subreddit") or ""
            created = post.get("created_utc")
            when = (
                datetime.fromtimestamp(float(created), tz=timezone.utc)
                if created is not None
                else datetime.now(tz=timezone.utc)
            )

            if _is_noise(title):
                kind, retailer = "news", "unknown"
            else:
                kind, retailer = _infer_kind(title), _infer_retailer(title)

            events.append(
                DropEvent(
                    source=self.id,
                    title=title,
                    url=link,
                    detected_at=when,
                    kind=kind,
                    region="US",
                    retailer=retailer,
                    raw={"subreddit": sub_name, "id": entry_id},
                )
            )

        if first_new_id:
            meta["last_id_combined"] = first_new_id
        return events


def _extract_subreddit(entry: Any) -> str | None:
    """Best-effort pull the subreddit name out of a combined-feed entry.

    Reddit's Atom entries carry a ``<category term="r/foo"/>`` tag; feedparser
    exposes it as ``entry.tags[i].term``. Returns just the name (no ``r/``
    prefix) or None if the shape doesn't match."""
    tags = getattr(entry, "tags", None) or []
    for tag in tags:
        term = getattr(tag, "term", "") or ""
        if term.startswith("r/"):
            return term[2:]
    # Fallback: parse from the entry link, e.g. https://www.reddit.com/r/foo/comments/...
    link = getattr(entry, "link", "") or ""
    m = re.search(r"reddit\.com/r/([^/]+)/", link)
    return m.group(1) if m else None


def _entry_time(entry: Any) -> datetime:
    for key in ("published", "updated"):
        raw = getattr(entry, key, None)
        if raw:
            try:
                return dateparser.parse(raw).astimezone(timezone.utc)
            except (ValueError, TypeError):
                continue
    return datetime.now(tz=timezone.utc)


def _infer_kind(title: str) -> str:
    for label, pattern in _KIND_MATCHERS:
        if pattern.search(title):
            return label
    return "news"


def _infer_retailer(title: str) -> str:
    clean = _TAG_RE.sub("", title)
    for label, pattern in _RETAILER_MATCHERS:
        if pattern.search(clean):
            return label
    return "unknown"
