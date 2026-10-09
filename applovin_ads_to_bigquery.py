#!/usr/bin/env python3
"""
AppLovin Ads -> BigQuery  ·  v1.0  (2026-10-09)
==============================================================================
WHAT
  Loads AppLovin Ads data (the ADVERTISER / UA side, formerly AppDiscovery):
  spend, installs, impressions and clicks per campaign / platform / country /
  day, plus an optional cohort table (revenue / retention by install day).

  This is NOT MAX. MAX ad revenue keeps flowing through applovin_to_bigquery.py,
  untouched. This loader has its own secret (APPLOVIN_ADS_REPORT_KEY), its own
  dataset (applovin_ads) and its own workflow (applovin_ads_sync.yml).

API
  GET https://r.applovin.com/report?report_type=advertiser
  All data is UTC. Dates must be inside the last 45 days.

TABLES   (dataset = $BQ_DATASET, e.g. applovin_ads)
  campaign_country_daily  grain: day x campaign_key x platform x country  (realtime)
  campaign_cohort_daily   grain: same, but day = install (cohort) day     (day_column=day)
  load_log                one row per load run: status, counts, API totals, full errors
  apps_correction_map     manual package -> app master overrides (used by staging SQL)

SAFETY: why this cannot silently corrupt data
  1. Reconciliation  Every day's detail rows are summed and compared with a separate
                     day-level totals request. Settled days must match to rounding
                     (installs/impressions exactly). Recent days (today, yesterday)
                     may only GROW by a bounded amount between the two calls. A day
                     that fails, even after a single-day re-fetch, is NOT written.
  2. Paging          limit/offset until an EMPTY page (survives silent server caps).
                     Overlapping pages (duplicate rows) are detected and the chunk
                     is re-fetched day by day; still duplicated -> refuse.
  3. Drift guard     A day whose spend OR installs would drop more than MAX_CHANGE_PCT
                     (50%) vs BigQuery is NOT replaced; a settled day that would jump
                     by more than that is not replaced either. This protects history
                     from API/key glitches. Override for one run: FORCE_REPLACE=true.
  4. Atomic replace  Per-day DELETE+INSERT inside ONE BigQuery transaction, from a
                     staged batch load; no streaming buffer, no half-written days;
                     post-write row-count verification.
  5. Columns         An optional column the API rejects (or omits) is dropped with a
                     warning, and its EXISTING values in BigQuery are preserved (never
                     overwritten with NULL). A required column rejected, missing, or
                     empty in every row -> red, nothing written.
  6. Honest exit     Transient trouble (AppLovin or Google side) -> green + warning,
                     unless the last successful load is older than STALE_HOURS -> red.
                     Auth / config / data problems -> red. Paused campaigns -> green.
                     A total time budget (RUN_BUDGET_SEC) keeps the job from being
                     killed by the runner timeout.
  7. Secret hygiene  The report key is redacted from every log line, annotation and
                     traceback, and URL query strings are stripped from exception text.
                     This is a PUBLIC repo, so campaign names and money values are never
                     printed; full error details and API totals go to load_log only.

MODES  (env MODE)
  load      normal run (default)
  dry-run   fetch + every check + the write plan; writes NOTHING
  probe     tests the key and columns; BigQuery not needed

CLI
  python applovin_ads_to_bigquery.py --print-ddl [project] [dataset]
"""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import logging
import math
import os
import random
import re
import sys
import time
import traceback
import uuid
from collections import defaultdict
from dataclasses import dataclass, field
from urllib.parse import quote, quote_plus

import requests

VERSION = "1.0"
LOG = logging.getLogger("applovin_ads")
DEFAULT_API_URL = "https://r.applovin.com/report"
API_MAX_LOOKBACK = 44          # the API accepts dates within the last 45 days -> today-44 .. today
CORE_PROBE_LAG = 2             # column check on a settled day
COHORT_PROBE_LAG = 10          # column check on a mature cohort (young cohorts may lack values)


# =============================================================================
# Errors
# =============================================================================
class LoaderError(Exception):
    """Base class."""


class ConfigError(LoaderError):
    """Needs a human (bad env, missing secret, rejected required column) -> red."""


class AuthError(ConfigError):
    """Report key rejected (401/403)."""


class DataError(LoaderError):
    """The API returned something we refuse to load -> red, nothing written."""


class PostWriteCheckError(DataError):
    """The transaction COMMITTED but the post-write check failed or could not run."""


class CommitStateUnknown(DataError):
    """The transaction query raised: it may or may not have committed -> red, check by hand."""


class TransientAPIError(LoaderError):
    """Network / 5xx / 429 still failing after all retries, or time budget exhausted."""


class RequestRejected(LoaderError):
    """HTTP 4xx (other than 401/403/408/429), or JSON 'code' 4xx."""

    def __init__(self, status: int, body: str):
        super().__init__(f"HTTP {status}: {body}")
        self.status = status
        self.body = body


class _RetryableBody(Exception):
    """HTTP 200 whose body is not usable yet (HTML, empty, code 5xx). Retried."""


class _DuplicateRows(Exception):
    """Two rows with identical dimensions: overlapping pages."""


# =============================================================================
# Secret redaction (PUBLIC repo: GitHub masks the raw secret, but not its
# URL-encoded form; requests puts the full URL inside exception messages)
# =============================================================================
class Redactor:
    _KEY_IN_URL = re.compile(r"(api_key=)[^&\s'\"<>]+", re.IGNORECASE)

    def __init__(self) -> None:
        self._secrets: list[str] = []

    def add(self, secret: str | None) -> None:
        if not secret:
            return
        for form in {secret, quote(secret, safe=""), quote_plus(secret), quote(secret)}:
            if len(form) >= 4 and form not in self._secrets:
                self._secrets.append(form)
        self._secrets.sort(key=len, reverse=True)

    def __call__(self, text: object) -> str:
        s = str(text)
        for secret in self._secrets:
            s = s.replace(secret, "***")
        return self._KEY_IN_URL.sub(r"\1***", s)


REDACT = Redactor()
_QUERY_STRING = re.compile(r"\?[^\s'\"()<>]+")


def safe_exc(e: object) -> str:
    """Exception text without ANY URL query string (requests embeds the full URL,
    api_key included, in ConnectionError/Timeout messages), then redacted."""
    return REDACT(_QUERY_STRING.sub("?<query hidden>", str(e)))


def public_exc(e: BaseException) -> str:
    """Short, data-free description for PUBLIC logs. Google errors can quote cell values
    (e.g. a campaign name in a load-job parse error) -> only type, code and reason."""
    try:
        from google.api_core import exceptions as gexc
        if isinstance(e, gexc.GoogleAPICallError):
            reasons = sorted({str(x.get("reason")) for x in (getattr(e, "errors", None) or []) if isinstance(x, dict)})
            return f"{type(e).__name__} (code {getattr(e, 'code', '?')}, reason {','.join(reasons) or '?'})"
    except ImportError:  # pragma: no cover
        pass
    return f"{type(e).__name__}: {safe_exc(e)[:300]}"


_TRANSIENT_REASONS = {"ratelimitexceeded", "backenderror", "internalerror", "jobbackenderror"}


def google_reasons(e: BaseException) -> set:
    return {str(x.get("reason", "")).lower() for x in (getattr(e, "errors", None) or []) if isinstance(x, dict)}


def is_transient_infra(e: BaseException) -> bool:
    """Google/BigQuery/network hiccups that a later run will get past."""
    try:
        from google.api_core import exceptions as gexc
        if isinstance(e, (gexc.ServiceUnavailable, gexc.InternalServerError, gexc.BadGateway,
                          gexc.GatewayTimeout, gexc.TooManyRequests, gexc.RetryError, gexc.DeadlineExceeded)):
            return True
        if isinstance(e, gexc.GoogleAPICallError) and google_reasons(e) & _TRANSIENT_REASONS:
            return True     # e.g. 403 rateLimitExceeded, 400 backendError
    except ImportError:  # pragma: no cover
        pass
    try:
        from google.auth import exceptions as gauth
        if isinstance(e, gauth.TransportError):
            return True
        if isinstance(e, gauth.GoogleAuthError) and getattr(e, "retryable", False):
            return True     # RefreshError(retryable=True) after token-endpoint 5xx
    except ImportError:  # pragma: no cover
        pass
    return isinstance(e, (requests.ConnectionError, requests.Timeout, ConnectionError, TimeoutError))


class RedactingFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        try:
            msg = record.getMessage()
        except Exception:  # noqa: BLE001 - never let logging crash the loader
            return True
        clean = REDACT(msg)
        if record.exc_info:
            clean += "\n" + safe_exc("".join(traceback.format_exception(*record.exc_info)))
            record.exc_info = None
            record.exc_text = None
        if clean != msg:
            record.msg, record.args = clean, ()
        return True


def setup_logging() -> None:
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)-7s %(message)s", "%H:%M:%S"))
    handler.addFilter(RedactingFilter())
    root = logging.getLogger()
    root.handlers[:] = [handler]
    root.setLevel(logging.INFO)
    for noisy in ("urllib3", "requests", "google", "google.auth", "google.cloud"):
        logging.getLogger(noisy).setLevel(logging.ERROR)


def gh_annotation(level: str, message: str) -> None:
    """GitHub ::warning:: / ::error:: line (redacted, single line)."""
    msg = REDACT(message).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    print(f"::{level}::{msg}", flush=True)


# =============================================================================
# Config (every env var validated; destination is NEVER defaulted)
# =============================================================================
def _env(name: str) -> str | None:
    v = os.environ.get(name)
    if v is None or v.strip() == "":
        return None
    return v.strip()


def env_int(name: str, default: int, lo: int, hi: int) -> int:
    raw = _env(name)
    if raw is None:
        return default
    try:
        v = int(raw)
    except ValueError:
        raise ConfigError(f"{name}={raw!r} is not an integer") from None
    if not lo <= v <= hi:
        raise ConfigError(f"{name}={v} is outside [{lo}, {hi}]")
    return v


def env_float(name: str, default: float, lo: float, hi: float) -> float:
    raw = _env(name)
    if raw is None:
        return default
    try:
        v = float(raw)
    except ValueError:
        raise ConfigError(f"{name}={raw!r} is not a number") from None
    if not (math.isfinite(v) and lo <= v <= hi):
        raise ConfigError(f"{name}={v} is outside [{lo}, {hi}]")
    return v


def env_bool(name: str, default: bool) -> bool:
    raw = _env(name)
    if raw is None:
        return default
    low = raw.lower()
    if low in ("1", "true", "yes", "y", "on"):
        return True
    if low in ("0", "false", "no", "n", "off"):
        return False
    raise ConfigError(f"{name}={raw!r} is not a boolean (true/false)")


@dataclass(frozen=True)
class Config:
    api_key: str
    api_url: str
    mode: str
    project: str | None
    dataset: str | None
    location: str
    creds_json: str | None
    lookback_days: int
    chunk_days: int
    page_limit: int
    max_pages: int
    include_cohort: bool
    force_replace: bool
    max_change_pct: float
    guard_min_cost: float
    guard_min_conv: int
    reconcile_pct: float
    recent_growth_pct: float
    stale_hours: int
    recent_days: int
    max_retry_days: int
    http_attempts: int
    http_read_timeout: int
    backoff_base: float
    request_pause: float
    run_budget_sec: int
    run_id: str
    lookback_clamped_from: int | None = None

    @staticmethod
    def from_env() -> "Config":
        key = _env("APPLOVIN_ADS_REPORT_KEY")
        if not key:
            raise ConfigError(
                "APPLOVIN_ADS_REPORT_KEY is empty. Add the AppLovin **Ads** Report Key under "
                "repo Settings -> Secrets and variables -> Actions."
            )
        REDACT.add(key)
        mode = (_env("MODE") or "load").lower()
        if mode not in ("load", "dry-run", "probe"):
            raise ConfigError(f"MODE={mode!r} must be load | dry-run | probe")

        project = _env("GCP_PROJECT")
        dataset = _env("BQ_DATASET")
        if mode != "probe":
            if not project:
                raise ConfigError("GCP_PROJECT is empty (secret missing?)")
            if not dataset:
                raise ConfigError("BQ_DATASET is empty; set it explicitly in the workflow (no silent default)")
            if not re.fullmatch(r"[A-Za-z0-9_]{1,1024}", dataset):
                raise ConfigError(f"BQ_DATASET={dataset!r} is not a valid dataset id")
            if not re.fullmatch(r"[a-z][a-z0-9\-]{4,61}[a-z0-9]|[a-z0-9.\-:]+", project):
                raise ConfigError("GCP_PROJECT does not look like a project id")

        raw_lb = env_int("LOOKBACK_DAYS", API_MAX_LOOKBACK, 0, 3650)
        lookback = min(raw_lb, API_MAX_LOOKBACK)

        gh_run = _env("GITHUB_RUN_ID")
        run_id = (f"gh-{gh_run}-{_env('GITHUB_RUN_ATTEMPT') or '1'}" if gh_run
                  else "local-" + dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S"))

        return Config(
            api_key=key,
            api_url=_env("APPLOVIN_ADS_REPORT_URL") or DEFAULT_API_URL,
            mode=mode,
            project=project,
            dataset=dataset,
            location=_env("BQ_LOCATION") or "US",
            creds_json=_env("GCP_CREDENTIALS_JSON"),
            lookback_days=lookback,
            chunk_days=env_int("CHUNK_DAYS", 7, 1, 45),
            page_limit=env_int("PAGE_LIMIT", 10000, 1, 1_000_000),
            max_pages=env_int("MAX_PAGES", 500, 1, 100_000),
            include_cohort=env_bool("INCLUDE_COHORT", True),
            force_replace=env_bool("FORCE_REPLACE", False),
            max_change_pct=env_float("MAX_CHANGE_PCT", 50.0, 1.0, 1000.0),
            guard_min_cost=env_float("GUARD_MIN_COST", 5.0, 0.0, 1e9),
            guard_min_conv=env_int("GUARD_MIN_CONV", 20, 0, 10**9),
            reconcile_pct=env_float("RECONCILE_PCT", 0.0, 0.0, 10.0),
            recent_growth_pct=env_float("RECENT_GROWTH_PCT", 10.0, 0.0, 100.0),
            stale_hours=env_int("STALE_HOURS", 30, 1, 24 * 30),
            recent_days=env_int("RECENT_DAYS", 1, 0, 7),
            max_retry_days=env_int("MAX_RETRY_DAYS", 15, 0, 45),
            http_attempts=env_int("HTTP_ATTEMPTS", 5, 1, 10),
            http_read_timeout=env_int("HTTP_READ_TIMEOUT", 180, 5, 900),
            backoff_base=env_float("HTTP_BACKOFF_BASE", 2.0, 0.0, 60.0),
            request_pause=env_float("REQUEST_PAUSE", 0.5, 0.0, 30.0),
            run_budget_sec=env_int("RUN_BUDGET_SEC", 2400, 30, 6 * 3600),
            run_id=run_id,
            lookback_clamped_from=raw_lb if raw_lb != lookback else None,
        )


# =============================================================================
# Report specs
# =============================================================================
@dataclass(frozen=True)
class FieldDef:
    name: str
    type: str          # BigQuery legacy type names: STRING INTEGER FLOAT DATE TIMESTAMP
    mode: str = "NULLABLE"
    description: str = ""


STRING_DIMS = [  # fixed order (also the column order in BigQuery)
    "campaign_id_external", "campaign", "campaign_package_name", "campaign_store_id",
    "campaign_type", "campaign_ad_type", "platform", "country",
]
DIM_DESC = {
    "campaign_id_external": "Stable AppLovin campaign id (survives renames)",
    "campaign": "Campaign name as reported by AppLovin",
    "campaign_package_name": "Promoted app: Android package / iOS bundle id",
    "campaign_store_id": "Promoted app store id: numeric iTunes id (iOS) or package name",
    "campaign_type": "CPP / CPE / AD_ROAS / IAP_ROAS / ROAS ...",
    "campaign_ad_type": "ua (user acquisition) or rt (retargeting)",
    "platform": "android / ios / fireos / tvos (lowercased)",
    "country": "ISO-2 country code (uppercased)",
}
REV_SUFFIXES = ["0d", "1d", "3d", "7d", "14d", "30d"]
RET_SUFFIXES = ["1d", "3d", "7d", "14d", "28d"]
PUR_SUFFIXES = ["0d", "7d", "30d"]


@dataclass(frozen=True)
class ReportSpec:
    name: str
    table: str
    day_column: str | None
    required: tuple[str, ...]
    optional_groups: dict
    int_metrics: tuple[str, ...]
    float_metrics: tuple[str, ...]
    rate_metrics: tuple[str, ...]
    zero_if_empty: tuple[str, ...]
    reconcile_metrics: tuple[str, ...]
    probe_lag: int
    description: str

    @property
    def all_columns(self) -> list[str]:
        cols = list(self.required)
        for group in self.optional_groups.values():
            cols += [c for c in group if c not in cols]
        return cols

    @property
    def dims(self) -> list[str]:
        cols = set(self.all_columns)
        return [d for d in STRING_DIMS if d in cols]

    @property
    def metrics(self) -> tuple[str, ...]:
        return self.int_metrics + self.float_metrics + self.rate_metrics

    def metric_desc(self, m: str) -> str:
        if m == "cost":
            return "Advertiser spend, USD"
        if m == "conversions":
            return "Installs (conversions)"
        if m in ("impressions", "clicks"):
            return m.capitalize()
        if m.startswith("ret_"):
            return f"Retention {m[4:]} as returned by AppLovin (a RATE; do not SUM)"
        if m.startswith("unique_purchasers_"):
            return f"Unique purchasers within {m.rsplit('_', 1)[1]} of install"
        for pfx, label in (("total_rev_", "Total"), ("ad_rev_", "Ad"), ("iap_rev_", "IAP")):
            if m.startswith(pfx):
                return f"{label} revenue USD within {m[len(pfx):]} of install (cohort)"
        return m

    def schema(self) -> list[FieldDef]:
        cohort = self.day_column == "day"
        fields = [
            FieldDef("day", "DATE", "REQUIRED",
                     "Install (cohort) day, UTC" if cohort else "Activity day, UTC (AppLovin realtime)"),
            FieldDef("campaign_key", "STRING", "REQUIRED",
                     "campaign_id_external, else 'name:'+campaign; part of the grain"),
        ]
        fields += [FieldDef(d, "STRING", "NULLABLE", DIM_DESC[d]) for d in self.dims]
        fields += [FieldDef(m, "INTEGER", "NULLABLE", self.metric_desc(m)) for m in self.int_metrics]
        fields += [FieldDef(m, "FLOAT", "NULLABLE", self.metric_desc(m)) for m in self.float_metrics]
        fields += [FieldDef(m, "FLOAT", "NULLABLE", self.metric_desc(m)) for m in self.rate_metrics]
        fields += [
            FieldDef("_run_id", "STRING", "NULLABLE", "Loader run that wrote this row"),
            FieldDef("_ingested_at", "TIMESTAMP", "NULLABLE", "When this row was written (UTC)"),
        ]
        return fields


CORE = ReportSpec(
    name="core",
    table="campaign_country_daily",
    day_column=None,
    required=("day", "campaign", "campaign_id_external", "campaign_package_name",
              "platform", "country", "impressions", "clicks", "conversions", "cost"),
    optional_groups={"campaign_attrs": ["campaign_store_id", "campaign_type", "campaign_ad_type"]},
    int_metrics=("impressions", "clicks", "conversions"),
    float_metrics=("cost",),
    rate_metrics=(),
    zero_if_empty=("impressions", "clicks", "conversions", "cost"),
    reconcile_metrics=("cost", "conversions", "impressions"),
    probe_lag=CORE_PROBE_LAG,
    description="AppLovin Ads spend/installs per day x campaign x platform x country (realtime, UTC)",
)

COHORT = ReportSpec(
    name="cohort",
    table="campaign_cohort_daily",
    day_column="day",
    required=("day", "campaign", "campaign_id_external", "campaign_package_name",
              "platform", "country", "conversions", "cost"),
    optional_groups={
        "total_rev": [f"total_rev_{s}" for s in REV_SUFFIXES],
        "ad_rev": [f"ad_rev_{s}" for s in REV_SUFFIXES],
        "iap_rev": [f"iap_rev_{s}" for s in REV_SUFFIXES],
        "retention": [f"ret_{s}" for s in RET_SUFFIXES],
        "purchasers": [f"unique_purchasers_{s}" for s in PUR_SUFFIXES],
    },
    int_metrics=("conversions",) + tuple(f"unique_purchasers_{s}" for s in PUR_SUFFIXES),
    float_metrics=("cost",) + tuple(f"{p}_{s}" for p in ("total_rev", "ad_rev", "iap_rev") for s in REV_SUFFIXES),
    rate_metrics=tuple(f"ret_{s}" for s in RET_SUFFIXES),
    zero_if_empty=("conversions", "cost"),
    reconcile_metrics=("cost", "conversions"),
    probe_lag=COHORT_PROBE_LAG,
    description="AppLovin Ads cohort metrics by install day (day_column=day): revenue, retention, purchasers",
)

LOAD_LOG_SCHEMA = [
    FieldDef("run_id", "STRING", "REQUIRED"),
    FieldDef("run_at", "TIMESTAMP", "REQUIRED"),
    FieldDef("loader_version", "STRING"),
    FieldDef("mode", "STRING"),
    FieldDef("status", "STRING", description="ok | ok_with_warnings | ok_empty | partial | failed | transient_skip"),
    FieldDef("window_start", "DATE"),
    FieldDef("window_end", "DATE"),
    FieldDef("core_rows_written", "INTEGER"),
    FieldDef("core_days_replaced", "INTEGER"),
    FieldDef("core_days_protected", "STRING", description="JSON list of days NOT replaced by the drift guard"),
    FieldDef("core_days_unverified", "STRING", description="JSON list of days that failed reconciliation"),
    FieldDef("cohort_rows_written", "INTEGER"),
    FieldDef("cohort_days_replaced", "INTEGER"),
    FieldDef("api_cost_total", "FLOAT", description="Sum of API day totals (cost) over the window"),
    FieldDef("api_conversions_total", "INTEGER"),
    FieldDef("dropped_columns", "STRING", description="JSON: optional columns rejected/omitted (old values kept)"),
    FieldDef("warnings", "STRING"),
    FieldDef("errors", "STRING", description="JSON: FULL error details (private; public logs show a short form)"),
    FieldDef("duration_sec", "FLOAT"),
]

CORRECTION_MAP_SCHEMA = [
    FieldDef("applovin_package", "STRING", "REQUIRED", "campaign_package_name or campaign_store_id as AppLovin reports it"),
    FieldDef("platform", "STRING", "REQUIRED", "android | ios | fireos (lowercase)"),
    FieldDef("master_android_package", "STRING"),
    FieldDef("master_apple_id", "INTEGER"),
    FieldDef("master_ios_bundle_id", "STRING"),
    FieldDef("note", "STRING"),
    FieldDef("added_by", "STRING"),
    FieldDef("added_at", "TIMESTAMP"),
]


@dataclass(frozen=True)
class TableDef:
    name: str
    schema: list
    partition_field: str | None
    clustering: tuple
    description: str


def table_defs() -> list[TableDef]:
    return [
        TableDef(CORE.table, CORE.schema(), "day", ("campaign_package_name", "platform", "country"), CORE.description),
        TableDef(COHORT.table, COHORT.schema(), "day", ("campaign_package_name", "platform", "country"), COHORT.description),
        TableDef("load_log", LOAD_LOG_SCHEMA, None, (), "One row per AppLovin Ads loader run (audit trail)"),
        TableDef("apps_correction_map", CORRECTION_MAP_SCHEMA, None, (),
                 "Manual AppLovin package -> app master overrides, read by applovin_ads_staging"),
    ]


# =============================================================================
# Parsing helpers
# =============================================================================
_NUM_RE = re.compile(r"^[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?$")
_EMPTY_TOKENS = {"", "-", "n/a", "na", "null", "none", "nan"}


def value_shape(v: object) -> str:
    """Describe a value WITHOUT revealing it (used by probe; safe for public logs)."""
    if v is None:
        return "null"
    if isinstance(v, bool):
        return "bool"
    if isinstance(v, int):
        return "int"
    if isinstance(v, float):
        return "float"
    s = str(v).strip()
    if s == "":
        return "empty"
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", s):
        return "date"
    if re.fullmatch(r"[+-]?\d+", s):
        return "int-string"
    if re.fullmatch(r"[+-]?(\d+\.\d*|\.\d+)", s):
        return "decimal-string"
    if s.endswith("%"):
        return "percent-string"
    if re.fullmatch(r"[a-z]{2}", s):
        return "2-letter-lower"
    if re.fullmatch(r"[A-Z]{2}", s):
        return "2-letter-upper"
    return "text"


def is_empty_value(v: object) -> bool:
    return v is None or (isinstance(v, str) and v.strip().lower() in _EMPTY_TOKENS)


def parse_number(v: object, *, integer: bool, column: str, empty_as):
    """Strict: garbage raises DataError (never silently 0). Commas are REJECTED
    (could be a decimal comma -> 12,34 must not become 1234)."""
    if v is None:
        return empty_as
    if isinstance(v, bool):
        raise DataError(f"column {column}: boolean where a number was expected")
    if isinstance(v, (int, float)):
        x = float(v)
    else:
        s = str(v).strip()
        if s.lower() in _EMPTY_TOKENS:
            return empty_as
        s = s.replace("$", "").strip()
        if s.endswith("%"):
            s = s[:-1].strip()
        if not _NUM_RE.match(s):
            raise DataError(f"column {column}: non-numeric value (shape={value_shape(v)})")
        x = float(s)
    if not math.isfinite(x):
        raise DataError(f"column {column}: non-finite number")
    if integer:
        if abs(x - round(x)) > 1e-6:
            raise DataError(f"column {column}: expected a whole number, got a fraction")
        return int(round(x))
    return x


def parse_day(v: object, what: str) -> dt.date:
    s = "" if v is None else str(v).strip()
    try:
        return dt.date.fromisoformat(s[:10])
    except ValueError:
        raise DataError(f"{what}: unparseable 'day' value (shape={value_shape(v)})") from None


def clean_str(v: object) -> str | None:
    if v is None:
        return None
    s = str(v).strip()
    return s or None


def iso(d: dt.date) -> str:
    return d.isoformat()


def days_between(start: dt.date, end: dt.date) -> list[dt.date]:
    return [start + dt.timedelta(days=i) for i in range((end - start).days + 1)]


def chunk_ranges(start: dt.date, end: dt.date, size: int) -> list[tuple[dt.date, dt.date]]:
    out, cur = [], start
    while cur <= end:
        stop = min(end, cur + dt.timedelta(days=size - 1))
        out.append((cur, stop))
        cur = stop + dt.timedelta(days=1)
    return out


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


# =============================================================================
# Run state
# =============================================================================
@dataclass
class ReportResult:
    rows_written: int = 0
    api_rows: int = 0
    days_replaced: list = field(default_factory=list)
    days_protected: list = field(default_factory=list)
    days_unverified: list = field(default_factory=list)
    days_recent_skipped: list = field(default_factory=list)
    api_cost_total: float = 0.0
    api_conversions_total: int = 0
    columns_used: list = field(default_factory=list)
    skipped_reason: str | None = None


@dataclass
class RunState:
    warnings: list = field(default_factory=list)
    errors: list = field(default_factory=list)          # public (short) forms
    private_errors: list = field(default_factory=list)  # full detail -> load_log only
    dropped: dict = field(default_factory=dict)
    core: ReportResult = field(default_factory=ReportResult)
    cohort: ReportResult = field(default_factory=ReportResult)
    status: str = "running"
    window: tuple | None = None

    def warn(self, msg: str) -> None:
        msg = REDACT(msg)
        if msg in self.warnings:
            return
        self.warnings.append(msg)
        LOG.warning(msg)
        gh_annotation("warning", msg)

    def error(self, msg: str, private: str | None = None) -> None:
        msg = REDACT(msg)
        self.errors.append(msg)
        self.private_errors.append(REDACT(private) if private else msg)
        LOG.error(msg)
        gh_annotation("error", msg)


# =============================================================================
# AppLovin API client
# =============================================================================
class AppLovinAdsAPI:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.session = requests.Session()
        self.session.headers["User-Agent"] = f"terafort-applovin-ads-loader/{VERSION}"
        self.calls = 0
        self.deadline = time.monotonic() + cfg.run_budget_sec

    def _sleep(self, attempt: int, retry_after: str | None) -> None:
        if attempt >= self.cfg.http_attempts:
            return
        wait = self.cfg.backoff_base * (2 ** (attempt - 1)) + random.uniform(0, self.cfg.backoff_base)
        if retry_after:
            try:
                wait = max(wait, min(float(retry_after), 120.0))
            except ValueError:
                pass
        wait = min(wait, 120.0, max(0.0, self.deadline - time.monotonic()))
        time.sleep(wait)

    @staticmethod
    def _parse_body(text: str) -> list[dict]:
        if not text.strip():
            raise _RetryableBody("HTTP 200 with an empty body")
        try:
            data = json.loads(text)
        except ValueError:
            raise _RetryableBody(f"HTTP 200 with a non-JSON body (shape={value_shape(text[:40])})") from None
        if isinstance(data, list):
            rows = data
        elif isinstance(data, dict):
            code = data.get("code")
            try:
                code = int(code) if code is not None else None
            except (TypeError, ValueError):
                code = None
            if code is not None and code != 200:
                msg = REDACT(json.dumps(data, default=str))[:400]      # redact FIRST, then cut
                if code in (401, 403):
                    raise AuthError(f"AppLovin rejected the report key (code {code}): {msg}")
                if code in (408, 425, 429) or code >= 500:
                    raise _RetryableBody(f"JSON code {code}")
                raise RequestRejected(code, msg)
            if "results" not in data:
                raise DataError(f"JSON response without 'results' (keys={sorted(map(str, data))[:10]})")
            rows = data["results"]
        else:
            raise DataError(f"unexpected JSON type {type(data).__name__}")
        if rows is None:
            rows = []
        if not isinstance(rows, list) or any(not isinstance(r, dict) for r in rows):
            raise DataError("'results' is not a list of objects")
        return [{str(k).strip().lower(): v for k, v in r.items()} for r in rows]

    def get(self, params: dict, what: str) -> list[dict]:
        q = dict(params)
        q.update(api_key=self.cfg.api_key, format="json", report_type="advertiser")
        last = "no attempt"
        for attempt in range(1, self.cfg.http_attempts + 1):
            remaining = self.deadline - time.monotonic()
            if remaining <= 5:
                raise TransientAPIError(f"{what}: run time budget ({self.cfg.run_budget_sec}s) exhausted - last: {last}")
            self.calls += 1
            retry_after = None
            try:
                resp = self.session.get(self.cfg.api_url, params=q,
                                        timeout=(15, max(5, min(self.cfg.http_read_timeout, int(remaining)))))
            except requests.RequestException as e:
                last = f"{type(e).__name__}: {safe_exc(e)[:300]}"
            else:
                status = resp.status_code
                if status == 200:
                    try:
                        return self._parse_body(resp.text)
                    except _RetryableBody as e:
                        last = str(e)
                else:
                    body = REDACT(resp.text)[:400].replace("\n", " ")       # redact FIRST, then cut
                    if status in (401, 403):
                        raise AuthError(
                            f"{what}: AppLovin rejected the report key (HTTP {status}). Make sure "
                            f"APPLOVIN_ADS_REPORT_KEY is the Report Key of the AppLovin ADS account. Body: {body}")
                    if status in (408, 425, 429) or status >= 500:
                        last = f"HTTP {status}: {body[:200]}"
                        retry_after = resp.headers.get("Retry-After")
                    else:
                        raise RequestRejected(status, body)
            if attempt < self.cfg.http_attempts:
                LOG.warning("%s: attempt %d/%d failed (%s) - retrying", what, attempt, self.cfg.http_attempts, last)
            self._sleep(attempt, retry_after)
        raise TransientAPIError(f"{what}: gave up after {self.cfg.http_attempts} attempts - last: {last}")

    def get_paged(self, params: dict, what: str) -> list[dict]:
        """limit/offset pagination until an EMPTY page (works even if the server silently
        caps page size). Stops early only on a page identical to the previous one (API
        ignoring offset). Truncation / overlap are caught later (duplicates + reconciliation)."""
        out: list[dict] = []
        offset, prev_sig, prev_len = 0, None, None
        for page_no in range(1, self.cfg.max_pages + 1):
            p = dict(params, limit=self.cfg.page_limit, offset=offset)
            try:
                page = self.get(p, f"{what} page {page_no}")
            except RequestRejected as e:
                if page_no != 1:
                    # Most likely the API rejects an offset past the end (row count was a multiple
                    # of the page size, or the previous page was short). Treat as end of data:
                    # reconciliation against the day totals still proves completeness, and a day
                    # that is really missing rows is NOT written.
                    LOG.warning("%s: page %d rejected (HTTP %s) after %d rows (last page %s) - treating as "
                                "end of data; reconciliation will verify", what, page_no, e.status, len(out),
                                "short" if (prev_len or 0) < self.cfg.page_limit else "full")
                    return out
                # API refused limit/offset (e.g. limit too large) -> one unpaged request;
                # reconciliation still proves completeness.
                LOG.warning("%s: limit/offset rejected (HTTP %s) - retrying unpaged", what, e.status)
                return self.get(dict(params), f"{what} unpaged")
            if not page:
                return out
            sig = hashlib.sha256(json.dumps(page, sort_keys=True, default=str).encode()).hexdigest()
            if sig == prev_sig:
                LOG.warning("%s: page %d identical to the previous page (API ignores offset?) - stopping",
                            what, page_no)
                return out
            prev_sig, prev_len = sig, len(page)
            out.extend(page)
            offset += len(page)
            if self.cfg.request_pause:
                time.sleep(self.cfg.request_pause)
        raise DataError(f"{what}: more than {self.cfg.max_pages} pages; refusing (raise PAGE_LIMIT/MAX_PAGES)")


# =============================================================================
# Fetch + normalize + aggregate
# =============================================================================
@dataclass
class Tot:
    cost: float = 0.0
    conversions: int = 0
    impressions: int = 0
    rows: int = 0


EMPTY_CHECK_MIN_COST = 50.0          # witness volume before "metric empty everywhere" is fatal
EMPTY_CHECK_MIN_IMPRESSIONS = 10000


def check_response(rows: list[dict], requested: list[str], spec: ReportSpec, what: str,
                   strict_empty: bool = True) -> list[str]:
    """Validate one response. Returns requested OPTIONAL columns absent from every row.
    Fatal (DataError): a REQUIRED column missing, a required metric empty in EVERY row while
    there is activity (a silently broken 'cost'/'conversions' must never load as 0), or two
    rows with identical dimensions (_DuplicateRows: overlapping pages)."""
    if not rows:
        return []
    seen: set = set()
    for r in rows:
        seen.update(r.keys())
    missing = [c for c in requested if c not in seen]
    req_missing = [c for c in missing if c in spec.required]
    if req_missing:
        raise DataError(f"{what}: API response is missing required column(s) {req_missing}")
    if strict_empty and len(rows) >= 5:
        def total(col: str) -> float:
            t = 0.0
            for r in rows:
                try:
                    t += parse_number(r.get(col), integer=False, column=col, empty_as=0.0) or 0.0
                except DataError:
                    pass
            return t
        for m in spec.zero_if_empty:
            if m in requested and all(is_empty_value(r.get(m)) for r in rows):
                witness = "impressions" if m == "cost" else "cost"
                floor = EMPTY_CHECK_MIN_IMPRESSIONS if witness == "impressions" else EMPTY_CHECK_MIN_COST
                if witness in requested and total(witness) >= floor:
                    raise DataError(f"{what}: required metric '{m}' is empty in every row although "
                                    f"'{witness}' shows real activity; refusing to load it as 0")
    dims = [c for c in requested if c not in spec.metrics]
    keys = set()
    for r in rows:
        k = tuple(str(r.get(c)) for c in dims)
        if k in keys:
            raise _DuplicateRows(what)
        keys.add(k)
    return missing


def normalize_row(raw: dict, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date,
                  run_id: str, ingested_at: str, what: str) -> dict:
    day = parse_day(raw.get("day"), what)
    if not lo <= day <= hi:
        raise DataError(f"{what}: row for {day} is outside the requested range {lo}..{hi}")
    colset = set(cols)
    row: dict = {"day": day}
    for d in spec.dims:
        row[d] = clean_str(raw.get(d)) if d in colset else None
    if row.get("platform"):
        row["platform"] = row["platform"].lower()
    if row.get("country"):
        row["country"] = row["country"].upper()
    cid, name = row.get("campaign_id_external"), row.get("campaign")
    row["campaign_key"] = cid if cid else (f"name:{name}" if name else "unknown")
    for m in spec.int_metrics:
        row[m] = (parse_number(raw.get(m), integer=True, column=m,
                               empty_as=0 if m in spec.zero_if_empty else None) if m in colset else None)
    for m in spec.float_metrics + spec.rate_metrics:
        row[m] = (parse_number(raw.get(m), integer=False, column=m,
                               empty_as=0.0 if m in spec.zero_if_empty else None) if m in colset else None)
    row["_run_id"] = run_id
    row["_ingested_at"] = ingested_at
    return row


def _add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return a + b


def aggregate(rows: list[dict], spec: ReportSpec) -> tuple[dict, int, int]:
    """One row per (day, campaign_key, platform, country). Only rows that differ in some
    dimension can reach here (identical-dimension rows are rejected as page overlap), e.g.
    a renamed campaign under the same id, or country 'us' vs 'US'. Sums additive metrics,
    conversion-weighted mean for rates, attributes from the bigger-spend row."""
    out: dict = {}
    merged = conflicts = 0
    for r in rows:
        k = (r["day"], r["campaign_key"], r.get("platform"), r.get("country"))
        a = out.get(k)
        if a is None:
            out[k] = dict(r)
            continue
        merged += 1
        if any(r.get(d) and a.get(d) and r.get(d) != a.get(d) for d in spec.dims):
            conflicts += 1
        if (r.get("cost") or 0) > (a.get("cost") or 0):
            for d in spec.dims:
                if r.get(d):
                    a[d] = r[d]
        wa, wb = a.get("conversions") or 0, r.get("conversions") or 0
        for m in spec.rate_metrics:
            va, vb = a.get(m), r.get(m)
            if va is None or vb is None:
                a[m] = va if vb is None else vb
            elif wa + wb > 0:
                a[m] = (va * wa + vb * wb) / (wa + wb)
            else:
                a[m] = (va + vb) / 2
        for m in spec.int_metrics + spec.float_metrics:
            a[m] = _add(a.get(m), r.get(m))
    return out, merged, conflicts


def totals_by_day(rows) -> dict:
    out: dict = defaultdict(Tot)
    for r in rows:
        t = out[r["day"]]
        t.cost += r.get("cost") or 0.0
        t.conversions += r.get("conversions") or 0
        t.impressions += r.get("impressions") or 0
        t.rows += 1
    return dict(out)


RECENT_ABS_SLACK = {"cost": 1.0, "conversions": 5, "impressions": 2000}


def reconcile(det: Tot, tot: Tot, metrics, *, settled: bool, cfg: Config) -> list[str]:
    """Metrics that do NOT reconcile (empty list = day is good).
    Totals are always fetched BEFORE detail, so detail can only legitimately be >= totals.
      settled day: |detail - total| <= rounding (+ optional RECONCILE_PCT). Counts exact.
      recent day : total - rounding <= detail <= total * (1 + RECENT_GROWTH_PCT) + slack.
    Cost rounding: per-row 2-decimal rounding, 5-sigma bound = 0.01 + 0.015*sqrt(rows)."""
    bad = []
    for m in metrics:
        a, b = getattr(det, m), getattr(tot, m)
        rnd = (0.01 + 0.015 * math.sqrt(max(det.rows, 1))) if m == "cost" else 0.0
        rel = cfg.reconcile_pct / 100.0 * abs(b)
        lo_ok = b - rnd - rel
        hi_ok = b + rnd + rel
        if not settled:
            hi_ok += max(cfg.recent_growth_pct / 100.0 * abs(b), RECENT_ABS_SLACK.get(m, 0))
        if not (lo_ok - 1e-9 <= a <= hi_ok + 1e-9):
            pct = f"{(a - b) / b * 100:+.2f}%" if b else "vs 0"
            bad.append(f"{m} {pct}")
    return bad


class Fetcher:
    def __init__(self, api: AppLovinAdsAPI, cfg: Config, run: RunState, today: dt.date | None = None):
        self.api, self.cfg, self.run = api, cfg, run
        self.ingested_at = utc_now().replace(tzinfo=None).isoformat()  # proven format for BQ JSON loads
        self.recent_cut = (today or utc_now().date()) - dt.timedelta(days=cfg.recent_days)

    def _params(self, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date) -> dict:
        p = {"start": iso(lo), "end": iso(hi), "columns": ",".join(cols)}
        if spec.day_column:
            p["day_column"] = spec.day_column
        return p

    def _drop(self, spec: ReportSpec, cols: list[str], why: str) -> None:
        cur = self.run.dropped.setdefault(spec.name, [])
        new = [c for c in cols if c not in cur]
        if not new:
            return
        cur.extend(new)
        self.run.warn(f"{spec.name}: optional column(s) {new} {why}; loading without them "
                      f"(existing values in BigQuery are kept, never overwritten with NULL)")

    def resolve_columns(self, spec: ReportSpec, probe_day: dt.date) -> tuple[list[str], list[dict]]:
        """Validate columns on a 1-day request (settled day; mature cohort). Optional groups the
        API rejects or omits are dropped (their old values are preserved at write time)."""
        want = spec.all_columns
        what = f"{spec.name} column check ({probe_day})"
        try:
            rows = self.api.get(self._params(spec, want, probe_day, probe_day), what)
            try:
                missing = check_response(rows, want, spec, what)
            except _DuplicateRows:
                missing = []          # judged properly on the real fetch
            if missing:
                self._drop(spec, missing, "absent from the API response")
                want = [c for c in want if c not in missing]
            return want, rows
        except RequestRejected as e:
            first_err = e
        LOG.warning("%s: full column set rejected (%s); testing groups one by one", what, first_err.body[:160])
        req = list(spec.required)
        try:
            rows = self.api.get(self._params(spec, req, probe_day, probe_day), what + " [required only]")
        except RequestRejected as e2:
            raise ConfigError(f"{spec.name}: AppLovin rejected even the REQUIRED columns {req}: {e2}") from None
        keep = list(req)
        for gname, gcols in spec.optional_groups.items():
            try:
                self.api.get(self._params(spec, req + gcols, probe_day, probe_day), f"{what} [+{gname}]")
                keep += gcols
            except RequestRejected as e3:
                self._drop(spec, gcols, f"rejected by the API (HTTP {e3.status})")
        if keep != req:
            rows = self.api.get(self._params(spec, keep, probe_day, probe_day), what + " [resolved]")
        return keep, rows

    def totals(self, spec: ReportSpec, lo: dt.date, hi: dt.date) -> dict:
        cols = ["day"] + list(spec.reconcile_metrics)
        what = f"{spec.name} totals {lo}..{hi}"
        for attempt in (1, 2):
            rows = self.api.get_paged(self._params(spec, cols, lo, hi), what)
            days = [parse_day(r.get("day"), what) for r in rows]
            if len(days) == len(set(days)):
                break
            if attempt == 2:
                raise DataError(f"{what}: a day appears twice in a day-level totals response, twice in a row "
                                f"(unstable paging); nothing written")
            LOG.warning("%s: duplicate day rows (overlapping pages) - re-fetching once", what)
        out: dict = defaultdict(Tot)
        for r in rows:
            d = parse_day(r.get("day"), what)
            if not lo <= d <= hi:
                raise DataError(f"{what}: day {d} outside the requested range")
            t = out[d]
            t.cost += parse_number(r.get("cost"), integer=False, column="cost", empty_as=0.0)
            t.conversions += parse_number(r.get("conversions"), integer=True, column="conversions", empty_as=0)
            if "impressions" in spec.reconcile_metrics:
                t.impressions += parse_number(r.get("impressions"), integer=True, column="impressions", empty_as=0)
            t.rows += 1
        return dict(out)

    def _fetch(self, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date) -> list[dict]:
        what = f"{spec.name} {lo}..{hi}"
        raw = self.api.get_paged(self._params(spec, cols, lo, hi), what)
        # "metric empty everywhere" is only judged when the response includes settled days
        missing = check_response(raw, cols, spec, what, strict_empty=lo < self.recent_cut)  # may raise _DuplicateRows
        if missing:
            self._drop(spec, missing, "absent from the API response")
        return [normalize_row(r, spec, cols, lo, hi, self.cfg.run_id, self.ingested_at, what) for r in raw]

    def detail(self, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date) -> list[dict]:
        rows: list[dict] = []
        for c_lo, c_hi in chunk_ranges(lo, hi, self.cfg.chunk_days):
            try:
                part = self._fetch(spec, cols, c_lo, c_hi)
            except _DuplicateRows:
                LOG.warning("%s %s..%s: duplicate rows (overlapping pages) - re-fetching day by day",
                            spec.name, c_lo, c_hi)
                part = []
                for d in days_between(c_lo, c_hi):
                    try:
                        part += self._fetch(spec, cols, d, d)
                    except _DuplicateRows:
                        raise DataError(f"{spec.name} {d}: API returned duplicate rows even for a single "
                                        f"day (unstable paging); nothing written. Try a larger PAGE_LIMIT.") from None
            rows += part
            LOG.info("%s %s..%s: %d rows", spec.name, c_lo, c_hi, len(part))
            if self.cfg.request_pause:
                time.sleep(self.cfg.request_pause)
        return rows


# =============================================================================
# BigQuery warehouse
# =============================================================================
@dataclass
class Existing:
    cost: float
    conversions: int
    last_ingested: dt.datetime | None


class BigQueryWarehouse:
    def __init__(self, cfg: Config):
        from google.cloud import bigquery  # imported lazily: probe mode needs no GCP
        self.bq = bigquery
        self.cfg = cfg
        if cfg.creds_json:
            from google.oauth2 import service_account
            try:
                info = json.loads(cfg.creds_json)
            except ValueError:
                raise ConfigError("GCP_CREDENTIALS_JSON is not valid JSON") from None
            creds = service_account.Credentials.from_service_account_info(
                info, scopes=["https://www.googleapis.com/auth/cloud-platform"])
            self.client = bigquery.Client(project=cfg.project, credentials=creds, location=cfg.location)
        else:  # Application Default Credentials (e.g. Workload Identity Federation)
            self.client = bigquery.Client(project=cfg.project, location=cfg.location)
        self.ds = f"{cfg.project}.{cfg.dataset}"

    # ---- helpers ------------------------------------------------------------
    def fq(self, table: str) -> str:
        return f"{self.ds}.{table}"

    def _schema(self, fields) -> list:
        return [self.bq.SchemaField(f.name, f.type, mode=f.mode, description=f.description or None) for f in fields]

    def _retry(self, fn, what: str):
        from google.api_core import exceptions as gexc
        retryable = (gexc.ServiceUnavailable, gexc.InternalServerError, gexc.BadGateway,
                     gexc.GatewayTimeout, gexc.TooManyRequests)
        for attempt in range(1, 6):
            try:
                return fn()
            except retryable as e:
                err = e
            except gexc.GoogleAPICallError as e:
                low = str(e).lower()
                if not (google_reasons(e) & _TRANSIENT_REASONS or "concurrent update" in low
                        or "could not serialize" in low):
                    raise
                err = e
            if attempt == 5:
                raise err
            wait = min(60.0, 2 ** attempt + random.random())
            LOG.warning("BigQuery %s: %s (attempt %d/5) - retrying in %.0fs", what, type(err).__name__, attempt, wait)
            time.sleep(wait)
        return None

    def query(self, sql: str, params=None, what: str = "query"):
        cfg = self.bq.QueryJobConfig(query_parameters=params or [])
        return self._retry(lambda: list(self.client.query(sql, job_config=cfg).result()), what)

    def table_exists(self, table: str) -> bool:
        from google.api_core.exceptions import NotFound
        try:
            self.client.get_table(self.fq(table))
            return True
        except NotFound:
            return False

    # ---- setup ----------------------------------------------------------------
    def ensure(self) -> None:
        """Create dataset/tables if missing; add new NULLABLE columns (schema evolution)."""
        from google.api_core.exceptions import Forbidden, NotFound
        try:
            ds = self.client.get_dataset(self.ds)
            if (ds.location or "").upper() != self.cfg.location.upper():
                raise ConfigError(f"dataset {self.cfg.dataset} is in {ds.location}, expected {self.cfg.location}")
        except NotFound:
            try:
                ds = self.bq.Dataset(self.ds)
                ds.location = self.cfg.location
                ds.description = "AppLovin Ads (advertiser/UA) raw data - loaded by applovin_ads_to_bigquery.py"
                self.client.create_dataset(ds, exists_ok=True)
                LOG.info("created dataset %s (%s)", self.cfg.dataset, self.cfg.location)
            except Forbidden:
                raise ConfigError(f"dataset {self.cfg.dataset} does not exist and the service account cannot "
                                  "create it. Run sql/01_applovin_ads_setup.sql once in the BigQuery console.") from None
        norm = {"INT64": "INTEGER", "FLOAT64": "FLOAT", "BOOL": "BOOLEAN"}
        for td in table_defs():
            try:
                t = self.client.get_table(self.fq(td.name))
            except NotFound:
                t = self.bq.Table(self.fq(td.name), schema=self._schema(td.schema))
                if td.partition_field:
                    t.time_partitioning = self.bq.TimePartitioning(
                        type_=self.bq.TimePartitioningType.DAY, field=td.partition_field)
                if td.clustering:
                    t.clustering_fields = list(td.clustering)
                t.description = td.description
                self.client.create_table(t, exists_ok=True)
                LOG.info("created table %s", td.name)
                continue
            have = {f.name.lower(): f for f in t.schema}
            for f in td.schema:
                cur = have.get(f.name.lower())
                if cur is not None and norm.get(cur.field_type, cur.field_type) != f.type:
                    raise ConfigError(f"{td.name}.{f.name} is {cur.field_type} in BigQuery, loader expects {f.type}")
            missing = [f for f in td.schema if f.name.lower() not in have]
            if missing:
                t.schema = list(t.schema) + [self.bq.SchemaField(f.name, f.type, mode="NULLABLE",
                                                                 description=f.description or None) for f in missing]
                self.client.update_table(t, ["schema"])
                LOG.info("%s: added column(s) %s", td.name, [f.name for f in missing])

    # ---- reads ----------------------------------------------------------------
    def existing_by_day(self, table: str, lo: dt.date, hi: dt.date) -> dict:
        if not self.table_exists(table):
            return {}
        P = self.bq.ScalarQueryParameter
        rows = self.query(
            f"SELECT day, SUM(IFNULL(cost, 0)) AS cost, SUM(IFNULL(conversions, 0)) AS conversions, "
            f"MAX(_ingested_at) AS last_ingested FROM `{self.fq(table)}` "
            f"WHERE day BETWEEN @lo AND @hi GROUP BY day",
            [P("lo", "DATE", lo), P("hi", "DATE", hi)], what=f"read {table}")
        return {r["day"]: Existing(float(r["cost"] or 0), int(r["conversions"] or 0), r["last_ingested"])
                for r in rows}

    def first_success_at(self) -> dt.datetime | None:
        if not self.table_exists("load_log"):
            return None
        rows = self.query(
            f"SELECT MIN(run_at) AS t FROM `{self.fq('load_log')}` "
            f"WHERE mode = 'load' AND status IN ('ok', 'ok_with_warnings', 'ok_empty', 'partial')",
            what="read load_log")
        return rows[0]["t"] if rows else None

    def last_success_at(self, cohort: bool = False) -> dt.datetime | None:
        if not self.table_exists("load_log"):
            return None
        extra = " AND cohort_days_replaced > 0" if cohort else ""
        rows = self.query(
            f"SELECT MAX(run_at) AS t FROM `{self.fq('load_log')}` "
            f"WHERE mode = 'load' AND status IN ('ok', 'ok_with_warnings', 'ok_empty', 'partial'){extra}",
            what="read load_log")
        return rows[0]["t"] if rows else None

    # ---- writes ---------------------------------------------------------------
    def replace_days(self, spec: ReportSpec, days: list, rows: list[dict], preserve: list | None = None) -> int:
        """Atomic: stage rows (batch load) -> keep old values of dropped columns -> ONE
        transaction DELETE days + INSERT -> verify. Raises PostWriteCheckError if the
        commit happened but the count check fails."""
        if not days:
            return 0
        fields = spec.schema()
        names = [f.name for f in fields]
        preserve = [c for c in (preserve or []) if c in names]
        target = self.fq(spec.table)
        tag = re.sub(r"[^A-Za-z0-9_]", "_", self.cfg.run_id) + "_" + uuid.uuid4().hex[:6]
        stg = self.fq(f"zz_stg_{spec.table}_{tag}")
        # Dates are generated by this code (never user text) -> safe as literals.
        day_list = "[" + ", ".join(f"DATE '{iso(d)}'" for d in sorted(days)) + "]"
        stg_created = False
        try:
            if rows:
                t = self.bq.Table(stg, schema=self._schema(fields))
                t.expires = utc_now() + dt.timedelta(hours=6)
                self.client.create_table(t)
                stg_created = True
                payload = [{n: (r.get(n).isoformat() if isinstance(r.get(n), dt.date) else r.get(n))
                            for n in names} for r in rows]
                # WRITE_TRUNCATE -> a retried load can never double the staged rows
                job_cfg = self.bq.LoadJobConfig(schema=self._schema(fields),
                                                write_disposition=self.bq.WriteDisposition.WRITE_TRUNCATE)
                self._retry(lambda: self.client.load_table_from_json(payload, stg, job_config=job_cfg).result(),
                            f"stage {spec.table}")
                staged = self.query(f"SELECT COUNT(*) AS n FROM `{stg}`", what=f"count staged {spec.table}")
                if int(staged[0]["n"]) != len(rows):
                    raise DataError(f"{spec.table}: staged {staged[0]['n']} rows, expected {len(rows)}; "
                                    "nothing written")
                if preserve and self.table_exists(spec.table):
                    sets = ", ".join(f"`{c}` = COALESCE(s.`{c}`, t.`{c}`)" for c in preserve)
                    self.query(
                        f"UPDATE `{stg}` s SET {sets} FROM `{target}` t "
                        f"WHERE t.day IN UNNEST({day_list}) AND t.day = s.day AND t.campaign_key = s.campaign_key "
                        f"AND t.platform IS NOT DISTINCT FROM s.platform AND t.country IS NOT DISTINCT FROM s.country",
                        what=f"preserve dropped columns {spec.table}")
            col_list = ", ".join(f"`{n}`" for n in names)
            insert = (f"INSERT INTO `{target}` ({col_list})\nSELECT {col_list} FROM `{stg}`;\n" if rows else "")
            # No session mode: any failing statement -> BigQuery rolls the whole transaction back
            # automatically and the job fails with the ORIGINAL error (documented behaviour).
            # A retry re-runs DELETE+INSERT from the same staging table -> idempotent.
            sql = (
                "BEGIN TRANSACTION;\n"
                f"DELETE FROM `{target}` WHERE day IN UNNEST({day_list});\n"
                f"{insert}"
                "COMMIT TRANSACTION;"
            )
            try:
                self.query(sql, what=f"replace {spec.table}")
            except Exception as e:  # noqa: BLE001
                raise CommitStateUnknown(
                    f"{spec.table}: the replace transaction failed or its outcome is unknown ({public_exc(e)}). "
                    f"BigQuery rolls back failed transactions, but verify days {sorted(iso(d) for d in days)[:3]}... "
                    f"with sql/03 before trusting them") from e
            try:
                check = self.query(f"SELECT COUNT(*) AS n FROM `{target}` WHERE day IN UNNEST({day_list})",
                                   what=f"verify {spec.table}")
            except Exception as e:  # noqa: BLE001
                raise PostWriteCheckError(f"{spec.table}: COMMITTED, but the post-write check could not run "
                                          f"({public_exc(e)})") from e
            n = int(check[0]["n"]) if check else -1
            if n != len(rows):
                raise PostWriteCheckError(f"{spec.table}: COMMITTED, but the post-write check found {n} rows "
                                          f"for the replaced days, expected {len(rows)}")
            return len(rows)
        finally:
            if stg_created:
                try:
                    self.client.delete_table(stg, not_found_ok=True)
                except Exception as e:  # noqa: BLE001 - staging expires in 6h anyway
                    LOG.warning("could not drop staging table (%s); it expires in 6h", type(e).__name__)

    def write_log(self, rec: dict) -> None:
        P = self.bq.ScalarQueryParameter
        types = {f.name: f.type for f in LOAD_LOG_SCHEMA}
        bq_type = {"STRING": "STRING", "INTEGER": "INT64", "FLOAT": "FLOAT64", "DATE": "DATE", "TIMESTAMP": "TIMESTAMP"}
        cols = [c for c in rec if c != "run_at"]
        params = [P(c, bq_type[types[c]], rec[c]) for c in cols]
        sql = (f"INSERT INTO `{self.fq('load_log')}` (run_at, {', '.join(cols)}) "
               f"VALUES (CURRENT_TIMESTAMP(), {', '.join('@' + c for c in cols)})")
        self.query(sql, params, what="write load_log")


# =============================================================================
# Pipeline
# =============================================================================
def drift_guard(writable: list, new: dict, existing: dict, today: dt.date, cfg: Config) -> dict:
    """day -> reason, for days that must NOT be replaced.
    Shrink (any day): spend or installs would drop by > MAX_CHANGE_PCT vs BigQuery.
    Jump (settled day whose stored value was itself written when already settled):
      spend or installs would rise by > MAX_CHANGE_PCT."""
    p = cfg.max_change_pct / 100.0
    out = {}
    for d in writable:
        old = existing.get(d)
        if old is None:
            continue
        n_cost, n_conv = new.get(d, (0.0, 0))
        reasons = []
        if old.cost >= cfg.guard_min_cost and n_cost < old.cost * (1 - p):
            reasons.append(f"spend {(n_cost / old.cost - 1) * 100:+.0f}%")
        if old.conversions >= cfg.guard_min_conv and n_conv < old.conversions * (1 - p):
            reasons.append(f"installs {(n_conv / old.conversions - 1) * 100:+.0f}%")
        last = old.last_ingested
        if last is not None and last.tzinfo is None:
            last = last.replace(tzinfo=dt.timezone.utc)
        stored_settled = last is not None and last.date() >= d + dt.timedelta(days=2)
        if d <= today - dt.timedelta(days=2) and stored_settled:
            if old.cost >= cfg.guard_min_cost and n_cost > old.cost * (1 + p):
                reasons.append(f"spend {(n_cost / old.cost - 1) * 100:+.0f}% on a settled day")
            if old.conversions >= cfg.guard_min_conv and n_conv > old.conversions * (1 + p):
                reasons.append(f"installs {(n_conv / old.conversions - 1) * 100:+.0f}% on a settled day")
        if reasons:
            out[d] = ", ".join(reasons)
    return out


def process_report(spec: ReportSpec, cols: list[str], fetcher: Fetcher, wh, cfg: Config, run: RunState,
                   lo: dt.date, hi: dt.date, today: dt.date) -> ReportResult:
    res = run.core if spec is CORE else run.cohort
    res.columns_used = cols
    window = days_between(lo, hi)
    recent_cut = today - dt.timedelta(days=cfg.recent_days)

    api_tot = fetcher.totals(spec, lo, hi)            # totals BEFORE detail (detail may only grow)
    rows = fetcher.detail(spec, cols, lo, hi)
    res.api_rows = len(rows)
    by_day: dict = defaultdict(list)
    for r in rows:
        by_day[r["day"]].append(r)

    # ---- 1. reconciliation --------------------------------------------------------
    verdict: dict = {}
    retry_days = []
    for d in window:
        bad = reconcile(totals_by_day(by_day.get(d, [])).get(d, Tot()), api_tot.get(d, Tot()),
                        spec.reconcile_metrics, settled=d < recent_cut, cfg=cfg)
        if bad:
            retry_days.append(d)
            LOG.warning("%s %s: does not reconcile (%s) - re-fetching this day alone", spec.name, d, ", ".join(bad))
        verdict[d] = "ok" if not bad else "retry"

    if len(retry_days) > cfg.max_retry_days:
        for d in retry_days:
            verdict[d] = "mismatch"
        run.error(f"{spec.name}: {len(retry_days)} days do not reconcile (systemic: truncated/overlapping pages "
                  f"or an API change?). They were NOT written. Try CHUNK_DAYS=1.")
    else:
        for d in retry_days:
            tot_d = fetcher.totals(spec, d, d)        # again totals first
            rows_d = fetcher.detail(spec, cols, d, d)
            bad = reconcile(totals_by_day(rows_d).get(d, Tot()), tot_d.get(d, Tot()),
                            spec.reconcile_metrics, settled=d < recent_cut, cfg=cfg)
            if bad:
                verdict[d] = "mismatch" if d < recent_cut else "recent_skip"
            else:
                verdict[d] = "ok"
                by_day[d] = rows_d
                api_tot[d] = tot_d.get(d, Tot())
        settled_bad = [iso(d) for d in retry_days if verdict[d] == "mismatch"]
        recent_bad = [iso(d) for d in retry_days if verdict[d] == "recent_skip"]
        if settled_bad:
            run.error(f"{spec.name}: {len(settled_bad)} settled day(s) still do not reconcile after a single-day "
                      f"re-fetch and were NOT written: {settled_bad}")
        if recent_bad:
            run.warn(f"{spec.name}: still-updating day(s) {recent_bad} did not reconcile even after a re-fetch; "
                     f"kept the previous values, the next run retries")
    res.days_unverified = sorted(d for d in window if verdict[d] == "mismatch")
    res.days_recent_skipped = sorted(d for d in window if verdict[d] == "recent_skip")
    res.api_cost_total = round(sum(t.cost for t in api_tot.values()), 6)
    res.api_conversions_total = sum(t.conversions for t in api_tot.values())

    # ---- 2. aggregate to grain ----------------------------------------------------
    writable = [d for d in window if verdict[d] == "ok"]
    agg, merged, conflicts = aggregate([r for d in writable for r in by_day.get(d, [])], spec)
    if merged:
        LOG.info("%s: merged %d same-key row(s) with differing dimensions (%d with differing campaign "
                 "attributes)", spec.name, merged, conflicts)
    new: dict = defaultdict(lambda: (0.0, 0))
    for r in agg.values():
        c, n = new[r["day"]]
        new[r["day"]] = (c + (r.get("cost") or 0.0), n + (r.get("conversions") or 0))

    # ---- 3. drift guard -----------------------------------------------------------
    existing = wh.existing_by_day(spec.table, lo, hi) if wh is not None else {}
    blocked = drift_guard(writable, new, existing, today, cfg)
    if blocked:
        detail = {iso(d): why for d, why in sorted(blocked.items())}
        if cfg.force_replace:
            run.warn(f"{spec.name}: FORCE_REPLACE=true; replacing {len(blocked)} day(s) that changed sharply vs "
                     f"BigQuery: {detail}")
            blocked = {}
        else:
            run.error(f"{spec.name}: {len(blocked)} day(s) NOT replaced; they changed more than "
                      f"{cfg.max_change_pct:.0f}% vs BigQuery: {detail}. Check the AppLovin Ads dashboard; if the "
                      f"change is real, re-run the workflow with force_replace=true.")
    res.days_protected = sorted(blocked)
    to_replace = sorted(set(writable) - set(blocked))
    keep = set(to_replace)
    out_rows = [r for r in agg.values() if r["day"] in keep]

    # ---- 4. write -----------------------------------------------------------------
    # Optional columns (campaign attributes, cohort metrics) never legitimately go from a value
    # back to NULL, so a blank/absent/dropped value always keeps what BigQuery already has.
    preserve = [c for g in spec.optional_groups.values() for c in g]
    if cfg.mode == "load":
        try:
            res.rows_written = wh.replace_days(spec, to_replace, out_rows, preserve=preserve)
        except PostWriteCheckError:
            res.days_replaced, res.rows_written = to_replace, len(out_rows)
            raise
        res.days_replaced = to_replace
        LOG.info("%s: replaced %d day(s) with %d row(s) in %s", spec.name, len(to_replace), res.rows_written, spec.table)
    else:
        res.days_replaced = to_replace
        LOG.info("[dry-run] %s: WOULD replace %d day(s) with %d row(s) in %s", spec.name, len(to_replace),
                 len(out_rows), spec.table)
    return res


def run_probe(fetcher: Fetcher, cfg: Config, run: RunState, today: dt.date) -> None:
    safe_enums = {"platform", "campaign_type", "campaign_ad_type"}
    specs = [CORE] + ([COHORT] if cfg.include_cohort else [])
    for spec in specs:
        probe_day = today - dt.timedelta(days=spec.probe_lag)
        try:
            cols, rows = fetcher.resolve_columns(spec, probe_day)
        except ConfigError as e:
            run.error(str(e))
            if isinstance(e, AuthError):
                return
            continue
        LOG.info("=== probe %s (%s): HTTP OK, %d rows, %d columns accepted ===", spec.name, probe_day, len(rows), len(cols))
        if not rows:
            run.warn(f"probe {spec.name}: 0 rows for {probe_day}. Key accepted, but no data that day. If you "
                     f"expect spend, check that the key belongs to the AppLovin ADS account (not MAX).")
            continue
        keys = sorted({k for r in rows for k in r})
        LOG.info("returned columns: %s", ", ".join(keys))
        for c in keys:
            shapes: dict = defaultdict(int)
            for r in rows:
                shapes[value_shape(r.get(c))] += 1
            extra = ""
            if c in safe_enums:
                extra = "  values=" + ",".join(sorted({str(r.get(c)) for r in rows})[:10])
            elif c == "country":
                extra = f"  distinct={len({r.get(c) for r in rows})}"
            LOG.info("  %-28s %s%s", c, dict(shapes), extra)
        try:
            check_response(rows, cols, spec, "probe")
            for r in rows:
                normalize_row(r, spec, cols, probe_day, probe_day, cfg.run_id, fetcher.ingested_at, "probe")
            LOG.info("  -> all %d rows pass the loader's strict checks", len(rows))
        except _DuplicateRows:
            run.warn(f"probe {spec.name}: duplicate rows in a single response (API paging?)")
        except DataError as e:
            run.error(f"probe {spec.name}: {e}")


def write_summary(cfg: Config, run: RunState, duration: float, calls: int) -> None:
    path = _env("GITHUB_STEP_SUMMARY")
    icon = {"ok": "✅", "ok_with_warnings": "🟡", "ok_empty": "⚪", "partial": "🟠",
            "failed": "🔴", "transient_skip": "🟡"}.get(run.status, "❔")
    if run.errors and run.status in ("transient_skip", "ok", "ok_with_warnings", "ok_empty"):
        icon = "🔴"
    lines = [f"## {icon} AppLovin Ads -> BigQuery · `{run.status}`", "",
             f"- mode **{cfg.mode}** · loader v{VERSION} · run `{cfg.run_id}`"]
    if run.window:
        lines.append(f"- window **{run.window[0]} -> {run.window[1]}** (UTC) · API calls {calls} · {duration:.0f}s")
    if cfg.mode != "probe":
        lines += ["", "| table | API rows | days replaced | rows written | protected | unverified | recent kept |",
                  "|---|---:|---:|---:|---:|---:|---:|"]
        for name, r in (("campaign_country_daily", run.core), ("campaign_cohort_daily", run.cohort)):
            if r.skipped_reason:
                lines.append(f"| {name} | - | - | - | - | - | skipped: {r.skipped_reason} |")
            else:
                lines.append(f"| {name} | {r.api_rows} | {len(r.days_replaced)} | {r.rows_written} | "
                             f"{len(r.days_protected)} | {len(r.days_unverified)} | {len(r.days_recent_skipped)} |")
        lines.append("")
        lines.append("_Money values and full error details are not shown here (public repo). See `load_log` in BigQuery._")
    if run.dropped:
        lines += ["", f"**Dropped optional columns (old values kept):** `{json.dumps(run.dropped)}`"]
    if run.errors:
        lines += ["", "### 🔴 Errors"] + [f"- {REDACT(e)}" for e in run.errors]
    if run.warnings:
        lines += ["", "### 🟡 Warnings"] + [f"- {REDACT(w)}" for w in run.warnings]
    text = REDACT("\n".join(lines)) + "\n"
    if path:
        try:
            with open(path, "a", encoding="utf-8") as fh:
                fh.write(text)
        except OSError:
            pass
    LOG.info("summary:\n%s", text)


def build_log_record(cfg: Config, run: RunState, duration: float) -> dict:
    return {
        "run_id": cfg.run_id,
        "loader_version": VERSION,
        "mode": cfg.mode,
        "status": run.status,
        "window_start": run.window[0] if run.window else None,
        "window_end": run.window[1] if run.window else None,
        "core_rows_written": run.core.rows_written,
        "core_days_replaced": len(run.core.days_replaced),
        "core_days_protected": json.dumps([iso(d) for d in run.core.days_protected]),
        "core_days_unverified": json.dumps([iso(d) for d in run.core.days_unverified]),
        "cohort_rows_written": run.cohort.rows_written,
        "cohort_days_replaced": len(run.cohort.days_replaced),
        "api_cost_total": run.core.api_cost_total,
        "api_conversions_total": run.core.api_conversions_total,
        "dropped_columns": json.dumps(run.dropped),
        "warnings": json.dumps(run.warnings)[:20000],
        "errors": json.dumps(run.private_errors)[:20000],
        "duration_sec": round(duration, 1),
    }


def _age_hours(ts: dt.datetime | None) -> float | None:
    if ts is None:
        return None
    if ts.tzinfo is None:
        ts = ts.replace(tzinfo=dt.timezone.utc)
    return (utc_now() - ts).total_seconds() / 3600


def _transient_outcome(cfg: Config, run: RunState, wh, detail: str) -> int:
    """Decide green/red for a transient failure that stopped the core load."""
    run.status = "transient_skip"
    if cfg.mode != "load":
        run.error(f"AppLovin/Google unreachable during {cfg.mode}: {detail}")
        return 1
    if wh is None:   # the BigQuery client itself could not be created (transient infra)
        run.warn(f"transient failure before BigQuery was reachable ({detail}); skipping, the next run retries")
        return 0
    try:
        age_h = _age_hours(wh.last_success_at())
    except Exception as e:  # noqa: BLE001 - BigQuery itself unreachable: outages are short
        run.warn(f"transient failure ({detail}); load_log unreadable too ({public_exc(e)}); "
                 f"skipping, the next run retries")
        return 0
    if age_h is not None and age_h <= cfg.stale_hours:
        run.warn(f"temporary failure; run skipped, nothing written. Last good load {age_h:.1f}h ago "
                 f"(limit {cfg.stale_hours}h); the next run retries. Detail: {detail}")
        return 0
    since = (f"the last good load was {age_h:.1f}h ago" if age_h is not None
             else "no successful load is recorded yet")
    run.error(f"loader keeps failing transiently and {since} (limit {cfg.stale_hours}h). Detail: {detail}")
    return 1


def run_loader(cfg: Config, warehouse_factory=BigQueryWarehouse, api: AppLovinAdsAPI | None = None,
               today: dt.date | None = None) -> int:
    """Returns the process exit code. Injectable for tests."""
    started = time.time()
    run = RunState()
    api = api or AppLovinAdsAPI(cfg)
    today = today or utc_now().date()
    fetcher = Fetcher(api, cfg, run, today)
    lo, hi = today - dt.timedelta(days=cfg.lookback_days), today
    run.window = (lo, hi)
    wh = None
    LOG.info("AppLovin Ads loader v%s · mode=%s · window %s..%s · cohort=%s", VERSION, cfg.mode, lo, hi, cfg.include_cohort)
    if cfg.lookback_clamped_from is not None:
        run.warn(f"LOOKBACK_DAYS={cfg.lookback_clamped_from} clamped to {API_MAX_LOOKBACK} "
                 f"(AppLovin only serves the last 45 days)")

    try:
        if cfg.mode == "probe":
            run_probe(fetcher, cfg, run, today)
            run.status = "failed" if run.errors else ("ok_with_warnings" if run.warnings else "ok")
            return 1 if run.errors else 0

        wh = warehouse_factory(cfg)
        if cfg.mode == "load":
            wh.ensure()

        core_cols, _ = fetcher.resolve_columns(CORE, today - dt.timedelta(days=CORE.probe_lag))
        process_report(CORE, core_cols, fetcher, wh, cfg, run, lo, hi, today)
        if run.core.api_rows == 0 and not run.core.days_protected:
            run.warn(f"AppLovin Ads API returned 0 rows for {lo}..{hi} (campaigns paused?). If you expect spend, "
                     f"confirm APPLOVIN_ADS_REPORT_KEY is the Report Key of the AppLovin ADS account (not MAX).")

        if cfg.include_cohort:
            try:
                cohort_cols, _ = fetcher.resolve_columns(COHORT, today - dt.timedelta(days=COHORT.probe_lag))
                process_report(COHORT, cohort_cols, fetcher, wh, cfg, run, lo, hi, today)
            except Exception as e:  # noqa: BLE001 - core is already safely loaded
                if isinstance(e, TransientAPIError) or is_transient_infra(e):
                    run.cohort.skipped_reason = "transient error"
                    age, never = None, False
                    try:
                        if cfg.mode == "load":
                            age = _age_hours(wh.last_success_at(cohort=True))
                            if age is None:           # cohort NEVER loaded: stale once the loader is older
                                never, age = True, _age_hours(wh.first_success_at())
                    except Exception:  # noqa: BLE001
                        age = None
                    if cfg.mode == "load" and age is not None and age > cfg.stale_hours:
                        since = (f"cohort has never loaded although the loader has run for {age:.1f}h" if never
                                 else f"last cohort load {age:.1f}h ago")
                        run.error(f"cohort keeps failing transiently; {since} (limit {cfg.stale_hours}h): "
                                  f"{public_exc(e)}", private=safe_exc(e))
                    else:
                        run.warn(f"cohort skipped this run (core already loaded): {public_exc(e)}")
                elif isinstance(e, PostWriteCheckError):
                    run.cohort.skipped_reason = None
                    run.error(f"cohort: {e}")
                else:
                    run.cohort.skipped_reason = type(e).__name__
                    run.error(f"cohort failed (core already loaded): {public_exc(e)}", private=safe_exc(e))
        else:
            run.cohort.skipped_reason = "INCLUDE_COHORT=false"

        if run.errors:
            run.status = "partial" if run.core.days_replaced else "failed"
        elif run.core.api_rows == 0:
            run.status = "ok_empty"
        elif run.warnings:
            run.status = "ok_with_warnings"
        else:
            run.status = "ok"
        return 1 if run.errors else 0

    except TransientAPIError as e:
        return _transient_outcome(cfg, run, wh, str(e))
    except (ConfigError, DataError, RequestRejected) as e:
        run.status = "partial" if run.core.days_replaced else "failed"
        run.error(f"{type(e).__name__}: {e}")
        return 1
    except Exception as e:  # noqa: BLE001 - last line of defence, always redacted
        if is_transient_infra(e) and not run.core.days_replaced:
            return _transient_outcome(cfg, run, wh, public_exc(e))
        run.status = "partial" if run.core.days_replaced else "failed"
        run.error(f"unexpected {public_exc(e)}", private=safe_exc(traceback.format_exc()))
        return 1
    finally:
        duration = time.time() - started
        if cfg.mode == "load" and wh is not None:
            try:
                wh.write_log(build_log_record(cfg, run, duration))
            except Exception as e:  # noqa: BLE001
                LOG.warning("could not write load_log (%s)", public_exc(e))
        write_summary(cfg, run, duration, api.calls)


# =============================================================================
# DDL (kept in sync with the code: generated from the same schema objects)
# =============================================================================
def print_ddl(project: str, dataset: str, location: str = "US") -> str:
    sqltype = {"STRING": "STRING", "INTEGER": "INT64", "FLOAT": "FLOAT64", "DATE": "DATE", "TIMESTAMP": "TIMESTAMP"}
    out = [f"CREATE SCHEMA IF NOT EXISTS `{project}.{dataset}`\n"
           f"  OPTIONS (location = '{location}', description = "
           f"{json.dumps('AppLovin Ads (advertiser/UA) raw data - loaded by applovin_ads_to_bigquery.py')});"]
    for td in table_defs():
        cols = ",\n".join(
            f"  `{f.name}` {sqltype[f.type]}{' NOT NULL' if f.mode == 'REQUIRED' else ''}"
            + (f" OPTIONS (description = {json.dumps(f.description)})" if f.description else "")
            for f in td.schema)
        part = f"\nPARTITION BY {td.partition_field}" if td.partition_field else ""
        clus = f"\nCLUSTER BY {', '.join(td.clustering)}" if td.clustering else ""
        out.append(f"CREATE TABLE IF NOT EXISTS `{project}.{dataset}.{td.name}` (\n{cols}\n){part}{clus}\n"
                   f"OPTIONS (description = {json.dumps(td.description)});")
    return "\n\n".join(out) + "\n"


def main(argv: list[str]) -> int:
    setup_logging()
    if len(argv) > 1 and argv[1] == "--print-ddl":
        print(print_ddl(argv[2] if len(argv) > 2 else "terafort", argv[3] if len(argv) > 3 else "applovin_ads"))
        return 0
    try:
        cfg = Config.from_env()
    except ConfigError as e:
        gh_annotation("error", str(e))
        LOG.error("%s", e)
        return 1
    try:
        return run_loader(cfg)
    except BaseException as e:  # noqa: BLE001 - make sure nothing unredacted escapes
        LOG.error("fatal %s\n%s", public_exc(e), safe_exc(traceback.format_exc()))
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
