#!/usr/bin/env python3
"""
AppLovin Ads -> BigQuery  ·  v2.0  (2026-10-09)
==============================================================================
WHAT
  Everything AppLovin Ads (the ADVERTISER / UA side, formerly AppDiscovery)
  exposes through its APIs, loaded into BigQuery dataset $BQ_DATASET:

  Reporting API  r.applovin.com/report   (Report Key)
    core          campaign_country_daily  day x campaign x platform x country (+ campaign settings,
                                          sales, target events)              -- the money table
    cohort        campaign_cohort_daily   install day x campaign x platform x country: revenue
                                          (total/ad/IAP), purchasers, sales, target events 0..30d,
                                          retention 1..28d
    creative      creative_daily          day x campaign x creative set x ad x creative type
    supply        supply_daily            day x campaign x traffic source x placement x size x ad type x device
    site          site_daily              day x campaign x publisher app (site) -- for blocklists
    hourly        hourly                  day x hour x campaign (last 30 days)               [best effort]
    ska           ska_daily               r.applovin.com/skaReport (iOS SKAdNetwork)          [best effort]
    probabilistic probabilistic_daily     r.applovin.com/probabilisticReport                  [best effort]
  Asset Reporting API  r.applovin.com/assetAnalyticsReport   (Report Key)
    assets        asset_daily             day x asset x creative set x campaign               [best effort]
  [best effort] = not guaranteed for every account: if AppLovin doesn't serve it, the run stays
  green with a warning (repeated only as info while it stays unavailable).
  Campaign Management API  api.ads.axon.ai/manage/v1   (separate Campaign Management key; optional)
    mgmt          mgmt_campaign_snapshot / mgmt_creative_set_snapshot / mgmt_asset_snapshot
                  (one snapshot per UTC day: budgets, goals, bidding, targeting, status ...)
                  mgmt_campaign_operation_log (change history of all campaigns, de-duplicated)

  NOT stored on purpose: ratios the API also offers (ctr, conversion_rate, average_cpa/cpc,
  roas_x, ad_roas_x, cpp_x, cost_per_target_event_x). They are exactly derivable from the stored
  sums, and summing a ratio is wrong. 90d / 1y cohort windows are not stored either: the API only
  serves the last 45 days, so those values could never mature.

SAFETY (applies to every table)
  1. Reconciliation  strict (core, cohort): every day's rows must add up to AppLovin's own day
                     total (installs exactly). upper (breakdowns): rows may never EXCEED the day
                     total (duplication guard); coverage % is logged (iOS/SKAN rows can be absent
                     from breakdowns). A failing settled day is not written; recent days may only
                     grow by a bounded amount, else the previous values are kept.
  2. Paging          limit/offset until an EMPTY page; overlapping pages are detected and the chunk
                     is re-fetched day by day. Reports that reconciliation cannot prove complete
                     (breakdowns, assets, Campaign Management lists) REFUSE every ambiguous paging end
                     (rejected page after a full page, identical full page, paging not accepted)
                     instead of writing a possibly truncated result.
  3. Drift guard     a day whose spend or installs would drop (or, when settled, jump) by more than
                     MAX_CHANGE_PCT vs BigQuery is not replaced. Override: FORCE_REPLACE=true.
  4. Atomic replace  per-day DELETE+INSERT in ONE BigQuery transaction from a staged batch load.
  5. Columns         an optional column the API rejects/omits/blanks keeps its existing BigQuery
                     value (never NULLed). Optional endpoints that this account doesn't have are
                     skipped with a warning; core failing is red.
  6. Honest exit     transient trouble -> green + warning unless that report's last success is
                     older than STALE_HOURS -> red (a report that never loaded: counted from when it was
                     first attempted; best-effort ones never go red for that). A best-effort report
                     that DID load before and is now refused -> warning, red after STALE_HOURS.
                     Auth/config/data problems -> red.
  7. Secret hygiene  keys redacted everywhere; no campaign names or money values in public logs.

MODES (MODE env)  load (default) | dry-run (fetch + checks, writes nothing) | probe (keys + columns)
REPORTS env       all | comma list of: core,cohort,creative,supply,site,hourly,ska,probabilistic,assets,mgmt
CLI               python applovin_ads_to_bigquery.py --print-ddl [project] [dataset]
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

VERSION = "2.0"
LOG = logging.getLogger("applovin_ads")
DEFAULT_API_BASE = "https://r.applovin.com"
DEFAULT_MGMT_BASE = "https://api.ads.axon.ai/manage/v1"
API_MAX_LOOKBACK = 44          # the API accepts dates within the last 45 days -> today-44 .. today
ALL_REPORTS = ("core", "cohort", "creative", "supply", "site", "hourly", "ska", "probabilistic", "assets", "mgmt")


# =============================================================================
# Errors
# =============================================================================
class LoaderError(Exception):
    """Base class."""


class ConfigError(LoaderError):
    """Needs a human (bad env, missing secret, rejected required column) -> red."""


class AuthError(ConfigError):
    """Key rejected (401/403)."""


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


class _FirstPageRejected(Exception):
    """Page 1 of a limit/offset request was rejected (internal: try a smaller limit / unpaged)."""

    def __init__(self, status: int):
        super().__init__(status)
        self.status = status


# =============================================================================
# Secret redaction (PUBLIC repo: GitHub masks the raw secret, but not its URL-encoded
# form; requests puts the full URL inside exception messages)
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
    """Exception text without ANY URL query string, then redacted."""
    return REDACT(_QUERY_STRING.sub("?<query hidden>", str(e)))


def public_exc(e: BaseException) -> str:
    """Short, data-free description for PUBLIC logs (Google errors can quote cell values)."""
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
            return True
    except ImportError:  # pragma: no cover
        pass
    try:
        from google.auth import exceptions as gauth
        if isinstance(e, gauth.TransportError):
            return True
        if isinstance(e, gauth.GoogleAuthError) and getattr(e, "retryable", False):
            return True
    except ImportError:  # pragma: no cover
        pass
    return isinstance(e, (requests.ConnectionError, requests.Timeout, ConnectionError, TimeoutError))


class RedactingFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        try:
            msg = record.getMessage()
        except Exception:  # noqa: BLE001
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
    msg = REDACT(message).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    print(f"::{level}::{msg}", flush=True)


# =============================================================================
# Config
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


def parse_reports(raw: str | None, include_cohort: bool) -> tuple:
    if raw is None or raw.strip().lower() == "all":
        names = list(ALL_REPORTS)
    else:
        names = [x.strip().lower() for x in raw.split(",") if x.strip()]
        bad = [x for x in names if x not in ALL_REPORTS]
        if bad:
            raise ConfigError(f"REPORTS contains unknown report(s) {bad}; allowed: all or {','.join(ALL_REPORTS)}")
    if not include_cohort:
        names = [x for x in names if x != "cohort"]
    return tuple(x for x in ALL_REPORTS if x in names)      # canonical order (core first)


@dataclass(frozen=True)
class Config:
    api_key: str
    api_base: str
    mode: str
    project: str | None
    dataset: str | None
    location: str
    creds_json: str | None
    lookback_days: int
    chunk_days: int
    page_limit: int
    max_pages: int
    reports: tuple
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
    mgmt_key: str | None = None
    account_id: str | None = None
    mgmt_base: str = DEFAULT_MGMT_BASE
    lookback_clamped_from: int | None = None

    @property
    def include_cohort(self) -> bool:
        return "cohort" in self.reports

    @staticmethod
    def from_env() -> "Config":
        key = _env("APPLOVIN_ADS_REPORT_KEY")
        if not key:
            raise ConfigError("APPLOVIN_ADS_REPORT_KEY is empty. Add the AppLovin **Ads** Report Key under "
                              "repo Settings -> Secrets and variables -> Actions.")
        REDACT.add(key)
        mgmt_key = _env("APPLOVIN_ADS_MGMT_KEY")
        REDACT.add(mgmt_key)
        account_id = _env("APPLOVIN_ADS_ACCOUNT_ID")
        if account_id and not re.fullmatch(r"\d{1,20}", account_id):
            raise ConfigError("APPLOVIN_ADS_ACCOUNT_ID must be the numeric account id")
        mode = (_env("MODE") or "load").lower()
        if mode not in ("load", "dry-run", "probe"):
            raise ConfigError(f"MODE={mode!r} must be load | dry-run | probe")
        project, dataset = _env("GCP_PROJECT"), _env("BQ_DATASET")
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
            api_base=(_env("APPLOVIN_ADS_API_BASE") or DEFAULT_API_BASE).rstrip("/"),
            mode=mode, project=project, dataset=dataset,
            location=_env("BQ_LOCATION") or "US",
            creds_json=_env("GCP_CREDENTIALS_JSON"),
            lookback_days=lookback,
            chunk_days=env_int("CHUNK_DAYS", 7, 1, 45),
            page_limit=env_int("PAGE_LIMIT", 10000, 1, 1_000_000),
            max_pages=env_int("MAX_PAGES", 500, 1, 100_000),
            reports=parse_reports(_env("REPORTS"), env_bool("INCLUDE_COHORT", True)),
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
            run_budget_sec=env_int("RUN_BUDGET_SEC", 2400, 30, 12 * 3600),
            run_id=run_id,
            mgmt_key=mgmt_key, account_id=account_id,
            mgmt_base=(_env("APPLOVIN_ADS_MGMT_BASE") or DEFAULT_MGMT_BASE).rstrip("/"),
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


DIM_DESC = {
    # campaign attributes
    "campaign_id_external": "Stable AppLovin campaign id (survives renames)",
    "campaign_id": "AppLovin campaign id (= campaign_id_external in the Reporting API)",
    "campaign": "Campaign name as reported by AppLovin",
    "campaign_package_name": "Promoted app: Android package / iOS bundle id",
    "campaign_store_id": "Promoted app store id: numeric iTunes id (iOS) or package name",
    "campaign_type": "CPP / CPE / AD_ROAS / IAP_ROAS / ROAS ...",
    "campaign_ad_type": "ua (user acquisition) or rt (retargeting)",
    "campaign_bid_goal": "Bid goal in USD (CPP / CPE campaigns), as reported (text)",
    "campaign_roas_goal": "ROAS goal in percent (ROAS campaigns), as reported (text)",
    "optimization_day_target": "Optimization day targeted by the campaign (e.g. day 0, day 7)",
    "bidding_and_billing_method": "AUTO_BIDDING_WITH_CPM_BILLING / ... as reported",
    "target_event": "Custom event targeted (CPE campaigns)",
    # breakdowns
    "platform": "android / ios / fireos / tvos (lowercased)",
    "country": "ISO-2 country code (uppercased)",
    "creative_set": "Creative set name",
    "creative_set_id": "Creative set id (stable across renames)",
    "ad": "Ad (creative) name",
    "ad_id": "Ad (creative) id",
    "ad_creative_type": "GRAPHIC / PLAYABLE / VIDEO / VIDEO_GRAPHIC / VIDEO_PLAYABLE",
    "custom_page_id": "iOS Custom Product Page / Android Store Listing id of the creative set",
    "traffic_source": "AppLovin or the exchange name",
    "placement_type": "APP_OPEN / BANNER / CTV / INTER / LEADER / MREC / NATIVE / REWARDED_INTER",
    "size": "BANNER / INTER / LEADER / MREC / NATIVE / PRELOAD",
    "ad_type": "APPOPEN / GRAPHIC / PLAY / REWARD / VIDEO",
    "device_type": "phone / tablet / other",
    "app_id_external": "Hashed publisher application (site) id",
    "external_placement_id": "Encrypted publisher application id",
    "application": "Publisher (source) application name",
    "hour": "Hour of day, UTC, as reported (e.g. 13:00)",
    "asset_id": "Creative asset id",
    "asset_name": "Creative asset name",
    "asset_url": "URL of the raw asset before processing",
}

# Cohort windows, from AppLovin's column list (90d / 1y are left out: they cannot mature inside the
# 45-day API window). A group is accepted or rejected as a whole, so windows that v1 proved in
# production stay in their own group and a rejected newer window can never take them down.
REV8 = ["0d", "1d", "2d", "3d", "7d", "14d", "28d", "30d"]   # total_rev_x, ad_rev_x
EVT7 = ["0d", "1d", "2d", "3d", "7d", "14d", "30d"]          # sales_x, target_event_count_x, unique_purchasers_x
RET5 = ["1d", "3d", "7d", "14d", "28d"]
IAP_V1, IAP_NEW = ["0d", "1d", "3d", "7d", "14d", "30d"], ["2d", "28d"]       # iap_rev_x (legacy list only)
PUR_V1, PUR_NEW = ["0d", "7d", "30d"], ["1d", "2d", "3d", "14d"]               # unique_purchasers_x
REV_V1, REV_NEW = ["0d", "1d", "3d", "7d", "14d", "30d"], ["2d", "28d"]       # total_rev_x / ad_rev_x
CAMPAIGN_ATTRS = ("campaign_id_external", "campaign", "campaign_package_name")


@dataclass(frozen=True)
class ReportSpec:
    name: str
    table: str
    endpoint: str                       # report | skaReport | probabilisticReport | assetAnalyticsReport
    report_type: str | None             # "advertiser" (Reporting API) or None (asset API)
    day_column: str | None              # "day" -> cohort metrics
    required: tuple
    optional_groups: dict
    attr_dims: tuple                    # attributes (merged, not part of the row key)
    grain_dims: tuple                   # part of the row key (with day + campaign_key)
    int_metrics: tuple = ()
    float_metrics: tuple = ()
    rate_metrics: tuple = ()
    zero_if_empty: tuple = ()
    reconcile: str = "strict"           # strict | upper | none
    reconcile_metrics: tuple = ("cost", "conversions", "impressions")
    critical: bool = False              # failure of a critical report is red even if "unavailable"
    best_effort: bool = False           # endpoint/column not guaranteed for every account: "not available" = warning
    per_day: bool = False              # one request per day; 'day' injected (asset API has no day column)
    campaign_id_col: str = "campaign_id_external"
    lookback_cap: int | None = None
    probe_lag: int = 2
    description: str = ""

    @property
    def all_columns(self) -> list[str]:
        cols = list(self.required)
        for group in self.optional_groups.values():
            cols += [c for c in group if c not in cols]
        return cols

    @property
    def dims(self) -> list[str]:
        return list(self.attr_dims) + list(self.grain_dims)

    @property
    def metrics(self) -> tuple:
        return self.int_metrics + self.float_metrics + self.rate_metrics

    @property
    def key_cols(self) -> list[str]:
        return ["day", "campaign_key"] + list(self.grain_dims)

    @property
    def preserve_cols(self) -> list[str]:
        """Optional non-key columns: a blank/absent/dropped value keeps the stored one."""
        opt = [c for g in self.optional_groups.values() for c in g]
        return [c for c in opt if c not in self.grain_dims]

    def metric_desc(self, m: str) -> str:
        fixed = {"cost": "Advertiser spend, USD", "conversions": "Installs (conversions)",
                 "impressions": "Impressions", "clicks": "Clicks",
                 "sales": "Attributed sales events (needs revenue postbacks)",
                 "target_event_count": "Unique target events (CPE)"}
        if m in fixed:
            return fixed[m]
        for pfx, label in (("total_rev_", "Total revenue USD"), ("ad_rev_", "Ad revenue USD"),
                           ("iap_rev_", "IAP revenue USD"), ("sales_", "Sales"),
                           ("target_event_count_", "Unique target events"),
                           ("unique_purchasers_", "Unique purchasers")):
            if m.startswith(pfx):
                return f"{label} within {m[len(pfx):]} of install (cohort)"
        if m.startswith("ret_"):
            return f"Retention {m[4:]} as returned by AppLovin (a RATE; do not SUM)"
        return m

    def schema(self) -> list[FieldDef]:
        cohort = self.day_column == "day"
        fields = [
            FieldDef("day", "DATE", "REQUIRED",
                     "Install (cohort) day, UTC" if cohort else "Activity day, UTC (AppLovin realtime)"),
            FieldDef("campaign_key", "STRING", "REQUIRED",
                     f"{self.campaign_id_col}, else 'name:'+campaign; part of the row key"),
        ]
        fields += [FieldDef(d, "STRING", "NULLABLE", DIM_DESC.get(d, d)) for d in self.dims]
        fields += [FieldDef(m, "INTEGER", "NULLABLE", self.metric_desc(m)) for m in self.int_metrics]
        fields += [FieldDef(m, "FLOAT", "NULLABLE", self.metric_desc(m)) for m in self.float_metrics]
        fields += [FieldDef(m, "FLOAT", "NULLABLE", self.metric_desc(m)) for m in self.rate_metrics]
        fields += [FieldDef("_run_id", "STRING", "NULLABLE", "Loader run that wrote this row"),
                   FieldDef("_ingested_at", "TIMESTAMP", "NULLABLE", "When this row was written (UTC)")]
        return fields


REALTIME_METRICS = dict(int_metrics=("impressions", "clicks", "conversions", "sales", "target_event_count"),
                        float_metrics=("cost",),
                        zero_if_empty=("impressions", "clicks", "conversions", "cost"))
EVENT_GROUP = {"events": ["sales", "target_event_count"]}
BASE_REQ = ("day", "campaign", "campaign_id_external", "campaign_package_name", "platform",
            "impressions", "clicks", "conversions", "cost")

CORE = ReportSpec(
    name="core", table="campaign_country_daily", endpoint="report", report_type="advertiser", day_column=None,
    required=BASE_REQ + ("country",),
    optional_groups={"campaign_attrs": ["campaign_store_id", "campaign_type", "campaign_ad_type"],
                     "campaign_settings": ["campaign_bid_goal", "campaign_roas_goal", "optimization_day_target",
                                           "bidding_and_billing_method", "target_event"],
                     **EVENT_GROUP},
    attr_dims=CAMPAIGN_ATTRS + ("campaign_store_id", "campaign_type", "campaign_ad_type", "campaign_bid_goal",
                                "campaign_roas_goal", "optimization_day_target", "bidding_and_billing_method",
                                "target_event"),
    grain_dims=("platform", "country"),
    reconcile="strict", critical=True, probe_lag=2,
    description="AppLovin Ads spend/installs per day x campaign x platform x country (realtime, UTC)",
    **REALTIME_METRICS,
)

COHORT = ReportSpec(
    name="cohort", table="campaign_cohort_daily", endpoint="report", report_type="advertiser", day_column="day",
    required=("day", "campaign", "campaign_id_external", "campaign_package_name", "platform", "country",
              "conversions", "cost"),
    optional_groups={
        "total_rev": [f"total_rev_{s}" for s in REV_V1],
        "ad_rev": [f"ad_rev_{s}" for s in REV_V1],
        "iap_rev": [f"iap_rev_{s}" for s in IAP_V1],
        "purchasers": [f"unique_purchasers_{s}" for s in PUR_V1],
        "retention": [f"ret_{s}" for s in RET5],
        "total_rev_more": [f"total_rev_{s}" for s in REV_NEW],
        "ad_rev_more": [f"ad_rev_{s}" for s in REV_NEW],
        "iap_rev_more": [f"iap_rev_{s}" for s in IAP_NEW],
        "purchasers_more": [f"unique_purchasers_{s}" for s in PUR_NEW],
        "sales": [f"sales_{s}" for s in EVT7],
        "target_events": [f"target_event_count_{s}" for s in EVT7],
    },
    attr_dims=CAMPAIGN_ATTRS, grain_dims=("platform", "country"),
    int_metrics=("conversions",) + tuple(f"unique_purchasers_{s}" for s in EVT7)
               + tuple(f"sales_{s}" for s in EVT7) + tuple(f"target_event_count_{s}" for s in EVT7),
    float_metrics=("cost",) + tuple(f"{p}_{s}" for p in ("total_rev", "ad_rev", "iap_rev") for s in REV8),
    rate_metrics=tuple(f"ret_{s}" for s in RET5),
    zero_if_empty=("conversions", "cost"),
    reconcile="strict", reconcile_metrics=("cost", "conversions"), critical=True, probe_lag=10,
    description="AppLovin Ads cohort metrics by install day (day_column=day): revenue, purchasers, sales, events, retention",
)

CREATIVE = ReportSpec(
    name="creative", table="creative_daily", endpoint="report", report_type="advertiser", day_column=None,
    required=BASE_REQ + ("creative_set",),
    optional_groups={"creative_set_id": ["creative_set_id"], "ad": ["ad"],
                     "creative_type": ["ad_creative_type"], "custom_page": ["custom_page_id"], **EVENT_GROUP},
    attr_dims=CAMPAIGN_ATTRS,
    grain_dims=("platform", "creative_set_id", "creative_set", "ad", "ad_creative_type", "custom_page_id"),
    reconcile="upper", probe_lag=2,
    description="AppLovin Ads per day x campaign x creative set x ad x creative type",
    **REALTIME_METRICS,
)

SUPPLY = ReportSpec(
    name="supply", table="supply_daily", endpoint="report", report_type="advertiser", day_column=None,
    required=BASE_REQ,
    optional_groups={"traffic_source": ["traffic_source"], "placement_type": ["placement_type"], "size": ["size"],
                     "ad_type": ["ad_type"], "device_type": ["device_type"], **EVENT_GROUP},
    attr_dims=CAMPAIGN_ATTRS,
    grain_dims=("platform", "traffic_source", "placement_type", "size", "ad_type", "device_type"),
    reconcile="upper", probe_lag=2,
    description="AppLovin Ads per day x campaign x traffic source x placement x size x ad type x device",
    **REALTIME_METRICS,
)

SITE = ReportSpec(
    name="site", table="site_daily", endpoint="report", report_type="advertiser", day_column=None,
    required=BASE_REQ + ("app_id_external",),
    optional_groups={"application": ["application"], "external_placement_id": ["external_placement_id"], **EVENT_GROUP},
    attr_dims=CAMPAIGN_ATTRS + ("application",),
    grain_dims=("platform", "app_id_external", "external_placement_id"),
    reconcile="upper", probe_lag=2,
    description="AppLovin Ads per day x campaign x publisher application (site)",
    **REALTIME_METRICS,
)

HOURLY = ReportSpec(
    name="hourly", table="hourly", endpoint="report", report_type="advertiser", day_column=None,
    required=BASE_REQ + ("hour",),
    optional_groups=dict(EVENT_GROUP),
    attr_dims=CAMPAIGN_ATTRS, grain_dims=("platform", "hour"),
    reconcile="upper", lookback_cap=29, probe_lag=2, best_effort=True,   # 'hour': past 30 days only
    description="AppLovin Ads per day x hour (UTC) x campaign x platform (last 30 days)",
    **REALTIME_METRICS,
)

_ALT_OPT = {"campaign_id_external": ["campaign_id_external"], "campaign_package_name": ["campaign_package_name"],
            "platform": ["platform"], "country": ["country"], "impressions": ["impressions"],
            "clicks": ["clicks"], "conversions": ["conversions"]}

SKA = ReportSpec(
    name="ska", table="ska_daily", endpoint="skaReport", report_type="advertiser", day_column=None,
    required=("day", "campaign", "cost"), optional_groups=dict(_ALT_OPT),
    attr_dims=CAMPAIGN_ATTRS, grain_dims=("platform", "country"),
    int_metrics=("impressions", "clicks", "conversions"), float_metrics=("cost",), zero_if_empty=("cost",),
    reconcile="upper", reconcile_metrics=("cost",), probe_lag=3, best_effort=True,
    description="AppLovin Ads SKAdNetwork report (skaReport endpoint), if the account has it",
)

PROBABILISTIC = ReportSpec(
    name="probabilistic", table="probabilistic_daily", endpoint="probabilisticReport", report_type="advertiser",
    day_column=None, required=("day", "campaign", "cost"), optional_groups=dict(_ALT_OPT),
    attr_dims=CAMPAIGN_ATTRS, grain_dims=("platform", "country"),
    int_metrics=("impressions", "clicks", "conversions"), float_metrics=("cost",), zero_if_empty=("cost",),
    reconcile="upper", reconcile_metrics=("cost",), probe_lag=2, best_effort=True,
    description="AppLovin Ads probabilistic report (probabilisticReport endpoint), if the account has it",
)

ASSETS = ReportSpec(
    name="assets", table="asset_daily", endpoint="assetAnalyticsReport", report_type=None, day_column=None,
    required=("asset_id", "campaign_id", "impressions", "clicks", "cost"),
    optional_groups={"asset_name": ["asset_name"], "asset_url": ["asset_url"], "campaign": ["campaign"],
                     "campaign_package_name": ["campaign_package_name"], "creative_set": ["creative_set"],
                     "creative_set_id": ["creative_set_id"]},
    attr_dims=("campaign_id", "campaign", "campaign_package_name", "asset_name", "asset_url", "creative_set"),
    grain_dims=("asset_id", "creative_set_id"),
    int_metrics=("impressions", "clicks"), float_metrics=("cost",), zero_if_empty=("impressions", "clicks", "cost"),
    reconcile="none", reconcile_metrics=(), per_day=True, campaign_id_col="campaign_id", probe_lag=2,
    best_effort=True,
    description="AppLovin Ads per day x creative asset x creative set x campaign (assetAnalyticsReport, one request per day)",
)

REPORT_SPECS = [CORE, COHORT, CREATIVE, SUPPLY, SITE, HOURLY, SKA, PROBABILISTIC, ASSETS]
SPEC_BY_NAME = {s.name: s for s in REPORT_SPECS}

# ---- Campaign Management API snapshot tables -----------------------------------------------
_S = lambda n, d="": FieldDef(n, "STRING", "NULLABLE", d)  # noqa: E731
SNAP_TAIL = [_S("raw_json", "Full object as returned by the API (JSON text)"),
             FieldDef("_run_id", "STRING"), FieldDef("_ingested_at", "TIMESTAMP")]
MGMT_CAMPAIGN_FIELDS = [
    FieldDef("day", "DATE", "REQUIRED", "Snapshot day, UTC"), FieldDef("id", "STRING", "REQUIRED", "Campaign id"),
    _S("hashed_id"), _S("name"), _S("status", "LIVE / PAUSED"), _S("type"), _S("platform"), _S("package_name"),
    _S("itunes_id"), _S("bidding_strategy"), _S("start_date"), _S("end_date"), _S("created_at"),
    FieldDef("daily_budget_usd", "FLOAT", "NULLABLE", "budget.daily_budget_for_all_countries"),
    _S("country_budgets_json", "budget.country_code_to_daily_budget"),
    _S("goal_type", "CPI / CPE / CPP / AD_ROAS / CHK_ROAS / BLD_ROAS"),
    FieldDef("goal_value", "FLOAT", "NULLABLE", "goal.goal_value_for_all_countries"),
    _S("country_goals_json", "goal.country_code_to_goal_value"), _S("roas_day_target"), _S("event_target"),
    _S("targeting_json"), _S("tracking_method"), _S("is_continuous_delivery"), _S("is_composite_banner_enabled"),
] + SNAP_TAIL
MGMT_CREATIVE_SET_FIELDS = [
    FieldDef("day", "DATE", "REQUIRED", "Snapshot day, UTC"), FieldDef("id", "STRING", "REQUIRED", "Creative set id"),
    _S("hashed_id"), _S("campaign_id"), _S("campaign_ids_json", "All campaigns using this creative set"),
    _S("name"), _S("type"), _S("status", "LIVE / PAUSED"), _S("version"),
    _S("product_page"), _S("created_at"), _S("languages_json"), _S("countries_json"), _S("assets_json"),
    FieldDef("asset_count", "INTEGER"),
] + SNAP_TAIL
MGMT_ASSET_FIELDS = [
    FieldDef("day", "DATE", "REQUIRED", "Snapshot day, UTC"), FieldDef("id", "STRING", "REQUIRED", "Asset id"),
    _S("name"), _S("status", "IN_REVIEW / REJECTED / ACTIVE / PAUSED"), _S("url"), _S("asset_type"),
    _S("resource_type", "IMAGE / VIDEO / HTML"), _S("asset_hash"), _S("upload_time"), _S("violation_reasons_json"),
] + SNAP_TAIL
MGMT_OPLOG_FIELDS = [
    FieldDef("log_key", "STRING", "REQUIRED", "op:<operation_id>:<campaign_id>, else h:<sha256 of the entry>; de-duplication key"),
    _S("operation_id"), _S("operation_time", "ISO-8601 UTC, as returned"),
    _S("operation_type", "CREATE_CAMPAIGN / UPDATE_CAMPAIGN / UPDATE_CAMPAIGN_STATUS / ARCHIVE_CAMPAIGN ..."),
    _S("operator_name"), _S("campaign_id"), _S("campaign_name"), _S("campaign_type"),
    _S("detail_json", "detail: campaign (create) or before/after (updates)"),
    _S("raw_json", "Operation log entry as returned by the API (JSON text)"),
    FieldDef("first_seen_at", "TIMESTAMP", "NULLABLE", "When the loader first stored this entry"),
    FieldDef("_run_id", "STRING"),
]

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
    FieldDef("api_cost_total", "FLOAT", description="Sum of API day totals (cost) over the window (core)"),
    FieldDef("api_conversions_total", "INTEGER"),
    FieldDef("dropped_columns", "STRING", description="JSON: optional columns rejected/omitted (old values kept)"),
    FieldDef("warnings", "STRING"),
    FieldDef("errors", "STRING", description="JSON: FULL error details (private; public logs show a short form)"),
    FieldDef("duration_sec", "FLOAT"),
    FieldDef("report_stats", "STRING", description="JSON per report: ok, rows, days replaced/protected/unverified, coverage"),
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
    key_cols: tuple = ()


MGMT_TABLES = {
    "campaign": TableDef("mgmt_campaign_snapshot", MGMT_CAMPAIGN_FIELDS, "day", ("id",),
                         "Daily snapshot of AppLovin Ads campaigns (Campaign Management API)", ("day", "id")),
    "creative_set": TableDef("mgmt_creative_set_snapshot", MGMT_CREATIVE_SET_FIELDS, "day", ("campaign_id", "id"),
                             "Daily snapshot of AppLovin Ads creative sets (Campaign Management API)", ("day", "id")),
    "asset": TableDef("mgmt_asset_snapshot", MGMT_ASSET_FIELDS, "day", ("id",),
                      "Daily snapshot of AppLovin Ads assets (Campaign Management API)", ("day", "id")),
    "oplog": TableDef("mgmt_campaign_operation_log", MGMT_OPLOG_FIELDS, None, ("campaign_id",),
                      "AppLovin Ads campaign change history (Campaign Management API), de-duplicated", ("log_key",)),
}


def table_defs() -> list[TableDef]:
    out = [TableDef(s.table, s.schema(), "day", tuple(c for c in ("campaign_package_name", "platform") if c in s.dims)
                    + ((s.grain_dims[1],) if len(s.grain_dims) > 1 and s.grain_dims[1] != "platform" else ()),
                    s.description, tuple(s.key_cols)) for s in REPORT_SPECS]
    out += list(MGMT_TABLES.values())
    out += [TableDef("load_log", LOAD_LOG_SCHEMA, None, (), "One row per AppLovin Ads loader run (audit trail)"),
            TableDef("apps_correction_map", CORRECTION_MAP_SCHEMA, None, (),
                     "Manual AppLovin package -> app master overrides, read by applovin_ads_staging")]
    return out


# =============================================================================
# Parsing helpers
# =============================================================================
_NUM_RE = re.compile(r"^[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?$")
_EMPTY_TOKENS = {"", "-", "n/a", "na", "null", "none", "nan"}


def value_shape(v: object) -> str:
    """Describe a value WITHOUT revealing it (safe for public logs)."""
    if v is None:
        return "null"
    if isinstance(v, bool):
        return "bool"
    if isinstance(v, int):
        return "int"
    if isinstance(v, float):
        return "float"
    if isinstance(v, (dict, list)):
        return type(v).__name__
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
    """Strict: garbage raises DataError (never silently 0). Commas are REJECTED."""
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
    if isinstance(v, (dict, list)):
        return json.dumps(v, sort_keys=True, default=str)
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
    coverage_pct: float | None = None
    columns_used: list = field(default_factory=list)
    skipped_reason: str | None = None
    ok: bool = False
    attempted: bool = False


@dataclass
class RunState:
    warnings: list = field(default_factory=list)
    errors: list = field(default_factory=list)
    private_errors: list = field(default_factory=list)
    dropped: dict = field(default_factory=dict)
    results: dict = field(default_factory=lambda: {n: ReportResult() for n in ALL_REPORTS})
    status: str = "running"
    window: tuple | None = None

    @property
    def core(self) -> ReportResult:
        return self.results["core"]

    @property
    def cohort(self) -> ReportResult:
        return self.results["cohort"]

    def any_replaced(self) -> bool:
        return any(r.days_replaced for r in self.results.values())

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
# AppLovin Reporting / Asset API client (Report Key)
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
                msg = REDACT(json.dumps(data, default=str))[:400]
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

    def get(self, params: dict, what: str, endpoint: str = "report", report_type: str | None = "advertiser") -> list[dict]:
        q = dict(params)
        q.update(api_key=self.cfg.api_key, format="json")
        if report_type:
            q["report_type"] = report_type
        url = f"{self.cfg.api_base}/{endpoint}"
        last = "no attempt"
        for attempt in range(1, self.cfg.http_attempts + 1):
            remaining = self.deadline - time.monotonic()
            if remaining <= 5:
                raise TransientAPIError(f"{what}: run time budget ({self.cfg.run_budget_sec}s) exhausted - last: {last}")
            self.calls += 1
            retry_after = None
            try:
                resp = self.session.get(url, params=q, timeout=(15, max(5, min(self.cfg.http_read_timeout, int(remaining)))))
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
                    body = REDACT(resp.text)[:400].replace("\n", " ")
                    if status in (401, 403):
                        raise AuthError(f"{what}: AppLovin rejected the report key (HTTP {status}). Make sure "
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

    def get_paged(self, params: dict, what: str, endpoint: str = "report",
                  report_type: str | None = "advertiser", verifiable: bool = True) -> list[dict]:
        """limit/offset until an EMPTY page.
        verifiable=True : the caller reconciles the result against AppLovin's own day totals (core,
                          cohort, every totals call), so ambiguous paging ends are tolerated and the
                          reconciliation decides.
        verifiable=False: nothing downstream can detect missing rows (breakdowns may legitimately be
                          below the day total; assets have no totals), so every ambiguous end REFUSES:
                          a rejected page right after a full page, an identical full page, or limit/offset
                          not accepted at all."""
        limits = [self.cfg.page_limit] + ([1000] if self.cfg.page_limit > 1000 else [])
        for i, limit in enumerate(limits):
            try:
                return self._paged(params, what, endpoint, report_type, verifiable, limit)
            except _FirstPageRejected as e:
                if i + 1 < len(limits):
                    LOG.warning("%s: limit=%d rejected (HTTP %s) - retrying with limit=%d", what, limit, e.status,
                                limits[i + 1])
                    continue
                if not verifiable:
                    raise DataError(f"{what}: AppLovin rejected limit/offset paging (HTTP {e.status}); an unpaged "
                                    f"response could be silently capped and this report has no completeness "
                                    f"check, so nothing is written") from None
                LOG.warning("%s: limit/offset rejected (HTTP %s) - retrying unpaged; reconciliation will verify",
                            what, e.status)
                return self.get(dict(params), f"{what} unpaged", endpoint, report_type)
        raise AssertionError("unreachable")

    def _paged(self, params: dict, what: str, endpoint: str, report_type: str | None, verifiable: bool,
               limit: int) -> list[dict]:
        out: list[dict] = []
        offset, prev_sig = 0, None
        lens: list[int] = []
        for page_no in range(1, self.cfg.max_pages + 1):
            p = dict(params, limit=limit, offset=offset)
            try:
                page = self.get(p, f"{what} page {page_no}", endpoint, report_type)
            except RequestRejected as e:
                if page_no == 1:
                    raise _FirstPageRejected(e.status) from None
                # "Full" = the requested limit, OR as long as the longest earlier page (the server may
                # silently cap pages below our limit; a cap-sized page is not a last page).
                prev_full = lens[-1] >= limit or (len(lens) > 1 and lens[-1] >= max(lens[:-1]))
                if prev_full and not verifiable:
                    raise TransientAPIError(f"{what}: page {page_no} rejected (HTTP {e.status}) right after a FULL "
                                            f"page; refusing a possibly truncated result (this report has no "
                                            f"completeness check). The next run retries.") from None
                LOG.warning("%s: page %d rejected (HTTP %s) after %d rows (last page %s) - treating as end of "
                            "data%s", what, page_no, e.status, len(out), "full" if prev_full else "short",
                            "; reconciliation will verify" if verifiable else "")
                return out
            if not page:
                return out
            sig = hashlib.sha256(json.dumps(page, sort_keys=True, default=str).encode()).hexdigest()
            if sig == prev_sig:
                if not verifiable and len(page) >= limit:
                    raise DataError(f"{what}: page {page_no} is identical to the previous FULL page (API ignores "
                                    f"offset?); refusing a possibly truncated result")
                LOG.warning("%s: page %d identical to the previous page (API ignores offset?) - stopping", what, page_no)
                return out
            prev_sig = sig
            lens.append(len(page))
            out.extend(page)
            offset += len(page)
            if self.cfg.request_pause:
                time.sleep(self.cfg.request_pause)
        raise DataError(f"{what}: more than {self.cfg.max_pages} pages; refusing (raise PAGE_LIMIT/MAX_PAGES)")


# =============================================================================
# Campaign Management API client (separate key; read-only GETs)
# AppLovin blocks an account for 24h after 100 error responses in 5 minutes, so this client
# never retries 4xx and gives up after a handful of errors.
# =============================================================================
class MgmtAPI:
    MAX_ERRORS = 5
    ATTEMPTS = 3
    PAGE_SIZE = 100            # documented maximum; pages start at 1; the end is an EMPTY array

    def __init__(self, cfg: Config, deadline: float | None = None):
        self.cfg = cfg
        self.session = requests.Session()
        self.session.headers.update({"Authorization": cfg.mgmt_key or "", "Accept": "application/json",
                                     "User-Agent": f"terafort-applovin-ads-loader/{VERSION}"})
        self.errors = 0
        self.calls = 0
        self.deadline = deadline if deadline is not None else time.monotonic() + cfg.run_budget_sec

    def _get(self, path: str, params: dict, what: str):
        q = dict(params, account_id=self.cfg.account_id)
        url = f"{self.cfg.mgmt_base}/{path.lstrip('/')}"
        last = "no attempt"
        for attempt in range(1, self.ATTEMPTS + 1):
            if self.errors >= self.MAX_ERRORS:
                raise TransientAPIError(f"{what}: stopped after {self.errors} error responses "
                                        f"(AppLovin blocks accounts at 100 errors / 5 min)")
            remaining = self.deadline - time.monotonic()
            if remaining <= 5:
                raise TransientAPIError(f"{what}: run time budget ({self.cfg.run_budget_sec}s) exhausted - last: {last}")
            self.calls += 1
            try:
                resp = self.session.get(url, params=q, timeout=(15, max(5, min(120, int(remaining)))))
            except requests.RequestException as e:
                self.errors += 1
                last = f"{type(e).__name__}: {safe_exc(e)[:200]}"
            else:
                if resp.status_code == 200:
                    try:
                        return resp.json()
                    except ValueError:
                        self.errors += 1
                        last = "non-JSON body"
                else:
                    self.errors += 1
                    code = resp.headers.get("x-al-error-code", "")
                    msg = REDACT(resp.headers.get("x-al-error-message", "") or resp.text)[:300]
                    if resp.status_code in (401, 403):
                        raise AuthError(f"{what}: Campaign Management API rejected the key (HTTP {resp.status_code} "
                                        f"{code}). APPLOVIN_ADS_MGMT_KEY must be the *Campaign Management* key and "
                                        f"APPLOVIN_ADS_ACCOUNT_ID the numeric account id. {msg}")
                    if resp.status_code == 429:
                        raise TransientAPIError(f"{what}: rate limited (HTTP 429 {code}); not retrying to avoid a "
                                                f"24h block. {msg}")
                    if resp.status_code < 500:
                        raise RequestRejected(resp.status_code, f"{code} {msg}")
                    last = f"HTTP {resp.status_code} {code}"
            if attempt < self.ATTEMPTS:
                time.sleep(min(30.0, self.cfg.backoff_base * (2 ** attempt),
                               max(0.0, self.deadline - time.monotonic())))
        raise TransientAPIError(f"{what}: gave up after {self.ATTEMPTS} attempts - last: {last}")

    def list_all(self, path: str, what: str, extra: dict | None = None) -> list:
        """page=1,2,... until an EMPTY array (as documented). An identical page means the API ignored
        'page': stop there instead of looping."""
        out, seen_sig = [], None
        for page in range(1, 1001):
            data = self._get(path, dict(extra or {}, page=page, size=self.PAGE_SIZE), f"{what} page {page}")
            if isinstance(data, dict):           # documented as a bare array; tolerate {"data": [...]}
                lists = [v for v in data.values() if isinstance(v, list)]
                if len(lists) != 1:
                    raise DataError(f"{what}: expected a JSON array, got an object with keys {sorted(data)[:10]}")
                data = lists[0]
            if not isinstance(data, list):
                raise DataError(f"{what}: expected a JSON array, got {type(data).__name__}")
            if not data:
                return out
            sig = hashlib.sha256(json.dumps(data, sort_keys=True, default=str).encode()).hexdigest()
            if sig == seen_sig:
                if len(data) >= self.PAGE_SIZE:
                    raise DataError(f"{what}: page {page} is identical to the previous FULL page (API ignores "
                                    f"'page'?); refusing a truncated snapshot")
                LOG.warning("%s: page %d identical to the previous short page - stopping", what, page)
                return out
            seen_sig = sig
            out.extend(x for x in data if isinstance(x, dict))
            if self.cfg.request_pause:
                time.sleep(min(self.cfg.request_pause, 1.0))
        raise DataError(f"{what}: more than 1000 pages")


# =============================================================================
# Fetch + normalize + aggregate
# =============================================================================
@dataclass
class Tot:
    cost: float = 0.0
    conversions: int = 0
    impressions: int = 0
    rows: int = 0


EMPTY_CHECK_MIN_COST = 50.0
EMPTY_CHECK_MIN_IMPRESSIONS = 10000


def check_response(rows: list[dict], requested: list[str], spec: ReportSpec, what: str,
                   strict_empty: bool = True) -> list[str]:
    """Returns requested OPTIONAL columns absent from every row. Raises DataError for a missing
    REQUIRED column or a required metric empty in every row despite activity; _DuplicateRows for
    identical-dimension rows (overlapping pages)."""
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
    cid, name = row.get(spec.campaign_id_col), row.get("campaign")
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


def row_key(r: dict, spec: ReportSpec) -> tuple:
    return (r["day"], r["campaign_key"]) + tuple(r.get(g) for g in spec.grain_dims)


def _add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return a + b


def aggregate(rows: list[dict], spec: ReportSpec) -> tuple[dict, int, int]:
    """One row per key (day, campaign_key, *grain_dims). Sums additive metrics, conversion-weighted
    mean for rates, attributes from the bigger-spend row."""
    out: dict = {}
    merged = conflicts = 0
    for r in rows:
        k = row_key(r, spec)
        a = out.get(k)
        if a is None:
            out[k] = dict(r)
            continue
        merged += 1
        if any(r.get(d) and a.get(d) and r.get(d) != a.get(d) for d in spec.attr_dims):
            conflicts += 1
        if (r.get("cost") or 0) > (a.get("cost") or 0):
            for d in spec.attr_dims:
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


def reconcile(det: Tot, tot: Tot, metrics, *, settled: bool, cfg: Config, mode: str = "strict") -> list[str]:
    """Metrics that do NOT reconcile. Totals are always fetched BEFORE detail, so detail can only
    legitimately be >= totals on still-moving days.
      strict: settled |detail - total| <= rounding (+RECONCILE_PCT), counts exact; recent may grow.
      upper : detail may never EXCEED the total (+rounding, +growth on recent days); lower is free
              (breakdowns can legitimately miss iOS/SKAN or thresholded rows)."""
    bad = []
    for m in metrics:
        a, b = getattr(det, m), getattr(tot, m)
        rnd = (0.01 + 0.015 * math.sqrt(max(det.rows, 1))) if m == "cost" else 0.0
        rel = cfg.reconcile_pct / 100.0 * abs(b)
        lo_ok = (b - rnd - rel) if mode == "strict" else -math.inf
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
        self.known_dropped: dict = {}      # report -> columns already dropped by a run in the last 72h

    def _params(self, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date) -> dict:
        p = {"start": iso(lo), "end": iso(hi), "columns": ",".join(cols)}
        if spec.day_column:
            p["day_column"] = spec.day_column
        return p

    def _get(self, spec, params, what, paged: bool, verifiable: bool = True):
        if paged:
            return self.api.get_paged(params, what, spec.endpoint, spec.report_type, verifiable=verifiable)
        return self.api.get(params, what, spec.endpoint, spec.report_type)

    def _drop(self, spec: ReportSpec, cols: list[str], why: str) -> None:
        cur = self.run.dropped.setdefault(spec.name, [])
        new = [c for c in cols if c not in cur]
        if not new:
            return
        cur.extend(new)
        msg = (f"{spec.name}: optional column(s) {new} {why}; loading without them "
               f"(existing values in BigQuery are kept, never overwritten with NULL)")
        if set(new) <= set(self.known_dropped.get(spec.name, ())):
            LOG.info("%s [same as recent runs: not a new warning]", REDACT(msg))   # still in load_log + summary
        else:
            self.run.warn(msg)

    def resolve_columns(self, spec: ReportSpec, probe_day: dt.date) -> tuple[list[str], list[dict]]:
        """Validate columns on a 1-day request. Optional groups the API rejects or omits are dropped."""
        want = spec.all_columns
        what = f"{spec.name} column check ({probe_day})"
        try:
            rows = self._get(spec, self._params(spec, want, probe_day, probe_day), what, paged=False)
            try:
                missing = check_response(rows, want, spec, what)
            except _DuplicateRows:
                missing = []
            if missing:
                self._drop(spec, missing, "absent from the API response")
                want = [c for c in want if c not in missing]
            return want, rows
        except RequestRejected as e:
            first_err = e
        LOG.warning("%s: full column set rejected (%s); testing groups one by one", what, first_err.body[:160])
        req = list(spec.required)
        try:
            rows = self._get(spec, self._params(spec, req, probe_day, probe_day), what + " [required only]", paged=False)
        except RequestRejected as e2:
            raise ConfigError(f"{spec.name}: AppLovin rejected even the REQUIRED columns {req}: {e2}") from None
        keep = list(req)
        for gname, gcols in spec.optional_groups.items():
            try:
                self._get(spec, self._params(spec, req + gcols, probe_day, probe_day), f"{what} [+{gname}]", paged=False)
                keep += gcols
            except RequestRejected as e3:
                self._drop(spec, gcols, f"rejected by the API (HTTP {e3.status})")
        if keep != req:
            rows = self._get(spec, self._params(spec, keep, probe_day, probe_day), what + " [resolved]", paged=False)
        return keep, rows

    def totals(self, spec: ReportSpec, lo: dt.date, hi: dt.date) -> dict:
        cols = ["day"] + list(spec.reconcile_metrics)
        what = f"{spec.name} totals {lo}..{hi}"
        for attempt in (1, 2):
            rows = self._get(spec, self._params(spec, cols, lo, hi), what, paged=True)
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
            if "conversions" in spec.reconcile_metrics:
                t.conversions += parse_number(r.get("conversions"), integer=True, column="conversions", empty_as=0)
            if "impressions" in spec.reconcile_metrics:
                t.impressions += parse_number(r.get("impressions"), integer=True, column="impressions", empty_as=0)
            t.rows += 1
        return dict(out)

    def _fetch(self, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date) -> list[dict]:
        what = f"{spec.name} {lo}..{hi}"
        # Only strict reconciliation proves a detail fetch complete; 'upper' (rows may be below the day
        # total) and 'none' cannot, so for those every ambiguous paging end must refuse instead of guess.
        raw = self._get(spec, self._params(spec, cols, lo, hi), what, paged=True,
                        verifiable=spec.reconcile == "strict")
        if spec.per_day:                     # asset API: no 'day' column -> the requested day
            for r in raw:
                r["day"] = iso(lo)
        missing = check_response(raw, cols, spec, what, strict_empty=lo < self.recent_cut)
        if missing:
            self._drop(spec, missing, "absent from the API response")
        return [normalize_row(r, spec, cols, lo, hi, self.cfg.run_id, self.ingested_at, what) for r in raw]

    def detail(self, spec: ReportSpec, cols: list[str], lo: dt.date, hi: dt.date) -> list[dict]:
        rows: list[dict] = []
        size = 1 if spec.per_day else self.cfg.chunk_days
        for c_lo, c_hi in chunk_ranges(lo, hi, size):
            try:
                part = self._fetch(spec, cols, c_lo, c_hi)
            except _DuplicateRows:
                LOG.warning("%s %s..%s: duplicate rows (overlapping pages) - re-fetching day by day", spec.name, c_lo, c_hi)
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
        from google.cloud import bigquery  # lazily: probe mode needs no GCP
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
        else:
            self.client = bigquery.Client(project=cfg.project, location=cfg.location)
        self.ds = f"{cfg.project}.{cfg.dataset}"

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
                    t.clustering_fields = list(td.clustering)[:4]
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
    def existing_by_day(self, spec: ReportSpec, lo: dt.date, hi: dt.date) -> dict:
        if not self.table_exists(spec.table):
            return {}
        P = self.bq.ScalarQueryParameter
        conv = "SUM(IFNULL(conversions, 0))" if "conversions" in spec.metrics else "0"
        rows = self.query(
            f"SELECT day, SUM(IFNULL(cost, 0)) AS cost, {conv} AS conversions, "
            f"MAX(_ingested_at) AS last_ingested FROM `{self.fq(spec.table)}` "
            f"WHERE day BETWEEN @lo AND @hi GROUP BY day",
            [P("lo", "DATE", lo), P("hi", "DATE", hi)], what=f"read {spec.table}")
        return {r["day"]: Existing(float(r["cost"] or 0), int(r["conversions"] or 0), r["last_ingested"]) for r in rows}

    def _log_time(self, extra: str) -> dt.datetime | None:
        if not self.table_exists("load_log"):
            return None
        rows = self.query(f"SELECT {extra} AS t FROM `{self.fq('load_log')}` WHERE mode = 'load' "
                          f"AND status IN ('ok', 'ok_with_warnings', 'ok_empty', 'partial')", what="read load_log")
        return rows[0]["t"] if rows else None

    def first_success_at(self, report: str | None = None) -> dt.datetime | None:
        """First successful load run (report=None) or first successful run that ATTEMPTED `report`."""
        if report is None:
            return self._log_time("MIN(run_at)")
        if not re.fullmatch(r"[a-z_]+", report):
            raise ValueError(report)
        return self._log_time(f"MIN(IF(JSON_VALUE(report_stats, '$.{report}.attempted') = 'true', run_at, NULL))")

    def last_success_at(self, report: str | None = None) -> dt.datetime | None:
        if report is None:
            return self._log_time("MAX(run_at)")
        if not re.fullmatch(r"[a-z_]+", report):
            raise ValueError(report)
        legacy = " OR cohort_days_replaced > 0" if report == "cohort" else ""
        return self._log_time(f"MAX(IF(JSON_VALUE(report_stats, '$.{report}.ok') = 'true'{legacy}, run_at, NULL))")

    def last_loaded_with_rows_at(self, report: str) -> dt.datetime | None:
        """Last successful run in which `report` actually returned rows (proof the endpoint really works)."""
        if not re.fullmatch(r"[a-z_]+", report):
            raise ValueError(report)
        return self._log_time(f"MAX(IF(JSON_VALUE(report_stats, '$.{report}.ok') = 'true' AND "
                              f"SAFE_CAST(JSON_VALUE(report_stats, '$.{report}.api_rows') AS INT64) > 0, run_at, NULL))")

    def recent_history(self, hours: int = 72) -> tuple[dict, set]:
        """(report -> optional columns dropped, reports 'not available') in load runs of the last N hours.
        Used only to avoid repeating the SAME warning every run; a new problem still warns."""
        if not self.table_exists("load_log"):
            return {}, set()
        rows = self.query(f"SELECT dropped_columns, report_stats FROM `{self.fq('load_log')}` WHERE mode = 'load' "
                          f"AND run_at >= TIMESTAMP_SUB(CURRENT_TIMESTAMP(), INTERVAL {int(hours)} HOUR)",
                          what="read load_log history")
        dropped: dict = defaultdict(set)
        unavailable: set = set()
        for r in rows:
            try:
                d = json.loads(r["dropped_columns"] or "{}")
            except (TypeError, ValueError):
                d = {}
            for k, v in (d.items() if isinstance(d, dict) else []):
                if isinstance(v, list):
                    dropped[str(k)].update(str(c) for c in v)
            try:
                s = json.loads(r["report_stats"] or "{}")
            except (TypeError, ValueError):
                s = {}
            for k, v in (s.items() if isinstance(s, dict) else []):
                if isinstance(v, dict) and str(v.get("skipped") or "").startswith("not available"):
                    unavailable.add(str(k))
        return dict(dropped), unavailable

    # ---- writes ---------------------------------------------------------------
    def _replace(self, table: str, fields: list, days: list, rows: list[dict], key_cols: list, preserve: list) -> int:
        """Atomic: stage rows -> keep old values of preserve cols -> ONE transaction DELETE days + INSERT -> verify."""
        if not days:
            return 0
        names = [f.name for f in fields]
        preserve = [c for c in preserve if c in names and c not in key_cols]
        target = self.fq(table)
        tag = re.sub(r"[^A-Za-z0-9_]", "_", self.cfg.run_id) + "_" + uuid.uuid4().hex[:6]
        stg = self.fq(f"zz_stg_{table}_{tag}")
        day_list = "[" + ", ".join(f"DATE '{iso(d)}'" for d in sorted(days)) + "]"
        stg_created = False
        try:
            if rows:
                t = self.bq.Table(stg, schema=self._schema(fields))
                t.expires = utc_now() + dt.timedelta(hours=6)
                self.client.create_table(t)
                stg_created = True
                payload = [{n: (r.get(n).isoformat() if isinstance(r.get(n), dt.date) else r.get(n)) for n in names}
                           for r in rows]
                job_cfg = self.bq.LoadJobConfig(schema=self._schema(fields),
                                                write_disposition=self.bq.WriteDisposition.WRITE_TRUNCATE)
                self._retry(lambda: self.client.load_table_from_json(payload, stg, job_config=job_cfg).result(),
                            f"stage {table}")
                staged = self.query(f"SELECT COUNT(*) AS n FROM `{stg}`", what=f"count staged {table}")
                if int(staged[0]["n"]) != len(rows):
                    raise DataError(f"{table}: staged {staged[0]['n']} rows, expected {len(rows)}; nothing written")
                if preserve and self.table_exists(table):
                    sets = ", ".join(f"`{c}` = COALESCE(s.`{c}`, t.`{c}`)" for c in preserve)
                    on = " AND ".join(f"t.`{k}` IS NOT DISTINCT FROM s.`{k}`" for k in key_cols)
                    self.query(f"UPDATE `{stg}` s SET {sets} FROM `{target}` t WHERE t.day IN UNNEST({day_list}) AND {on}",
                               what=f"preserve optional columns {table}")
            col_list = ", ".join(f"`{n}`" for n in names)
            insert = f"INSERT INTO `{target}` ({col_list})\nSELECT {col_list} FROM `{stg}`;\n" if rows else ""
            sql = ("BEGIN TRANSACTION;\n"
                   f"DELETE FROM `{target}` WHERE day IN UNNEST({day_list});\n"
                   f"{insert}"
                   "COMMIT TRANSACTION;")
            try:
                self.query(sql, what=f"replace {table}")
            except Exception as e:  # noqa: BLE001
                raise CommitStateUnknown(
                    f"{table}: the replace transaction failed or its outcome is unknown ({public_exc(e)}). "
                    f"BigQuery rolls back failed transactions, but verify days {sorted(iso(d) for d in days)[:3]}... "
                    f"before trusting them") from e
            try:
                check = self.query(f"SELECT COUNT(*) AS n FROM `{target}` WHERE day IN UNNEST({day_list})",
                                   what=f"verify {table}")
            except Exception as e:  # noqa: BLE001
                raise PostWriteCheckError(f"{table}: COMMITTED, but the post-write check could not run ({public_exc(e)})") from e
            n = int(check[0]["n"]) if check else -1
            if n != len(rows):
                raise PostWriteCheckError(f"{table}: COMMITTED, but the post-write check found {n} rows "
                                          f"for the replaced days, expected {len(rows)}")
            return len(rows)
        finally:
            if stg_created:
                try:
                    self.client.delete_table(stg, not_found_ok=True)
                except Exception as e:  # noqa: BLE001
                    LOG.warning("could not drop staging table (%s); it expires in 6h", type(e).__name__)

    def replace_days(self, spec: ReportSpec, days: list, rows: list[dict], preserve: list | None = None) -> int:
        return self._replace(spec.table, spec.schema(), days, rows, spec.key_cols, preserve or [])

    def replace_snapshot(self, td: TableDef, day: dt.date, rows: list[dict]) -> int:
        return self._replace(td.name, td.schema, [day], rows, list(td.key_cols), [])

    def insert_new(self, td: TableDef, rows: list[dict]) -> int:
        """Append rows whose key is not in the table yet (MERGE ... WHEN NOT MATCHED). Idempotent."""
        if not rows:
            return 0
        names = [f.name for f in td.schema]
        key = td.key_cols[0]
        stg = self.fq(f"zz_stg_{td.name}_{re.sub(r'[^A-Za-z0-9_]', '_', self.cfg.run_id)}_{uuid.uuid4().hex[:6]}")
        t = self.bq.Table(stg, schema=self._schema(td.schema))
        t.expires = utc_now() + dt.timedelta(hours=6)
        self.client.create_table(t)
        try:
            payload = [{n: r.get(n) for n in names} for r in rows]
            job_cfg = self.bq.LoadJobConfig(schema=self._schema(td.schema),
                                            write_disposition=self.bq.WriteDisposition.WRITE_TRUNCATE)
            self._retry(lambda: self.client.load_table_from_json(payload, stg, job_config=job_cfg).result(),
                        f"stage {td.name}")
            cols = ", ".join(f"`{n}`" for n in names)
            src = ", ".join(f"s.`{n}`" for n in names)
            before = self.query(f"SELECT COUNT(*) AS n FROM `{self.fq(td.name)}`", what=f"count {td.name}")
            self.query(f"MERGE `{self.fq(td.name)}` t USING (SELECT * FROM `{stg}` WHERE `{key}` IS NOT NULL "
                       f"QUALIFY ROW_NUMBER() OVER (PARTITION BY `{key}` ORDER BY `{key}`) = 1) s "
                       f"ON t.`{key}` = s.`{key}` "
                       f"WHEN NOT MATCHED THEN INSERT ({cols}) VALUES ({src})", what=f"merge {td.name}")
            after = self.query(f"SELECT COUNT(*) AS n FROM `{self.fq(td.name)}`", what=f"count {td.name}")
            return int(after[0]["n"]) - int(before[0]["n"])
        finally:
            try:
                self.client.delete_table(stg, not_found_ok=True)
            except Exception:  # noqa: BLE001
                pass

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
    """day -> reason, for days that must NOT be replaced (shrink any day; jump on settled days)."""
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
    res = run.results[spec.name]
    res.columns_used = cols
    if spec.lookback_cap is not None:
        lo = max(lo, today - dt.timedelta(days=spec.lookback_cap))
    window = days_between(lo, hi)
    recent_cut = today - dt.timedelta(days=cfg.recent_days)

    api_tot = fetcher.totals(spec, lo, hi) if spec.reconcile != "none" else {}
    rows = fetcher.detail(spec, cols, lo, hi)
    res.api_rows = len(rows)
    by_day: dict = defaultdict(list)
    for r in rows:
        by_day[r["day"]].append(r)

    # ---- 1. reconciliation ------------------------------------------------------
    verdict: dict = {d: "ok" for d in window}
    if spec.reconcile != "none":
        retry_days = []
        for d in window:
            bad = reconcile(totals_by_day(by_day.get(d, [])).get(d, Tot()), api_tot.get(d, Tot()),
                            spec.reconcile_metrics, settled=d < recent_cut, cfg=cfg, mode=spec.reconcile)
            if bad:
                retry_days.append(d)
                verdict[d] = "retry"
                LOG.warning("%s %s: does not reconcile (%s) - re-fetching this day alone", spec.name, d, ", ".join(bad))
        if len(retry_days) > cfg.max_retry_days:
            for d in retry_days:
                verdict[d] = "mismatch"
            run.error(f"{spec.name}: {len(retry_days)} days do not reconcile (systemic: truncated/overlapping pages "
                      f"or an API change?). They were NOT written. Try CHUNK_DAYS=1.")
        else:
            for d in retry_days:
                tot_d = fetcher.totals(spec, d, d)
                rows_d = fetcher.detail(spec, cols, d, d)
                bad = reconcile(totals_by_day(rows_d).get(d, Tot()), tot_d.get(d, Tot()),
                                spec.reconcile_metrics, settled=d < recent_cut, cfg=cfg, mode=spec.reconcile)
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
        res.api_cost_total = round(sum(t.cost for t in api_tot.values()), 6)
        res.api_conversions_total = sum(t.conversions for t in api_tot.values())
        if spec.reconcile == "upper":
            settled = [d for d in window if d < recent_cut and verdict[d] == "ok"]
            tc = sum(api_tot.get(d, Tot()).cost for d in settled)
            dc = sum(totals_by_day(by_day.get(d, [])).get(d, Tot()).cost for d in settled)
            res.coverage_pct = round(dc / tc * 100, 2) if tc > 0 else None
    res.days_unverified = sorted(d for d in window if verdict[d] == "mismatch")
    res.days_recent_skipped = sorted(d for d in window if verdict[d] == "recent_skip")

    # ---- 2. aggregate to grain --------------------------------------------------
    writable = [d for d in window if verdict[d] == "ok"]
    agg, merged, conflicts = aggregate([r for d in writable for r in by_day.get(d, [])], spec)
    if merged:
        LOG.info("%s: merged %d same-key row(s) (%d with differing attributes)", spec.name, merged, conflicts)
    new: dict = defaultdict(lambda: (0.0, 0))
    for r in agg.values():
        c, n = new[r["day"]]
        new[r["day"]] = (c + (r.get("cost") or 0.0), n + (r.get("conversions") or 0))

    # ---- 3. drift guard ---------------------------------------------------------
    existing = wh.existing_by_day(spec, lo, hi) if wh is not None else {}
    blocked = drift_guard(writable, new, existing, today, cfg)
    if blocked:
        detail = {iso(d): why for d, why in sorted(blocked.items())}
        if cfg.force_replace:
            run.warn(f"{spec.name}: FORCE_REPLACE=true; replacing {len(blocked)} day(s) that changed sharply: {detail}")
            blocked = {}
        else:
            run.error(f"{spec.name}: {len(blocked)} day(s) NOT replaced; they changed more than "
                      f"{cfg.max_change_pct:.0f}% vs BigQuery: {detail}. Check the AppLovin Ads dashboard; if the "
                      f"change is real, re-run the workflow with force_replace=true.")
    res.days_protected = sorted(blocked)
    to_replace = sorted(set(writable) - set(blocked))
    keep = set(to_replace)
    out_rows = [r for r in agg.values() if r["day"] in keep]

    # ---- 4. write ---------------------------------------------------------------
    if cfg.mode == "load":
        try:
            res.rows_written = wh.replace_days(spec, to_replace, out_rows, preserve=spec.preserve_cols)
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


# ---- Campaign Management snapshots ---------------------------------------------------------------
def _js(v) -> str | None:
    return None if v is None else json.dumps(v, sort_keys=True, default=str)


def _num(v) -> float | None:
    try:
        x = float(v)
        return x if math.isfinite(x) else None
    except (TypeError, ValueError):
        return None


def _str(v) -> str | None:
    if v is None:
        return None
    if isinstance(v, (dict, list)):
        return _js(v)
    s = str(v).strip()
    return s or None


def snapshot_rows(kind: str, objs: list, day: dt.date, run_id: str, ingested_at: str) -> list[dict]:
    out, seen = [], set()
    for o in objs:
        oid = _str(o.get("id")) or _str(o.get("hashed_id")) or hashlib.sha256(_js(o).encode()).hexdigest()[:32]
        if oid in seen:
            continue
        seen.add(oid)
        base = {"day": day, "id": oid, "raw_json": _js(o), "_run_id": run_id, "_ingested_at": ingested_at}
        if kind == "campaign":
            budget, goal, tracking = (o.get("budget") or {}), (o.get("goal") or {}), (o.get("tracking") or {})
            budget = budget if isinstance(budget, dict) else {}
            goal = goal if isinstance(goal, dict) else {}
            tracking = tracking if isinstance(tracking, dict) else {}
            base.update(hashed_id=_str(o.get("hashed_id")), name=_str(o.get("name")), status=_str(o.get("status")),
                        type=_str(o.get("type")), platform=_str(o.get("platform")), package_name=_str(o.get("package_name")),
                        itunes_id=_str(o.get("itunes_id")), bidding_strategy=_str(o.get("bidding_strategy")),
                        start_date=_str(o.get("start_date")), end_date=_str(o.get("end_date")),
                        created_at=_str(o.get("created_at")),
                        daily_budget_usd=_num(budget.get("daily_budget_for_all_countries")),
                        country_budgets_json=_js(budget.get("country_code_to_daily_budget")),
                        goal_type=_str(goal.get("goal_type")), goal_value=_num(goal.get("goal_value_for_all_countries")),
                        country_goals_json=_js(goal.get("country_code_to_goal_value")),
                        roas_day_target=_str(goal.get("roas_day_target")), event_target=_str(goal.get("event_target")),
                        targeting_json=_js(o.get("targeting")), tracking_method=_str(tracking.get("tracking_method")),
                        is_continuous_delivery=_str(o.get("is_continuous_delivery")),
                        is_composite_banner_enabled=_str(o.get("is_composite_banner_enabled")))
        elif kind == "creative_set":
            assets = o.get("assets")
            base.update(hashed_id=_str(o.get("hashed_id")), campaign_id=_str(o.get("campaign_id")),
                        campaign_ids_json=_js(o.get("campaign_ids")), name=_str(o.get("name")),
                        type=_str(o.get("type")), status=_str(o.get("status")), version=_str(o.get("version")),
                        product_page=_str(o.get("product_page")), created_at=_str(o.get("created_at")),
                        languages_json=_js(o.get("languages")), countries_json=_js(o.get("countries")),
                        assets_json=_js(assets), asset_count=len(assets) if isinstance(assets, list) else None)
        elif kind == "asset":
            base.update(name=_str(o.get("name")), status=_str(o.get("status")), url=_str(o.get("url")),
                        asset_type=_str(o.get("asset_type") or o.get("type")), resource_type=_str(o.get("resource_type")),
                        asset_hash=_str(o.get("asset_hash")), upload_time=_str(o.get("upload_time")),
                        violation_reasons_json=_js(o.get("violation_reasons")))
        out.append(base)
    return out


def oplog_rows(entries: list, run_id: str, ingested_at: str) -> list[dict]:
    out, seen = [], set()
    for e in entries:
        raw = _js(e)
        op_id, cid = _str(e.get("operation_id")), _str(e.get("campaign_id"))
        key = f"op:{op_id}:{cid or '-'}" if op_id else "h:" + hashlib.sha256(raw.encode()).hexdigest()
        if key in seen:
            continue
        seen.add(key)
        out.append({"log_key": key, "operation_id": op_id, "operation_time": _str(e.get("operation_time")),
                    "operation_type": _str(e.get("operation_type")), "operator_name": _str(e.get("operator_name")),
                    "campaign_id": cid, "campaign_name": _str(e.get("campaign_name")),
                    "campaign_type": _str(e.get("campaign_type")), "detail_json": _js(e.get("detail")),
                    "raw_json": raw, "first_seen_at": ingested_at, "_run_id": run_id})
    return out


def run_mgmt(cfg: Config, run: RunState, wh, today: dt.date, deadline: float | None = None) -> None:
    res = run.results["mgmt"]
    if not cfg.mgmt_key or not cfg.account_id:
        res.skipped_reason = "no APPLOVIN_ADS_MGMT_KEY / APPLOVIN_ADS_ACCOUNT_ID"
        LOG.info("mgmt: skipped (%s)", res.skipped_reason)
        return
    res.attempted = True
    api = MgmtAPI(cfg, deadline)
    ingested = utc_now().replace(tzinfo=None).isoformat()
    campaigns = api.list_all("campaign/list", "mgmt campaigns")
    creative_sets = api.list_all("creative_set/list", "mgmt creative sets")
    assets = api.list_all("asset/list", "mgmt assets")
    snaps = {"campaign": snapshot_rows("campaign", campaigns, today, cfg.run_id, ingested),
             "creative_set": snapshot_rows("creative_set", creative_sets, today, cfg.run_id, ingested),
             "asset": snapshot_rows("asset", assets, today, cfg.run_id, ingested)}
    # Change history of ALL campaigns (no 'id' = every campaign), latest 30 UTC days incl. today.
    try:
        entries = api.list_all("operation_logs/campaign", "mgmt operation log",
                               {"start_date": iso(today - dt.timedelta(days=29)), "end_date": iso(today)})
    except RequestRejected as e:
        run.warn(f"mgmt: operation log request rejected (HTTP {e.status}); snapshots loaded, change history skipped")
        entries = []
    oplog = oplog_rows(entries, cfg.run_id, ingested)
    total = sum(len(v) for v in snaps.values())
    res.api_rows = total + len(oplog)
    LOG.info("mgmt: %d campaigns, %d creative sets, %d assets, %d operation-log entries",
             len(snaps["campaign"]), len(snaps["creative_set"]), len(snaps["asset"]), len(oplog))
    if cfg.mode == "load":
        for kind, rows in snaps.items():
            res.rows_written += wh.replace_snapshot(MGMT_TABLES[kind], today, rows)
        res.rows_written += wh.insert_new(MGMT_TABLES["oplog"], oplog)
        res.days_replaced = [today]
    res.ok = True


def run_probe(fetcher: Fetcher, cfg: Config, run: RunState, today: dt.date) -> None:
    safe_enums = {"platform", "campaign_type", "campaign_ad_type", "ad_creative_type", "placement_type", "size",
                  "ad_type", "device_type", "traffic_source", "bidding_and_billing_method"}
    core_ok = False
    for name in cfg.reports:
        if name == "mgmt":
            if not cfg.mgmt_key or not cfg.account_id:
                LOG.info("=== probe mgmt: skipped (no APPLOVIN_ADS_MGMT_KEY / APPLOVIN_ADS_ACCOUNT_ID) ===")
                continue
            try:
                data = MgmtAPI(cfg)._get("campaign/list", {"page": 1, "size": 5}, "mgmt probe")
                n = len(data) if isinstance(data, list) else "?"
                keys = sorted({k for o in (data if isinstance(data, list) else []) if isinstance(o, dict) for k in o})
                LOG.info("=== probe mgmt: OK, %s campaign(s) on page 1; fields: %s ===", n, ", ".join(keys) or "-")
            except (ConfigError, TransientAPIError, RequestRejected, DataError) as e:
                run.error(f"probe mgmt: {e}")
            continue
        spec = SPEC_BY_NAME[name]
        probe_day = today - dt.timedelta(days=spec.probe_lag)
        try:
            cols, rows = fetcher.resolve_columns(spec, probe_day)
        except AuthError as e:
            if spec.best_effort and core_ok:       # same key works for core -> this endpoint isn't enabled
                run.warn(f"probe {spec.name}: not available for this account - {e}")
                continue
            run.error(str(e))
            return
        except (ConfigError, DataError) as e:
            (run.warn if spec.best_effort else run.error)(f"probe {spec.name}: not available - {e}")
            continue
        core_ok = core_ok or spec.name == "core"
        LOG.info("=== probe %s (%s, %s): HTTP OK, %d rows, %d columns accepted ===",
                 spec.name, spec.endpoint, probe_day, len(rows), len(cols))
        if not rows:
            if spec.name == "core":
                run.warn(f"probe core: 0 rows for {probe_day}. Key accepted, but no data that day.")
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
            if spec.per_day:
                for r in rows:
                    r["day"] = iso(probe_day)
            check_response(rows, cols, spec, "probe")
            for r in rows:
                normalize_row(r, spec, cols, probe_day, probe_day, cfg.run_id, fetcher.ingested_at, "probe")
            LOG.info("  -> all %d rows pass the loader's strict checks", len(rows))
        except _DuplicateRows:
            run.warn(f"probe {spec.name}: duplicate rows in a single response (API paging?)")
        except DataError as e:
            (run.warn if spec.best_effort else run.error)(f"probe {spec.name}: {e}")


def write_summary(cfg: Config, run: RunState, duration: float, calls: int) -> None:
    path = _env("GITHUB_STEP_SUMMARY")
    icon = {"ok": "✅", "ok_with_warnings": "🟡", "ok_empty": "⚪", "partial": "🟠",
            "failed": "🔴", "transient_skip": "🟡"}.get(run.status, "❔")
    if run.errors and run.status in ("transient_skip", "ok", "ok_with_warnings", "ok_empty"):
        icon = "🔴"
    lines = [f"## {icon} AppLovin Ads -> BigQuery · `{run.status}`", "",
             f"- mode **{cfg.mode}** · loader v{VERSION} · run `{cfg.run_id}` · reports `{','.join(cfg.reports)}`"]
    if run.window:
        lines.append(f"- window **{run.window[0]} -> {run.window[1]}** (UTC) · API calls {calls} · {duration:.0f}s")
    if cfg.mode != "probe":
        lines += ["", "| report | table | API rows | days replaced | rows written | protected | unverified | recent kept | coverage |",
                  "|---|---|---:|---:|---:|---:|---:|---:|---:|"]
        for name in cfg.reports:
            r = run.results[name]
            table = SPEC_BY_NAME[name].table if name in SPEC_BY_NAME else "mgmt_*"
            if r.skipped_reason:
                lines.append(f"| {name} | {table} | - | - | - | - | - | - | skipped: {r.skipped_reason} |")
            else:
                cov = f"{r.coverage_pct:.1f}%" if r.coverage_pct is not None else "-"
                lines.append(f"| {name} | {table} | {r.api_rows} | {len(r.days_replaced)} | {r.rows_written} | "
                             f"{len(r.days_protected)} | {len(r.days_unverified)} | {len(r.days_recent_skipped)} | {cov} |")
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
    stats = {}
    for name in cfg.reports:
        r = run.results[name]
        stats[name] = {"ok": r.ok, "attempted": r.attempted, "skipped": r.skipped_reason, "api_rows": r.api_rows,
                       "rows_written": r.rows_written, "days_replaced": len(r.days_replaced),
                       "days_protected": [iso(d) for d in r.days_protected],
                       "days_unverified": [iso(d) for d in r.days_unverified],
                       "coverage_pct": r.coverage_pct, "api_cost_total": r.api_cost_total}
    return {
        "run_id": cfg.run_id, "loader_version": VERSION, "mode": cfg.mode, "status": run.status,
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
        "report_stats": json.dumps(stats, default=str)[:50000],
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
    if wh is None:
        run.warn(f"transient failure before BigQuery was reachable ({detail}); skipping, the next run retries")
        return 0
    try:
        age_h = _age_hours(wh.last_success_at())
    except Exception as e:  # noqa: BLE001
        run.warn(f"transient failure ({detail}); load_log unreadable too ({public_exc(e)}); skipping, the next run retries")
        return 0
    if age_h is not None and age_h <= cfg.stale_hours:
        run.warn(f"temporary failure; run skipped, nothing written. Last good load {age_h:.1f}h ago "
                 f"(limit {cfg.stale_hours}h); the next run retries. Detail: {detail}")
        return 0
    since = f"the last good load was {age_h:.1f}h ago" if age_h is not None else "no successful load is recorded yet"
    run.error(f"loader keeps failing transiently and {since} (limit {cfg.stale_hours}h). Detail: {detail}")
    return 1


def _secondary_failure(name: str, e: BaseException, cfg: Config, run: RunState, wh,
                       known_unavailable: frozenset | set = frozenset()) -> None:
    """A non-core report failed: transient -> warn unless that report is stale; best-effort endpoint
    not available for this account -> warn (info if it was already unavailable in the last 72h);
    anything else -> red."""
    res = run.results[name]
    spec = SPEC_BY_NAME.get(name)
    if isinstance(e, TransientAPIError) or is_transient_infra(e):
        res.skipped_reason = "transient error"
        age, never = None, False
        try:
            if cfg.mode == "load" and wh is not None:
                age = _age_hours(wh.last_success_at(name))
                if age is None:
                    # Never loaded. How long has it been FAILING to load?
                    never = True
                    if spec is not None and spec.critical:      # cohort: since the loader first succeeded
                        age = _age_hours(wh.first_success_at())
                    elif spec is not None and spec.best_effort:  # may simply not exist for this account
                        age = None
                    else:                                        # creative/supply/site/mgmt: since first attempted
                        age = _age_hours(wh.first_success_at(name))
        except Exception:  # noqa: BLE001
            age = None
        if cfg.mode == "load" and age is not None and age > cfg.stale_hours:
            since = (f"{name} has never loaded in the {age:.1f}h it has been expected" if never
                     else f"last {name} load {age:.1f}h ago")
            run.error(f"{name} keeps failing transiently; {since} (limit {cfg.stale_hours}h): {public_exc(e)}",
                      private=safe_exc(e))
        else:
            run.warn(f"{name} skipped this run (core already loaded): {public_exc(e)}")
    elif isinstance(e, PostWriteCheckError):
        run.error(f"{name}: {e}")
    elif (isinstance(e, ConfigError) and spec is not None and spec.best_effort
          and (not isinstance(e, AuthError) or run.core.ok)):     # key proven by core -> endpoint not enabled
        res.skipped_reason = "not available for this account"
        msg = f"{name} ({spec.endpoint}): not available for this account, skipped - {e}"
        prev = None
        try:
            if cfg.mode == "load" and wh is not None:
                prev = _age_hours(wh.last_loaded_with_rows_at(name))   # an empty 200 proves nothing
        except Exception:  # noqa: BLE001
            prev = None
        if prev is not None and prev > cfg.stale_hours:
            # It DID deliver rows before, so this is not "the account doesn't have it": AppLovin changed something.
            run.error(f"{name} loaded before but AppLovin now refuses it; last {name} load {prev:.1f}h ago "
                      f"(limit {cfg.stale_hours}h). Check the endpoint/columns, or drop '{name}' via the repo variable "
                      f"APPLOVIN_ADS_DAILY_REPORTS: "
                      f"{public_exc(e)}", private=safe_exc(e))
        elif prev is not None:
            run.warn(msg + f" (it loaded {prev:.1f}h ago; red after {cfg.stale_hours}h)")
        elif name in known_unavailable:
            LOG.info("%s [same as recent runs: not a new warning]", REDACT(msg))
        else:
            run.warn(msg)
    else:
        res.skipped_reason = type(e).__name__
        run.error(f"{name} failed (core already loaded): {public_exc(e)}", private=safe_exc(e))


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
    LOG.info("AppLovin Ads loader v%s · mode=%s · window %s..%s · reports=%s", VERSION, cfg.mode, lo, hi, ",".join(cfg.reports))
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
        known_unavailable: set = set()
        try:
            fetcher.known_dropped, known_unavailable = wh.recent_history()
        except Exception as e:  # noqa: BLE001 - only de-duplicates warnings; never blocks a load
            LOG.info("load_log history not readable (%s); every dropped column will warn", public_exc(e))

        if "core" in cfg.reports:
            run.core.attempted = True
            core_cols, _ = fetcher.resolve_columns(CORE, today - dt.timedelta(days=CORE.probe_lag))
            process_report(CORE, core_cols, fetcher, wh, cfg, run, lo, hi, today)
            run.core.ok = True
            if run.core.api_rows == 0 and not run.core.days_protected:
                run.warn(f"AppLovin Ads API returned 0 rows for {lo}..{hi} (campaigns paused?). If you expect spend, "
                         f"confirm APPLOVIN_ADS_REPORT_KEY is the Report Key of the AppLovin ADS account (not MAX).")

        for name in cfg.reports:
            if name == "core":
                continue
            errs_before = len(run.errors)
            try:
                if name == "mgmt":
                    run_mgmt(cfg, run, wh, today, api.deadline)
                    continue
                spec = SPEC_BY_NAME[name]
                run.results[name].attempted = True
                try:
                    cols, _ = fetcher.resolve_columns(spec, today - dt.timedelta(days=spec.probe_lag))
                except DataError as e:
                    if spec.best_effort:     # endpoint answers, but not in a shape we can load
                        raise ConfigError(f"unexpected response ({e})") from e
                    raise
                process_report(spec, cols, fetcher, wh, cfg, run, lo, hi, today)
                run.results[name].ok = len(run.errors) == errs_before
            except Exception as e:  # noqa: BLE001 - core is already safely loaded
                _secondary_failure(name, e, cfg, run, wh, known_unavailable)

        if run.errors:
            run.status = "partial" if run.any_replaced() else "failed"
        elif "core" in cfg.reports and run.core.api_rows == 0:
            run.status = "ok_empty"
        elif run.warnings:
            run.status = "ok_with_warnings"
        else:
            run.status = "ok"
        return 1 if run.errors else 0

    except TransientAPIError as e:
        return _transient_outcome(cfg, run, wh, str(e))
    except (ConfigError, DataError, RequestRejected) as e:
        run.status = "partial" if run.any_replaced() else "failed"
        run.error(f"{type(e).__name__}: {e}")
        return 1
    except Exception as e:  # noqa: BLE001
        if is_transient_infra(e) and not run.any_replaced():
            return _transient_outcome(cfg, run, wh, public_exc(e))
        run.status = "partial" if run.any_replaced() else "failed"
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
# DDL (generated from the same schema objects the loader uses)
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
        clus = f"\nCLUSTER BY {', '.join(list(td.clustering)[:4])}" if td.clustering else ""
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
    except BaseException as e:  # noqa: BLE001
        LOG.error("fatal %s\n%s", public_exc(e), safe_exc(traceback.format_exc()))
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
