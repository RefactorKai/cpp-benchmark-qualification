"""Offline benchmark expansion analyzer, fixture-readiness inventory builder,
and blind-author agreement calculator (stdlib-only, deterministic, receipt-bound).

Implements the benchmark expansion protocol (intake freeze 8a969245...) and Amendments 1--5:
- Primary confirmatory family {P1, P2, P3} with Holm alpha=0.05, exact two-sided
  binomial tests (vs fixed 147-pair references 14/147 and 4/13), exact whole-cluster
  sign-flip test, exact 95% Clopper-Pearson intervals, and whole-cluster percentile
  bootstrap (seed=42, 10,000 draws, nearest ranks 250 and 9,750).
- Explicit Amendment 4 handling of `indeterminate` (terminal S1 desk stop; stays in
  post-S0 denominators; counts as desk stop in P2/S1 and not reaching execution in
  P1/S9; never advances to S2; outside P3 fitted denominator; tracked separately
  from the 133 held `desk_unrateable` pairs).
- Explicit Amendment 5 (`17de6626...`) handling of `fixture_stop` (terminal post-S1
  stop before S3; stays in post-S0 denominators; counts as not executed in P1/S9,
  keeps desk_stop=0, executed=0 in P2; outside P3; reported as S14) and pre-closure
  `not_executed` pairs (truncated-prefix K < 183 frozen bounds + conditional yield).
- Secondary outcomes S1-S10, S12-S14 (S11 omitted under Amendment 2) and Section 11
  execution-policy sensitivity disclosures.
- Blind 50-case author check (descriptive item 3): exact & bucket agreement,
  Cohen's kappa, and cluster bootstrap 95% CI.
- Direct de-identified `--aggregate-json` ingestion (e.g., final-a5-stats-agg.json),
  JSON/JSONL `--ledger` parsing, and receipt-bound `benchmark_slots.tex` emission.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
import math
from math import comb, lcm
from pathlib import Path
import random
import statistics
from typing import Any

getcontext().prec = 60

MANIFEST_SHA = "5b432d827f324c073eb7ed14b4df4b5d18f5eb2a90c4d97d358405a800d27346"
PROTOCOL_SHA = "8a9692457cdba6d9b2860717b8bc254dae47dc48eebe7baacabb17a82007953e"
HELD_SHA = "6bc97deac805d67528e1939481c75745f51cf7350c0d3ee757598eb55c5dad01"
AMENDMENT_4_SHA = "0d070e99d12c7b872a2db023e056586921c5aadcef90abe376fcee5006328940"
AMENDMENT_5_SHA = "17de6626bb871cc30f80040bd63f123da8c0b4498231ff63b607045b36fdb469"
AUTHOR_DRAW_SHA = "70a52d37793ecadea5c927ce61b6f1d3b7c5174adc4ae342bf0f680dd775cc44"
ANON_MEASUREMENTS_SHA = "c2ba8209b5401ef79c69ee14b33e662064bbf33eca72fa5c1ce29a9be58ad230"
FORENSICS_AGG_SHA = "b8ea9b8c258566350502bb26f58faf751146b4d1d259d5f3f827bb0f00edffb8"

SEED = 42
DRAWS = 10_000
REF_R1 = Fraction(103, 147)
REF_P1 = Fraction(14, 147)
REF_P3 = Fraction(4, 13)
REF_R4 = Fraction(4, 147)
REF_R5 = Fraction(12, 26)
REF_R6 = Fraction(1, 14)
MIN_CONFIRMATORY_CLUSTERS = 200
MIN_FITTED_CLUSTERS = 30
MIN_FRAME_CLUSTERS = 30

S0_STOPS = frozenset({"intake_unretrievable", "intake_duplicate"})
S1_DESK_STOPS = frozenset({"desk_excluded", "desk_blocked", "desk_unrateable", "indeterminate"})
S3_EXECUTED = frozenset({"execution_oracle_failure", "insufficient_fit", "no_alert", "alert"})
S4_FITTED = frozenset({"no_alert", "alert"})
ALL_TERMINALS = (
    S0_STOPS
    | S1_DESK_STOPS
    | {"fixture_stop", "support_boundary_closed", "execution_infrastructure_failure", "not_executed"}
    | S3_EXECUTED
)

# Path B 147-pair executed PIE problem IDs stored as SHA-256 16-hex prefixes (zero raw problem IDs in code)
PATH_B_CASE_PY_HASHES = frozenset({"45a9bcfe247938f2", "4f23d3c314cf8991", "618d0ddc523d5e9e", "aa5157db847afc3a"})
PATH_B_HIST_EXEC_HASHES = frozenset({"03a272e6774b6f51", "4ddfcec8d2e011f1", "642a20fcd5e99ccd", "a9df78c69eb7737a", "c60745048fd1e046", "d2fee06853e67aa3"})
PATH_B_EXECUTED_PIE_HASHES = PATH_B_CASE_PY_HASHES | PATH_B_HIST_EXEC_HASHES

CAPS = ("tick_cap", "cpu_cap", "wall_timeout", "memory_cap", "tasks_cap", "file_cap")


def digest(raw: bytes) -> str:
    return sha256(raw).hexdigest()


def dump(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def pair_key(row: dict[str, Any]) -> str:
    return f'{row["corpus"]}:{row["id"]}'


def representative_rank(row: dict[str, Any]) -> tuple[str, str]:
    payload = dump(["eapg-expansion-v1", row["corpus"], row["cluster_id"], row["id"]]).encode("utf-8")
    return digest(payload), row["id"]


def holm(p_values: dict[str, float]) -> dict[str, float]:
    adjusted: dict[str, float] = {}
    running = 0.0
    ordered = sorted(p_values, key=p_values.__getitem__)
    for remaining, key in zip(range(len(ordered), 0, -1), ordered, strict=True):
        running = max(running, min(1.0, remaining * p_values[key]))
        adjusted[key] = running
    return adjusted


@lru_cache(maxsize=None)
def clopper_pearson(k: int, n: int) -> tuple[float, float]:
    if not 0 <= k <= n or n <= 0:
        raise ValueError(f"Invalid Clopper-Pearson input: {k}/{n}")

    log_n1 = math.lgamma(n + 1)

    def lower(successes: int) -> float:
        if successes == 0:
            return 0.0
        terms = [(i, log_n1 - math.lgamma(i + 1) - math.lgamma(n - i + 1)) for i in range(successes, n + 1)]
        lo, hi = 0.0, 1.0
        for _ in range(56):
            p = (lo + hi) / 2.0
            if p <= 0.0:
                tail = 0.0
            elif p >= 1.0:
                tail = 1.0
            else:
                lp = math.log(p)
                lq = math.log1p(-p)
                tail = math.fsum(math.exp(lg_c + i * lp + (n - i) * lq) for i, lg_c in terms)
            if tail < 0.025:
                lo = p
            else:
                hi = p
        return (lo + hi) / 2.0

    return lower(k), 1.0 - lower(n - k)


def rate_summary(k: int, n: int) -> dict[str, Any]:
    if n == 0:
        return {"count": 0, "total": 0, "percent": None, "clopper_pearson_95pct_percent": None}
    lo, hi = clopper_pearson(k, n)
    return {
        "count": k,
        "total": n,
        "percent": round(100.0 * k / n, 1),
        "clopper_pearson_95pct_percent": [round(100.0 * lo, 1), round(100.0 * hi, 1)],
        "half_width_pp": round(50.0 * (hi - lo), 1),
    }


def exact_binomial_two_sided_p(k: int, n: int, p0: Fraction) -> float:
    """Exact two-sided binomial p-value using 60-digit Decimal arithmetic."""
    if not 0 <= k <= n or n <= 0:
        raise ValueError(f"Invalid binomial input: {k}/{n}")
    p = Decimal(p0.numerator) / Decimal(p0.denominator)
    q = Decimal(1) - p

    def pmf(i: int) -> Decimal:
        return Decimal(comb(n, i)) * (p**i) * (q ** (n - i))

    obs = pmf(k)
    tol = obs * (Decimal(1) + Decimal("1e-12"))
    total = sum((pmf(i) for i in range(n + 1) if pmf(i) <= tol), Decimal(0))
    return float(min(Decimal(1), total))


def sign_flip_p(weights: list[int]) -> float:
    """Exact two-sided whole-cluster sign-flip p-value (zero-effect clusters fixed)."""
    nonzero = [w for w in weights if w != 0]
    observed = abs(sum(nonzero))
    if observed == 0:
        return 1.0
    totals: Counter[int] = Counter({0: 1})
    for w in nonzero:
        nxt: Counter[int] = Counter()
        for val, cnt in totals.items():
            nxt[val + w] += cnt
            nxt[val - w] += cnt
        totals = nxt
    extreme = sum(cnt for val, cnt in totals.items() if abs(val) >= observed)
    return extreme / totals.total()


def cluster_contrast_from_effects(effects: list[Fraction], pairs: int, pair_sum: int) -> dict[str, Any]:
    """Equal-cluster contrast from ordered cluster Fractions with exact sign-flip + seed-42 bootstrap."""
    n = len(effects)
    if n == 0:
        return {"clusters": 0, "pairs": 0, "group_weighted_delta_pp": None}
    total = sum(effects, Fraction(0))
    denom = lcm(*(e.denominator for e in effects))
    int_weights = [int(e * denom) for e in effects]

    rng = random.Random(SEED)
    samples = sorted(sum(rng.choices(int_weights, k=n)) for _ in range(DRAWS))
    ci_lo = Fraction(samples[249], n * denom)
    ci_hi = Fraction(samples[9749], n * denom)
    loo = [(total - e) / (n - 1) for e in effects] if n > 1 else []
    return {
        "clusters": n,
        "pairs": pairs,
        "pair_weighted_delta_pp": round(float(Fraction(pair_sum * 100, pairs)), 1),
        "group_weighted_delta_pp": round(float(total * 100 / n), 1),
        "bootstrap_95pct_delta_pp": [round(float(ci_lo * 100), 1), round(float(ci_hi * 100), 1)],
        "leave_one_cluster_out_range_pp": (
            [round(float(min(loo) * 100), 1), round(float(max(loo) * 100), 1)] if loo else None
        ),
        "cluster_sign_flip_p": sign_flip_p(int_weights),
        "nonzero_clusters": sum(1 for w in int_weights if w != 0),
        "bootstrap_seed": SEED,
        "bootstrap_draws": DRAWS,
    }


def cluster_contrast(groups_by_cluster: dict[str, list[int]]) -> dict[str, Any]:
    """Equal-cluster contrast with exact sign-flip test and seed-42 bootstrap."""
    ordered_keys = sorted(groups_by_cluster)
    ordered = [groups_by_cluster[k] for k in ordered_keys]
    if not ordered:
        return {"clusters": 0, "pairs": 0, "group_weighted_delta_pp": None}
    effects = [Fraction(sum(g), len(g)) for g in ordered]
    pairs = sum(len(g) for g in ordered)
    pair_sum = sum(sum(g) for g in ordered)
    return cluster_contrast_from_effects(effects, pairs, pair_sum)


def cluster_rate(groups_by_cluster: dict[str, list[int]]) -> dict[str, Any]:
    """Equal-cluster binary rate (%) with seed-42 whole-cluster percentile bootstrap."""
    ordered_keys = sorted(groups_by_cluster)
    ordered = [groups_by_cluster[k] for k in ordered_keys]
    n = len(ordered)
    if n == 0:
        return {
            "clusters": 0,
            "pairs": 0,
            "pair_weighted_pct": None,
            "equal_cluster_pct": None,
            "bootstrap_95pct_pct": None,
            "leave_one_cluster_out_range_pct": None,
        }
    effects = [Fraction(sum(g), len(g)) for g in ordered]
    total = sum(effects, Fraction(0))
    pairs = sum(len(g) for g in ordered)
    pair_sum = sum(sum(g) for g in ordered)
    denom = lcm(*(e.denominator for e in effects))
    int_weights = [int(e * denom) for e in effects]

    rng = random.Random(SEED)
    samples = sorted(sum(rng.choices(int_weights, k=n)) for _ in range(DRAWS))
    ci_lo = Fraction(samples[249], n * denom)
    ci_hi = Fraction(samples[9749], n * denom)
    loo = [(total - e) / (n - 1) for e in effects] if n > 1 else []
    return {
        "clusters": n,
        "pairs": pairs,
        "pair_weighted_pct": round(float(Fraction(pair_sum * 100, pairs)), 1),
        "equal_cluster_pct": round(float(total * 100 / n), 1),
        "bootstrap_95pct_pct": [round(float(ci_lo * 100), 1), round(float(ci_hi * 100), 1)],
        "leave_one_cluster_out_range_pct": (
            [round(float(min(loo) * 100), 1), round(float(max(loo) * 100), 1)] if loo else None
        ),
        "bootstrap_seed": SEED,
        "bootstrap_draws": DRAWS,
    }


def calculate_fit(points: list[tuple[int, int | float, int | float]]) -> dict[str, float | None] | None:
    """OLS fit of log(T/Q) on log(n); requires >= 4 distinct sizes spanning >= 8x."""
    return _ols_log_ratio_fit(points)


def select_representatives(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    by_cluster: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_cluster[row["cluster_id"]].append(row)
    return {cid: min(members, key=representative_rank) for cid, members in sorted(by_cluster.items())}


def flow_table(manifest_pairs: list[dict[str, Any]], dispositions: dict[str, str]) -> dict[str, dict[str, int]]:
    frames = ("Contest", "Repository", "Union")
    buckets = (
        "drawn",
        "s0_intake_stop",
        "s0_intake_duplicate",
        "s0_intake_unretrievable",
        "s1_desk_stop_total",
        "s1_desk_excluded",
        "s1_desk_blocked",
        "s1_desk_unrateable",
        "s1_indeterminate",
        "s2_fixture_stop",
        "s2_preprocessing_stop",
        "s3_infra_failure",
        "not_executed",
        "s3_oracle_failure",
        "s4_no_fit",
        "s5_no_alert",
        "s5_alert",
    )
    table = {f: {b: 0 for b in buckets} for f in frames}
    for row in manifest_pairs:
        key = pair_key(row)
        term = row.get("intake_stop") or dispositions.get(key)
        if term not in ALL_TERMINALS:
            raise ValueError(f"Missing or unknown terminal disposition for {key}: {term!r}")
        targets = (row["frame"], "Union")
        for f in targets:
            table[f]["drawn"] += 1
            if term in S0_STOPS:
                table[f]["s0_intake_stop"] += 1
                table[f][f"s0_{term}"] += 1
            elif term in S1_DESK_STOPS:
                table[f]["s1_desk_stop_total"] += 1
                table[f][f"s1_{term}"] += 1
            elif term == "fixture_stop":
                table[f]["s2_fixture_stop"] += 1
            elif term == "support_boundary_closed":
                table[f]["s2_preprocessing_stop"] += 1
            elif term == "execution_infrastructure_failure":
                table[f]["s3_infra_failure"] += 1
            elif term == "not_executed":
                table[f]["not_executed"] += 1
            elif term == "execution_oracle_failure":
                table[f]["s3_oracle_failure"] += 1
            elif term == "insufficient_fit":
                table[f]["s4_no_fit"] += 1
            elif term == "no_alert":
                table[f]["s5_no_alert"] += 1
            elif term == "alert":
                table[f]["s5_alert"] += 1
    return table


def _bucket_label(term: str, meta: dict[str, Any] | None) -> str:
    if term in ("desk_unrateable", "indeterminate"):
        return term
    b = (meta or {}).get("bucket")
    return str(b) if b in ("source", "contract", "route") else "unspecified"


def _uncapped_points(stream_pts: list[Any]) -> list[tuple[int, int | float, int | float]]:
    pts: list[tuple[int, int | float, int | float]] = []
    for p in stream_pts:
        if isinstance(p, dict):
            if p.get("capped") or p.get("target") is None or p.get("reference") is None:
                continue
            pts.append((p["size"], p["target"], p["reference"]))
        else:
            if p[1] is None or p[2] is None:
                continue
            pts.append((p[0], p[1], p[2]))
    pts.sort()
    return pts


def _extract_s7_s8_row(
    row: dict[str, Any] | None,
    disposition: str,
) -> tuple[bool | None, dict[str, Any] | None]:
    """Return (any_stream_alert, drop_largest_info) for a fitted pair when available."""
    if disposition not in S4_FITTED:
        return None, None
    if row is None:
        return (True if disposition == "alert" else None), None

    any_alert: bool | None = None
    if isinstance(row.get("any_stream_alert"), bool):
        any_alert = row["any_stream_alert"]
    elif isinstance(row.get("fits"), dict) and row["fits"]:
        fits = [
            f
            for f in row["fits"].values()
            if isinstance(f, dict) and "slope" in f and "largest_ratio" in f
        ]
        if fits and len(fits) == len(row["fits"]):
            any_alert = any(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in fits)
    elif isinstance(row.get("stream_screens"), list) and row["stream_screens"]:
        fits = [s.get("fit", s) for s in row["stream_screens"]]
        if all(isinstance(f, dict) and "slope" in f and "largest_ratio" in f for f in fits):
            any_alert = any(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in fits)
    elif disposition == "alert":
        any_alert = True

    drop_info: dict[str, Any] | None = None
    if isinstance(row.get("drop_largest"), dict) and "admitted" in row["drop_largest"]:
        dl = row["drop_largest"]
        drop_info = {
            "admitted": bool(dl["admitted"]),
            "all_stream_alert": bool(dl.get("all_stream_alert", False)) if dl["admitted"] else False,
            "any_stream_alert": bool(dl.get("any_stream_alert", False)) if dl["admitted"] else False,
        }
    else:
        drop_fits: list[dict[str, Any] | None] | None = None
        if isinstance(row.get("drop_largest"), dict) and row["drop_largest"]:
            drop_fits = list(row["drop_largest"].values())
        elif isinstance(row.get("stream_screens"), list) and row["stream_screens"]:
            cand: list[dict[str, Any] | None] = []
            ok = True
            for s in row["stream_screens"]:
                if "drop_largest" in s:
                    cand.append(s["drop_largest"])
                elif isinstance(s.get("points"), list):
                    cand.append(calculate_fit(_uncapped_points(s["points"])[:-1]))
                else:
                    ok = False
                    break
            if ok:
                drop_fits = cand
        elif isinstance(row.get("points"), dict) and row["points"]:
            drop_fits = [
                calculate_fit(_uncapped_points(stream_pts)[:-1])
                for stream_pts in row["points"].values()
            ]
        elif isinstance(row.get("fits"), dict) and row["fits"]:
            fits = list(row["fits"].values())
            if all(isinstance(f, dict) and ("drop_largest" in f or "points" in f) for f in fits):
                drop_fits = []
                for f in fits:
                    if "drop_largest" in f:
                        drop_fits.append(f["drop_largest"])
                    else:
                        drop_fits.append(calculate_fit(_uncapped_points(f["points"])[:-1]))

        if drop_fits is not None and len(drop_fits) > 0:
            admitted = all(d is not None for d in drop_fits)
            if admitted:
                drop_all = all(d["slope"] >= 0.50 and d["largest_ratio"] >= 1.50 for d in drop_fits if d is not None)
                drop_any = any(d["slope"] >= 0.50 and d["largest_ratio"] >= 1.50 for d in drop_fits if d is not None)
            else:
                drop_all = False
                drop_any = False
            drop_info = {
                "admitted": admitted,
                "all_stream_alert": drop_all,
                "any_stream_alert": drop_any,
            }

    return any_alert, drop_info


def _build_s12_summary(
    quar: list[dict[str, Any]],
    dispositions: dict[str, str],
    desk_meta: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    quar_reps = select_representatives(quar)
    quar_rep_list = list(quar_reps.values())
    quar_counts = Counter(dispositions[pair_key(r)] for r in quar)
    quar_rep_counts = Counter(dispositions[pair_key(r)] for r in quar_rep_list)

    def _subset_rates(rows: list[dict[str, Any]]) -> dict[str, Any]:
        n = len(rows)
        desk_rows = [r for r in rows if dispositions[pair_key(r)] in S1_DESK_STOPS]
        post_desk = [r for r in rows if dispositions[pair_key(r)] not in S1_DESK_STOPS]
        exec_rows = [r for r in rows if dispositions[pair_key(r)] in S3_EXECUTED]
        fit_rows = [r for r in rows if dispositions[pair_key(r)] in S4_FITTED]
        alert_rows = [r for r in rows if dispositions[pair_key(r)] == "alert"]
        fix_rows = [r for r in post_desk if dispositions[pair_key(r)] == "fixture_stop"]
        unrun_rows = [r for r in post_desk if dispositions[pair_key(r)] == "not_executed"]
        buckets = Counter(_bucket_label(dispositions[pair_key(r)], desk_meta.get(pair_key(r))) for r in desk_rows)
        return {
            "S1_desk_stop": {**rate_summary(len(desk_rows), n), "bucket_counts": dict(sorted(buckets.items()))},
            "P1_exec_yield": rate_summary(len(exec_rows), n),
            "P3_alerts_per_fitted": rate_summary(len(alert_rows), len(fit_rows)),
            "S2_alerts_per_selected": rate_summary(len(alert_rows), n),
            "S14_fixture_stops_after_s1_pass": rate_summary(len(fix_rows), len(post_desk)),
            "not_executed_after_s1_pass": rate_summary(len(unrun_rows), len(post_desk)),
        }

    q_desk_groups: dict[str, list[int]] = defaultdict(list)
    q_exec_groups: dict[str, list[int]] = defaultdict(list)
    q_fit_groups: dict[str, list[int]] = defaultdict(list)
    q_alert_groups: dict[str, list[int]] = defaultdict(list)
    for r in quar:
        t = dispositions[pair_key(r)]
        cid = r["cluster_id"]
        q_desk_groups[cid].append(int(t in S1_DESK_STOPS))
        q_exec_groups[cid].append(int(t in S3_EXECUTED))
        q_alert_groups[cid].append(int(t == "alert"))
        if t in S4_FITTED:
            q_fit_groups[cid].append(int(t == "alert"))

    pair_rates = _subset_rates(quar)
    pair_rates["S1_desk_stop"]["equal_cluster"] = cluster_rate(q_desk_groups)
    pair_rates["P1_exec_yield"]["equal_cluster"] = cluster_rate(q_exec_groups)
    pair_rates["P3_alerts_per_fitted"]["equal_cluster"] = cluster_rate(q_fit_groups)
    pair_rates["S2_alerts_per_selected"]["equal_cluster"] = cluster_rate(q_alert_groups)

    return {
        "pairs_past_s0": len(quar),
        "clusters_past_s0": len(quar_reps),
        "pair_dispositions": dict(sorted(quar_counts.items())),
        "rep_dispositions": dict(sorted(quar_rep_counts.items())),
        "cluster_rates": _subset_rates(quar_rep_list),
        "pair_rates": pair_rates,
    }


def _s14_summary(
    s14_fix_k: int,
    post_desk_n: int,
    unrun_n: int,
    bucket_counts_reps: dict[str, int] | None = None,
    reason_counts_reps: dict[str, int] | None = None,
    bucket_counts_pairs: dict[str, int] | None = None,
    reason_counts_pairs: dict[str, int] | None = None,
) -> dict[str, Any]:
    attempted = post_desk_n - unrun_n
    bounds = (
        [
            round(100.0 * s14_fix_k / post_desk_n, 1),
            round(100.0 * (s14_fix_k + unrun_n) / post_desk_n, 1),
        ]
        if post_desk_n > 0
        else None
    )
    out: dict[str, Any] = {
        **rate_summary(s14_fix_k, post_desk_n),
        "truncated": unrun_n > 0,
        "attempted_count": attempted,
        "not_executed_count": unrun_n,
        "prefix_conditional": rate_summary(s14_fix_k, attempted),
        "frozen_bounds_pct": bounds,
    }
    if bucket_counts_reps is not None:
        out["bucket_counts_reps"] = bucket_counts_reps
    if reason_counts_reps is not None:
        out["reason_counts_reps"] = reason_counts_reps
    if bucket_counts_pairs is not None:
        out["bucket_counts_pairs"] = bucket_counts_pairs
    if reason_counts_pairs is not None:
        out["reason_counts_pairs"] = reason_counts_pairs
    return out


def analyze_cohort(
    manifest: dict[str, Any],
    dispositions: dict[str, str],
    *,
    desk_meta: dict[str, dict[str, Any]] | None = None,
    ledger_rows: dict[str, dict[str, Any]] | None = None,
    drop_unrateable: bool = False,
) -> dict[str, Any]:
    """Compute primary (P1--P3) Holm family and secondary (S1--S14) qualification analyses."""
    desk_meta = desk_meta or {}
    ledger_rows = ledger_rows or {}
    pairs = manifest["pairs"]
    s0_pass = [r for r in pairs if not r.get("intake_stop")]
    if drop_unrateable:
        s0_pass = [r for r in s0_pass if dispositions[pair_key(r)] != "desk_unrateable"]

    conf = [r for r in s0_pass if not r["quarantined"]]
    quar = [r for r in s0_pass if r["quarantined"]]
    conf_reps = select_representatives(conf)
    rep_rows = list(conf_reps.values())
    n_conf_clusters = len(rep_rows)

    # P1: Execution yield among confirmatory representatives past S0
    p1_k = sum(dispositions[pair_key(r)] in S3_EXECUTED for r in rep_rows)
    p1_gate = n_conf_clusters >= MIN_CONFIRMATORY_CLUSTERS
    p1_rate = rate_summary(p1_k, n_conf_clusters)
    p1_p = exact_binomial_two_sided_p(p1_k, n_conf_clusters, REF_P1) if p1_gate else None

    # P2: Equal-cluster (desk_stop - reached_execution) across all confirmatory S0-pass pairs
    p2_groups: dict[str, list[int]] = defaultdict(list)
    for r in conf:
        t = dispositions[pair_key(r)]
        p2_groups[r["cluster_id"]].append(int(t in S1_DESK_STOPS) - int(t in S3_EXECUTED))
    p2_gate = len(p2_groups) >= MIN_CONFIRMATORY_CLUSTERS
    p2_stats = cluster_contrast(p2_groups)
    p2_p = p2_stats["cluster_sign_flip_p"] if p2_gate else None

    # P3: All-stream alerts among fitted confirmatory representatives
    fitted_reps = [r for r in rep_rows if dispositions[pair_key(r)] in S4_FITTED]
    p3_n = len(fitted_reps)
    p3_k = sum(dispositions[pair_key(r)] == "alert" for r in fitted_reps)
    p3_gate = p3_n >= MIN_FITTED_CLUSTERS
    p3_rate = rate_summary(p3_k, p3_n)
    p3_p = exact_binomial_two_sided_p(p3_k, p3_n, REF_P3) if p3_gate else None

    # Fixed 3-outcome Holm family (protocol section 5); ungated outcomes keep p=1.0
    # conservatively so gating never weakens family-wise alpha=0.05 protection.
    holm_inputs = {
        "P1": p1_p if p1_p is not None else 1.0,
        "P2": p2_p if p2_p is not None else 1.0,
        "P3": p3_p if p3_p is not None else 1.0,
    }
    holm_adj = holm(holm_inputs)

    # S1: Desk stop rate vs R1 (103/147) + source/contract/route split
    s1_desk_reps = [r for r in rep_rows if dispositions[pair_key(r)] in S1_DESK_STOPS]
    s1_desk_k = len(s1_desk_reps)
    s1_desk_pairs = [r for r in conf if dispositions[pair_key(r)] in S1_DESK_STOPS]
    s1_bucket_reps = Counter(
        _bucket_label(
            dispositions[pair_key(r)],
            desk_meta.get(pair_key(r)) or ledger_rows.get(pair_key(r), {}).get("desk"),
        )
        for r in s1_desk_reps
    )
    s1_bucket_pairs = Counter(
        _bucket_label(
            dispositions[pair_key(r)],
            desk_meta.get(pair_key(r)) or ledger_rows.get(pair_key(r), {}).get("desk"),
        )
        for r in s1_desk_pairs
    )

    # S2, S3, S4, S6, S14 on confirmatory representatives
    s2_alert_k = sum(dispositions[pair_key(r)] == "alert" for r in rep_rows)
    post_desk = [r for r in rep_rows if dispositions[pair_key(r)] not in S1_DESK_STOPS]
    unrun_reps = [r for r in post_desk if dispositions[pair_key(r)] == "not_executed"]
    attempted_post_desk = [r for r in post_desk if dispositions[pair_key(r)] != "not_executed"]
    s3_prep_k = sum(dispositions[pair_key(r)] == "support_boundary_closed" for r in post_desk)
    exec_reps = [r for r in rep_rows if dispositions[pair_key(r)] in S3_EXECUTED]
    s4_oracle_k = sum(dispositions[pair_key(r)] == "execution_oracle_failure" for r in exec_reps)
    non_infra = [r for r in rep_rows if dispositions[pair_key(r)] != "execution_infrastructure_failure"]
    s6_k = sum(dispositions[pair_key(r)] in S3_EXECUTED for r in non_infra)
    fix_reps = [r for r in post_desk if dispositions[pair_key(r)] == "fixture_stop"]
    s14_fix_k = len(fix_reps)

    fix_bucket_reps: Counter[str] = Counter()
    fix_reason_reps: Counter[str] = Counter()
    for r in fix_reps:
        k = pair_key(r)
        meta = ledger_rows.get(k, {}).get("fixture_stop") or ledger_rows.get(k, {}).get("desk") or desk_meta.get(k) or {}
        if meta.get("bucket"):
            fix_bucket_reps[str(meta["bucket"])] += 1
        if meta.get("reason"):
            fix_reason_reps[str(meta["reason"])] += 1
    fix_bucket_pairs: Counter[str] = Counter()
    fix_reason_pairs: Counter[str] = Counter()
    for r in conf:
        k = pair_key(r)
        if dispositions[k] == "fixture_stop":
            meta = ledger_rows.get(k, {}).get("fixture_stop") or ledger_rows.get(k, {}).get("desk") or desk_meta.get(k) or {}
            if meta.get("bucket"):
                fix_bucket_pairs[str(meta["bucket"])] += 1
            if meta.get("reason"):
                fix_reason_pairs[str(meta["reason"])] += 1

    # S5: R8 contrast replicated (alert - no_alert among confirmatory fitted pairs, equal-cluster)
    s5_groups: dict[str, list[int]] = defaultdict(list)
    for r in conf:
        t = dispositions[pair_key(r)]
        if t in S4_FITTED:
            s5_groups[r["cluster_id"]].append(int(t == "alert") - int(t == "no_alert"))
    s5_stats = cluster_contrast(s5_groups)
    s5_gate = s5_stats["clusters"] >= MIN_FITTED_CLUSTERS

    # S7 (any-stream alert rule) & S8 (drop-largest refit + range-limited counts)
    s7_flags: list[bool] = []
    s7_missing = 0
    s8_admitted_reps = 0
    s8_range_limited_reps = 0
    s8_admitted_all_alerts = 0
    s8_admitted_any_alerts = 0
    s8_retained_alerts = 0
    s8_flipped_alerts = 0
    s8_range_limited_alerts = 0
    s8_missing = 0
    for r in fitted_reps:
        k = pair_key(r)
        any_flag, drop_info = _extract_s7_s8_row(ledger_rows.get(k), dispositions[k])
        if any_flag is None:
            s7_missing += 1
        else:
            s7_flags.append(any_flag)
        if drop_info is None:
            s8_missing += 1
        else:
            if drop_info["admitted"]:
                s8_admitted_reps += 1
                if drop_info["all_stream_alert"]:
                    s8_admitted_all_alerts += 1
                    if dispositions[k] == "alert":
                        s8_retained_alerts += 1
                elif dispositions[k] == "alert":
                    s8_flipped_alerts += 1
                if drop_info["any_stream_alert"]:
                    s8_admitted_any_alerts += 1
            else:
                s8_range_limited_reps += 1
                if dispositions[k] == "alert":
                    s8_range_limited_alerts += 1

    if p3_n == 0:
        s7_res: dict[str, Any] = {
            "available": False,
            **rate_summary(0, 0),
            "alerts_per_selected": rate_summary(0, n_conf_clusters),
        }
    elif s7_missing == 0:
        s7_k = sum(s7_flags)
        s7_res = {
            "available": True,
            **rate_summary(s7_k, p3_n),
            "alerts_per_selected": rate_summary(s7_k, n_conf_clusters),
        }
    else:
        s7_res = {
            "available": False,
            "count": None,
            "total": p3_n,
            "percent": None,
            "clopper_pearson_95pct_percent": None,
            "all_stream_floor": p3_k,
            "missing_fit_details": s7_missing,
        }

    s8_contrast_groups: dict[str, list[int]] = defaultdict(list)
    if p3_n > 0 and s8_missing == 0:
        for r in conf:
            k = pair_key(r)
            if dispositions[k] in S4_FITTED:
                _, d_info = _extract_s7_s8_row(ledger_rows.get(k), dispositions[k])
                if d_info and d_info["admitted"]:
                    s8_contrast_groups[r["cluster_id"]].append(
                        int(dispositions[k] == "alert") - int(d_info["all_stream_alert"])
                    )
        s8_res: dict[str, Any] = {
            "available": True,
            "fitted_total": p3_n,
            "admitted_count": s8_admitted_reps,
            "range_limited_count": s8_range_limited_reps,
            "alerts_among_admitted": rate_summary(s8_admitted_all_alerts, s8_admitted_reps),
            "any_stream_alerts_among_admitted": rate_summary(s8_admitted_any_alerts, s8_admitted_reps),
            "retained_all_stream_alerts": s8_retained_alerts,
            "flipped_all_stream_alerts": s8_flipped_alerts,
            "range_limited_all_stream_alerts": s8_range_limited_alerts,
            "admitted_contrast": cluster_contrast(s8_contrast_groups),
        }
    else:
        s8_res = {
            "available": False,
            "fitted_total": p3_n,
            "admitted_count": None,
            "range_limited_count": None,
            "missing_drop_largest_details": s8_missing,
        }

    # S9: All-pair equal-cluster versions of P1 and P3
    s9_p1_groups: dict[str, list[int]] = defaultdict(list)
    s9_p3_groups: dict[str, list[int]] = defaultdict(list)
    s9_p1_pairs = 0
    s9_p3_pairs = 0
    s9_p3_alerts = 0
    for r in conf:
        t = dispositions[pair_key(r)]
        cid = r["cluster_id"]
        is_exec = int(t in S3_EXECUTED)
        s9_p1_groups[cid].append(is_exec)
        s9_p1_pairs += is_exec
        if t in S4_FITTED:
            is_alert = int(t == "alert")
            s9_p3_groups[cid].append(is_alert)
            s9_p3_pairs += 1
            s9_p3_alerts += is_alert
    s9_res = {
        "P1_equal_cluster": {
            **cluster_rate(s9_p1_groups),
            "pair_level_working_independence_cp": rate_summary(s9_p1_pairs, len(conf)),
        },
        "P3_equal_cluster": {
            **cluster_rate(s9_p3_groups),
            "pair_level_working_independence_cp": rate_summary(s9_p3_alerts, s9_p3_pairs),
        },
    }

    # S10: Per-frame rates (Contest and Repository)
    s10_res: dict[str, Any] = {}
    for frame in ("Contest", "Repository"):
        f_conf = [r for r in conf if r["frame"] == frame]
        f_reps = list(select_representatives(f_conf).values())
        f_n = len(f_reps)
        f_desk_k = sum(dispositions[pair_key(r)] in S1_DESK_STOPS for r in f_reps)
        f_exec_rows = [r for r in f_reps if dispositions[pair_key(r)] in S3_EXECUTED]
        f_post_desk = [r for r in f_reps if dispositions[pair_key(r)] not in S1_DESK_STOPS]
        f_fit_rows = [r for r in f_reps if dispositions[pair_key(r)] in S4_FITTED]
        f_alert_k = sum(dispositions[pair_key(r)] == "alert" for r in f_reps)
        f_prep_k = sum(dispositions[pair_key(r)] == "support_boundary_closed" for r in f_post_desk)
        f_fix_k = sum(dispositions[pair_key(r)] == "fixture_stop" for r in f_post_desk)
        f_oracle_k = sum(dispositions[pair_key(r)] == "execution_oracle_failure" for r in f_exec_rows)
        counts_only = frame == "Repository" and all(
            dispositions[pair_key(r)] == "desk_unrateable" for r in f_conf
        )
        s10_res[frame] = {
            "clusters_past_s0": f_n,
            "pairs_past_s0": len(f_conf),
            "gate_met": f_n >= MIN_FRAME_CLUSTERS,
            "counts_only": counts_only,
            "P1_exec_yield": rate_summary(len(f_exec_rows), f_n),
            "S1_desk_stop": rate_summary(f_desk_k, f_n),
            "S2_alerts_per_selected": rate_summary(f_alert_k, f_n),
            "P3_alerts_per_fitted": {
                **rate_summary(f_alert_k, len(f_fit_rows)),
                "fitted_gate_met": len(f_fit_rows) >= MIN_FRAME_CLUSTERS,
            },
            "S3_preprocessing_stops_after_desk": rate_summary(f_prep_k, len(f_post_desk)),
            "S14_fixture_stops_after_s1_pass": rate_summary(f_fix_k, len(f_post_desk)),
            "S4_oracle_failures_among_executed": rate_summary(f_oracle_k, len(f_exec_rows)),
        }

    # Truncated-prefix (K < len(post_desk)) fallback bounds
    unrun_rep_n = len(unrun_reps)
    unrun_pair_n = sum(dispositions[pair_key(r)] == "not_executed" for r in conf)
    if unrun_rep_n > 0 and n_conf_clusters > 0:
        p2_worst_groups: dict[str, list[int]] = defaultdict(list)
        for r in conf:
            t = dispositions[pair_key(r)]
            is_desk = int(t in S1_DESK_STOPS)
            is_exec_worst = int(t in S3_EXECUTED or t == "not_executed")
            p2_worst_groups[r["cluster_id"]].append(is_desk - is_exec_worst)
        p2_worst = cluster_contrast(p2_worst_groups)
        attempted_total = s1_desk_k + len(attempted_post_desk)
        trunc_sens: dict[str, Any] = {
            "truncated": True,
            "s1_pass_reps": len(post_desk),
            "attempted_s1_pass_reps": len(attempted_post_desk),
            "not_executed_reps": unrun_rep_n,
            "not_executed_pairs": unrun_pair_n,
            "P1_frozen_bounds_pct": [
                round(100.0 * p1_k / n_conf_clusters, 1),
                round(100.0 * (p1_k + unrun_rep_n) / n_conf_clusters, 1),
            ],
            "P1_prefix_conditional_overall": rate_summary(p1_k, attempted_total),
            "P1_prefix_conditional_among_s1_passes": rate_summary(p1_k, len(attempted_post_desk)),
            "P2_frozen_bounds_delta_pp": [
                p2_worst["group_weighted_delta_pp"],
                p2_stats["group_weighted_delta_pp"],
            ],
            "P2_worst_case_sign_flip_p": p2_worst["cluster_sign_flip_p"],
            "S14_frozen_bounds_pct": [
                round(100.0 * s14_fix_k / len(post_desk), 1),
                round(100.0 * (s14_fix_k + unrun_rep_n) / len(post_desk), 1),
            ],
            "S14_prefix_conditional": rate_summary(s14_fix_k, len(attempted_post_desk)),
        }
    else:
        trunc_sens = {
            "truncated": False,
            "s1_pass_reps": len(post_desk),
            "attempted_s1_pass_reps": len(attempted_post_desk),
            "not_executed_reps": 0,
            "not_executed_pairs": 0,
        }

    def _is_exit137_cpu_cap(row_l: dict[str, Any]) -> bool:
        return bool(row_l.get("cpu_cap_exit137")) or any(
            "cpu_cap" in (ev.get("caps") or []) and ev.get("exit") in (-9, 137)
            for ev in (row_l.get("measurements") or [])
        )

    def _is_alignment_rebuild(row_l: dict[str, Any]) -> bool:
        return bool(row_l.get("alignment_rebuild") or row_l.get("superseded_fixture_stop"))

    # Execution checks (caps, restoration, O0/O2/O3, sham, §11 exit-137) when ledger_rows are provided
    conf_keys = [pair_key(r) for r in conf]
    has_exec_meta = any(
        isinstance(ledger_rows.get(k, {}).get("measurements"), list)
        or "restoration" in ledger_rows.get(k, {})
        or "caps" in ledger_rows.get(k, {})
        for k in conf_keys
    )
    if has_exec_meta:
        cap_counts = Counter({c: 0 for c in CAPS})
        capped_pairs = 0
        cpu_exit137_pairs = 0
        align_reb_pairs = 0
        rest_counts = Counter({"passed": 0, "no_excess": 0, "failed": 0, "unmeasured": 0})
        for r in conf:
            k = pair_key(r)
            row_l = ledger_rows.get(k, {})
            row_caps: set[str] = set(row_l.get("caps") or [])
            meas = row_l.get("measurements") or []
            for ev in meas:
                row_caps.update(ev.get("caps") or [])
            if _is_exit137_cpu_cap(row_l):
                cpu_exit137_pairs += 1
            if _is_alignment_rebuild(row_l):
                align_reb_pairs += 1
            if row_caps:
                capped_pairs += 1
                for c in row_caps:
                    if c in cap_counts:
                        cap_counts[c] += 1
            if dispositions[k] in S4_FITTED and isinstance(row_l.get("restoration"), dict):
                checks = [chk for stream_chks in row_l["restoration"].values() for chk in stream_chks]
                if not checks:
                    rest_counts["no_excess"] += 1
                elif all(chk.get("passes") for chk in checks):
                    rest_counts["passed"] += 1
                else:
                    rest_counts["failed"] += 1
            else:
                rest_counts["unmeasured"] += 1
        exec_checks: dict[str, Any] = {
            "available": True,
            "caps": dict(cap_counts),
            "pairs_with_any_cap": capped_pairs,
            "restoration": dict(rest_counts),
        }
        sec11: dict[str, Any] = {
            "available": True,
            "cpu_cap_exit137_pairs": cpu_exit137_pairs,
            "wave2_alignment_rebuilds_to_oracle_fail": align_reb_pairs,
        }
        if cpu_exit137_pairs > 0:
            cpu_exit137_reps = sum(
                1
                for r in rep_rows
                if dispositions[pair_key(r)] in S3_EXECUTED
                and _is_exit137_cpu_cap(ledger_rows.get(pair_key(r), {}))
            )
            s11_p1_k = max(0, p1_k - cpu_exit137_reps)
            s11_p2_groups: dict[str, list[int]] = defaultdict(list)
            for r in conf:
                k = pair_key(r)
                t = dispositions[k]
                is_137 = _is_exit137_cpu_cap(ledger_rows.get(k, {}))
                is_exec = int(t in S3_EXECUTED and not is_137)
                s11_p2_groups[r["cluster_id"]].append(int(t in S1_DESK_STOPS) - is_exec)
            cpu_exit137_fitted = sum(
                1
                for r in rep_rows
                if dispositions[pair_key(r)] in S4_FITTED
                and _is_exit137_cpu_cap(ledger_rows.get(pair_key(r), {}))
            )
            s11_p3_rate = rate_summary(p3_k, max(0, p3_n - cpu_exit137_fitted)) if cpu_exit137_fitted > 0 else p3_rate
            sec11["cpu_cap_exit137_reps"] = cpu_exit137_reps
            sec11["cpu_cap_exit137_fitted_no_alert_reps"] = cpu_exit137_fitted
            sec11["unpatched_cpu_cap_as_not_executed"] = {
                "P1": rate_summary(s11_p1_k, n_conf_clusters),
                "P2": cluster_contrast(s11_p2_groups),
                "P3": s11_p3_rate,
            }
        if align_reb_pairs > 0:
            align_reb_reps = sum(
                1
                for r in rep_rows
                if dispositions[pair_key(r)] in S3_EXECUTED
                and _is_alignment_rebuild(ledger_rows.get(pair_key(r), {}))
            )
            s11_a_exec = max(0, p1_k - align_reb_reps)
            s11_a_fix = s14_fix_k + align_reb_reps
            s11_a_oracle = max(0, s4_oracle_k - align_reb_reps)
            s11_a_p2_groups: dict[str, list[int]] = defaultdict(list)
            for r in conf:
                k = pair_key(r)
                t = dispositions[k]
                is_reb = _is_alignment_rebuild(ledger_rows.get(k, {}))
                is_exec = int(t in S3_EXECUTED and not is_reb)
                s11_a_p2_groups[r["cluster_id"]].append(int(t in S1_DESK_STOPS) - is_exec)
            sec11["superseded_alignment_as_fixture_stop"] = {
                "P1": rate_summary(s11_a_exec, n_conf_clusters),
                "P2": cluster_contrast(s11_a_p2_groups),
                "S14": rate_summary(s11_a_fix, len(post_desk)),
                "S4": rate_summary(s11_a_oracle, s11_a_exec),
            }
    else:
        exec_checks = {"available": False}
        sec11 = {"available": False}

    return {
        "drop_unrateable": drop_unrateable,
        "confirmatory_pairs_past_s0": len(conf),
        "confirmatory_clusters_past_s0": n_conf_clusters,
        "P1": {
            "gate_met": p1_gate,
            "rate": p1_rate,
            "ref": "14/147",
            "p_unadjusted": p1_p,
            "p_holm": holm_adj["P1"] if p1_gate else None,
        },
        "P2": {
            "gate_met": p2_gate,
            "contrast": p2_stats,
            "p_unadjusted": p2_p,
            "p_holm": holm_adj["P2"] if p2_gate else None,
        },
        "P3": {
            "gate_met": p3_gate,
            "rate": p3_rate,
            "ref": "4/13",
            "p_unadjusted": p3_p,
            "p_holm": holm_adj["P3"] if p3_gate else None,
            "reporting_mode": "confirmatory" if p3_gate else "descriptive_only_below_30_fitted_clusters",
        },
        "secondary": {
            "S1_desk_stop": {
                **rate_summary(s1_desk_k, n_conf_clusters),
                "ref": "103/147",
                "nominal_p_vs_103_147": (
                    exact_binomial_two_sided_p(s1_desk_k, n_conf_clusters, REF_R1)
                    if n_conf_clusters > 0
                    else None
                ),
                "bucket_counts_reps": dict(sorted(s1_bucket_reps.items())),
                "bucket_counts_pairs": dict(sorted(s1_bucket_pairs.items())),
            },
            "S2_alerts_per_selected": {
                **rate_summary(s2_alert_k, n_conf_clusters),
                "ref": "4/147",
                "nominal_p_vs_4_147": (
                    exact_binomial_two_sided_p(s2_alert_k, n_conf_clusters, REF_R4)
                    if n_conf_clusters > 0
                    else None
                ),
            },
            "S3_preprocessing_stops_after_desk": {
                **rate_summary(s3_prep_k, len(post_desk)),
                "ref": "12/26",
                "nominal_p_vs_12_26": (
                    exact_binomial_two_sided_p(s3_prep_k, len(post_desk), REF_R5)
                    if post_desk
                    else None
                ),
                "all_s1_passes": rate_summary(s3_prep_k, len(post_desk)),
                "runner_evaluated": rate_summary(
                    s3_prep_k,
                    sum(
                        1
                        for r in post_desk
                        if dispositions[pair_key(r)] != "fixture_stop"
                        or (ledger_rows.get(pair_key(r), {}).get("fixture_stop") or {}).get("reason") == "overlay_fixture_stop"
                    ),
                ),
                "excluding_not_executed": (
                    rate_summary(s3_prep_k, len(attempted_post_desk)) if unrun_rep_n > 0 else None
                ),
            },
            "S4_oracle_failures_among_executed": {
                **rate_summary(s4_oracle_k, len(exec_reps)),
                "ref": "1/14",
                "nominal_p_vs_1_14": (
                    exact_binomial_two_sided_p(s4_oracle_k, len(exec_reps), REF_R6)
                    if exec_reps
                    else None
                ),
            },
            "S5_alert_minus_no_alert_among_fits": {
                **s5_stats,
                "ref": "-33.3 pp (12 clusters, R8)",
                "gate_met": s5_gate,
                "nominal_p": s5_stats.get("cluster_sign_flip_p"),
                "reporting_mode": (
                    "exploratory_nominal" if s5_gate else "descriptive_only_below_30_fitted_clusters"
                ),
            },
            "S6_P1_without_infra": rate_summary(s6_k, len(non_infra)),
            "S7_any_stream_alerts": s7_res,
            "S8_drop_largest_refit": s8_res,
            "S9_all_pair_equal_cluster": s9_res,
            "S10_per_frame": s10_res,
            "S12_quarantined": _build_s12_summary(quar, dispositions, desk_meta),
            "S14_fixture_stops_after_s1_pass": _s14_summary(
                s14_fix_k,
                len(post_desk),
                unrun_rep_n,
                bucket_counts_reps=dict(sorted(fix_bucket_reps.items())) if fix_bucket_reps else None,
                reason_counts_reps=dict(sorted(fix_reason_reps.items())) if fix_reason_reps else None,
                bucket_counts_pairs=dict(sorted(fix_bucket_pairs.items())) if fix_bucket_pairs else None,
                reason_counts_pairs=dict(sorted(fix_reason_pairs.items())) if fix_reason_pairs else None,
            ),
        },
        "truncation_sensitivity": trunc_sens,
        "execution_checks": exec_checks,
        "section_11_sensitivity": sec11,
        "indeterminate_counts": {
            "confirmatory_pairs": sum(dispositions[pair_key(r)] == "indeterminate" for r in conf),
            "confirmatory_reps": sum(dispositions[pair_key(r)] == "indeterminate" for r in rep_rows),
            "quarantined_pairs": sum(dispositions[pair_key(r)] == "indeterminate" for r in quar),
        },
    }

def _norm_flow_frame(raw: dict[str, Any]) -> dict[str, int]:
    dup = raw.get("s0_intake_duplicate", raw.get("intake_duplicate"))
    unret = raw.get("s0_intake_unretrievable", raw.get("intake_unretrievable"))
    s0_total = raw.get("s0_intake_stop", raw.get("intake_stop"))
    if s0_total is None:
        if dup is None and unret is None:
            raise ValueError("Flow frame missing s0_intake_stop")
        s0_total = int(dup or 0) + int(unret or 0)
    elif dup is not None and unret is not None and int(dup) + int(unret) != int(s0_total):
        raise ValueError("s0_intake_duplicate + s0_intake_unretrievable != s0_intake_stop")

    desk_ex = int(raw.get("s1_desk_excluded", raw.get("desk_excluded", 0)))
    desk_bl = int(raw.get("s1_desk_blocked", raw.get("desk_blocked", 0)))
    desk_unr = int(raw.get("s1_desk_unrateable", raw.get("desk_unrateable", 0)))
    desk_ind = int(raw.get("s1_indeterminate", raw.get("indeterminate", 0)))
    desk_tot_raw = raw.get("s1_desk_stop_total", raw.get("s1_desk_stop"))
    if desk_tot_raw is not None:
        desk_tot = int(desk_tot_raw)
        if any(
            k in raw
            for k in (
                "s1_desk_excluded", "desk_excluded",
                "s1_desk_blocked", "desk_blocked",
                "s1_desk_unrateable", "desk_unrateable",
                "s1_indeterminate", "indeterminate",
            )
        ):
            if desk_ex + desk_bl + desk_unr + desk_ind != desk_tot:
                raise ValueError("S1 desk stop sub-counts do not sum to s1_desk_stop_total")
    else:
        desk_tot = desk_ex + desk_bl + desk_unr + desk_ind

    fix = int(raw.get("s2_fixture_stop", raw.get("fixture_stop", 0)))
    prep = int(raw.get("s2_preprocessing_stop", raw.get("support_boundary_closed", 0)))
    infra = int(raw.get("s3_infra_failure", raw.get("execution_infrastructure_failure", 0)))
    unrun = int(raw.get("not_executed", 0))
    oracle = int(raw.get("s3_oracle_failure", raw.get("execution_oracle_failure", 0)))
    nofit = int(raw.get("s4_no_fit", raw.get("insufficient_fit", 0)))
    noalert = int(raw.get("s5_no_alert", raw.get("no_alert", 0)))
    alert = int(raw.get("s5_alert", raw.get("alert", 0)))
    drawn = int(raw["drawn"])
    part_sum = int(s0_total) + desk_tot + fix + prep + infra + unrun + oracle + nofit + noalert + alert
    if part_sum != drawn:
        raise ValueError(f"Flow table partition mismatch: sum={part_sum} != drawn={drawn}")

    out: dict[str, int] = {
        "drawn": drawn,
        "s0_intake_stop": int(s0_total),
        "s1_desk_stop_total": desk_tot,
        "s1_desk_excluded": desk_ex,
        "s1_desk_blocked": desk_bl,
        "s1_desk_unrateable": desk_unr,
        "s1_indeterminate": desk_ind,
        "s2_fixture_stop": fix,
        "s2_preprocessing_stop": prep,
        "s3_infra_failure": infra,
        "not_executed": unrun,
        "s3_oracle_failure": oracle,
        "s4_no_fit": nofit,
        "s5_no_alert": noalert,
        "s5_alert": alert,
    }
    if dup is not None:
        out["s0_intake_duplicate"] = int(dup)
    if unret is not None:
        out["s0_intake_unretrievable"] = int(unret)
    return out


def _effects_from_spec(spec: Any) -> list[Fraction]:
    effects: list[Fraction] = []
    if isinstance(spec, list):
        for item in spec:
            if isinstance(item, (list, tuple)) and len(item) == 2:
                effects.append(Fraction(int(item[0]), int(item[1])))
            elif isinstance(item, int):
                effects.append(Fraction(item, 1))
            else:
                effects.append(Fraction(str(item)))
    elif isinstance(spec, dict):
        for val_key, count in spec.items():
            frac = Fraction(str(val_key))
            effects.extend([frac] * int(count))
    return effects


def _analyze_aggregate_cohort(
    c: dict[str, Any],
    *,
    quar: dict[str, Any],
    flow: dict[str, dict[str, int]],
    drop_unrateable: bool,
) -> dict[str, Any]:
    rep_disp: dict[str, int] = dict(c.get("rep_dispositions") or {})
    pair_disp: dict[str, int] = dict(c.get("pair_dispositions") or rep_disp)
    if drop_unrateable:
        rep_disp = {**rep_disp, "desk_unrateable": 0}
        pair_disp = {**pair_disp, "desk_unrateable": 0}

    n_conf_clusters = (
        int(c["clusters_past_s0_without_unrateable"])
        if drop_unrateable and "clusters_past_s0_without_unrateable" in c
        else sum(rep_disp.values())
    )
    n_conf_pairs = (
        int(c["pairs_past_s0_without_unrateable"])
        if drop_unrateable and "pairs_past_s0_without_unrateable" in c
        else sum(pair_disp.values())
    )
    if "clusters_past_s0" in c and not drop_unrateable and n_conf_clusters == 0:
        n_conf_clusters = int(c["clusters_past_s0"])
    if "pairs_past_s0" in c and not drop_unrateable and n_conf_pairs == 0:
        n_conf_pairs = int(c["pairs_past_s0"])

    exec_k = sum(rep_disp.get(t, 0) for t in S3_EXECUTED)
    p1_gate = n_conf_clusters >= MIN_CONFIRMATORY_CLUSTERS
    p1_rate = rate_summary(exec_k, n_conf_clusters)
    p1_p = exact_binomial_two_sided_p(exec_k, n_conf_clusters, REF_P1) if p1_gate else None

    desk_rep_k = sum(rep_disp.get(t, 0) for t in S1_DESK_STOPS)
    desk_pair_k = sum(pair_disp.get(t, 0) for t in S1_DESK_STOPS)
    exec_pair_k = sum(pair_disp.get(t, 0) for t in S3_EXECUTED)

    p2_key = "p2_ordered_effects_without_unrateable" if drop_unrateable else "p2_ordered_effects"
    p2_pre_key = "p2_contrast_without_unrateable" if drop_unrateable else "p2_contrast"
    if c.get(p2_key):
        eff = _effects_from_spec(c[p2_key])
        p2_stats = cluster_contrast_from_effects(eff, n_conf_pairs, desk_pair_k - exec_pair_k)
    elif isinstance(c.get(p2_pre_key), dict):
        p2_stats = dict(c[p2_pre_key])
    else:
        other_rep_k = n_conf_clusters - desk_rep_k - exec_k
        eff = [Fraction(1, 1)] * desk_rep_k + [Fraction(-1, 1)] * exec_k + [Fraction(0, 1)] * other_rep_k
        p2_stats = cluster_contrast_from_effects(eff, n_conf_pairs, desk_pair_k - exec_pair_k)
    p2_gate = (p2_stats.get("clusters") or 0) >= MIN_CONFIRMATORY_CLUSTERS
    p2_p = p2_stats.get("cluster_sign_flip_p") if p2_gate else None

    fitted_n = sum(rep_disp.get(t, 0) for t in S4_FITTED)
    alert_k = rep_disp.get("alert", 0)
    p3_gate = fitted_n >= MIN_FITTED_CLUSTERS
    p3_rate = rate_summary(alert_k, fitted_n)
    p3_p = exact_binomial_two_sided_p(alert_k, fitted_n, REF_P3) if p3_gate else None

    holm_adj = holm({
        "P1": p1_p if p1_p is not None else 1.0,
        "P2": p2_p if p2_p is not None else 1.0,
        "P3": p3_p if p3_p is not None else 1.0,
    })

    s1_buckets_reps = dict(
        c.get("s1_buckets_reps")
        or c.get("s1_bucket_counts_reps")
        or c.get("s1_buckets")
        or c.get("desk_stop_buckets")
        or {}
    )
    s1_buckets_pairs = dict(c.get("s1_buckets_pairs") or c.get("s1_bucket_counts_pairs") or s1_buckets_reps)
    if s1_buckets_reps:
        if not drop_unrateable and rep_disp.get("desk_unrateable", 0) > 0:
            s1_buckets_reps.setdefault("desk_unrateable", rep_disp["desk_unrateable"])
        if rep_disp.get("indeterminate", 0) > 0:
            s1_buckets_reps.setdefault("indeterminate", rep_disp["indeterminate"])
    if s1_buckets_pairs:
        if not drop_unrateable and pair_disp.get("desk_unrateable", 0) > 0:
            s1_buckets_pairs.setdefault("desk_unrateable", pair_disp["desk_unrateable"])
        if pair_disp.get("indeterminate", 0) > 0:
            s1_buckets_pairs.setdefault("indeterminate", pair_disp["indeterminate"])
    if drop_unrateable:
        s1_buckets_reps.pop("desk_unrateable", None)
        s1_buckets_pairs.pop("desk_unrateable", None)

    post_desk_n = n_conf_clusters - desk_rep_k
    unrun_rep_n = rep_disp.get("not_executed", 0)
    attempted_post_desk_n = post_desk_n - unrun_rep_n
    prep_k = rep_disp.get("support_boundary_closed", 0)
    s3_denom = int(c.get("s3_runner_denom") or post_desk_n)
    oracle_k = rep_disp.get("execution_oracle_failure", 0)
    infra_k = rep_disp.get("execution_infrastructure_failure", 0)
    fix_k = rep_disp.get("fixture_stop", 0)
    non_infra_n = n_conf_clusters - infra_k

    # S5
    fitted_pairs_n = sum(pair_disp.get(t, 0) for t in S4_FITTED)
    alert_pairs_k = pair_disp.get("alert", 0)
    no_alert_pairs_k = pair_disp.get("no_alert", 0)
    if c.get("s5_ordered_effects"):
        s5_eff = _effects_from_spec(c["s5_ordered_effects"])
        s5_stats = cluster_contrast_from_effects(s5_eff, fitted_pairs_n, alert_pairs_k - no_alert_pairs_k)
    elif isinstance(c.get("s5_contrast"), dict):
        s5_stats = dict(c["s5_contrast"])
    else:
        s5_eff = [Fraction(1, 1)] * alert_k + [Fraction(-1, 1)] * (fitted_n - alert_k)
        s5_stats = cluster_contrast_from_effects(s5_eff, fitted_pairs_n, alert_pairs_k - no_alert_pairs_k)
    s5_gate = (s5_stats.get("clusters") or 0) >= MIN_FITTED_CLUSTERS

    # S7
    s7_raw = c.get("s7_any_stream_alerts")
    if isinstance(s7_raw, int):
        s7_res: dict[str, Any] = {
            "available": fitted_n > 0,
            **rate_summary(s7_raw, fitted_n),
            "alerts_per_selected": rate_summary(s7_raw, n_conf_clusters),
        }
    elif isinstance(s7_raw, dict):
        cnt = int(s7_raw["count"])
        tot = int(s7_raw.get("total", fitted_n))
        s7_res = {"available": tot > 0, **rate_summary(cnt, tot), "alerts_per_selected": rate_summary(cnt, n_conf_clusters)}
    else:
        s7_res = {"available": False, "count": None, "total": fitted_n, "percent": None, "clopper_pearson_95pct_percent": None}

    def _count_val(val: Any, default: int = 0) -> int:
        if val is None:
            return default
        if isinstance(val, dict):
            return int(val.get("count", default))
        return int(val)

    # S8
    s8_raw = c.get("s8_drop_largest")
    if isinstance(s8_raw, dict) and ("admitted" in s8_raw or "admitted_count" in s8_raw):
        adm = int(s8_raw.get("admitted", s8_raw.get("admitted_count", 0)))
        rng_lim = int(s8_raw.get("range_limited", s8_raw.get("range_limited_count", fitted_n - adm)))
        adm_alerts = _count_val(s8_raw.get("alerts_among_admitted"), 0)
        adm_any_raw = s8_raw.get("any_stream_alerts_among_admitted")
        adm_any = _count_val(adm_any_raw, 0) if adm_any_raw is not None else None
        ret_alerts = int(s8_raw.get("retained_all_stream_alerts", adm_alerts))
        rl_alerts = int(s8_raw.get("range_limited_all_stream_alerts", 0))
        flip_alerts = int(s8_raw.get("flipped_all_stream_alerts", max(0, alert_k - ret_alerts - rl_alerts)))
        flip_gain = max(0, adm_alerts - ret_alerts)
        if isinstance(s8_raw.get("admitted_contrast"), dict):
            s8_con = s8_raw["admitted_contrast"]
        else:
            s8_eff = (
                [Fraction(1, 1)] * flip_alerts
                + [Fraction(-1, 1)] * flip_gain
                + [Fraction(0, 1)] * max(0, adm - flip_alerts - flip_gain)
            )
            s8_con = cluster_contrast_from_effects(s8_eff, adm, flip_alerts - flip_gain)
        s8_res: dict[str, Any] = {
            "available": True,
            "fitted_total": fitted_n,
            "admitted_count": adm,
            "range_limited_count": rng_lim,
            "alerts_among_admitted": rate_summary(adm_alerts, adm),
            "any_stream_alerts_among_admitted": rate_summary(adm_any, adm) if adm_any is not None else None,
            "retained_all_stream_alerts": ret_alerts,
            "flipped_all_stream_alerts": flip_alerts,
            "range_limited_all_stream_alerts": rl_alerts,
            "admitted_contrast": s8_con,
        }
    else:
        s8_res = {"available": False, "fitted_total": fitted_n, "admitted_count": None, "range_limited_count": None}

    # S9
    if isinstance(c.get("s9_all_pair_equal_cluster"), dict) and not drop_unrateable:
        s9_res = c["s9_all_pair_equal_cluster"]
    else:
        p1_pair_rate = rate_summary(exec_pair_k, n_conf_pairs)
        p3_pair_rate = rate_summary(alert_pairs_k, fitted_pairs_n)
        s9_p1_key = "s9_p1_ordered_effects_without_unrateable" if drop_unrateable else "s9_p1_ordered_effects"
        s9_p3_key = "s9_p3_ordered_effects_without_unrateable" if drop_unrateable else "s9_p3_ordered_effects"
        if c.get(s9_p1_key):
            p1_eff = _effects_from_spec(c[s9_p1_key])
        else:
            p1_eff = [Fraction(1, 1)] * exec_k + [Fraction(0, 1)] * (n_conf_clusters - exec_k)
        if c.get(s9_p3_key):
            p3_eff = _effects_from_spec(c[s9_p3_key])
        else:
            p3_eff = [Fraction(1, 1)] * alert_k + [Fraction(0, 1)] * (fitted_n - alert_k)
        def _equal_cluster_boot(effects: list[Fraction], k_pairs: int, n_pairs_total: int, pair_pct: float) -> dict[str, Any]:
            m_cl = len(effects)
            if m_cl == 0:
                return {"clusters": 0, "pairs": n_pairs_total, "pair_weighted_pct": pair_pct, "equal_cluster_pct": 0.0, "bootstrap_95pct_pct": [0.0, 0.0]}
            mean_val = float(sum(effects) / m_cl)
            rng_s9 = random.Random(SEED)
            draws_s9 = sorted(sum(rng_s9.choices(effects, k=m_cl)) / m_cl for _ in range(DRAWS))
            return {
                "clusters": m_cl,
                "pairs": n_pairs_total,
                "pair_weighted_pct": pair_pct,
                "equal_cluster_pct": round(100.0 * mean_val, 1),
                "bootstrap_95pct_pct": [round(100.0 * float(draws_s9[249]), 1), round(100.0 * float(draws_s9[9749]), 1)],
            }

        s9_p1_boot = _equal_cluster_boot(p1_eff, exec_pair_k, n_conf_pairs, p1_pair_rate["percent"])
        s9_p3_boot = _equal_cluster_boot(p3_eff, alert_pairs_k, fitted_pairs_n, p3_pair_rate["percent"])
        s9_res = {
            "P1_equal_cluster": {
                **s9_p1_boot,
                "pair_level_working_independence_cp": p1_pair_rate,
            },
            "P3_equal_cluster": {
                **s9_p3_boot,
                "pair_level_working_independence_cp": p3_pair_rate,
            },
        }

    # S10 per-frame
    if isinstance(c.get("s10_per_frame"), dict) and not drop_unrateable:
        s10_res = c["s10_per_frame"]
    else:
        if drop_unrateable:
            repo_clusters = 0
            repo_pairs = 0
            contest_clusters = n_conf_clusters
            contest_pairs = n_conf_pairs
        else:
            repo_pairs = int(c.get("repo_pairs_past_s0", flow["Repository"]["drawn"] - flow["Repository"]["s0_intake_stop"]))
            contest_pairs = int(
                c.get(
                    "contest_pairs_past_s0",
                    max(0, (flow["Contest"]["drawn"] - flow["Contest"]["s0_intake_stop"]) - int(quar.get("pairs_past_s0", 0))),
                )
            )
            if "contest_clusters_past_s0" in c:
                contest_clusters = int(c["contest_clusters_past_s0"])
                repo_clusters = int(c.get("repo_clusters_past_s0", max(0, n_conf_clusters - contest_clusters)))
            elif "repo_clusters_past_s0" in c:
                repo_clusters = int(c["repo_clusters_past_s0"])
                contest_clusters = max(0, n_conf_clusters - repo_clusters)
            else:
                contest_clusters = min(contest_pairs, n_conf_clusters)
                repo_clusters = max(0, n_conf_clusters - contest_clusters)
        s10_res = {
            "Contest": {
                "clusters_past_s0": contest_clusters,
                "pairs_past_s0": contest_pairs,
                "gate_met": contest_clusters >= MIN_FRAME_CLUSTERS,
                "counts_only": False,
                "P1_exec_yield": rate_summary(exec_k, contest_clusters),
                "S1_desk_stop": rate_summary(max(0, desk_rep_k - repo_clusters), contest_clusters),
                "S2_alerts_per_selected": rate_summary(alert_k, contest_clusters),
                "P3_alerts_per_fitted": {
                    **rate_summary(alert_k, fitted_n),
                    "fitted_gate_met": fitted_n >= MIN_FRAME_CLUSTERS,
                },
                "S3_preprocessing_stops_after_desk": rate_summary(prep_k, post_desk_n),
                "S14_fixture_stops_after_s1_pass": rate_summary(fix_k, post_desk_n),
                "S4_oracle_failures_among_executed": rate_summary(oracle_k, exec_k),
            },
            "Repository": {
                "clusters_past_s0": repo_clusters,
                "pairs_past_s0": repo_pairs,
                "gate_met": repo_clusters >= MIN_FRAME_CLUSTERS,
                "counts_only": True,
                "P1_exec_yield": rate_summary(0, repo_clusters),
                "S1_desk_stop": rate_summary(repo_clusters, repo_clusters),
                "S2_alerts_per_selected": rate_summary(0, repo_clusters),
                "P3_alerts_per_fitted": {**rate_summary(0, 0), "fitted_gate_met": False},
                "S3_preprocessing_stops_after_desk": rate_summary(0, 0),
                "S14_fixture_stops_after_s1_pass": rate_summary(0, 0),
                "S4_oracle_failures_among_executed": rate_summary(0, 0),
            },
        }

    # S12 quarantined
    q_pairs_n = int(quar.get("pairs_past_s0", 0))
    q_clusters_n = int(quar.get("clusters_past_s0", 0))
    q_pair_disp = dict(quar.get("pair_dispositions") or {})
    q_rep_disp = dict(quar.get("rep_dispositions") or {})
    if drop_unrateable:
        if q_pair_disp:
            q_pair_disp = {**q_pair_disp, "desk_unrateable": 0}
            q_pairs_n = sum(q_pair_disp.values())
        else:
            q_pairs_n = 0
        if q_rep_disp:
            q_rep_disp = {**q_rep_disp, "desk_unrateable": 0}
            q_clusters_n = sum(q_rep_disp.values())
        else:
            q_clusters_n = max(0, q_clusters_n - int(quar.get("unrateable_clusters", 0)))

    def _agg_subset_rates(d: dict[str, int], total_n: int, buckets: dict[str, int] | None = None) -> dict[str, Any]:
        desk_k = sum(d.get(t, 0) for t in S1_DESK_STOPS)
        post_n = total_n - desk_k
        ex_k = sum(d.get(t, 0) for t in S3_EXECUTED)
        fit_n = sum(d.get(t, 0) for t in S4_FITTED)
        al_k = d.get("alert", 0)
        fx_k = d.get("fixture_stop", 0)
        un_k = d.get("not_executed", 0)
        return {
            "S1_desk_stop": {**rate_summary(desk_k, total_n), "bucket_counts": buckets or {}},
            "P1_exec_yield": rate_summary(ex_k, total_n),
            "P3_alerts_per_fitted": rate_summary(al_k, fit_n),
            "S2_alerts_per_selected": rate_summary(al_k, total_n),
            "S14_fixture_stops_after_s1_pass": rate_summary(fx_k, post_n),
            "not_executed_after_s1_pass": rate_summary(un_k, post_n),
        }

    def _missing_rep_cluster_rates(total_clusters: int, p_disp: dict[str, int]) -> dict[str, Any]:
        unavail = {"count": None, "total": total_clusters, "percent": None, "clopper_pearson_95pct_percent": None}
        zero_exec = bool(p_disp) and sum(p_disp.get(t, 0) for t in S3_EXECUTED) == 0
        zero_fit = bool(p_disp) and sum(p_disp.get(t, 0) for t in S4_FITTED) == 0
        zero_alert = bool(p_disp) and p_disp.get("alert", 0) == 0
        return {
            "S1_desk_stop": {**unavail, "bucket_counts": quar.get("s1_buckets_reps") or {}},
            "P1_exec_yield": rate_summary(0, total_clusters) if zero_exec else dict(unavail),
            "P3_alerts_per_fitted": rate_summary(0, 0) if zero_fit else {"count": None, "total": 0, "percent": None, "clopper_pearson_95pct_percent": None},
            "S2_alerts_per_selected": rate_summary(0, total_clusters) if zero_alert else dict(unavail),
            "S14_fixture_stops_after_s1_pass": {"count": None, "total": 0, "percent": None, "clopper_pearson_95pct_percent": None},
            "not_executed_after_s1_pass": {"count": None, "total": 0, "percent": None, "clopper_pearson_95pct_percent": None},
        }

    if isinstance(quar.get("cluster_rates"), dict) and not drop_unrateable:
        q_cluster_rates = quar["cluster_rates"]
    elif q_rep_disp or q_clusters_n == 0:
        q_cluster_rates = _agg_subset_rates(q_rep_disp, q_clusters_n or sum(q_rep_disp.values()), quar.get("s1_buckets_reps"))
    else:
        q_cluster_rates = _missing_rep_cluster_rates(q_clusters_n, q_pair_disp)

    q_pair_rates = (
        quar["pair_rates"]
        if isinstance(quar.get("pair_rates"), dict) and not drop_unrateable
        else _agg_subset_rates(q_pair_disp, q_pairs_n or sum(q_pair_disp.values()), quar.get("s1_buckets_pairs"))
    )
    s12_res = {
        "pairs_past_s0": q_pairs_n,
        "clusters_past_s0": q_clusters_n,
        "pair_dispositions": dict(sorted(q_pair_disp.items())),
        "rep_dispositions": dict(sorted(q_rep_disp.items())),
        "cluster_rates": q_cluster_rates,
        "pair_rates": q_pair_rates,
    }

    # Truncation sensitivity
    unrun_pair_n = pair_disp.get("not_executed", 0)
    if unrun_rep_n > 0 and n_conf_clusters > 0:
        p2_worst_eff = (
            [Fraction(1, 1)] * desk_rep_k
            + [Fraction(-1, 1)] * (exec_k + unrun_rep_n)
            + [Fraction(0, 1)] * max(0, n_conf_clusters - desk_rep_k - exec_k - unrun_rep_n)
        )
        p2_worst = cluster_contrast_from_effects(p2_worst_eff, n_conf_pairs, desk_pair_k - (exec_pair_k + unrun_pair_n))
        trunc_sens: dict[str, Any] = {
            "truncated": True,
            "s1_pass_reps": post_desk_n,
            "attempted_s1_pass_reps": attempted_post_desk_n,
            "not_executed_reps": unrun_rep_n,
            "not_executed_pairs": unrun_pair_n,
            "P1_frozen_bounds_pct": [
                round(100.0 * exec_k / n_conf_clusters, 1),
                round(100.0 * (exec_k + unrun_rep_n) / n_conf_clusters, 1),
            ],
            "P1_prefix_conditional_overall": rate_summary(exec_k, desk_rep_k + attempted_post_desk_n),
            "P1_prefix_conditional_among_s1_passes": rate_summary(exec_k, attempted_post_desk_n),
            "P2_frozen_bounds_delta_pp": [p2_worst["group_weighted_delta_pp"], p2_stats["group_weighted_delta_pp"]],
            "P2_worst_case_sign_flip_p": p2_worst["cluster_sign_flip_p"],
            "S14_frozen_bounds_pct": [
                round(100.0 * fix_k / post_desk_n, 1),
                round(100.0 * (fix_k + unrun_rep_n) / post_desk_n, 1),
            ],
            "S14_prefix_conditional": rate_summary(fix_k, attempted_post_desk_n),
        }
    else:
        trunc_sens = {
            "truncated": False,
            "s1_pass_reps": post_desk_n,
            "attempted_s1_pass_reps": attempted_post_desk_n,
            "not_executed_reps": 0,
            "not_executed_pairs": 0,
        }

    # Execution checks & §11 sensitivity
    exec_checks = dict(c["execution_checks"]) if isinstance(c.get("execution_checks"), dict) else {"available": False}
    if "available" not in exec_checks:
        exec_checks["available"] = bool(exec_checks)

    sec11 = dict(c.get("section_11_sensitivity") or c.get("section_11_disclosures") or {})
    if sec11:
        sec11.setdefault("available", True)
        cpu137 = int(sec11.get("cpu_cap_exit137_pairs", 0))
        cpu137_reps = int(sec11.get("cpu_cap_exit137_reps", cpu137))
        align_reb = int(sec11.get("wave2_alignment_rebuilds_to_oracle_fail", 0))
        align_reb_reps = int(sec11.get("wave2_alignment_rebuilds_reps", align_reb))
        if cpu137_reps > 0 and "unpatched_cpu_cap_as_not_executed" not in sec11 and n_conf_clusters > 0:
            s11_exec = max(0, exec_k - cpu137_reps)
            s11_other = max(0, n_conf_clusters - desk_rep_k - s11_exec)
            s11_eff = [Fraction(1, 1)] * desk_rep_k + [Fraction(-1, 1)] * s11_exec + [Fraction(0, 1)] * s11_other
            cpu137_fitted = int(sec11.get("cpu_cap_exit137_fitted_no_alert_reps", 0))
            s11_p3_rate = rate_summary(alert_k, max(0, fitted_n - cpu137_fitted)) if cpu137_fitted > 0 else p3_rate
            sec11["unpatched_cpu_cap_as_not_executed"] = {
                "P1": rate_summary(s11_exec, n_conf_clusters),
                "P2": cluster_contrast_from_effects(s11_eff, n_conf_pairs, desk_pair_k - max(0, exec_pair_k - cpu137)),
                "P3": s11_p3_rate,
            }
        if align_reb_reps > 0 and "superseded_alignment_as_fixture_stop" not in sec11 and n_conf_clusters > 0:
            s11_a_exec = max(0, exec_k - align_reb_reps)
            s11_a_fix = fix_k + align_reb_reps
            s11_a_oracle = max(0, oracle_k - align_reb_reps)
            s11_a_other = max(0, n_conf_clusters - desk_rep_k - s11_a_exec)
            s11_a_eff = [Fraction(1, 1)] * desk_rep_k + [Fraction(-1, 1)] * s11_a_exec + [Fraction(0, 1)] * s11_a_other
            sec11["superseded_alignment_as_fixture_stop"] = {
                "P1": rate_summary(s11_a_exec, n_conf_clusters),
                "P2": cluster_contrast_from_effects(s11_a_eff, n_conf_pairs, desk_pair_k - max(0, exec_pair_k - align_reb)),
                "S14": rate_summary(s11_a_fix, post_desk_n),
                "S4": rate_summary(s11_a_oracle, s11_a_exec),
            }
    else:
        sec11 = {"available": False}

    return {
        "drop_unrateable": drop_unrateable,
        "confirmatory_pairs_past_s0": n_conf_pairs,
        "confirmatory_clusters_past_s0": n_conf_clusters,
        "P1": {
            "gate_met": p1_gate,
            "rate": p1_rate,
            "ref": "14/147",
            "p_unadjusted": p1_p,
            "p_holm": holm_adj["P1"] if p1_gate else None,
        },
        "P2": {
            "gate_met": p2_gate,
            "contrast": p2_stats,
            "p_unadjusted": p2_p,
            "p_holm": holm_adj["P2"] if p2_gate else None,
        },
        "P3": {
            "gate_met": p3_gate,
            "rate": p3_rate,
            "ref": "4/13",
            "p_unadjusted": p3_p,
            "p_holm": holm_adj["P3"] if p3_gate else None,
            "reporting_mode": "confirmatory" if p3_gate else "descriptive_only_below_30_fitted_clusters",
        },
        "secondary": {
            "S1_desk_stop": {
                **rate_summary(desk_rep_k, n_conf_clusters),
                "ref": "103/147",
                "nominal_p_vs_103_147": (
                    exact_binomial_two_sided_p(desk_rep_k, n_conf_clusters, REF_R1) if n_conf_clusters > 0 else None
                ),
                "bucket_counts_reps": dict(sorted(s1_buckets_reps.items())),
                "bucket_counts_pairs": dict(sorted(s1_buckets_pairs.items())),
            },
            "S2_alerts_per_selected": {
                **rate_summary(alert_k, n_conf_clusters),
                "ref": "4/147",
                "nominal_p_vs_4_147": (
                    exact_binomial_two_sided_p(alert_k, n_conf_clusters, REF_R4) if n_conf_clusters > 0 else None
                ),
            },
            # Raw-ledger path uses all post_desk passes (183); aggregate JSON reports runner-evaluated 154 alongside 183 under all_s1_passes.
            "S3_preprocessing_stops_after_desk": {
                **rate_summary(prep_k, s3_denom),
                "ref": "12/26",
                "nominal_p_vs_12_26": (
                    exact_binomial_two_sided_p(prep_k, s3_denom, REF_R5) if s3_denom > 0 else None
                ),
                "all_s1_passes": rate_summary(prep_k, post_desk_n),
                "excluding_not_executed": rate_summary(prep_k, attempted_post_desk_n) if unrun_rep_n > 0 else None,
            },
            "S4_oracle_failures_among_executed": {
                **rate_summary(oracle_k, exec_k),
                "ref": "1/14",
                "nominal_p_vs_1_14": (
                    exact_binomial_two_sided_p(oracle_k, exec_k, REF_R6) if exec_k > 0 else None
                ),
            },
            "S5_alert_minus_no_alert_among_fits": {
                **s5_stats,
                "ref": "-33.3 pp (12 clusters, R8)",
                "gate_met": s5_gate,
                "nominal_p": s5_stats.get("cluster_sign_flip_p"),
                "reporting_mode": (
                    "exploratory_nominal" if s5_gate else "descriptive_only_below_30_fitted_clusters"
                ),
            },
            "S6_P1_without_infra": rate_summary(exec_k, non_infra_n),
            "S7_any_stream_alerts": s7_res,
            "S8_drop_largest_refit": s8_res,
            "S9_all_pair_equal_cluster": s9_res,
            "S10_per_frame": s10_res,
            "S12_quarantined": s12_res,
            "S14_fixture_stops_after_s1_pass": _s14_summary(
                fix_k,
                post_desk_n,
                unrun_rep_n,
                bucket_counts_reps=c.get("fixture_stop_buckets"),
                reason_counts_reps=c.get("fixture_stop_reasons"),
            ),
        },
        "truncation_sensitivity": trunc_sens,
        "execution_checks": exec_checks,
        "section_11_sensitivity": sec11,
        "indeterminate_counts": {
            "confirmatory_pairs": pair_disp.get("indeterminate", 0),
            "confirmatory_reps": rep_disp.get("indeterminate", 0),
            "quarantined_pairs": q_pair_disp.get("indeterminate", 0),
        },
    }


def _adapt_final_a5_aggregate(agg: dict[str, Any]) -> dict[str, Any]:
    """Adapt an eapg.expansion.final.a5.aggregate.v1 JSON into analyze_aggregate() shape."""
    pins = agg.get("pins") or {}
    raw_flow = agg.get("flow") or {}
    secs = agg.get("secondaries") or {}

    def _map_post_s0_disp(raw_d: dict[str, int]) -> dict[str, int]:
        alias = {
            "S1_blocked": "desk_blocked",
            "S1_excluded": "desk_excluded",
            "S1_indeterminate": "indeterminate",
            "S1_not_rateable": "desk_unrateable",
        }
        out_d: dict[str, int] = {}
        for k, v in (raw_d or {}).items():
            if k in ("intake_duplicate", "intake_unretrievable"):
                continue
            nk = alias.get(k, k)
            out_d[nk] = out_d.get(nk, 0) + int(v)
        return out_d

    def _frame_flow(frame_obj: dict[str, Any]) -> dict[str, int]:
        all_obj = frame_obj.get("all") or {}
        pd = all_obj.get("pair_dispositions") or {}
        return {
            "drawn": int(all_obj.get("pairs", 0)),
            "s0_intake_stop": int(all_obj.get("S0_stops", 0)),
            "s0_intake_duplicate": int(pd.get("intake_duplicate", 0)),
            "s0_intake_unretrievable": int(pd.get("intake_unretrievable", 0)),
            "s1_desk_excluded": int(pd.get("S1_excluded", 0)),
            "s1_desk_blocked": int(pd.get("S1_blocked", 0)),
            "s1_desk_unrateable": int(pd.get("S1_not_rateable", 0)),
            "s1_indeterminate": int(pd.get("S1_indeterminate", 0)),
            "s1_desk_stop_total": int(all_obj.get("S1_stops", 0)),
            "s2_fixture_stop": int(pd.get("fixture_stop", 0)),
            "s2_preprocessing_stop": int(pd.get("support_boundary_closed", 0)),
            "s3_infra_failure": int(pd.get("execution_infrastructure_failure", 0)),
            "not_executed": int(pd.get("not_executed", 0)),
            "s3_oracle_failure": int(pd.get("execution_oracle_failure", 0)),
            "s4_no_fit": int(pd.get("insufficient_fit", 0)),
            "s5_no_alert": int(pd.get("no_alert", 0)),
            "s5_alert": int(pd.get("alert", 0)),
        }

    flow_table_dict = {
        "Contest": _frame_flow(raw_flow["Contest"]),
        "Repository": _frame_flow(raw_flow["Repository"]),
        "Union": _frame_flow(raw_flow["Union"]),
    }

    u_conf = raw_flow["Union"]["confirmatory"]
    c_quar = raw_flow["Contest"]["quarantined"]
    conf_rep = _map_post_s0_disp(u_conf.get("rep_dispositions") or {})
    conf_pair = _map_post_s0_disp(u_conf.get("pair_dispositions") or {})
    quar_rep = _map_post_s0_disp(c_quar.get("rep_dispositions") or {})
    quar_pair = _map_post_s0_disp(c_quar.get("pair_dispositions") or {})

    s1_b = {
        k: int(v)
        for k, v in ((secs.get("S1") or {}).get("bucket_counts") or {}).items()
        if k in ("contract", "source", "route")
    }
    fix_buckets: dict[str, int] = {}
    fix_reasons: dict[str, int] = {}
    for br, cnt in (agg.get("fixture_stop_by_bucket_reason") or {}).items():
        if ":" in br:
            bkt, rsn = br.split(":", 1)
        else:
            bkt, rsn = "unspecified", br
        fix_buckets[bkt] = fix_buckets.get(bkt, 0) + int(cnt)
        fix_reasons[rsn] = fix_reasons.get(rsn, 0) + int(cnt)

    s8_src = secs.get("S8") or {}
    s8_adm = int(s8_src.get("representative_admitted", s8_src.get("admitted_pairs", 0)))
    s8_alerts = int(s8_src.get("representative_alerts_after_refit", s8_src.get("alerts_after_refit", 0)))
    s8_orig_adm = int(s8_src.get("original_alerts_among_admitted", s8_alerts))
    s8_mapped = {
        "admitted_count": s8_adm,
        "range_limited_count": int(s8_src.get("range_limited_pairs", 0)),
        "alerts_among_admitted": s8_alerts,
        "retained_all_stream_alerts": s8_alerts,
        "flipped_all_stream_alerts": max(0, s8_orig_adm - s8_alerts),
        "range_limited_all_stream_alerts": max(0, conf_rep.get("alert", 0) - s8_orig_adm),
    }

    s5_rest = (secs.get("S5") or {}).get("restoration_counts") or {}
    s6_caps = (secs.get("S6") or {}).get("cap_events") or {}
    s9_all = (secs.get("S9") or {}).get("preregistered_all_pair_equal_cluster") or {}
    s13_drop = (secs.get("S13") or {}).get("preregistered_drop_not_rateable") or {}
    disc = agg.get("disclosures") or {}

    confirmatory_obj: dict[str, Any] = {
        "rep_dispositions": conf_rep,
        "pair_dispositions": conf_pair,
        "contest_clusters_past_s0": int(raw_flow["Contest"]["confirmatory"]["representative_clusters"]) - int(raw_flow["Contest"]["confirmatory"]["S0_stops"]),
        "contest_pairs_past_s0": int(raw_flow["Contest"]["confirmatory"]["pairs"]) - int(raw_flow["Contest"]["confirmatory"]["S0_stops"]),
        "repo_clusters_past_s0": int(raw_flow["Repository"]["confirmatory"]["representative_clusters"]) - int(raw_flow["Repository"]["confirmatory"]["S0_stops"]),
        "repo_pairs_past_s0": int(raw_flow["Repository"]["confirmatory"]["pairs"]) - int(raw_flow["Repository"]["confirmatory"]["S0_stops"]),
        "s3_runner_denom": int((secs.get("S3") or {}).get("total", 0)),
        "p2_ordered_effects": agg.get("p2_ordered_effects") or [],
        "p2_ordered_effects_without_unrateable": (s13_drop.get("P2") or {}).get("ordered_effects") or [],
        "s5_ordered_effects": agg.get("s5_ordered_effects") or [],
        "s9_p1_ordered_effects": ((s9_all.get("P1") or {}).get("equal_cluster_bootstrap") or {}).get("ordered_effects") or [],
        "s9_p3_ordered_effects": ((s9_all.get("P3") or {}).get("equal_cluster_bootstrap") or {}).get("ordered_effects") or [],
        "s1_buckets_reps": dict(s1_b),
        "s1_buckets_pairs": dict(s1_b),
        "fixture_stop_buckets": fix_buckets,
        "fixture_stop_reasons": fix_reasons,
        "s7_any_stream_alerts": (secs.get("S7") or {}).get("any_stream_alerts_per_fitted_representative"),
        "s8_drop_largest": s8_mapped,
        "execution_checks": {
            "available": True,
            "caps": dict(s6_caps),
            "positions_with_cap": dict((secs.get("S6") or {}).get("positions_with_cap") or {}),
            "restoration": {
                "passed": int(s5_rest.get("pass", 0)),
                "no_excess": int(s5_rest.get("no_measurable_excess", 0)),
                "failed": int(s5_rest.get("fail", 0)),
                "unmeasured": int(s5_rest.get("unmeasured", 0)),
            },
            "fitted_restoration": {
                "passed": int(((secs.get("S5") or {}).get("protocol_common_uncapped_fitted_restoration") or {}).get("pass", 0)),
                "no_excess": int(((secs.get("S5") or {}).get("protocol_common_uncapped_fitted_restoration") or {}).get("no_measurable_excess", 0)),
                "failed": int(((secs.get("S5") or {}).get("protocol_common_uncapped_fitted_restoration") or {}).get("fail", 0)),
            },
            "o0_o2_o3_agreement": (secs.get("S9") or {}).get("O0_O2_O3_agreement"),
            "target_vs_sham": (secs.get("S10") or {}).get("target_vs_sham"),
        },
        "section_11_sensitivity": {
            "available": True,
            "cpu_cap_exit137_pairs": len(disc.get("patched_reexecution_positions") or []),
            "cpu_cap_exit137_reps": len(disc.get("patched_reexecution_positions") or []),
            "cpu_cap_exit137_fitted_no_alert_reps": len(disc.get("patched_reexecution_positions") or []),
        },
    }

    quarantined_obj: dict[str, Any] = {
        "pairs_past_s0": sum(quar_pair.values()),
        "clusters_past_s0": sum(quar_rep.values()),
        "pair_dispositions": quar_pair,
        "rep_dispositions": quar_rep,
    }

    return {
        "manifest_sha256": pins.get("manifest_sha256", MANIFEST_SHA),
        "held_list_sha256": HELD_SHA,
        "held_out_used": False,
        "s1_batches": 96,
        "execution_complete": bool((agg.get("completion") or {}).get("effective_completion", True)),
        "flow_table": flow_table_dict,
        "confirmatory": confirmatory_obj,
        "quarantined": quarantined_obj,
        "overlap_summary": {
            "cross_frame_shared_problem_keys": 0,
            "cross_frame_shared_pairs": 0,
        },
        "raw_a5_disclosures": {
            "disclosures": dict(disc),
            "pins": dict(pins),
            "sensitivity": dict(agg.get("sensitivity") or {}),
        },
    }


def analyze_aggregate(agg: dict[str, Any]) -> dict[str, Any]:
    """Ingest a de-identified aggregate JSON (e.g., final-a5-stats-agg.json) into a verified receipt."""
    if agg.get("schema") == "eapg.expansion.final.a5.aggregate.v1":
        agg = _adapt_final_a5_aggregate(agg)
    if agg.get("held_out_used") is True:
        raise ValueError("Aggregate input indicates held_out_used=True")
    if "manifest_sha256" in agg and agg["manifest_sha256"] != MANIFEST_SHA:
        raise ValueError("manifest SHA-256 mismatch in aggregate JSON")
    if "held_list_sha256" in agg and agg["held_list_sha256"] != HELD_SHA:
        raise ValueError("held_list SHA-256 mismatch in aggregate JSON")

    if agg.get("schema") == "eapg.expansion.analysis.v1":
        out = dict(agg)
        out["amendment_sha256"] = AMENDMENT_5_SHA
        return out

    raw_flow = agg.get("flow_table")
    if not isinstance(raw_flow, dict):
        raise ValueError("Aggregate JSON missing flow_table")
    union_raw = (
        raw_flow.get("Union")
        or raw_flow.get("Distinct union")
        or raw_flow.get("Distinct Union")
        or raw_flow.get("distinct_union")
    )
    if not isinstance(union_raw, dict):
        raise ValueError("Aggregate JSON flow_table missing Union / Distinct union frame")
    flow = {
        "Contest": _norm_flow_frame(raw_flow["Contest"]),
        "Repository": _norm_flow_frame(raw_flow["Repository"]),
        "Union": _norm_flow_frame(union_raw),
    }

    conf_raw = agg.get("confirmatory")
    quar = agg.get("quarantined") or agg.get("S12_quarantined") or {}
    if not isinstance(conf_raw, dict):
        raise ValueError("Aggregate JSON missing confirmatory breakdown")

    conf = dict(conf_raw)
    for key in (
        "execution_checks",
        "section_11_sensitivity",
        "section_11_disclosures",
        "s7_any_stream_alerts",
        "s8_drop_largest",
        "fixture_stop_reasons",
        "fixture_stop_buckets",
        "s1_buckets_reps",
        "s1_buckets_pairs",
        "s9_all_pair_equal_cluster",
        "s10_per_frame",
    ):
        if key not in conf and key in agg:
            conf[key] = agg[key]

    prim = _analyze_aggregate_cohort(conf, quar=quar, flow=flow, drop_unrateable=False)
    s13 = _analyze_aggregate_cohort(conf, quar=quar, flow=flow, drop_unrateable=True)

    u = flow["Union"]
    rateable_n = int(
        (agg.get("fixture_inventory") or {}).get(
            "total_rateable",
            u["drawn"] - u["s0_intake_stop"] - u["s1_desk_unrateable"],
        )
    )
    pass_n = (
        u["s2_fixture_stop"]
        + u["s2_preprocessing_stop"]
        + u["s3_infra_failure"]
        + u["not_executed"]
        + u["s3_oracle_failure"]
        + u["s4_no_fit"]
        + u["s5_no_alert"]
        + u["s5_alert"]
    )
    inv = dict(agg.get("fixture_inventory") or {})
    inv.setdefault("total_rateable", rateable_n)
    inv.setdefault(
        "s1_status_counts",
        {
            "desk_blocked": u["s1_desk_blocked"],
            "desk_excluded": u["s1_desk_excluded"],
            "indeterminate": u["s1_indeterminate"],
            "pass": pass_n,
        },
    )

    out: dict[str, Any] = {
        "schema": "eapg.expansion.analysis.v1",
        "amendment_sha256": AMENDMENT_5_SHA,
        "manifest_sha256": agg.get("manifest_sha256", MANIFEST_SHA),
        "held_list_sha256": agg.get("held_list_sha256", HELD_SHA),
        "held_out_used": bool(agg.get("held_out_used", False)),
        "s1_batches": int(agg.get("s1_batches", 96)),
        "flow_table": flow,
        "primary_all_post_s0": prim,
        "S13_without_desk_unrateable": s13,
        "fixture_inventory": inv,
    }
    if "overlap_summary" in agg:
        out["overlap_summary"] = agg["overlap_summary"]
    if "raw_a5_disclosures" in agg:
        out["raw_a5_disclosures"] = agg["raw_a5_disclosures"]
    if "execution_complete" in agg:
        out["execution_complete"] = bool(agg["execution_complete"])
    if "author_check" in agg and agg["author_check"] is not None:
        out["author_check"] = agg["author_check"]
    if "forensics" in agg and agg["forensics"] is not None:
        out["forensics"] = agg["forensics"]
    return out

def cohens_kappa(pairs_ab: list[tuple[str, str]]) -> float | None:
    n = len(pairs_ab)
    if n == 0:
        return None
    po = sum(a == b for a, b in pairs_ab) / n
    ca = Counter(a for a, _ in pairs_ab)
    cb = Counter(b for _, b in pairs_ab)
    labels = set(ca) | set(cb)
    pe = sum((ca[l] / n) * (cb[l] / n) for l in labels)
    if pe >= 1.0:
        return 1.0 if po == 1.0 else 0.0
    return (po - pe) / (1.0 - pe)


def author_check_agreement(
    draw_pairs: list[dict[str, Any]],
    manifest_by_key: dict[str, dict[str, Any]],
    primary_labels: dict[str, dict[str, Any]],
    author_labels: dict[str, dict[str, Any]],
    *,
    unblinded_keys: set[str] | None = None,
) -> dict[str, Any]:
    """Descriptive blind single-author check with cluster bootstrap."""
    unblinded_keys = unblinded_keys or set()
    by_cluster_exact: dict[str, list[tuple[str, str]]] = defaultdict(list)
    by_cluster_bucket: dict[str, list[tuple[str, str]]] = defaultdict(list)

    def exact_tag(rec: dict[str, Any]) -> str:
        st = rec["status"]
        if st in ("pass", "indeterminate", "desk_unrateable"):
            return st
        return f'{st}:{rec.get("bucket")}:{rec.get("reason")}'

    def bucket_tag(rec: dict[str, Any]) -> str:
        st = rec["status"]
        if st in ("pass", "indeterminate", "desk_unrateable"):
            return st
        return str(rec.get("bucket"))

    for item in draw_pairs:
        key = f'{item["corpus"]}:{item["pair_id"]}' if "pair_id" in item else pair_key(item)
        cid = manifest_by_key[key]["cluster_id"]
        by_cluster_exact[cid].append((exact_tag(primary_labels[key]), exact_tag(author_labels[key])))
        by_cluster_bucket[cid].append((bucket_tag(primary_labels[key]), bucket_tag(author_labels[key])))

    def summarize_level(grouped: dict[str, list[tuple[str, str]]]) -> dict[str, Any]:
        ordered_cids = sorted(grouped)
        flat = [pair for cid in ordered_cids for pair in grouped[cid]]
        agree = sum(a == b for a, b in flat)
        kappa = cohens_kappa(flat)
        rng = random.Random(SEED)
        boot: list[float] = []
        n_c = len(ordered_cids)
        for _ in range(DRAWS):
            draw_cids = rng.choices(ordered_cids, k=n_c)
            sample = [pair for cid in draw_cids for pair in grouped[cid]]
            kv = cohens_kappa(sample)
            if kv is not None:
                boot.append(kv)
        boot.sort()
        ci = [round(boot[249], 3), round(boot[9749], 3)] if len(boot) == DRAWS else None
        return {
            "n_pairs": len(flat),
            "n_clusters": n_c,
            "raw_agreement_count": agree,
            "raw_agreement_pct": round(100.0 * agree / len(flat), 1) if flat else None,
            "cohens_kappa": round(kappa, 3) if kappa is not None else None,
            "cluster_bootstrap_95pct_kappa": ci,
        }

    return {
        "descriptive_only": True,
        "unblinded_count": len(unblinded_keys),
        "exact": summarize_level(by_cluster_exact),
        "bucket": summarize_level(by_cluster_bucket),
    }


def fixture_readiness_inventory(
    manifest: dict[str, Any],
    s1_dispositions: dict[str, dict[str, Any]],
    holds: list[dict[str, Any]],
) -> dict[str, Any]:
    """Classify S1 passes for downstream fixture-effort forecasting."""
    hold_keys = {f'{h["corpus"]}:{h["pair_id"]}' for h in holds}
    s0_pass = [r for r in manifest["pairs"] if not r.get("intake_stop")]
    rateable = [r for r in s0_pass if pair_key(r) not in hold_keys]
    if set(s1_dispositions) != {pair_key(r) for r in rateable}:
        missing = len({pair_key(r) for r in rateable} - set(s1_dispositions))
        extra = len(set(s1_dispositions) - {pair_key(r) for r in rateable})
        raise ValueError(f"S1 coverage mismatch: missing={missing}, extra={extra}")

    passes = [r for r in rateable if s1_dispositions[pair_key(r)]["status"] == "pass"]
    conf_passes = [r for r in passes if not r["quarantined"]]
    quar_passes = [r for r in passes if r["quarantined"]]

    def classify_subset(sub: list[dict[str, Any]]) -> dict[str, Any]:
        by_problem: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for r in sub:
            by_problem[r.get("problem_id") or r["cluster_id"]].append(r)
        def _pid_h(pid: str) -> str:
            return sha256(pid.encode("utf-8")).hexdigest()[:16]

        reusable_oracle = [p for p in by_problem if _pid_h(p) in PATH_B_CASE_PY_HASHES]
        modest_adapt_oracle = [p for p in by_problem if _pid_h(p) in PATH_B_HIST_EXEC_HASHES]
        net_new_oracle = [p for p in by_problem if _pid_h(p) not in PATH_B_EXECUTED_PIE_HASHES]
        reusable_pairs = sum(len(by_problem[p]) for p in reusable_oracle)
        modest_pairs = sum(len(by_problem[p]) for p in modest_adapt_oracle)
        net_new_pairs = sum(len(by_problem[p]) for p in net_new_oracle)
        return {
            "total_pass_pairs": len(sub),
            "distinct_problems": len(by_problem),
            "by_corpus": dict(sorted(Counter(r["corpus"] for r in sub).items())),
            "oracle_workload_readiness": {
                "reusable_path_b_cases_py": {
                    "problems": len(reusable_oracle),
                    "pairs": reusable_pairs,
                    "problem_ids": sorted(reusable_oracle),
                },
                "modest_adapt_historical_driver": {
                    "problems": len(modest_adapt_oracle),
                    "pairs": modest_pairs,
                    "problem_ids": sorted(modest_adapt_oracle),
                },
                "net_new_oracle_and_workload_needed": {
                    "problems": len(net_new_oracle),
                    "pairs": net_new_pairs,
                },
            },
            "per_pair_work_needed": {
                "counter_restoration_sham_pairs": len(sub),
                "single_tu_pairs": sum(len(r["slow"]["files"]) == 1 and len(r["fast"]["files"]) == 1 for r in sub),
            },
            "top_multi_pair_problems": [
                {"problem_id": pid, "pairs": len(items)}
                for pid, items in sorted(by_problem.items(), key=lambda kv: (-len(kv[1]), kv[0]))[:15]
                if len(items) > 1
            ],
        }

    return {
        "total_rateable": len(rateable),
        "s1_status_counts": dict(sorted(Counter(v["status"] for v in s1_dispositions.values()).items())),
        "s1_bucket_counts": dict(
            sorted(Counter(str(v.get("bucket")) for v in s1_dispositions.values()).items())
        ),
        "all_passes": classify_subset(passes),
        "confirmatory_passes": classify_subset(conf_passes),
        "quarantined_passes": classify_subset(quar_passes),
    }


def _tex_int(n: int) -> str:
    return f"{n:,}".replace(",", "{,}")


def _tex_code(text: str) -> str:
    return r"\texttt{" + text.replace("_", r"\_") + "}"


def _tex_p_math(p: float) -> str:
    if p <= 0.0:
        return "< 10^{-300}"
    if p < 1e-3:
        mant, exp_str = f"{p:.2e}".split("e")
        return f"{mant} \\times 10^{{{int(exp_str)}}}"
    if p < 0.01:
        return f"{p:.4f}"
    return f"{p:.3f}"


def _tex_p(p: float | None, *, prefix: str = "p = ") -> str:
    if p is None:
        return r"\BenchCell"
    expr = _tex_p_math(p)
    if expr.startswith("< "):
        return f"${prefix.rstrip('= ')} {expr}$" if prefix else f"${expr}$"
    return f"${prefix}{expr}$"


def _tex_rate(r: dict[str, Any] | None) -> str:
    if not r or not r.get("total"):
        return r"\BenchCell"
    if r.get("count") is None or not r.get("clopper_pearson_95pct_percent"):
        return r"\BenchCell"
    lo, hi = r["clopper_pearson_95pct_percent"]
    return f'{_tex_int(r["count"])}/{_tex_int(r["total"])} = {r["percent"]:.1f}\\% (95\\% CP {lo:.1f}--{hi:.1f}\\%)'


def _tex_s1(v: float) -> str:
    return f"$-{abs(v):.1f}$" if v < 0 else f"{v:+.1f}"


def _tex_k3(v: float) -> str:
    return f"$-{abs(v):.3f}$" if v < 0 else f"{v:.3f}"


def _ols_log_ratio_fit(points: list[tuple[int, int | float, int | float]]) -> dict[str, Any] | None:
    pts = sorted(points, key=lambda item: item[0])
    if len(pts) < 4 or pts[0][0] <= 0 or pts[-1][0] < 8 * pts[0][0]:
        return None
    if any(n <= 0 or t <= 0 or r <= 0 for n, t, r in pts):
        return None
    xs = [math.log(n) for n, _, _ in pts]
    ys = [math.log(t / r) for _, t, r in pts]
    xb = math.fsum(xs) / len(xs)
    yb = math.fsum(ys) / len(ys)
    denom = math.fsum((x - xb) ** 2 for x in xs)
    if denom <= 0.0:
        return None
    slope = math.fsum((x - xb) * (y - yb) for x, y in zip(xs, ys)) / denom
    ss_err = math.fsum((y - yb - slope * (x - xb)) ** 2 for x, y in zip(xs, ys))
    ss_tot = math.fsum((y - yb) ** 2 for y in ys)
    _, t_last, r_last = pts[-1]
    return {
        "slope": slope,
        "largest_ratio": t_last / r_last,
        "r_squared": (1.0 - ss_err / ss_tot) if ss_tot > 0.0 else None,
    }


def _t_cdf_two_sided_p(t_abs: float, df: int) -> float:
    if df <= 0:
        return 1.0
    if not math.isfinite(t_abs):
        return 0.0
    if df == 2:
        cdf = 0.5 + t_abs / (2.0 * math.sqrt(2.0 + t_abs * t_abs))
        return max(0.0, 2.0 * (1.0 - cdf))
    if df == 3:
        th = math.atan(t_abs / math.sqrt(3.0))
        cdf = 0.5 + (th + math.sin(th) * math.cos(th)) / math.pi
        return max(0.0, 2.0 * (1.0 - cdf))
    if df == 4:
        u = math.sqrt(1.0 + t_abs * t_abs / 4.0)
        cdf = 0.5 + (3.0 / 8.0) * (t_abs / u) * (1.0 - (t_abs * t_abs) / (12.0 * (1.0 + t_abs * t_abs / 4.0)))
        return max(0.0, 2.0 * (1.0 - cdf))
    c = math.gamma((df + 1) / 2.0) / (math.sqrt(df * math.pi) * math.gamma(df / 2.0))
    n_steps = 2000
    h = t_abs / n_steps
    s = 0.0
    for i in range(n_steps + 1):
        u = i * h
        w = 1 if i in (0, n_steps) else (4 if i % 2 == 1 else 2)
        s += w * (1.0 + (u * u) / df) ** (-(df + 1) / 2.0)
    cdf = 0.5 + c * s * h / 3.0
    return max(0.0, min(1.0, 2.0 * (1.0 - cdf)))


def _ols_full_diagnostics(points: list[tuple[int, int, int]]) -> dict[str, Any]:
    xs = [math.log(n) for n, _, _ in points]
    ys = [math.log(t / r) for _, t, r in points]
    k = len(points)
    mx = math.fsum(xs) / k
    my = math.fsum(ys) / k
    sxx = math.fsum((x - mx) ** 2 for x in xs)
    sxy = math.fsum((x - mx) * (y - my) for x, y in zip(xs, ys))
    syy = math.fsum((y - my) ** 2 for y in ys)
    slope = sxy / sxx if sxx > 0.0 else 0.0
    resids = [y - (my + slope * (x - mx)) for x, y in zip(xs, ys)]
    sse = max(0.0, math.fsum(e * e for e in resids))
    r2 = 1.0 - sse / syy if syy > 1e-18 else None
    df = k - 2
    t_crit_map = {
        1: 12.706204736432095, 2: 4.30265272974946, 3: 3.182446305284263, 4: 2.7764451051977987,
        5: 2.570581835636314, 6: 2.446911851144969, 7: 2.3646242515927844, 8: 2.306004135204166,
        9: 2.262157162798205, 10: 2.228138851986273, 11: 2.200985160091639, 12: 2.178812829667229,
        13: 2.160368656462792, 14: 2.144786687917803, 15: 2.131449545559775, 16: 2.119905299221255,
        17: 2.109815577833319, 18: 2.100922040241043, 19: 2.093024054408309, 20: 2.085963447265862,
    }
    if df > 0 and df not in t_crit_map:
        raise ValueError(f"Unsupported degrees of freedom df={df} for exact t critical value")
    t_crit = t_crit_map.get(df, 1.959963984540054)
    if df > 0 and sse > 1e-18 and sxx > 0.0:
        mse = sse / df
        se = math.sqrt(mse / sxx)
        t_stat = slope / se
        p_val = _t_cdf_two_sided_p(abs(t_stat), df)
    elif df > 0 and abs(slope) > 1e-12:
        mse = 0.0
        se = 0.0
        t_stat = math.copysign(float("inf"), slope)
        p_val = 0.0
    else:
        mse = 0.0
        se = 0.0
        t_stat = 0.0
        p_val = 1.0
    ci_lo = slope - t_crit * se
    ci_hi = slope + t_crit * se
    pair_slopes = [
        (ys[j] - ys[i]) / (xs[j] - xs[i])
        for i, j in combinations(range(k), 2)
        if xs[j] != xs[i]
    ]
    ts_slope = statistics.median(pair_slopes) if pair_slopes else 0.0
    h_vals = [(1.0 / k + ((x - mx) ** 2) / sxx) if sxx > 0.0 else 1.0 / k for x in xs]
    h_last = h_vals[-1]
    cooks_all = [
        ((rv ** 2) / (2.0 * mse)) * (hv / ((1.0 - hv) ** 2)) if (mse > 1e-18 and hv < 1.0) else 0.0
        for rv, hv in zip(resids, h_vals)
    ]
    cooks_last = cooks_all[-1]
    cooks_max = max(cooks_all) if cooks_all else 0.0
    if k >= 3:
        xs_l, ys_l = xs[:-1], ys[:-1]
        mxl, myl = math.fsum(xs_l) / (k - 1), math.fsum(ys_l) / (k - 1)
        sxx_l = math.fsum((x - mxl) ** 2 for x in xs_l)
        beta_loo = (math.fsum((x - mxl) * (y - myl) for x, y in zip(xs_l, ys_l)) / sxx_l) if sxx_l > 0.0 else 0.0
    else:
        beta_loo = slope
    ratios = [t / r for _, t, r in points]
    mr = math.fsum(ratios) / k
    srx = math.fsum((x - mx) * (rv - mr) for x, rv in zip(xs, ratios))
    srr = math.fsum((rv - mr) ** 2 for rv in ratios)
    log_slope = srx / sxx if sxx > 0.0 else 0.0
    sse_log = max(0.0, math.fsum((rv - (mr + log_slope * (x - mx))) ** 2 for x, rv in zip(xs, ratios)))
    r2_logn = 1.0 - sse_log / srr if srr > 1e-18 else 0.0
    return {
        "slope": slope,
        "se": se,
        "ci_lo": ci_lo,
        "ci_hi": ci_hi,
        "t_stat": t_stat,
        "p_value": p_val,
        "r_squared": r2,
        "theil_sen_slope": ts_slope,
        "largest_ratio": points[-1][1] / points[-1][2],
        "max_leverage": h_last,
        "cooks_d_last": cooks_last,
        "cooks_d_max": cooks_max,
        "beta_loo": beta_loo,
        "delta_beta_loo": slope - beta_loo,
        "r2_logn": r2_logn,
    }


def _fisher_two_sided_exact(a: int, b: int, c: int, d: int) -> float:
    r1, r2 = a + b, c + d
    c1, n = a + c, a + b + c + d
    denom = comb(n, c1)
    if denom == 0:
        return 1.0

    def prob(x: int) -> float:
        return (comb(r1, x) * comb(r2, c1 - x)) / denom

    p0 = prob(a)
    lo, hi = max(0, c1 - r2), min(r1, c1)
    return min(1.0, sum(prob(x) for x in range(lo, hi + 1) if prob(x) <= p0 * (1.0 + 1e-12)))


def _mcnemar_exact(b: int, c: int) -> float:
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    return min(1.0, float(Decimal(2) * Decimal(sum(comb(n, i) for i in range(k + 1))) / (Decimal(2) ** n)))


def _irr_from_3x3(cm: dict[str, dict[str, int]]) -> dict[str, Any]:
    cats = ("pass", "contract", "source")
    n = sum(int(cm.get(r, {}).get(c, 0)) for r in cats for c in cats)
    if n == 0:
        return {"n": 0}
    diag3 = sum(int(cm.get(k, {}).get(k, 0)) for k in cats)
    po3 = diag3 / n
    row_m = [sum(int(cm.get(r, {}).get(c, 0)) for c in cats) for r in cats]
    col_m = [sum(int(cm.get(r, {}).get(c, 0)) for r in cats) for c in cats]
    pe3 = sum(r * c for r, c in zip(row_m, col_m)) / (n * n)
    k3 = (po3 - pe3) / (1.0 - pe3) if pe3 < 1.0 else (1.0 if po3 == 1.0 else 0.0)
    pmax3 = sum(min(r, c) for r, c in zip(row_m, col_m)) / n
    kmax3 = (pmax3 - pe3) / (1.0 - pe3) if pe3 < 1.0 else (1.0 if pmax3 == 1.0 else 0.0)
    pabak3 = (3 * po3 - 1.0) / 2.0
    pi_ave3 = [(r + c) / (2.0 * n) for r, c in zip(row_m, col_m)]
    pe_ac1_3 = sum(pi * (1.0 - pi) for pi in pi_ave3) / 2.0
    ac1_3 = (po3 - pe_ac1_3) / (1.0 - pe_ac1_3) if pe_ac1_3 < 1.0 else (1.0 if po3 == 1.0 else 0.0)

    # Binary pass vs stop (contract + source)
    a = int(cm.get("pass", {}).get("pass", 0))
    b = int(cm.get("pass", {}).get("contract", 0)) + int(cm.get("pass", {}).get("source", 0))
    c = int(cm.get("contract", {}).get("pass", 0)) + int(cm.get("source", {}).get("pass", 0))
    d = n - a - b - c
    po2 = (a + d) / n
    pe2 = ((a + b) * (a + c) + (c + d) * (b + d)) / (n * n)
    k2 = (po2 - pe2) / (1.0 - pe2) if pe2 < 1.0 else (1.0 if po2 == 1.0 else 0.0)
    pabak2 = 2.0 * po2 - 1.0
    pi1 = ((a + b) + (a + c)) / (2.0 * n)
    pe_ac1_2 = 2.0 * pi1 * (1.0 - pi1)
    ac1_2 = (po2 - pe_ac1_2) / (1.0 - pe_ac1_2) if pe_ac1_2 < 1.0 else 0.0
    bi2 = abs(b - c) / n
    pi2 = abs(a - d) / n
    mcn_p = _mcnemar_exact(b, c)
    bowker_q = 0.0
    off_pairs: list[int] = []
    for i, r in enumerate(cats):
        for j in range(i + 1, len(cats)):
            c_name = cats[j]
            nij = int(cm.get(r, {}).get(c_name, 0))
            nji = int(cm.get(c_name, {}).get(r, 0))
            if nij + nji > 0:
                bowker_q += ((nij - nji) ** 2) / (nij + nji)
                off_pairs.append(nij + nji)
    # exact chi-square df=3 tail: P(chi^2_3 >= q) = erfc(sqrt(q/2)) + sqrt(2*q/pi)*exp(-q/2)
    bowker_p = math.erfc(math.sqrt(bowker_q / 2.0)) + math.sqrt(2.0 * bowker_q / math.pi) * math.exp(-bowker_q / 2.0) if bowker_q > 0 else 1.0
    # Exact conditional Bowker binomial symmetry p-value over independent Bin(n_k, 0.5) pairs
    bowker_exact_p = bowker_p
    if off_pairs and sum(off_pairs) <= 40:
        dist: dict[float, int] = {0.0: 1}
        for tot_n in off_pairs:
            nxt: dict[float, int] = {}
            for q_prev, w_prev in dist.items():
                for x_i in range(tot_n + 1):
                    q_new = round(q_prev + ((2 * x_i - tot_n) ** 2) / tot_n, 9)
                    nxt[q_new] = nxt.get(q_new, 0) + w_prev * math.comb(tot_n, x_i)
            dist = nxt
        q_thresh = round(bowker_q, 9) - 1e-12
        tail_w = sum(w for qv, w in dist.items() if qv >= q_thresh)
        bowker_exact_p = tail_w / (1 << sum(off_pairs))
    return {
        "n": n,
        "bucket_agree_count": diag3,
        "bucket_agree_pct": round(100.0 * po3, 1),
        "bucket_kappa": round(k3, 3),
        "bucket_kappa_max": round(kmax3, 3),
        "bucket_pabak": round(pabak3, 3),
        "bucket_gwet_ac1": round(ac1_3, 3),
        "binary_matrix": [[a, b], [c, d]],
        "binary_agree_count": a + d,
        "binary_agree_pct": round(100.0 * po2, 1),
        "binary_kappa": round(k2, 3),
        "binary_pabak": round(pabak2, 3),
        "binary_gwet_ac1": round(ac1_2, 3),
        "binary_bias_index": round(bi2, 3),
        "binary_prevalence_index": round(pi2, 3),
        "binary_mcnemar_p": mcn_p,
        "bowker_exact_p": bowker_exact_p,
        "bowker_q_df3": round(bowker_q, 2),
        "bowker_p": bowker_p,
        "contract_to_author_pass_count": int(cm.get("contract", {}).get("pass", 0)),
        "contract_total": sum(int(cm.get("contract", {}).get(x, 0)) for x in cats),
    }


def verify_anon_and_forensics(
    forensics: dict[str, Any],
    anon_rows: list[dict[str, Any]] | None,
    report: dict[str, Any],
    author_check: dict[str, Any] | None = None,
    manifest: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Validate identifier-free forensics JSON and cross-verify against raw anonymous measurements."""
    if forensics.get("schema") != "eapg.expansion.forensics.agg.v1":
        raise ValueError(f"Unexpected forensics schema: {forensics.get('schema')!r}")
    prov = forensics.get("provenance") or {}
    lc = prov.get("leak_check") or {}
    if lc.get("identifier_matches", 0) != 0 or lc.get("per_case_author_records", 0) != 0:
        raise ValueError(f"Forensics leak check non-zero: {lc}")

    prim = report["primary_all_post_s0"]
    s13 = report["S13_without_desk_unrateable"]
    b1_fp_decomp: Counter[str] = Counter()
    deep_forensics: dict[str, Any] = {}

    if anon_rows is not None:
        if len(anon_rows) != 1000:
            raise ValueError(f"Expected 1000 anonymous measurement records, got {len(anon_rows)}")
        if sum(1 for r in anon_rows if r.get("S0_stop")) != 23:
            raise ValueError("S0_stop count mismatch in anonymous-measurements.json")
        if sum(1 for r in anon_rows if not r.get("S0_stop") and r.get("quarantined")) != 500:
            raise ValueError("Quarantined count mismatch in anonymous-measurements.json")

        conf = [r for r in anon_rows if not r.get("S0_stop") and not r.get("quarantined")]
        sides = ("target", "reference", "restored", "sham")
        modes = ("plain", "ubsan", "O0", "O2", "O3")
        o_agree = o_dis = o_cap = o_cap_events = o_oracle_abort = o_overlay_fix = o_infra_miss = 0
        s_agree = s_dis = s_cap = s_cap_events = s_oracle_abort = s_overlay_fix = s_infra_miss = 0
        cap_by_sm: Counter[tuple[str, str, str]] = Counter()
        cpu_cap_o0_only_pts = 0
        cpu_cap_total_pts = 0
        o2_o3_agree_on_o0_capped = 0
        o2_o3_disagree_on_o0_capped = 0
        oracle_prior_pf_pos: list[int] = []
        other_noncap_pf_pos: list[int] = []
        fitted_masked_failure_cnt = 0
        pf_rc_0_pos: list[int] = []
        pf_rc_134_pos: list[int] = []
        pf_rc_139_pos: list[int] = []

        max_parsed_counter = max(
            (int(val) for r in anon_rows for e in (r.get("measurements") or []) for val in (e.get("counter") or [])),
            default=0,
        )
        counters_ge_2_pow_64 = sum(
            1 for r in anon_rows for e in (r.get("measurements") or []) for val in (e.get("counter") or []) if int(val) >= (1 << 64)
        )
        if counters_ge_2_pow_64 != 0:
            raise ValueError(f"Found {counters_ge_2_pow_64} parsed counters >= 2^64")

        for row in conf:
            if not row.get("measurements"):
                continue
            et_row = row.get("effective_terminal")
            is_non_exec_fix = et_row == "fixture_stop"
            is_non_exec_inf = et_row == "execution_infrastructure_failure"
            is_oracle_abort = et_row == "execution_oracle_failure"
            exec_meas = [e for e in row["measurements"] if e["step"][0] == "execute"]
            grid = {tuple(e["step"][1:]): e for e in exec_meas}
            pf_rcs = {e.get("exit") for e in exec_meas if e.get("status") == "process_failure"}
            if pf_rcs:
                p_int = int(row["position"])
                if 0 in pf_rcs:
                    pf_rc_0_pos.append(p_int)
                if 134 in pf_rcs:
                    pf_rc_134_pos.append(p_int)
                if 139 in pf_rcs:
                    pf_rc_139_pos.append(p_int)
            first_pf_idx = next((idx_e for idx_e, e in enumerate(exec_meas) if e.get("status") in ("process_failure", "invalid_counter")), None)
            first_io_idx = next((idx_e for idx_e, e in enumerate(exec_meas) if e.get("status") == "invalid_output"), None)
            if first_pf_idx is not None:
                if is_oracle_abort and first_io_idx is not None and first_pf_idx < first_io_idx:
                    oracle_prior_pf_pos.append(int(row["position"]))
                elif not is_oracle_abort:
                    other_noncap_pf_pos.append(int(row["position"]))
                    if et_row in ("alert", "no_alert"):
                        fitted_masked_failure_cnt += 1
            for e in exec_meas:
                for cap in (e.get("caps") or []):
                    cap_by_sm[(str(cap), str(e["step"][2]), str(e["step"][3]))] += 1
                if e.get("status") in ("cpu_cap", "tick_cap"):
                    cap_by_sm[(str(e["status"]), str(e["step"][2]), str(e["step"][3]))] += 1
            for idx in range(len(row["samples"])):
                any_cpu_cap_pt = any(
                    grid.get((idx, s, m)) is not None and (
                        grid[idx, s, m]["status"] == "cpu_cap" or "cpu_cap" in (grid[idx, s, m].get("caps") or [])
                    )
                    for s in sides for m in modes
                )
                if any_cpu_cap_pt:
                    cpu_cap_total_pts += 1
                    all_non_o0_ok = all(
                        grid.get((idx, s, m)) is not None and grid[idx, s, m]["status"] == "complete"
                        for s in sides for m in ("plain", "ubsan", "O2", "O3")
                    )
                    if all_non_o0_ok:
                        cpu_cap_o0_only_pts += 1

                for side in sides:
                    pts = [grid.get((idx, side, m)) for m in ("O0", "O2", "O3")]
                    if all(p is not None and p["status"] == "complete" for p in pts):
                        vals = [p["counter"] for p in pts]
                        if vals[0] == vals[1] == vals[2]:
                            o_agree += 1
                        else:
                            o_dis += 1
                    else:
                        o_cap += 1
                        e0, e2, e3 = pts
                        if (
                            e0 is not None and e0.get("status") == "capped"
                            and "cpu_cap" in (e0.get("caps") or [])
                            and e2 is not None and e2.get("status") == "complete"
                            and e3 is not None and e3.get("status") == "complete"
                        ):
                            if e2["counter"] == e3["counter"]:
                                o2_o3_agree_on_o0_capped += 1
                            else:
                                o2_o3_disagree_on_o0_capped += 1
                        if is_non_exec_fix:
                            o_overlay_fix += 1
                        elif is_non_exec_inf:
                            o_infra_miss += 1
                        elif any(p is not None and (p.get("status") in ("capped", "cpu_cap", "tick_cap") or p.get("caps")) for p in pts):
                            o_cap_events += 1
                        elif is_oracle_abort:
                            o_oracle_abort += 1
                        else:
                            raise ValueError(f"Unclassified O0/O2/O3 missing triple at pos {row['position']} ({et_row})")
                for m in ("O0", "O2", "O3"):
                    tp, sp = grid.get((idx, "target", m)), grid.get((idx, "sham", m))
                    if tp is not None and sp is not None and tp["status"] == "complete" and sp["status"] == "complete":
                        if tp["counter"] == sp["counter"]:
                            s_agree += 1
                        else:
                            s_dis += 1
                    else:
                        s_cap += 1
                        if is_non_exec_fix:
                            s_overlay_fix += 1
                        elif is_non_exec_inf:
                            s_infra_miss += 1
                        elif any(p is not None and (p.get("status") in ("capped", "cpu_cap", "tick_cap") or p.get("caps")) for p in (tp, sp)):
                            s_cap_events += 1
                        elif is_oracle_abort:
                            s_oracle_abort += 1
                        else:
                            raise ValueError(f"Unclassified target-sham missing triple at pos {row['position']} ({et_row})")

        if o_cap_events + o_oracle_abort + o_overlay_fix + o_infra_miss != o_cap:
            raise ValueError("O0/O2/O3 4-way missing partition sum mismatch")
        if s_cap_events + s_oracle_abort + s_overlay_fix + s_infra_miss != s_cap:
            raise ValueError("target-sham 4-way missing partition sum mismatch")

        if o_dis != 0 or s_dis != 0:
            raise ValueError(f"Counter invariance disagreement detected: O0/O2/O3={o_dis}, sham={s_dis}")
        exec_chk = prim.get("execution_checks") or {}
        if exec_chk.get("o0_o2_o3_agreement"):
            exp_o = exec_chk["o0_o2_o3_agreement"]
            if (o_agree, o_cap) != (exp_o["agree"], exp_o["capped_or_missing"]):
                raise ValueError(f"O0/O2/O3 replay mismatch: {(o_agree, o_cap)} != {exp_o}")
        if exec_chk.get("target_vs_sham"):
            exp_s = exec_chk["target_vs_sham"]
            if (s_agree, s_cap) != (exp_s["agree"], exp_s["capped_or_missing"]):
                raise ValueError(f"target_vs_sham replay mismatch: {(s_agree, s_cap)} != {exp_s}")
        cr_obj = (author_check or {}).get("execution_policy_checks") or (author_check or {}).get("camera_ready_checks")
        if cr_obj:
            cr_ag = cr_obj["agreement"]
            if (o_agree, o_dis, o_cap) != (
                cr_ag["O0_O2_O3"]["agree"],
                cr_ag["O0_O2_O3"]["disagree"],
                cr_ag["O0_O2_O3"]["capped_or_missing"],
            ):
                raise ValueError("Execution-check O0/O2/O3 agreement disagrees with anonymous-measurements.json")

        by_cluster: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for row in conf:
            by_cluster[int(row["cluster"])].append(row)
        reps = [min(items, key=lambda r: int(r["ordinal"])) for items in by_cluster.values()]

        # 1. 17 execution_oracle_failure breakdown (strictly on invalid_output + concurrent plain SIGSEGV disclosure)
        oracle_reps = sorted([r for r in reps if r.get("effective_terminal") == "execution_oracle_failure"], key=lambda r: int(r["position"]))
        or_plain_tgt = or_plain_ref = or_ub_tgt = or_ub_ref = or_ub_all_tgt = or_ub_all_ref = or_rest = or_sham = 0
        or_plain_segv_and_ub = 0
        or_plain_segv_ub_pos = 0
        or_multi_events = 0
        inv_out_mode_exits: Counter[tuple[str, Any]] = Counter()
        for r in oracle_reps:
            bad = [e for e in (r.get("measurements") or []) if e["step"][0] == "execute" and e["status"] != "complete"]
            invs = [e for e in bad if e.get("status") == "invalid_output"]
            pfs = [e for e in bad if e.get("status") == "process_failure"]
            for be in invs:
                inv_out_mode_exits[(str(be["step"][3]), be.get("exit"))] += 1
            if len(bad) > 1:
                or_multi_events += 1
            p_sides = {e["step"][2] for e in invs if e["step"][3] == "plain"}
            u_sides = {e["step"][2] for e in invs if e["step"][3] == "ubsan"}
            p_pf_sides = {e["step"][2] for e in pfs if e["step"][3] == "plain"}
            if "restored" in p_sides or "restored" in u_sides:
                or_rest += 1
            elif "sham" in p_sides or "sham" in u_sides:
                or_sham += 1
            elif p_sides:
                if "target" in p_sides:
                    or_plain_tgt += 1
                elif "reference" in p_sides:
                    or_plain_ref += 1
                else:
                    raise ValueError(f"Unexpected plain oracle side set {p_sides} at pos {r['position']}")
            elif u_sides:
                if "target" in u_sides:
                    or_ub_all_tgt += 1
                    if "target" in p_pf_sides:
                        or_plain_segv_and_ub += 1
                        or_plain_segv_ub_pos = int(r["position"])
                    else:
                        or_ub_tgt += 1
                elif "reference" in u_sides:
                    or_ub_all_ref += 1
                    if "reference" in p_pf_sides:
                        or_plain_segv_and_ub += 1
                        or_plain_segv_ub_pos = int(r["position"])
                    else:
                        or_ub_ref += 1
                else:
                    raise ValueError(f"Unexpected ubsan oracle side set {u_sides} at pos {r['position']}")
            else:
                raise ValueError(f"Oracle failure at pos {r['position']} had no invalid_output event")
        or_upstream = or_plain_tgt + or_plain_ref + or_ub_all_tgt + or_ub_all_ref
        if or_upstream + or_rest + or_sham != len(oracle_reps):
            raise ValueError("Oracle failure partition mismatch")
        if inv_out_mode_exits.get(("plain", 0), 0) != or_plain_tgt + or_plain_ref + or_rest:
            raise ValueError("Plain invalid_output reconciliation mismatch")
        if inv_out_mode_exits.get(("ubsan", 1), 0) != or_ub_all_tgt + or_ub_all_ref:
            raise ValueError("UBSan invalid_output reconciliation mismatch")

        pos27_row = next((r for r in reps if r.get("position") is not None and int(r["position"]) == 27), None)
        pos27_o0_sigabrt_o2_clean = False
        if pos27_row:
            g27 = {tuple(e["step"][1:]): e for e in pos27_row.get("measurements") or [] if e["step"][0] == "execute"}
            pos27_o0_sigabrt_o2_clean = (
                all(g27.get((0, sd, md)) and g27[0, sd, md].get("status") == "complete" and g27[0, sd, md].get("exit") == 0 for sd in sides for md in ("plain", "ubsan", "O2", "O3"))
                and all(g27.get((0, sd, "O0")) and g27[0, sd, "O0"].get("status") == "process_failure" and g27[0, sd, "O0"].get("exit") == 134 for sd in ("target", "restored", "sham"))
            )

        # 2. 8 insufficient_fit breakdown (evaluate >=2 uncapped points on c0 + B3 check on all 8)
        insuf_reps = sorted([r for r in reps if r.get("effective_terminal") == "insufficient_fit"], key=lambda r: int(r["position"]))
        ins_q_zero = ins_both_zero = ins_tick_cap = 0
        ins_censor_alert = 0
        b3_insuf_hits = 0
        for r in insuf_reps:
            grid = {tuple(e["step"][1:]): e for e in r["measurements"] if e["step"][0] == "execute"}
            stot = defaultdict(list)
            sc0 = defaultdict(list)
            for idx, samp in enumerate(r["samples"]):
                if all(grid.get((idx, s, m)) and grid[idx, s, m]["status"] == "complete" for s in sides for m in modes):
                    t0, t1 = grid[idx, "target", "O2"]["counter"]
                    q0, q1 = grid[idx, "reference", "O2"]["counter"]
                    sc0[int(samp["stream"])].append((int(samp["size"]), t0, q0))
                    stot[int(samp["stream"])].append((int(samp["size"]), t0 + t1, q0 + q1))
            if len(stot) == 3:
                if all((_ols_log_ratio_fit(sorted(stot[s])) or {}).get("slope", -1.0) >= 0.50 and (_ols_log_ratio_fit(sorted(stot[s])) or {}).get("largest_ratio", 0.0) >= 1.50 for s in sorted(stot)):
                    b3_insuf_hits += 1
            has_tcap = any("tick_cap" in (e.get("caps") or []) or e["status"] == "tick_cap" for e in grid.values())
            if has_tcap:
                ins_tick_cap += 1
                pos_c0 = []
                for s in sorted(sc0):
                    valid0 = [(n, t, q) for n, t, q in sorted(sc0[s]) if t > 0 and q > 0]
                    if len(valid0) >= 2:
                        xs0 = [math.log(n) for n, _, _ in valid0]
                        ys0 = [math.log(t / q) for _, t, q in valid0]
                        mx0, my0 = sum(xs0) / len(xs0), sum(ys0) / len(ys0)
                        vx0 = sum((x - mx0) ** 2 for x in xs0)
                        sl0 = sum((x - mx0) * (y - my0) for x, y in zip(xs0, ys0)) / vx0 if vx0 > 0 else 0.0
                        lr0 = valid0[-1][1] / valid0[-1][2]
                        pos_c0.append((sl0, lr0))
                if pos_c0 and any(sl >= 0.45 and lr >= 1.50 for sl, lr in pos_c0):
                    ins_censor_alert += 1
            else:
                o2_pts = [(grid[idx, "target", "O2"]["counter"][0], grid[idx, "reference", "O2"]["counter"][0])
                          for idx in range(len(r["samples"]))
                          if (idx, "target", "O2") in grid and (idx, "reference", "O2") in grid
                          and grid[idx, "target", "O2"].get("status") == "complete"
                          and grid[idx, "reference", "O2"].get("status") == "complete"
                          and grid[idx, "target", "O2"].get("counter") is not None
                          and grid[idx, "reference", "O2"].get("counter") is not None]
                z_t = sum(1 for t0, _ in o2_pts if t0 == 0)
                z_q = sum(1 for _, q0 in o2_pts if q0 == 0)
                if z_t == 0 and z_q > 0:
                    ins_q_zero += 1
                else:
                    ins_both_zero += 1

        # 3. 124 fitted representatives deep audit
        fitted = sorted(
            [r for r in reps if r.get("effective_terminal") in ("alert", "no_alert")],
            key=lambda r: int(r["position"]),
        )
        if len(fitted) != 124:
            raise ValueError(f"Expected 124 confirmatory fitted representatives, got {len(fitted)}")

        dist_counts = {"all_124": Counter(), "alerts_6": Counter(), "no_alerts_118": Counter()}
        b0 = b1 = b2 = b3 = s7_cnt = 0
        dl_alerts: Counter[str] = Counter()
        dl_no_alerts: Counter[str] = Counter()
        s8_any_admitted = s8_any_alerts = 0
        alert_by_pos: dict[int, dict[str, Any]] = {}
        regime_counts: Counter[str] = Counter()
        min_slopes: list[float] = []
        min_ratios: list[float] = []
        beta_grid = {b: 0 for b in (0.10, 0.20, 0.30, 0.40, 0.50, 0.75, 1.00)}
        c1_only_hits: list[dict[str, Any]] = []
        q1_zero_t0_eq_q0_pos: list[int] = []
        t1_lt_q1_pos: list[int] = []
        rest_cats: Counter[str] = Counter()
        rest_tot_cats: Counter[str] = Counter()
        rest_tot_new_testable = 0
        rest_c0_fail_to_tot_pass = 0
        non_exact_pass_regimes: Counter[str] = Counter()
        all_pt_excess_fail_n = 0
        all_pt_r1_infl_n = 0
        all_pt_max_bound_fail_n = 0
        all_pt_nonreg_r0_pos: list[int] = []
        b2_only_info: list[dict[str, Any]] = []
        distinct1_c1_var = 0
        distinct1_obliv = 0
        pos77_log_r2 = 0.0
        pair_min_r2_all: list[float] = []
        pair_med_r2_all: list[float] = []
        alert_pair_min_r2: list[float] = []
        pair_all_zv_n = 0
        stream_pt_counts: Counter[int] = Counter()
        cpu_cap_fitted_pos: list[int] = []

        for row in fitted:
            pos = int(row["position"])
            is_alert = row["effective_terminal"] == "alert"
            grid = {tuple(e["step"][1:]): e for e in row["measurements"] if e["step"][0] == "execute"}
            if any(e.get("status") == "cpu_cap" or "cpu_cap" in (e.get("caps") or []) for e in grid.values()):
                cpu_cap_fitted_pos.append(pos)
            streams_c0: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
            streams_c1: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
            streams_tot: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
            streams_rest: dict[int, list[tuple[int, int, int, int, int, int, int]]] = defaultdict(list)
            exact_rest_eq_ref = True
            for idx, samp in enumerate(row["samples"]):
                side_vals = {}
                for side in sides:
                    pts = [grid[idx, side, m] for m in modes]
                    if all(p["status"] == "complete" for p in pts):
                        side_vals[side] = pts[2]["counter"]
                if len(side_vals) == 4:
                    sz = int(samp["size"])
                    st_id = int(samp["stream"])
                    t0, t1 = int(side_vals["target"][0]), int(side_vals["target"][1])
                    q0, q1 = int(side_vals["reference"][0]), int(side_vals["reference"][1])
                    r0, r1 = int(side_vals["restored"][0]), int(side_vals["restored"][1])
                    if (r0, r1) != (q0, q1):
                        exact_rest_eq_ref = False
                    streams_c0[st_id].append((sz, t0, q0))
                    streams_c1[st_id].append((sz, t1, q1))
                    streams_tot[st_id].append((sz, t0 + t1, q0 + q1))
                    streams_rest[st_id].append((sz, t0, q0, r0, t1, q1, r1))

            trajs = set()
            c0_fits = []
            c0_diag = []
            tot_fits = []
            tot_diag = []
            dl_fits = []
            c1_fits = []
            pair_r2_vals: list[float] = []
            pair_zv_streams = 0
            for st_id in sorted(streams_c0):
                pts0 = sorted(streams_c0[st_id])
                ptst = sorted(streams_tot[st_id])
                pts1 = sorted(streams_c1[st_id])
                trajs.add(tuple(pts0))
                stream_pt_counts[len(pts0)] += 1
                f0 = _ols_log_ratio_fit(pts0)
                ft = _ols_log_ratio_fit(ptst)
                fd = _ols_log_ratio_fit(pts0[:-1])
                if f0 is None or ft is None:
                    raise ValueError(f"Unexpected inadmissible fitted stream at pos {row['position']}")
                c0_fits.append(f0)
                d0 = _ols_full_diagnostics(pts0)
                c0_diag.append(d0)
                if d0.get("r_squared") is None:
                    pair_zv_streams += 1
                else:
                    pair_r2_vals.append(float(d0["r_squared"]))
                tot_fits.append(ft)
                tot_diag.append(_ols_full_diagnostics(ptst))
                dl_fits.append(fd)
                c1_fits.append(_ols_log_ratio_fit(pts1))
            if pair_zv_streams == len(streams_c0):
                pair_all_zv_n += 1
            if pair_r2_vals:
                pair_min_r2_all.append(min(pair_r2_vals))
                pair_med_r2_all.append(float(statistics.median(pair_r2_vals)))
                if is_alert:
                    alert_pair_min_r2.append(min(pair_r2_vals))
            if pos == 77 and c0_diag:
                pos77_log_r2 = round(min(d["r2_logn"] for d in c0_diag), 3)

            if len(trajs) == 1:
                trajs1 = {tuple(sorted(streams_c1[st_id])) for st_id in sorted(streams_c1)}
                if len(trajs1) > 1:
                    distinct1_c1_var += 1
                else:
                    distinct1_obliv += 1

            d_key = f"{len(trajs)}_distinct"
            dist_counts["all_124"][d_key] += 1
            dist_counts["alerts_6" if is_alert else "no_alerts_118"][d_key] += 1

            p_dual = all(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in c0_fits)
            if p_dual != is_alert:
                raise ValueError(f"Primary alert replay mismatch at position {row['position']}")
            s7_hit = any(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in c0_fits)
            if s7_hit:
                s7_cnt += 1
            b0 += p_dual
            b1_hit = all(f["largest_ratio"] >= 1.50 for f in c0_fits)
            b1 += b1_hit
            if b1_hit and not p_dual:
                slopes_0 = [f["slope"] for f in c0_fits]
                if s7_hit:
                    b1_fp_decomp["s7_stream_selective"] += 1
                elif max(slopes_0) <= -0.10:
                    b1_fp_decomp["negative_slope_precomp"] += 1
                elif all(abs(sv) <= 0.05 for sv in slopes_0):
                    b1_fp_decomp["flat_constant_factor"] += 1
                else:
                    b1_fp_decomp["positive_subthreshold"] += 1
            b2_hit = all(f["slope"] >= 0.50 for f in c0_fits)
            b2 += b2_hit
            if b2_hit and not p_dual:
                b2_only_info.append({
                    "position": pos,
                    "slope_range": [round(min(f["slope"] for f in c0_fits), 2), round(max(f["slope"] for f in c0_fits), 2)],
                    "ratio_range": [round(min(f["largest_ratio"] for f in c0_fits), 2), round(max(f["largest_ratio"] for f in c0_fits), 2)],
                })
            t_dual = all(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in tot_fits)
            b3 += t_dual

            ms = min(f["slope"] for f in c0_fits)
            mr = min(f["largest_ratio"] for f in c0_fits)
            min_slopes.append(ms)
            min_ratios.append(mr)
            for bv in beta_grid:
                if all(f["slope"] >= bv and f["largest_ratio"] >= 1.50 for f in c0_fits):
                    beta_grid[bv] += 1

            all_eq = all(p[1] == p[2] for st_id in streams_c0 for p in streams_c0[st_id])
            any_rev = any(f["largest_ratio"] < 0.99 or f["slope"] <= -0.10 for f in c0_fits)
            if is_alert:
                regime_lbl = "all_stream_alert"
            elif s7_hit:
                regime_lbl = "s7_stream_selective"
            elif all_eq:
                regime_lbl = "exact_identity_T_eq_Q"
            elif all(abs(f["slope"]) <= 0.05 for f in c0_fits):
                regime_lbl = "flat_constant_factor_ge_1.5" if b1_hit else "flat_near_1_lt_1.5"
            elif max(f["slope"] for f in c0_fits) <= -0.10:
                regime_lbl = "negative_slope_all_streams"
            elif any(f["slope"] > 0.05 for f in c0_fits) and not any_rev:
                regime_lbl = "positive_sub50_regime"
            else:
                regime_lbl = "mixed_or_reversed"
            regime_counts[regime_lbl] += 1

            if any(cf and cf["slope"] >= 0.50 and cf["largest_ratio"] >= 1.50 for cf in c1_fits) and not is_alert:
                hit_sts = [
                    (idx_c1 + 1, cf)
                    for idx_c1, cf in enumerate(c1_fits)
                    if cf and cf["slope"] >= 0.50 and cf["largest_ratio"] >= 1.50
                ]
                best_st_i, best_cf = max(hit_sts, key=lambda x: x[1]["largest_ratio"])
                c1_only_hits.append({
                    "position": pos,
                    "stream": f"W{best_st_i}",
                    "max_c1_slope": round(max(cf["slope"] for cf in c1_fits if cf), 2),
                    "max_c1_ratio": round(max(cf["largest_ratio"] for cf in c1_fits if cf), 1),
                })
            if any(
                streams_rest[st_id] and sorted(streams_rest[st_id])[-1][4] < sorted(streams_rest[st_id])[-1][5]
                for st_id in sorted(streams_rest)
            ):
                t1_lt_q1_pos.append(pos)

            if all(fd is not None for fd in dl_fits):
                dl_pass = all(fd["slope"] >= 0.50 and fd["largest_ratio"] >= 1.50 for fd in dl_fits if fd is not None)
                dl_any = any(fd["slope"] >= 0.50 and fd["largest_ratio"] >= 1.50 for fd in dl_fits if fd is not None)
                s8_any_admitted += 1
                s8_any_alerts += int(dl_any)
                if is_alert:
                    dl_alerts["admitted"] += 1
                    dl_alerts["retained_alert" if dl_pass else "flipped_no_alert"] += 1
                else:
                    dl_no_alerts["admitted"] += 1
                    dl_no_alerts["became_alert" if dl_pass else "stayed_no_alert"] += 1
            else:
                if is_alert:
                    dl_alerts["range_limited"] += 1
                else:
                    dl_no_alerts["range_limited"] += 1

            # Restoration check audit on 124 fits (c0 + c0+c1 + independent all-point replay)
            recs = []
            recs_all_pts = []
            has_allpt_r1_infl = False
            has_allpt_max_bound_r0 = False
            has_allpt_nonreg_r0 = False
            tot_eval_ok: list[bool] = []
            for st_id in sorted(streams_rest):
                pts_r = sorted(streams_rest[st_id])
                for _, t0, q0, r0, t1, q1, r1 in pts_r:
                    if t0 > q0:
                        recs_all_pts.append((t0 - r0) / (t0 - q0))
                    elif r0 > t0:
                        has_allpt_nonreg_r0 = True
                    if r0 > max(t0, q0):
                        has_allpt_max_bound_r0 = True
                    if r1 > max(t1, q1):
                        has_allpt_r1_infl = True
                for _, t0, q0, r0, t1, q1, r1 in pts_r[-2:]:
                    if t0 > q0:
                        recs.append((t0 - r0) / (t0 - q0))
                    tt, qq, rr = t0 + t1, q0 + q1, r0 + r1
                    if tt > qq:
                        tot_eval_ok.append(5 * (tt - rr) >= 4 * (tt - qq))
            rcat = row.get("restoration_category")
            calc_rcat = "no_measurable_excess" if not recs else ("pass" if all(x >= 0.80 - 1e-12 for x in recs) else "fail")
            if rcat != calc_rcat:
                raise ValueError(f"Restoration replay mismatch at pos {row['position']}: {rcat} vs {calc_rcat}")
            if recs:
                if rcat == "pass":
                    if any(x < 0.80 - 1e-12 for x in recs_all_pts):
                        all_pt_excess_fail_n += 1
                    if has_allpt_r1_infl:
                        all_pt_r1_infl_n += 1
                    if has_allpt_max_bound_r0:
                        all_pt_max_bound_fail_n += 1
                    if has_allpt_nonreg_r0:
                        all_pt_nonreg_r0_pos.append(pos)
                    mx_r = max(recs)
                    if exact_rest_eq_ref:
                        rest_cats["pass_exact_copy"] += 1
                    else:
                        non_exact_pass_regimes[regime_lbl] += 1
                        if mx_r > 1.20:
                            rest_cats["pass_over_gt_120"] += 1
                        elif mx_r > 1.05:
                            rest_cats["pass_mild_over_105_120"] += 1
                        else:
                            rest_cats["pass_surgical_80_105"] += 1
                else:
                    rest_cats["fail"] += 1
            else:
                rest_cats["no_excess"] += 1

            if not tot_eval_ok:
                rest_tot_cats["no_excess"] += 1
            elif all(tot_eval_ok):
                rest_tot_cats["pass"] += 1
                if not recs:
                    rest_tot_new_testable += 1
                elif row.get("restoration_category") == "fail":
                    rest_c0_fail_to_tot_pass += 1
            else:
                rest_tot_cats["fail"] += 1
                if not recs:
                    rest_tot_new_testable += 1

            all_q1_zero_t1_pos = bool(streams_c1) and all(
                all(t0 == q0 for _, t0, q0 in streams_c0[st_id])
                and all(t1 > 0 and q1 == 0 for _, t1, q1 in streams_c1[st_id])
                for st_id in streams_c1
            )
            if all_q1_zero_t1_pos:
                q1_zero_t0_eq_q0_pos.append(pos)

            if is_alert:
                alert_by_pos[pos] = {
                    "distinct": len(trajs),
                    "tot_alert": t_dual,
                    "c0_fits": c0_fits,
                    "c0_diag": c0_diag,
                    "tot_fits": tot_fits,
                    "tot_diag": tot_diag,
                }

        f124 = forensics["fitted_124_forensics"]
        for grp in ("all_124", "alerts_6", "no_alerts_118"):
            for k in ("3_distinct", "2_distinct", "1_distinct"):
                if dist_counts[grp][k] != f124["stream_distinctness_c0"][grp][k]:
                    raise ValueError(f"Stream distinctness mismatch on {grp}.{k}")
        bs = f124["baseline_screens_124"]
        if (
            b0 != bs["B0_primary_c0_dual"]["alerts"]
            or b1 != bs["B1_c0_ratio_ge_1_5_only"]["alerts"]
            or b2 != bs["B2_c0_slope_ge_0_5_only"]["alerts"]
            or b3 != bs["B3_total_ticks_c0_plus_c1_dual"]["alerts"]
            or s7_cnt != prim["secondary"]["S7_any_stream_alerts"]["count"]
        ):
            raise ValueError("Baseline screen or S7 count mismatch against anonymous-measurements.json")
        if (
            dl_alerts["admitted"] != f124["drop_largest_by_outcome"]["alerts_6"]["admitted"]
            or dl_no_alerts["admitted"] != f124["drop_largest_by_outcome"]["no_alerts_118"]["admitted"]
        ):
            raise ValueError("Drop-largest outcome split mismatch against anonymous-measurements.json")

        six_diag: dict[int, dict[str, Any]] = {}
        for item in forensics["six_alerts"]:
            pos = int(item["position"])
            chk = alert_by_pos[pos]
            if chk["distinct"] != item["distinct_c0_trajectories"] or chk["tot_alert"] != item["all_streams_total_ticks_alert"]:
                raise ValueError(f"Alert {pos} summary mismatch against anonymous-measurements.json")
            for idx_s, s_dict in enumerate(item["streams"]):
                if abs(chk["c0_fits"][idx_s]["slope"] - s_dict["primary_c0"]["slope"]) > 1e-9:
                    raise ValueError(f"Alert {pos} stream {idx_s} c0 slope mismatch")
                if abs(chk["tot_fits"][idx_s]["slope"] - s_dict["total_ticks_c0_plus_c1"]["slope"]) > 1e-9:
                    raise ValueError(f"Alert {pos} stream {idx_s} c0+c1 slope mismatch")
            c0_ps = [d["p_value"] for d in chk["c0_diag"]]
            c0_tss = [d["theil_sen_slope"] for d in chk["c0_diag"]]
            c0_ci_los = [d["ci_lo"] for d in chk["c0_diag"]]
            c0_ci_his = [d["ci_hi"] for d in chk["c0_diag"]]
            c0_cooks = [d["cooks_d_last"] for d in chk["c0_diag"]]
            c0_max_cooks = [d["cooks_d_max"] for d in chk["c0_diag"]]
            c0_loos = [d["beta_loo"] for d in chk["c0_diag"]]
            tot_ps = [d["p_value"] for d in chk["tot_diag"]]
            tot_tss = [d["theil_sen_slope"] for d in chk["tot_diag"]]
            ols_sig_all = all(pv < 0.05 for pv in c0_ps)
            ts_ge_50_all = all(ts >= 0.50 for ts in c0_tss)
            dl_ok = item["drop_largest_case_verdict"] == "retained_alert"
            # Exploratory 4-check distribution-free core (total ticks, drop-largest, Theil-Sen >= 0.50, restoration >= 80%)
            robust_pass = bool(chk["tot_alert"] and dl_ok and ts_ge_50_all and item["all_streams_restoration_pass"])
            six_diag[pos] = {
                "c0_max_p": max(c0_ps),
                "c0_min_ci_lo": min(c0_ci_los),
                "c0_stream_ci_los": c0_ci_los,
                "c0_stream_ci_his": c0_ci_his,
                "c0_stream_cooks_d": c0_cooks,
                "c0_stream_max_cooks_d": c0_max_cooks,
                "c0_max_cooks_d": max(c0_cooks),
                "c0_stream_loos": c0_loos,
                "c0_min_ts": min(c0_tss),
                "c0_max_lev": max(d["max_leverage"] for d in chk["c0_diag"]),
                "tot_max_p": max(tot_ps),
                "tot_min_ts": min(tot_tss),
                "ols_sig_all": ols_sig_all,
                "ts_ge_50_all": ts_ge_50_all,
                "robust_4check_pass": robust_pass,
            }
        if sum(b1_fp_decomp.values()) != bs["B1_c0_ratio_ge_1_5_only"]["fp_vs_primary"]:
            raise ValueError("B1 non-primary decomposition sum mismatch")

        # Multi-stream CPU marginal ns/tick (counted O2 & plain O2), B5 overlap with 4-core, robust spawn baselines, & additive delta-CPU
        core_positions_set = {p for p, d in six_diag.items() if d["robust_4check_pass"]}
        ns_per_tick_by_pos: dict[int, float] = {}
        ns_per_tick_stats: dict[int, dict[str, Any]] = {}
        spawn_floor_sub_alerts: dict[str, dict[str, Any]] = {}
        o2_minus_plain_subms_ms: list[float] = []
        o2_minus_plain_s0_all6_ms: list[float] = []
        b5_core_tp = 0
        pos94_ticks_m = 0.0
        pos94_cpu_ms = 0.0
        for item in forensics["six_alerts"]:
            p_i = int(item["position"])
            s0 = item["streams"][0]
            tot_hi = s0["primary_c0"]["target"][-1] + s0["aux_c1"]["target"][-1]
            o2_u = s0["cpu_usage_usec"]["O2"]["target_usec"]
            ns_per_tick_by_pos[p_i] = round((o2_u[-1] - o2_u[0]) * 1000.0 / max(1, tot_hi), 3)
            if p_i == 94:
                pos94_ticks_m = round(s0["primary_c0"]["target"][-1] / 1_000_000.0, 1)
                pos94_cpu_ms = round((o2_u[-1] - o2_u[0]) / 1000.0, 1)
            o2_vals, pl_vals, o2_ms_diffs = [], [], []
            sub_slopes, sub_ratios, pl0_slopes, o2_sub_slopes, pl_delta_ms = [], [], [], [], []
            add_pl_slopes, add_o2_slopes = [], []
            minref_pl_pass = minref_o2_pass = medref_pl_pass = medref_o2_pass = 0
            sub_dual_streams = pl0_dual_streams = o2_sub_dual_streams = 0
            b5_hit = True
            for st_d in item["streams"]:
                dt0 = st_d["primary_c0"]["target"][-1] - st_d["primary_c0"]["reference"][-1]
                o2_diff_us = st_d["cpu_usage_usec"]["O2"]["target_usec"][-1] - st_d["cpu_usage_usec"]["O2"]["reference_usec"][-1]
                pl_diff_us = st_d["cpu_usage_usec"]["plain"]["target_usec"][-1] - st_d["cpu_usage_usec"]["plain"]["reference_usec"][-1]
                o2_vals.append(o2_diff_us * 1000.0 / max(1, dt0))
                pl_vals.append(pl_diff_us * 1000.0 / max(1, dt0))
                o2_ms_diffs.append(o2_diff_us / 1000.0)
                pl_delta_ms.append(pl_diff_us / 1000.0)
                pl_obj = st_d["cpu_usage_usec"]["plain"]
                o2_obj = st_d["cpu_usage_usec"]["O2"]
                pl_r = pl_obj["largest_ratio"]
                t_pl_u, q_pl_u = pl_obj["target_usec"], pl_obj["reference_usec"]
                t_o2_u, q_o2_u = o2_obj["target_usec"], o2_obj["reference_usec"]
                if q_pl_u and q_o2_u and q_pl_u[0] is not None and q_o2_u[0] is not None:
                    o2_minus_plain_s0_all6_ms.append((q_o2_u[0] - q_pl_u[0]) / 1000.0)
                if p_i in (3, 13, 94, 97):
                    for uo, up in zip(q_o2_u, q_pl_u):
                        if up is not None and uo is not None:
                            o2_minus_plain_subms_ms.append((uo - up) / 1000.0)
                pl_max = max(t_pl_u[-1], q_pl_u[-1])
                if pl_r is None or pl_r < 1.50 or pl_max < 10_000:
                    b5_hit = False
                ln_ns = [math.log(int(sz_i)) for sz_i in st_d["sizes"]]
                mx_ln = sum(ln_ns) / len(ln_ns)
                sxx_ln = sum((x - mx_ln) ** 2 for x in ln_ns)
                if sxx_ln > 0:
                    d_pl_arr = [(tu - qu) / 1000.0 for tu, qu in zip(t_pl_u, q_pl_u)]
                    d_o2_arr = [(tu - qu) / 1000.0 for tu, qu in zip(t_o2_u, q_o2_u)]
                    add_pl_slopes.append(sum((x - mx_ln) * (y - sum(d_pl_arr) / len(d_pl_arr)) for x, y in zip(ln_ns, d_pl_arr)) / sxx_ln)
                    add_o2_slopes.append(sum((x - mx_ln) * (y - sum(d_o2_arr) / len(d_o2_arr)) for x, y in zip(ln_ns, d_o2_arr)) / sxx_ln)
                for tv_u, qv_u, base_fn, bucket in (
                    (t_pl_u, q_pl_u, lambda qv: min(qv) - 500.0, "minref_pl"),
                    (t_o2_u, q_o2_u, lambda qv: min(qv) - 500.0, "minref_o2"),
                    (t_pl_u, q_pl_u, lambda qv: statistics.median(qv) - 500.0, "medref_pl"),
                    (t_o2_u, q_o2_u, lambda qv: statistics.median(qv) - 500.0, "medref_o2"),
                ):
                    b_v = base_fn(qv_u)
                    f_rob = _ols_log_ratio_fit([(int(sz_i), max(500, int(round(tu - b_v))), max(500, int(round(qu - b_v)))) for sz_i, tu, qu in zip(st_d["sizes"], tv_u, qv_u)])
                    if f_rob is not None and f_rob["slope"] >= 0.50 and f_rob["largest_ratio"] >= 1.50:
                        if bucket == "minref_pl":
                            minref_pl_pass += 1
                        elif bucket == "minref_o2":
                            minref_o2_pass += 1
                        elif bucket == "medref_pl":
                            medref_pl_pass += 1
                        else:
                            medref_o2_pass += 1
                fl_us = min(t_pl_u[0], q_pl_u[0]) - 500.0
                pts_sub = [
                    (int(sz_i), max(500, int(round(tu - fl_us))), max(500, int(round(qu - fl_us))))
                    for sz_i, tu, qu in zip(st_d["sizes"], t_pl_u, q_pl_u)
                ]
                sub_fit = _ols_log_ratio_fit(pts_sub)
                if sub_fit is not None:
                    sub_slopes.append(round(float(sub_fit["slope"]), 4))
                    sub_ratios.append(round(float(sub_fit["largest_ratio"]), 2))
                    if sub_fit["slope"] >= 0.50 and sub_fit["largest_ratio"] >= 1.50:
                        sub_dual_streams += 1
                fl_zero_us = float(min(t_pl_u[0], q_pl_u[0]))
                pts_pl0 = [
                    (int(sz_i), max(500, int(round(tu - fl_zero_us))), max(500, int(round(qu - fl_zero_us))))
                    for sz_i, tu, qu in zip(st_d["sizes"], t_pl_u, q_pl_u)
                ]
                pl0_fit = _ols_log_ratio_fit(pts_pl0)
                if pl0_fit is not None:
                    pl0_slopes.append(round(float(pl0_fit["slope"]), 4))
                    if pl0_fit["slope"] >= 0.50 and pl0_fit["largest_ratio"] >= 1.50:
                        pl0_dual_streams += 1
                fl_o2_us = min(t_o2_u[0], q_o2_u[0]) - 500.0
                pts_o2_sub = [
                    (int(sz_i), max(500, int(round(tu - fl_o2_us))), max(500, int(round(qu - fl_o2_us))))
                    for sz_i, tu, qu in zip(st_d["sizes"], t_o2_u, q_o2_u)
                ]
                o2_sub_fit = _ols_log_ratio_fit(pts_o2_sub)
                if o2_sub_fit is not None:
                    o2_sub_slopes.append(round(float(o2_sub_fit["slope"]), 4))
                    if o2_sub_fit["slope"] >= 0.50 and o2_sub_fit["largest_ratio"] >= 1.50:
                        o2_sub_dual_streams += 1
            if b5_hit and p_i in core_positions_set:
                b5_core_tp += 1
            ns_per_tick_stats[p_i] = {
                "o2_min": round(min(o2_vals), 3),
                "o2_median": round(statistics.median(o2_vals), 3),
                "o2_max": round(max(o2_vals), 3),
                "plain_min": round(min(pl_vals), 3),
                "plain_median": round(statistics.median(pl_vals), 3),
                "plain_max": round(max(pl_vals), 3),
                "o2_ms_diff_min": round(min(o2_ms_diffs), 2),
                "o2_ms_diff_max": round(max(o2_ms_diffs), 2),
            }
            spawn_floor_sub_alerts[str(p_i)] = {
                "slope_min": min(sub_slopes) if sub_slopes else 0.0,
                "slope_max": max(sub_slopes) if sub_slopes else 0.0,
                "ratio_min": min(sub_ratios) if sub_ratios else 1.0,
                "ratio_max": max(sub_ratios) if sub_ratios else 1.0,
                "streams_dual_pass": sub_dual_streams,
                "all_streams_pass": sub_dual_streams == len(item["streams"]),
                "pl0_slope_min": min(pl0_slopes) if pl0_slopes else 0.0,
                "pl0_slope_max": max(pl0_slopes) if pl0_slopes else 0.0,
                "pl0_all_streams_pass": pl0_dual_streams == len(item["streams"]),
                "pl_delta_ms_min": round(min(pl_delta_ms), 1),
                "pl_delta_ms_max": round(max(pl_delta_ms), 1),
                "o2_slope_min": min(o2_sub_slopes) if o2_sub_slopes else 0.0,
                "o2_slope_max": max(o2_sub_slopes) if o2_sub_slopes else 0.0,
                "o2_streams_dual_pass": o2_sub_dual_streams,
                "o2_all_streams_pass": o2_sub_dual_streams == len(item["streams"]),
                "min_ref_plain_streams": minref_pl_pass,
                "min_ref_plain_all_pass": minref_pl_pass == len(item["streams"]),
                "min_ref_o2_streams": minref_o2_pass,
                "min_ref_o2_all_pass": minref_o2_pass == len(item["streams"]),
                "med_ref_plain_streams": medref_pl_pass,
                "med_ref_plain_all_pass": medref_pl_pass == len(item["streams"]),
                "med_ref_o2_streams": medref_o2_pass,
                "med_ref_o2_all_pass": medref_o2_pass == len(item["streams"]),
                "add_delta_pl_slope_min": round(min(add_pl_slopes), 2) if add_pl_slopes else 0.0,
                "add_delta_pl_slope_max": round(max(add_pl_slopes), 2) if add_pl_slopes else 0.0,
                "add_delta_o2_slope_min": round(min(add_o2_slopes), 2) if add_o2_slopes else 0.0,
                "add_delta_o2_slope_max": round(max(add_o2_slopes), 2) if add_o2_slopes else 0.0,
                "raw_plain_ge_1_5_all_streams": b5_hit,
            }
        fd_q4 = statistics.quantiles(o2_minus_plain_subms_ms, n=4) if len(o2_minus_plain_subms_ms) >= 4 else [0.0, 0.0, 0.0]
        fd_wrapper_overhead_ms = {
            "n": len(o2_minus_plain_subms_ms),
            "median": round(statistics.median(o2_minus_plain_subms_ms), 2) if o2_minus_plain_subms_ms else 0.0,
            "iqr": [round(fd_q4[0], 2), round(fd_q4[2], 2)],
        }
        s0_q4 = statistics.quantiles(o2_minus_plain_s0_all6_ms, n=4) if len(o2_minus_plain_s0_all6_ms) >= 4 else [0.0, 0.0, 0.0]
        o2_minus_plain_s0_ms = {
            "n": len(o2_minus_plain_s0_all6_ms),
            "median": round(statistics.median(o2_minus_plain_s0_all6_ms), 2) if o2_minus_plain_s0_all6_ms else 0.0,
            "iqr": [round(s0_q4[0], 2), round(s0_q4[2], 2)],
        }

        # Check whether relaxing -O0-only cpu_cap exclusions (admitting O2 == O3 points) changes any P3/SA7 verdict
        o0_relax_per_pos: dict[str, Any] = {}
        o0_relax_cap_pts = 0
        o0_relax_p3_delta = 0
        o0_relax_sa7_delta = 0
        for row_x in reps:
            if row_x.get("position") is None or not row_x.get("samples"):
                continue
            gp_x = {tuple(e["step"][1:]): e for e in row_x["measurements"] if e["step"][0] == "execute"}
            o0_only_x = []
            for idx_x, sp_x in enumerate(row_x["samples"]):
                o0_ms = [gp_x.get((idx_x, sd, "O0")) for sd in sides]
                non_o0 = [gp_x.get((idx_x, sd, md)) for sd in sides for md in ("plain", "ubsan", "O2", "O3")]
                if any(m and "cpu_cap" in (m.get("caps") or ()) for m in o0_ms) and all(
                    m and m["status"] == "complete" and not (m.get("caps") or []) for m in non_o0
                ):
                    o0_only_x.append((idx_x, int(sp_x["stream"]), int(sp_x["size"])))
            if not o0_only_x:
                continue
            o0_relax_cap_pts += len(o0_only_x)
            pos_x = int(row_x["position"])
            strict_by_s: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
            relax_by_s: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
            o2_o3_eq_all = True
            for idx_x, sp_x in enumerate(row_x["samples"]):
                st_x, sz_x = int(sp_x["stream"]), int(sp_x["size"])
                if all(gp_x.get((idx_x, sd, md)) and gp_x[(idx_x, sd, md)]["status"] == "complete" and not (gp_x[(idx_x, sd, md)].get("caps") or []) for sd in sides for md in ("plain", "ubsan", "O2", "O3")):
                    if not all(tuple(gp_x[(idx_x, sd, "O2")]["counter"]) == tuple(gp_x[(idx_x, sd, "O3")]["counter"]) for sd in sides):
                        o2_o3_eq_all = False
                    relax_by_s[st_x].append((sz_x, gp_x[(idx_x, "target", "O2")]["counter"][0], gp_x[(idx_x, "reference", "O2")]["counter"][0]))
                    if all(gp_x.get((idx_x, sd, "O0")) and gp_x[(idx_x, sd, "O0")]["status"] == "complete" and not (gp_x[(idx_x, sd, "O0")].get("caps") or []) for sd in sides):
                        strict_by_s[st_x].append((sz_x, gp_x[(idx_x, "target", "O2")]["counter"][0], gp_x[(idx_x, "reference", "O2")]["counter"][0]))
            strict_fits = [_ols_log_ratio_fit(sorted(strict_by_s[s])) for s in sorted(strict_by_s)]
            relax_fits = [_ols_log_ratio_fit(sorted(relax_by_s[s])) for s in sorted(relax_by_s)]
            st_all_al = bool(strict_fits) and all(f and f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in strict_fits)
            rl_all_al = bool(relax_fits) and all(f and f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in relax_fits)
            st_any_al = any(f and f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in strict_fits)
            rl_any_al = any(f and f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in relax_fits)
            o0_relax_p3_delta += int(rl_all_al) - int(st_all_al)
            o0_relax_sa7_delta += int(rl_any_al) - int(st_any_al)
            o0_relax_per_pos[str(pos_x)] = {
                "o0_only_points": len(o0_only_x),
                "o2_eq_o3": o2_o3_eq_all,
                "strict_w2_slope": round(strict_fits[1]["slope"], 3) if len(strict_fits) > 1 and strict_fits[1] else None,
                "relax_w2_slope": round(relax_fits[1]["slope"], 3) if len(relax_fits) > 1 and relax_fits[1] else None,
                "relax_slopes": [round(f["slope"], 3) if f else None for f in relax_fits],
                "relax_ratios": [round(f["largest_ratio"], 2) if f else None for f in relax_fits],
                "verdict_changed": (st_all_al != rl_all_al) or (st_any_al != rl_any_al),
            }
        o0_cpu_cap_relaxation = {
            "o0_only_cap_points_n": o0_relax_cap_pts,
            "affected_pairs_n": len(o0_relax_per_pos),
            "affected_positions": sorted(int(k) for k in o0_relax_per_pos),
            "p3_delta": o0_relax_p3_delta,
            "sa7_delta": o0_relax_sa7_delta,
            "per_position": o0_relax_per_pos,
        }

        by_pos_anon = {int(r["position"]): r for r in conf if r.get("position") is not None}

        def _max_stream_ratio(p_num: int, chan: int) -> float:
            rp = by_pos_anon.get(p_num)
            if not rp:
                return 0.0
            gp = {tuple(e["step"][1:]): e for e in rp["measurements"] if e["step"][0] == "execute"}
            by_s: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
            for idx_p, sp in enumerate(rp["samples"]):
                if not all(
                    (ev := gp.get((idx_p, sd_i, md_i))) is not None
                    and ev.get("status") == "complete"
                    and not (ev.get("caps") or [])
                    for sd_i in sides
                    for md_i in modes
                ):
                    continue
                et, eq = gp[(idx_p, "target", "O2")], gp[(idx_p, "reference", "O2")]
                tv = sum(et["counter"]) if chan < 0 else et["counter"][chan]
                qv = sum(eq["counter"]) if chan < 0 else eq["counter"][chan]
                if qv > 0:
                    by_s[int(sp["stream"])].append((int(sp["size"]), tv, qv))
            mx = 0.0
            for arr in by_s.values():
                arr.sort()
                mx = max(mx, arr[-1][1] / arr[-1][2])
            return mx

        def _max_tot_slope(pos_list: tuple[int, ...]) -> float:
            mx_s = 0.0
            for p_num in pos_list:
                rp = by_pos_anon.get(p_num)
                if not rp:
                    continue
                gp = {tuple(e["step"][1:]): e for e in rp["measurements"] if e["step"][0] == "execute"}
                by_s: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
                for idx_p, sp in enumerate(rp["samples"]):
                    et, eq = gp.get((idx_p, "target", "O2")), gp.get((idx_p, "reference", "O2"))
                    if et and eq and et["status"] == "complete" and eq["status"] == "complete":
                        tv, qv = sum(et["counter"]), sum(eq["counter"])
                        if tv > 0 and qv > 0:
                            by_s[int(sp["stream"])].append((int(sp["size"]), tv, qv))
                for arr in by_s.values():
                    arr.sort()
                    ft = _ols_log_ratio_fit(arr)
                    if ft is not None:
                        mx_s = max(mx_s, ft["slope"])
            return round(mx_s, 3)

        def _rest_rec_range(p_num: int) -> tuple[int, int]:
            rp = by_pos_anon.get(p_num)
            if not rp:
                return (0, 0)
            gp = {tuple(e["step"][1:]): e for e in rp["measurements"] if e["step"][0] == "execute"}
            by_s: dict[int, list[tuple[int, int, int, int]]] = defaultdict(list)
            for idx_p, sp in enumerate(rp["samples"]):
                et, eq, er = gp.get((idx_p, "target", "O2")), gp.get((idx_p, "reference", "O2")), gp.get((idx_p, "restored", "O2"))
                if et and eq and er and et["status"] == "complete" and eq["status"] == "complete" and er["status"] == "complete":
                    by_s[int(sp["stream"])].append((int(sp["size"]), et["counter"][0], eq["counter"][0], er["counter"][0]))
            vals = []
            for arr in by_s.values():
                arr.sort()
                for _, t0x, q0x, r0x in arr[-2:]:
                    if t0x > q0x:
                        vals.append(100.0 * (t0x - r0x) / (t0x - q0x))
            return (round(min(vals)), round(max(vals))) if vals else (0, 0)

        rest_c1_infl = 0
        rest_non_exact_c1_infl = 0
        for row_f in fitted:
            if row_f.get("restoration_category") != "pass":
                continue
            gf = {tuple(e["step"][1:]): e for e in row_f["measurements"] if e["step"][0] == "execute"}
            row_non_exact = False
            row_c1_infl = 0
            for idx_f in range(len(row_f["samples"])):
                et, eq, er = gf.get((idx_f, "target", "O2")), gf.get((idx_f, "reference", "O2")), gf.get((idx_f, "restored", "O2"))
                if et and eq and er and et["status"] == "complete" and eq["status"] == "complete" and er["status"] == "complete":
                    if tuple(er["counter"]) != tuple(eq["counter"]):
                        row_non_exact = True
                    if er["counter"][1] > max(et["counter"][1], eq["counter"][1]):
                        row_c1_infl += 1
            rest_c1_infl += row_c1_infl
            if row_non_exact:
                rest_non_exact_c1_infl += int(row_c1_infl > 0)

        rest_exec_counts = Counter(
            r.get("restoration_category")
            for r in reps
            if r.get("effective_terminal") in S3_EXECUTED
        )
        rest_s1_counts = Counter(
            r.get("restoration_category")
            for r in reps
            if r.get("effective_terminal") not in S1_DESK_STOPS
        )
        quar_all = [r for r in anon_rows if not r.get("S0_stop") and r.get("quarantined")]
        quar_source_stops_n = sum(1 for r in quar_all if r.get("bucket") == "source")

        r91_lo, r91_hi = _rest_rec_range(91)
        r129_lo, r129_hi = _rest_rec_range(129)
        exemplars = {
            "pos_77_c0_ratio": round(_max_stream_ratio(77, 0), 2),
            "pos_77_log_r2": pos77_log_r2,
            "pos_90_c0_ratio": round(_max_stream_ratio(90, 0)),
            "pos_145_c0_ratio": round(_max_stream_ratio(145, 0)),
            "pos_47_c1_ratio": round(_max_stream_ratio(47, 1)),
            "pos_164_tot_ratio": round(_max_stream_ratio(164, -1), 2),
            "pos_94_ticks_m": pos94_ticks_m,
            "pos_94_cpu_ms": pos94_cpu_ms,
            "pos_100_131_max_tot_slope": _max_tot_slope((100, 131)),
            "both_zero_max_tot_slope": _max_tot_slope((59, 106, 140, 160)),
            "pos_91_rec_pct_range": [r91_lo, r91_hi],
            "pos_129_rec_pct_range": [r129_lo, r129_hi],
            "rest_c1_inflation_events": rest_c1_infl,
            "non_exact_c1_inflation": rest_non_exact_c1_infl,
            "b2_only": b2_only_info[0] if b2_only_info else {"position": 0, "slope_range": [0.0, 0.0], "ratio_range": [0.0, 0.0]},
            "quar_source_stops": quar_source_stops_n,
        }

        mcn_scr_raw = {
            "B1": _mcnemar_exact(bs["B1_c0_ratio_ge_1_5_only"]["fp_vs_primary"], bs["B1_c0_ratio_ge_1_5_only"]["fn_vs_primary"]),
            "B2": _mcnemar_exact(bs["B2_c0_slope_ge_0_5_only"]["fp_vs_primary"], bs["B2_c0_slope_ge_0_5_only"]["fn_vs_primary"]),
            "B3": _mcnemar_exact(bs["B3_total_ticks_c0_plus_c1_dual"]["fp_vs_primary"], bs["B3_total_ticks_c0_plus_c1_dual"]["fn_vs_primary"]),
            "B4": _mcnemar_exact(bs["B4_plain_cpu_usec_dual_ge_10ms"]["fp_vs_primary"], bs["B4_plain_cpu_usec_dual_ge_10ms"]["fn_vs_primary"]),
            "B5": _mcnemar_exact(bs["B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms"]["fp_vs_primary"], bs["B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms"]["fn_vs_primary"]),
        }
        mcn_scr_holm = holm(mcn_scr_raw)
        b5_alerts_n = int(bs["B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms"]["alerts"])

        p1_r_d = prim["P1"]["rate"]
        p3_r_d = prim["P3"]["rate"]
        sa1_r_d = prim["secondary"]["S1_desk_stop"]
        sa2_r_d = prim["secondary"]["S2_alerts_per_selected"]
        sa3_r_d = prim["secondary"]["S3_preprocessing_stops_after_desk"]
        sa4_r_d = prim["secondary"]["S4_oracle_failures_among_executed"]
        s13_p1_cnt = int(s13["P1"]["rate"]["count"])
        s13_d_cnt = int(s13["secondary"]["S1_desk_stop"]["count"])

        ms_s = sorted(min_slopes)
        mr_s = sorted(min_ratios)
        core_positions = sorted(core_positions_set)
        core_min_ci_lo = min(six_diag[p]["c0_min_ci_lo"] for p in core_positions) if core_positions else 0.0
        fin_primary_holm = holm({
            "P1": _fisher_two_sided_exact(p1_r_d["count"], p1_r_d["total"] - p1_r_d["count"], 14, 147 - 14),
            "P2": float(prim["P2"]["p_unadjusted"]),
            "P3": _fisher_two_sided_exact(p3_r_d["count"], p3_r_d["total"] - p3_r_d["count"], 4, 13 - 4),
        })
        tot_pass_n = int(rest_tot_cats.get("pass", 0))
        tot_no_ex_n = int(rest_tot_cats.get("no_excess", 0))
        tot_fail_n = int(rest_tot_cats.get("fail", 0))
        tot_ex_n = tot_pass_n + tot_fail_n
        deep_forensics = {
            "missing_decomposition": {
                "O0_O2_O3": {
                    "agree": o_agree, "disagree": o_dis,
                    "capped": o_cap_events, "oracle_abort": o_oracle_abort,
                    "overlay_fixture_stop": o_overlay_fix, "infra_failure": o_infra_miss,
                    "missing_total": o_cap,
                    "o2_o3_agree_on_o0_capped": o2_o3_agree_on_o0_capped,
                    "o2_o3_disagree_on_o0_capped": o2_o3_disagree_on_o0_capped,
                },
                "target_vs_sham": {
                    "agree": s_agree, "disagree": s_dis,
                    "capped": s_cap_events, "oracle_abort": s_oracle_abort,
                    "overlay_fixture_stop": s_overlay_fix, "infra_failure": s_infra_miss,
                    "missing_total": s_cap,
                },
            },
            "chronological_failure_audit": {
                "oracle_prior_process_failure_positions": sorted(oracle_prior_pf_pos),
                "other_noncap_failure_positions": sorted(other_noncap_pf_pos),
                "fitted_masked_failure_count": fitted_masked_failure_cnt,
                "rc_0_stderr_positions": sorted(pf_rc_0_pos),
                "rc_134_sigabrt_positions": sorted(pf_rc_134_pos),
                "rc_139_sigsegv_positions": sorted(pf_rc_139_pos),
                "rc_0_stderr_count": len(pf_rc_0_pos),
                "rc_134_sigabrt_count": len(pf_rc_134_pos),
                "rc_139_sigsegv_count": len(pf_rc_139_pos),
                "max_parsed_counter": max_parsed_counter,
                "counters_ge_2_pow_64": counters_ge_2_pow_64,
            },
            "cap_mode_breakdown": {
                "counts_by_cap_side_mode": {f"{k[0]}:{k[1]}:{k[2]}": v for k, v in sorted(cap_by_sm.items())},
                "cpu_cap_o0_only_points": cpu_cap_o0_only_pts,
                "cpu_cap_total_points": cpu_cap_total_pts,
            },
            "oracle_failure_breakdown": {
                "total": len(oracle_reps),
                "upstream_total": or_upstream,
                "plain_target": or_plain_tgt,
                "plain_reference": or_plain_ref,
                "plain_invalid_total": or_plain_tgt + or_plain_ref + or_rest,
                "ubsan_only_target": or_ub_tgt,
                "ubsan_only_reference": or_ub_ref,
                "ubsan_invalid_target": or_ub_all_tgt,
                "ubsan_invalid_reference": or_ub_all_ref,
                "ubsan_invalid_total": or_ub_all_tgt + or_ub_all_ref,
                "plain_segv_and_ubsan_count": or_plain_segv_and_ub,
                "plain_segv_and_ubsan_pos": or_plain_segv_ub_pos,
                "restored_variant_failure": or_rest,
                "sham_variant_failure": or_sham,
                "multi_event_count": or_multi_events,
                "invalid_output_mode_exits": {f"{k[0]}:exit_{k[1]}": v for k, v in sorted(inv_out_mode_exits.items())},
                "pos27_o0_sigabrt_o2_clean": pos27_o0_sigabrt_o2_clean,
                "upstream_rate": rate_summary(or_upstream, prim["P1"]["rate"]["count"]),
            },
            "insufficient_fit_breakdown": {
                "total": len(insuf_reps),
                "q_zero_complete_elim": ins_q_zero,
                "both_zero_c0": ins_both_zero,
                "tick_cap_censored": ins_tick_cap,
                "tick_cap_censor_alert_candidates": ins_censor_alert,
                "censoring_upper_p3": rate_summary(
                    prim["P3"]["rate"]["count"] + ins_censor_alert,
                    prim["P3"]["rate"]["total"] + ins_tick_cap,
                ),
                "censoring_worst_p3": rate_summary(
                    prim["P3"]["rate"]["count"] + ins_tick_cap,
                    prim["P3"]["rate"]["total"] + ins_tick_cap,
                ),
                "censoring_worst_fisher_4_13": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap,
                    prim["P3"]["rate"]["total"] - prim["P3"]["rate"]["count"],
                    4,
                    13 - 4,
                ),
                "censoring_worst_fisher_4_12": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap,
                    prim["P3"]["rate"]["total"] - prim["P3"]["rate"]["count"],
                    4,
                    12 - 4,
                ),
                "censoring_worst_fisher_conserv": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap,
                    prim["P3"]["rate"]["total"] - prim["P3"]["rate"]["count"],
                    3,
                    12 - 3,
                ),
                "cpu_cap_fitted_positions": sorted(cpu_cap_fitted_pos),
                "censoring_plus_cpucap_excl_flat_n": prim["P3"]["rate"]["count"] + ins_tick_cap + sum(1 for p in cpu_cap_fitted_pos if p not in (99, 139)),
                "censoring_plus_cpucap_excl_flat_rate": rate_summary(
                    prim["P3"]["rate"]["count"] + ins_tick_cap + sum(1 for p in cpu_cap_fitted_pos if p not in (99, 139)),
                    prim["P3"]["rate"]["total"] + ins_tick_cap,
                ),
                "censoring_plus_cpucap_excl_flat_p": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap + sum(1 for p in cpu_cap_fitted_pos if p not in (99, 139)),
                    (prim["P3"]["rate"]["total"] + ins_tick_cap) - (prim["P3"]["rate"]["count"] + ins_tick_cap + sum(1 for p in cpu_cap_fitted_pos if p not in (99, 139))),
                    4,
                    13 - 4,
                ),
                "censoring_plus_cpucap_excl_flat_conserv_p": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap + sum(1 for p in cpu_cap_fitted_pos if p not in (99, 139)),
                    (prim["P3"]["rate"]["total"] + ins_tick_cap) - (prim["P3"]["rate"]["count"] + ins_tick_cap + sum(1 for p in cpu_cap_fitted_pos if p not in (99, 139))),
                    3,
                    12 - 3,
                ),
                "censoring_plus_cpucap_fisher_p": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap + len(cpu_cap_fitted_pos),
                    (prim["P3"]["rate"]["total"] + ins_tick_cap) - (prim["P3"]["rate"]["count"] + ins_tick_cap + len(cpu_cap_fitted_pos)),
                    4,
                    13 - 4,
                ),
                "censoring_plus_cpucap_fisher_4_12_p": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap + len(cpu_cap_fitted_pos),
                    (prim["P3"]["rate"]["total"] + ins_tick_cap) - (prim["P3"]["rate"]["count"] + ins_tick_cap + len(cpu_cap_fitted_pos)),
                    4,
                    12 - 4,
                ),
                "censoring_plus_cpucap_fisher_conserv_p": _fisher_two_sided_exact(
                    prim["P3"]["rate"]["count"] + ins_tick_cap + len(cpu_cap_fitted_pos),
                    (prim["P3"]["rate"]["total"] + ins_tick_cap) - (prim["P3"]["rate"]["count"] + ins_tick_cap + len(cpu_cap_fitted_pos)),
                    3,
                    12 - 3,
                ),
                "b3_all_non_oracle_exec": rate_summary(
                    b3 + b3_insuf_hits,
                    len(fitted) + len(insuf_reps),
                ),
            },
            "fit_124_taxonomy": {
                "regimes": dict(sorted(regime_counts.items())),
                "distinct1_c1_varying": distinct1_c1_var,
                "distinct1_fully_oblivious": distinct1_obliv,
                "min_slope_quantiles": {
                    lbl: round(ms_s[int(q * (len(ms_s) - 1))], 4)
                    for lbl, q in (("min", 0.0), ("q25", 0.25), ("median", 0.50), ("q75", 0.75), ("q95", 0.95), ("max", 1.0))
                },
                "min_ratio_quantiles": {
                    lbl: round(mr_s[int(q * (len(mr_s) - 1))], 3)
                    for lbl, q in (("min", 0.0), ("q25", 0.25), ("median", 0.50), ("q75", 0.75), ("q95", 0.95), ("max", 1.0))
                },
                "beta_min_grid": {str(k): v for k, v in beta_grid.items()},
                "c1_only_hits": c1_only_hits,
                "c1_only_hit_count": len(c1_only_hits),
                "q1_zero_t0_eq_q0_positions": sorted(q1_zero_t0_eq_q0_pos),
                "t1_lt_q1_positions": sorted(t1_lt_q1_pos),
                "s8_any_stream_alerts_among_admitted": rate_summary(s8_any_alerts, s8_any_admitted),
                "pair_level_r2": {
                    "all_zero_var_pairs": pair_all_zv_n,
                    "defined_r2_pairs": len(pair_min_r2_all),
                    "worst_stream_median_r2": round(float(statistics.median(pair_min_r2_all)), 3) if pair_min_r2_all else 0.0,
                    "cross_stream_median_r2": round(float(statistics.median(pair_med_r2_all)), 3) if pair_med_r2_all else 0.0,
                    "alert_worst_stream_median_r2": round(float(statistics.median(alert_pair_min_r2)), 4) if alert_pair_min_r2 else 0.0,
                    "stream_point_counts": {str(k): v for k, v in sorted(stream_pt_counts.items())},
                },
            },
            "six_alerts_robust_diagnostics": {
                "per_position": {str(k): v for k, v in sorted(six_diag.items())},
                "core_positions": core_positions,
                "core_count": len(core_positions),
                "core_rate": rate_summary(len(core_positions), 124),
                "realized_cpu_core_positions": [p for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("raw_plain_ge_1_5_all_streams")],
                "realized_cpu_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("raw_plain_ge_1_5_all_streams")),
                "plain_sub_500_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("all_streams_pass")),
                "o2_sub_500_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("o2_all_streams_pass")),
                "min_ref_plain_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("min_ref_plain_all_pass")),
                "min_ref_o2_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("min_ref_o2_all_pass")),
                "med_ref_plain_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("med_ref_plain_all_pass")),
                "med_ref_o2_core_n": sum(1 for p in core_positions if spawn_floor_sub_alerts.get(str(p), {}).get("med_ref_o2_all_pass")),
                "fd_wrapper_overhead_ms": fd_wrapper_overhead_ms,
                "o2_minus_plain_s0_ms": o2_minus_plain_s0_ms,
                "core_min_ci_lo": round(core_min_ci_lo, 2),
                "b5_vs_core": {
                    "tp": b5_core_tp,
                    "core_n": len(core_positions),
                    "b5_alerts": b5_alerts_n,
                    "precision": rate_summary(b5_core_tp, max(1, b5_alerts_n)),
                    "recall": rate_summary(b5_core_tp, max(1, len(core_positions))),
                },
                "spawn_floor_subtracted": spawn_floor_sub_alerts,
                "ns_per_tick_o2_by_position": {str(k): v for k, v in sorted(ns_per_tick_by_pos.items())},
                "ns_per_tick_stats": {str(k): v for k, v in sorted(ns_per_tick_stats.items())},
                "exemplars": exemplars,
            },
            "o0_cpu_cap_relaxation": o0_cpu_cap_relaxation,
            "restoration_forensics_124": {
                **dict(sorted(rest_cats.items())),
                "non_exact_pass": max(0, sum(v for k, v in rest_cats.items() if k.startswith("pass_") and k != "pass_exact_copy")),
                "non_exact_pass_regimes": dict(sorted(non_exact_pass_regimes.items())),
                "non_exact_c1_inflation": rest_non_exact_c1_infl,
                "all_point_excess_fail_n": all_pt_excess_fail_n,
                "all_point_r1_infl_n": all_pt_r1_infl_n,
                "all_point_max_bound_fail_n": all_pt_max_bound_fail_n,
                "all_point_nonreg_r0_fail_positions": sorted(all_pt_nonreg_r0_pos),
            },
            "restoration_total_ticks_124": {
                "pass": tot_pass_n,
                "no_excess": tot_no_ex_n,
                "fail": tot_fail_n,
                "excess_total": tot_ex_n,
                "fail_rate": rate_summary(tot_fail_n, max(1, tot_ex_n)),
                "newly_testable_from_c0_no_excess": rest_tot_new_testable,
                "c0_fail_to_tot_pass": rest_c0_fail_to_tot_pass,
            },
            "restoration_executed_149": {
                "pass": int(rest_exec_counts.get("pass", 0)),
                "no_excess": int(rest_exec_counts.get("no_measurable_excess", 0)),
                "fail": int(rest_exec_counts.get("fail", 0)),
                "unmeasured": int(rest_exec_counts.get("unmeasured", 0)),
            },
            "restoration_s1_pass_183": {
                "pass": int(rest_s1_counts.get("pass", 0)),
                "no_excess": int(rest_s1_counts.get("no_measurable_excess", 0)),
                "fail": int(rest_s1_counts.get("fail", 0)),
                "unmeasured": int(rest_s1_counts.get("unmeasured", 0)),
            },
            "exact_comparisons": {
                "fisher_two_sided": {
                    "P1": _fisher_two_sided_exact(p1_r_d["count"], p1_r_d["total"] - p1_r_d["count"], 14, 147 - 14),
                    "P3": _fisher_two_sided_exact(p3_r_d["count"], p3_r_d["total"] - p3_r_d["count"], 4, 13 - 4),
                    "P3_pilot_12cl": _fisher_two_sided_exact(p3_r_d["count"], p3_r_d["total"] - p3_r_d["count"], 4, 12 - 4),
                    "P3_pilot_12cl_conserv": _fisher_two_sided_exact(p3_r_d["count"], p3_r_d["total"] - p3_r_d["count"], 3, 12 - 3),
                    "S1": _fisher_two_sided_exact(sa1_r_d["count"], sa1_r_d["total"] - sa1_r_d["count"], 103, 147 - 103),
                    "S2": _fisher_two_sided_exact(sa2_r_d["count"], sa2_r_d["total"] - sa2_r_d["count"], 4, 147 - 4),
                    "S3": _fisher_two_sided_exact(sa3_r_d["count"], sa3_r_d["total"] - sa3_r_d["count"], 12, 26 - 12),
                    "SA3_incl_orig_compile_fail": _fisher_two_sided_exact(
                        int((prim["secondary"]["S14_fixture_stops_after_s1_pass"].get("reason_counts_reps") or {}).get("original_compile_failure", 4)),
                        int(prim["secondary"]["S14_fixture_stops_after_s1_pass"]["total"]) - int((prim["secondary"]["S14_fixture_stops_after_s1_pass"].get("reason_counts_reps") or {}).get("original_compile_failure", 4)),
                        12, 26 - 12,
                    ),
                    "S4": _fisher_two_sided_exact(sa4_r_d["count"], sa4_r_d["total"] - sa4_r_d["count"], 1, 14 - 1),
                },
                "pilot_neff_sensitivity": {
                    **{
                        f"n_eff_{ne}": {
                            "n_eff": ne,
                            "p1_k": round(14 / 147 * ne),
                            "p1_p": _fisher_two_sided_exact(p1_r_d["count"], p1_r_d["total"] - p1_r_d["count"], round(14 / 147 * ne), ne - round(14 / 147 * ne)),
                            "sa1_k": round(103 / 147 * ne),
                            "sa1_p": _fisher_two_sided_exact(sa1_r_d["count"], sa1_r_d["total"] - sa1_r_d["count"], round(103 / 147 * ne), ne - round(103 / 147 * ne)),
                        }
                        for ne in (30, 50, 75)
                    },
                    "p1_tip_neff_ge_05": next(
                        (
                            ne
                            for ne in range(30, 4, -1)
                            if _fisher_two_sided_exact(p1_r_d["count"], p1_r_d["total"] - p1_r_d["count"], round(14 / 147 * ne), ne - round(14 / 147 * ne)) >= 0.05
                        ),
                        19,
                    ),
                },
                "mcnemar_screens_vs_b0": mcn_scr_raw,
                "mcnemar_screens_vs_b0_holm5": mcn_scr_holm,
                "holm_primary_finite_sample": fin_primary_holm,
                "joint_conserv_holm_3": holm({
                    "P1": _fisher_two_sided_exact(p1_r_d["count"], p1_r_d["total"] - p1_r_d["count"], round(14 / 147 * 30), 30 - round(14 / 147 * 30)),
                    "P2": float(prim["P2"]["p_unadjusted"]),
                    "P3": _fisher_two_sided_exact(p3_r_d["count"], p3_r_d["total"] - p3_r_d["count"], 3, 12 - 3),
                }),
                "mcnemar_s13_p2": {
                    "baseline": _mcnemar_exact(s13_d_cnt, s13_p1_cnt),
                    "minus_10_oracle_overrides": _mcnemar_exact(s13_d_cnt, s13_p1_cnt - 10),
                    "minus_10_oracle_minus_3_cpucap": _mcnemar_exact(s13_d_cnt, s13_p1_cnt - 13),
                },
                "p2_decomposition": {
                    "total_pp": round(100.0 * (sa1_r_d["count"] - p1_r_d["count"]) / p1_r_d["total"], 1),
                    "unrateable_holds_pp": round(100.0 * (p1_r_d["total"] - int(s13["confirmatory_clusters_past_s0"])) / p1_r_d["total"], 1),
                    "rateable_contrib_pp": round(100.0 * (s13_d_cnt - s13_p1_cnt) / p1_r_d["total"], 1),
                    "holds_share_pct": round(100.0 * (p1_r_d["total"] - int(s13["confirmatory_clusters_past_s0"])) / (sa1_r_d["count"] - p1_r_d["count"]), 1),
                },
            },
        }

        if manifest is not None:
            ranked = sorted(manifest["pairs"], key=representative_rank)
            anon_ord = sorted(anon_rows, key=lambda r: int(r["ordinal"]))
            if sum(1 for r, mp in zip(anon_ord, ranked) if r["frame"] != mp["frame"] or bool(r["quarantined"]) != bool(mp.get("quarantined"))) == 0:
                corpus_split: dict[str, dict[str, int]] = {}
                for r, mp in zip(anon_ord, ranked):
                    if r["quarantined"]:
                        continue
                    c_name = str(mp["corpus"])
                    d = corpus_split.setdefault(c_name, Counter())
                    d["drawn"] += 1
                    if r["S0_stop"]:
                        d["s0_stop"] += 1
                    else:
                        d["s0_pass"] += 1
                        et = str(r["effective_terminal"])
                        if et in S1_DESK_STOPS:
                            d["s1_stop"] += 1
                            if et == "desk_unrateable":
                                d["s1_unrateable"] += 1
                        else:
                            d["s1_pass"] += 1
                        if et == "fixture_stop":
                            d["fixture_stop"] += 1
                        if et in S3_EXECUTED:
                            d["executed"] += 1
                        if et == "execution_oracle_failure":
                            d["oracle_failure"] += 1
                        if et in S4_FITTED:
                            d["fitted"] += 1
                        if et == "alert":
                            d["alert"] += 1
                deep_forensics["confirmatory_corpus_split"] = {k: dict(v) for k, v in sorted(corpus_split.items())}
                pie_d = corpus_split.get("pie-train") or {}
                cod_d = corpus_split.get("codenet") or {}
                if pie_d.get("s0_pass", 0) > 0 and cod_d.get("s0_pass", 0) > 0:
                    deep_forensics["corpus_exec_fisher_p"] = _fisher_two_sided_exact(
                        int(pie_d.get("executed", 0)),
                        int(pie_d["s0_pass"]) - int(pie_d.get("executed", 0)),
                        int(cod_d.get("executed", 0)),
                        int(cod_d["s0_pass"]) - int(cod_d.get("executed", 0)),
                    )

    acd = forensics.get("author_check_downstream_agg") or {}
    if author_check and acd.get("confirmatory_confusion_primary_x_author") and acd.get("quarantined_confusion_primary_x_author"):
        ov_irr = _irr_from_3x3(author_check["bucket_confusion_matrix_primary_x_author"])
        cf_cm = acd["confirmatory_confusion_primary_x_author"]
        cf_irr = _irr_from_3x3(cf_cm)
        qr_irr = _irr_from_3x3(acd["quarantined_confusion_primary_x_author"])
        # Singleton bootstrap CIs (seed 42, 10000 draws) on the 20 independent confirmatory pairs
        cf_pairs = []
        for r_k in ("pass", "contract", "source"):
            for c_k in ("pass", "contract", "source"):
                cf_pairs.extend([(r_k, c_k)] * int((cf_cm.get(r_k) or {}).get(c_k, 0)))
        cf_bkt_ci, cf_bin_ci, cf_pabak_ci, cf_ac1_ci = [0.0, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, 0.0]
        if cf_pairs:
            rng_cf = random.Random(42)
            bk_s, bn_s, pb_s, ac_s = [], [], [], []
            for _ in range(10000):
                samp = rng_cf.choices(cf_pairs, k=len(cf_pairs))
                cm_b: dict[str, dict[str, int]] = {"pass": {}, "contract": {}, "source": {}}
                for r_k, c_k in samp:
                    cm_b[r_k][c_k] = cm_b[r_k].get(c_k, 0) + 1
                ir_b = _irr_from_3x3(cm_b)
                bk_s.append(ir_b["bucket_kappa"])
                bn_s.append(ir_b["binary_kappa"])
                pb_s.append(ir_b["binary_pabak"])
                ac_s.append(ir_b["binary_gwet_ac1"])
            for arr, tgt in ((bk_s, cf_bkt_ci), (bn_s, cf_bin_ci), (pb_s, cf_pabak_ci), (ac_s, cf_ac1_ci)):
                arr.sort()
                tgt[0] = round(arr[249], 3)
                tgt[1] = round(arr[9749], 3)
        cf_irr["bucket_kappa_boot_ci"] = cf_bkt_ci
        cf_irr["binary_kappa_boot_ci"] = cf_bin_ci
        cf_irr["binary_pabak_boot_ci"] = cf_pabak_ci
        cf_irr["binary_ac1_boot_ci"] = cf_ac1_ci

        # Dynamic count of author-rejected LLM passes executing cleanly in Gate 1
        cp_down = acd.get("confirmatory_primary_pass_downstream") or {}
        rej_total = 0
        rej_exec = 0
        for bucket_key in ("author_contract_stop", "author_source_stop"):
            sub_b = cp_down.get(bucket_key) or {}
            rej_total += int(sub_b.get("n", 0))
            terms = sub_b.get("terminals") or {}
            rej_exec += sum(int(v) for tk, v in terms.items() if tk in S3_EXECUTED)
        rej_exec_ci = rate_summary(rej_exec, rej_total) if rej_total > 0 else rate_summary(0, 1)
        conf_fit_rej = 0
        conf_fit_tot = 0
        for bucket_key in ("author_contract_stop", "author_source_stop", "author_other", "author_pass"):
            terms = (cp_down.get(bucket_key) or {}).get("terminals") or {}
            n_fit_b = sum(int(v) for tk, v in terms.items() if tk in ("alert", "no_alert"))
            conf_fit_tot += n_fit_b
            if bucket_key != "author_pass":
                conf_fit_rej += n_fit_b
        conf_fit_rej_ci = rate_summary(conf_fit_rej, conf_fit_tot) if conf_fit_tot > 0 else rate_summary(0, 1)

        cohort_fisher_p = _fisher_two_sided_exact(
            cf_irr["bucket_agree_count"],
            cf_irr["n"] - cf_irr["bucket_agree_count"],
            qr_irr["bucket_agree_count"],
            qr_irr["n"] - qr_irr["bucket_agree_count"],
        )
        # Linear tipping-point curve on rateable S13 (358 clusters: 175 desk stops, 149 executed)
        s13_desk_n = int(s13["secondary"]["S1_desk_stop"]["count"])
        s13_exec_n = int(s13["P1"]["rate"]["count"])
        s13_tot_n = int(s13["confirmatory_clusters_past_s0"])
        p2_desk_n = int(prim["secondary"]["S1_desk_stop"]["count"])
        p2_exec_n = int(prim["P1"]["rate"]["count"])
        p2_tot_n = int(prim["confirmatory_clusters_past_s0"])
        s1_pass_exec_yield = p2_exec_n / max(1, p2_tot_n - p2_desk_n)  # 149/183
        y_denom = max(1, p2_tot_n - p2_desk_n)
        y_r = rate_summary(p2_exec_n, y_denom)
        cp_y_lo, cp_y_hi = clopper_pearson(p2_exec_n, y_denom)
        y_lo, y_hi = cp_y_lo, cp_y_hi
        stop_rev_r = rate_summary(
            cf_irr["binary_matrix"][1][0],
            cf_irr["binary_matrix"][1][0] + cf_irr["binary_matrix"][1][1],
        )
        p_fn = stop_rev_r["count"] / max(1, stop_rev_r["total"])
        cp_pfn_lo, cp_pfn_hi = clopper_pearson(stop_rev_r["count"], max(1, stop_rev_r["total"]))
        plug_theta = p_fn * s1_pass_exec_yield
        plug_theta_ci = [
            round(100.0 * cp_pfn_lo * s1_pass_exec_yield, 1),
            round(100.0 * cp_pfn_hi * s1_pass_exec_yield, 1),
        ]
        two_step_sa13_pp = round(
            100.0 * ((s13_desk_n - s13_exec_n) - s13_desk_n * p_fn * (1.0 + s1_pass_exec_yield)) / max(1, s13_tot_n),
            1,
        )
        one_step_y_lo = round(100.0 * ((s13_desk_n - s13_exec_n) - 2.0 * s13_desk_n * p_fn * y_hi) / max(1, s13_tot_n), 1)
        one_step_y_hi = round(100.0 * ((s13_desk_n - s13_exec_n) - 2.0 * s13_desk_n * p_fn * y_lo) / max(1, s13_tot_n), 1)
        one_step_y_half = round((one_step_y_hi - one_step_y_lo) / 2.0, 1)
        two_step_y_lo = round(100.0 * ((s13_desk_n - s13_exec_n) - s13_desk_n * p_fn * (1.0 + y_hi)) / max(1, s13_tot_n), 1)
        two_step_y_hi = round(100.0 * ((s13_desk_n - s13_exec_n) - s13_desk_n * p_fn * (1.0 + y_lo)) / max(1, s13_tot_n), 1)
        two_step_y_half = round((two_step_y_hi - two_step_y_lo) / 2.0, 1)
        se_pfn_only = math.sqrt((s1_pass_exec_yield ** 2) * p_fn * (1.0 - p_fn) / max(1, stop_rev_r["total"]))
        se_joint = math.sqrt(
            (s1_pass_exec_yield ** 2) * p_fn * (1.0 - p_fn) / max(1, stop_rev_r["total"])
            + (p_fn ** 2) * s1_pass_exec_yield * (1.0 - s1_pass_exec_yield) / y_denom
        )
        se_diff_pp = round(100.0 * (se_joint - se_pfn_only), 2)
        joint_rect_ci = [round(100.0 * cp_pfn_lo * cp_y_lo, 1), round(100.0 * cp_pfn_hi * cp_y_hi, 1)]
        def _betainc_reg(a: float, b: float, x: float) -> float:
            if x <= 0.0:
                return 0.0
            if x >= 1.0:
                return 1.0
            if x > (a + 1.0) / (a + b + 2.0):
                return 1.0 - _betainc_reg(b, a, 1.0 - x)
            front = math.exp(math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log1p(-x)) / a
            f_val = c_val = 1.0
            d_val = 1.0 - (a + b) * x / (a + 1.0)
            d_val = 1.0 / (d_val if abs(d_val) > 1e-30 else 1e-30)
            f_val = d_val
            for m_i in range(1, 200):
                m2 = 2 * m_i
                num = m_i * (b - m_i) * x / ((a + m2 - 1.0) * (a + m2))
                d_val = 1.0 + num * d_val
                d_val = 1.0 / (d_val if abs(d_val) > 1e-30 else 1e-30)
                c_val = 1.0 + num / (c_val if abs(c_val) > 1e-30 else 1e-30)
                f_val *= d_val * c_val
                num = -(a + m_i) * (a + b + m_i) * x / ((a + m2) * (a + m2 + 1.0))
                d_val = 1.0 + num * d_val
                d_val = 1.0 / (d_val if abs(d_val) > 1e-30 else 1e-30)
                c_val = 1.0 + num / (c_val if abs(c_val) > 1e-30 else 1e-30)
                delta = d_val * c_val
                f_val *= delta
                if abs(delta - 1.0) < 1e-13:
                    break
            return front * f_val

        a1_j = stop_rev_r["count"] + 0.5
        b1_j = max(0, stop_rev_r["total"] - stop_rev_r["count"]) + 0.5
        a2_j = p2_exec_n + 0.5
        b2_j = max(0, y_denom - p2_exec_n) + 0.5
        log_b2_norm = math.lgamma(a2_j + b2_j) - math.lgamma(a2_j) - math.lgamma(b2_j)

        def _prod_beta_cdf(z: float) -> float:
            if z <= 0.0:
                return 0.0
            if z >= 1.0:
                return 1.0
            n_sub = 800
            h_step = (1.0 - z) / n_sub
            acc_s = 0.0
            for j_i in range(n_sub + 1):
                y_pt = z + j_i * h_step
                if y_pt <= 0.0 or y_pt >= 1.0:
                    val_pt = 0.0
                else:
                    fy = math.exp(log_b2_norm + (a2_j - 1.0) * math.log(y_pt) + (b2_j - 1.0) * math.log1p(-y_pt))
                    val_pt = fy * _betainc_reg(a1_j, b1_j, min(1.0, z / y_pt))
                w_pt = 1.0 if j_i in (0, n_sub) else (4.0 if j_i % 2 == 1 else 2.0)
                acc_s += w_pt * val_pt
            return _betainc_reg(a2_j, b2_j, z) + (h_step / 3.0) * acc_s

        def _prod_beta_q(prob: float) -> float:
            lo_q, hi_q = 0.0, 1.0
            for _ in range(44):
                mid_q = 0.5 * (lo_q + hi_q)
                if _prod_beta_cdf(mid_q) < prob:
                    lo_q = mid_q
                else:
                    hi_q = mid_q
            return 0.5 * (lo_q + hi_q)

        joint_jeff_ci = [round(100.0 * _prod_beta_q(0.025), 1), round(100.0 * _prod_beta_q(0.975), 1)]
        plugin_grid = [
            {
                "p_fn_pct": round(100.0 * pf_v, 1),
                "y_stopped_pct": round(100.0 * y_v, 1),
                "theta_pct": round(100.0 * pf_v * y_v, 1),
                "sa13_two_step_delta_pp": round(100.0 * ((s13_desk_n - s13_exec_n) - s13_desk_n * pf_v * (1.0 + y_v)) / max(1, s13_tot_n), 1),
            }
            for pf_v in (0.05, 0.10, 0.15, p_fn)
            for y_v in (0.25, 0.50, s1_pass_exec_yield)
        ]

        p3_k_b = int(prim["P3"]["rate"]["count"])
        p3_n_b = int(prim["P3"]["rate"]["total"])
        ora_n_b = int(prim["secondary"]["S4_oracle_failures_among_executed"]["count"])
        def _tip_oracle(pk: int, pn: int) -> dict[str, Any]:
            for kk in range(ora_n_b + 1):
                pv = _fisher_two_sided_exact(p3_k_b + kk, (p3_n_b + ora_n_b) - (p3_k_b + kk), pk, pn - pk)
                if pv >= 0.05:
                    return {"min_k": kk, "denom": ora_n_b, "pct": round(100.0 * kk / max(1, ora_n_b), 1), "resulting_pct": round(100.0 * (p3_k_b + kk) / (p3_n_b + ora_n_b), 1), "fisher_p": pv}
            return {"min_k": ora_n_b, "denom": ora_n_b, "pct": 100.0, "resulting_pct": round(100.0 * (p3_k_b + ora_n_b) / (p3_n_b + ora_n_b), 1), "fisher_p": 1.0}
        def _tip_s1(pk: int, pn: int) -> dict[str, Any]:
            for kk in range(1, s13_desk_n + 1):
                pv = _fisher_two_sided_exact(p3_k_b + kk, p3_n_b - p3_k_b, pk, pn - pk)
                if pv >= 0.05:
                    return {"min_k": kk, "denom": s13_desk_n, "pct": round(100.0 * kk / max(1, s13_desk_n), 1), "resulting_pct": round(100.0 * (p3_k_b + kk) / (p3_n_b + kk), 1), "fisher_p": pv}
            return {"min_k": s13_desk_n, "denom": s13_desk_n, "pct": 100.0, "resulting_pct": round(100.0 * (p3_k_b + s13_desk_n) / (p3_n_b + s13_desk_n), 1), "fisher_p": 1.0}

        def _tip_oracle_adv(pk: int, pn: int) -> dict[str, Any]:
            for kk in range(1, ora_n_b + 1):
                pv = _fisher_two_sided_exact(p3_k_b + kk, p3_n_b - p3_k_b, pk, pn - pk)
                if pv >= 0.05:
                    return {"min_k": kk, "denom": ora_n_b, "pct": round(100.0 * kk / max(1, ora_n_b), 1), "resulting_pct": round(100.0 * (p3_k_b + kk) / (p3_n_b + kk), 1), "fisher_p": pv}
            return {"min_k": ora_n_b, "denom": ora_n_b, "pct": 100.0, "resulting_pct": round(100.0 * (p3_k_b + ora_n_b) / (p3_n_b + ora_n_b), 1), "fisher_p": 1.0}

        no_alert_n_b = max(0, p3_n_b - p3_k_b)

        def _tip_sa13_fp() -> dict[str, Any]:
            for kk in range(1, s13_exec_n + 1):
                pv = _mcnemar_exact(s13_desk_n + kk, s13_exec_n - kk)
                if pv < 0.05:
                    return {
                        "min_k": kk,
                        "denom": s13_exec_n,
                        "pct": round(100.0 * kk / max(1, s13_exec_n), 1),
                        "delta_pp": round(100.0 * ((s13_desk_n + kk) - (s13_exec_n - kk)) / max(1, s13_tot_n), 1),
                        "sign_p": pv,
                    }
            return {"min_k": s13_exec_n, "denom": s13_exec_n, "pct": 100.0, "delta_pp": 0.0, "sign_p": 1.0}

        def _tip_p3_fp(pk: int, pn: int) -> dict[str, Any]:
            for kk in range(1, no_alert_n_b + 1):
                pv = _fisher_two_sided_exact(p3_k_b, no_alert_n_b - kk, pk, pn - pk)
                if pv >= 0.05:
                    return {
                        "min_k": kk,
                        "denom": no_alert_n_b,
                        "pct": round(100.0 * kk / max(1, no_alert_n_b), 1),
                        "resulting_pct": round(100.0 * p3_k_b / max(1, p3_n_b - kk), 1),
                        "fisher_p": pv,
                    }
            return {"min_k": no_alert_n_b, "denom": no_alert_n_b, "pct": 100.0, "resulting_pct": 100.0, "fisher_p": 1.0}

        cohort_18cl_ps = [
            _fisher_two_sided_exact(cf_irr["bucket_agree_count"], cf_irr["n"] - cf_irr["bucket_agree_count"], kk, 18 - kk)
            for kk in (10, 11)
        ]

        deep_forensics["s1_irr_stratified"] = {
            "overall": ov_irr,
            "confirmatory": cf_irr,
            "quarantined": qr_irr,
            "cohort_bucket_fisher_p": cohort_fisher_p,
            "cohort_bucket_fisher_18cl_range": [round(min(cohort_18cl_ps), 3), round(max(cohort_18cl_ps), 3)],
            "confirmatory_contract_reversal_ci": rate_summary(cf_irr["contract_to_author_pass_count"], cf_irr["contract_total"]),
            "confirmatory_all_stop_reversal_ci": stop_rev_r,
            "author_rejected_pass_exec_ci": rej_exec_ci,
            "author_rejected_conf_fits_ci": conf_fit_rej_ci,
            "manski_bounds": {
                "tipping_theta_sa13_pct": round(100.0 * ((s13_desk_n - s13_exec_n) / 2.0) / max(1, s13_desk_n), 1),
                "tipping_theta_full_p2_pct": round(100.0 * ((p2_desk_n - p2_exec_n) / 2.0) / max(1, s13_desk_n), 1),
                "tipping_pfn_two_step_pct": round(100.0 * (s13_desk_n - s13_exec_n) / max(1e-9, s13_desk_n * (1.0 + s1_pass_exec_yield)), 1),
                "tipping_theta_two_step_pct": round(100.0 * ((s13_desk_n - s13_exec_n) / max(1e-9, s13_desk_n * (1.0 + s1_pass_exec_yield))) * s1_pass_exec_yield, 1),
                "sa13_fp_tipping": _tip_sa13_fp(),
                "p3_fp_tipping": {
                    "vs_3_12_conserv": _tip_p3_fp(3, 12),
                    "vs_4_13": _tip_p3_fp(4, 13),
                },
                "plugin_theta_pct": round(100.0 * plug_theta, 1),
                "plugin_theta_ci_pct": plug_theta_ci,
                "plugin_theta_joint_rect_ci_pct": joint_rect_ci,
                "plugin_theta_joint_jeffreys_ci_pct": joint_jeff_ci,
                "plugin_grid": plugin_grid,
                "p3_tipping": {
                    "oracle_vs_4_13": _tip_oracle(4, 13),
                    "oracle_vs_3_12_conserv": _tip_oracle(3, 12),
                    "oracle_adv_vs_4_13": _tip_oracle_adv(4, 13),
                    "oracle_adv_vs_3_12_conserv": _tip_oracle_adv(3, 12),
                    "s1_vs_4_13": _tip_s1(4, 13),
                    "s1_vs_3_12_conserv": _tip_s1(3, 12),
                },
                "plugin_sa13_delta_pp": round(100.0 * ((s13_desk_n - s13_exec_n) - 2.0 * s13_desk_n * plug_theta) / max(1, s13_tot_n), 1),
                "plugin_sa13_two_step_delta_pp": two_step_sa13_pp,
                "plugin_rateable_p1_pct": round(100.0 * (s13_exec_n + s13_desk_n * plug_theta) / max(1, s13_tot_n), 1),
                "plugin_full_p2_delta_pp": round(100.0 * ((p2_desk_n - p2_exec_n) - 2.0 * s13_desk_n * plug_theta) / max(1, p2_tot_n), 1),
                "plugin_sa13_y_ci_pp": [one_step_y_lo, one_step_y_hi],
                "plugin_sa13_y_half_width_pp": one_step_y_half,
                "plugin_sa13_two_step_y_ci_pp": [two_step_y_lo, two_step_y_hi],
                "plugin_sa13_two_step_y_half_width_pp": two_step_y_half,
                "plugin_theta_delta_se_diff_pp": se_diff_pp,
            },
        }

    enriched = dict(forensics)
    enriched["verified_from_anon_measurements"] = anon_rows is not None
    if anon_rows is not None:
        enriched["b1_fp_decomposition"] = dict(sorted(b1_fp_decomp.items()))
    if deep_forensics:
        enriched.update(deep_forensics)
    return enriched


def _fmt_range(vals: list[float], decimals: int = 2, *, suffix: str = "") -> str:
    lo, hi = min(vals), max(vals)
    if round(lo, decimals) == round(hi, decimals):
        return f"{lo:.{decimals}f}{suffix}"
    return f"{lo:.{decimals}f}--{hi:.{decimals}f}{suffix}"


def _fmt_ratio_range(vals: list[float]) -> str:
    lo, hi = min(vals), max(vals)
    if any(v >= 100_000 for v in (lo, hi)):
        def _sci(v: float) -> str:
            if v >= 1_000_000:
                return f"{v / 1e6:.2f}\\text{{M}}"
            mant, exp_s = f"{v:.2e}".split("e")
            return f"${mant}\\times 10^{{{int(exp_s)}}}$"
        s_lo, s_hi = _sci(lo), _sci(hi)
        if s_lo == s_hi:
            return f"{s_lo}$\\times$"
        return f"{s_lo}--{s_hi}$\\times$"

    def _one(v: float) -> str:
        if v >= 100:
            return _tex_int(int(round(v)))
        return f"{v:.2f}"
    s_lo, s_hi = _one(lo), _one(hi)
    if s_lo == s_hi:
        return f"{s_lo}$\\times$"
    return f"{s_lo}--{s_hi}$\\times$"


def build_paper_claims(
    slots_tex: str,
    *,
    manifest_sha: str = MANIFEST_SHA,
    protocol_sha: str = PROTOCOL_SHA,
    amendment_sha: str = AMENDMENT_5_SHA,
    agg_sha: str | None = None,
    author_sha: str | None = None,
    forensics_sha: str | None = None,
    anon_sha: str | None = None,
    grouped_sha: str | None = None,
) -> dict[str, Any]:
    """Emit machine-verifiable claim ledger mapping every manuscript macro to evidence class & SHA."""
    import re as _re

    frozen_consts = {
        "BenchPairs", "BenchPIE", "BenchVal", "BenchTrain", "BenchCodeNet", "BenchGitHub",
        "BenchContestPairs", "BenchGCC", "BenchUbuntuVer", "BenchBwrapVer", "BenchMemCapMiB", "BenchTasksCap",
        "BenchAsCapMiB", "BenchWallCapSec", "BenchCompileTimeoutSec", "BenchTickExitCode",
        "BenchMinClusters", "BenchMinFits", "BenchMinSizes",
        "BenchMinSpan", "BenchMinSlope", "BenchMinRatio", "BenchRecovery", "BenchAuthorSample",
        "BenchPinManifest", "BenchPinProtocol", "BenchPinHolds", "BenchPinAmendFive",
        "BenchCpuCapSec", "BenchStackCapMB", "BenchFileCapMB", "BenchTickCeiling", "BenchCpuFloorMs",
        "BenchSpawnFloorMs", "BenchCensorTolPct",
        "BenchNumVariants", "BenchNumModes", "BenchNumStreams", "BenchFDWire",
        "BenchBetaGridMin", "BenchBetaGridDrop",
        "BenchCensorSlopeMin",
        "BenchOLSMinRSq", "BenchPosThreeLev", "BenchRestTwoSidedBand",
        "BenchRestSurgicalBand", "BenchRestMildBand", "BenchRestHighBand",
    }
    pilot_archived_macros = {
        "BenchPilotPairs", "BenchPilotDeskN", "BenchPilotDeskPct", "BenchPilotExecN", "BenchPilotExecPct",
        "BenchPilotExecUpperPct", "BenchPilotFitN", "BenchPilotFitClustersN", "BenchPilotAlertN", "BenchPilotAlertPct", "BenchPilotIntakeAlertPct",
        "BenchPilotFitClustersFrac", "BenchPilotConservFrac", "BenchPilotNeffThirty", "BenchPilotNeffFifty", "BenchPilotNeffRange",
        "BenchPilotPrepN", "BenchPilotPrepDenom", "BenchPilotPrepPct", "BenchPilotOracleN", "BenchPilotOraclePct",
        "BenchPilotSAFiveDelta",
    }
    manifest_reexec_macros = {
        "BenchIntakeStopsN", "BenchIntakeDupN", "BenchIntakeUnretN", "BenchIntakeContestN", "BenchIntakeRepoN",
        "BenchSOPassN", "BenchQuarPairsN", "BenchQuarClustersN", "BenchConfPairsN", "BenchConfClustersN",
        "BenchConfContestClustersN", "BenchConfRepoClustersN", "BenchConfRepoPairsN", "BenchConfSingletonN",
        "BenchConfRepoSingletonN", "BenchConfContestDrawn", "BenchConfContestIntake", "BenchQuarIntakeN",
        "BenchFlowIntakeC", "BenchFlowIntakeR", "BenchFlowIntakeU",
    }
    trace_forensics_macros = {
        "BenchAlertForensicsRows", "BenchTableAppRows", "BenchTableCorpusRows",
        "BenchHeldUnratAllN", "BenchRepoDeskUnratN", "BenchContestUnbundledConfN",
        "BenchHeldUnratConfClustN", "BenchHeldConfPairsN", "BenchRateablePairsN",
        "BenchQuarPostSOneZeroN", "BenchMaxCounterVal",
        "BenchUnconfRestoredOracleN", "BenchFittedMaskedFailN",
        "BenchPosOneSixFourTotSlopeTwoDec", "BenchPosThreeWorstTS",
        "BenchPosNineSevenPlainStreamsN", "BenchAllPtMaxBoundFailN",
        "BenchBwrapOverheadMs", "BenchWaveOneOverrideN",
        "BenchPosNineFourPlainUpperNs", "BenchPosTwoNine", "BenchPinWaveTwoCap",
        "BenchPosNineZeroOZeroOnlyPts", "BenchPosNineSevenOtwoStreamsN",
        "BenchPosThirteenPlainStreamsFrac", "BenchPosThirteenOtwoStreamsFrac",
        "BenchPosOneSevenFivePlainStreamsFrac", "BenchPosOneSevenFiveOtwoStreamsFrac",
        "BenchPosOneSixFourPlainStreamsFrac", "BenchPosOneSixFourOtwoStreamsFrac",
        "BenchPosNineFourPlainStreamsFrac", "BenchPosNineFourOtwoStreamsFrac",
        "BenchPosNineSevenPlainStreamsFrac",
        "BenchOraclePlainSegvUBN", "BenchOraclePlainUpstreamN", "BenchOracleUBAllN",
        "BenchMinRefPlainCoreN", "BenchMinRefOtwoCoreN", "BenchMedRefPlainCoreN", "BenchMedRefOtwoCoreN",
        "BenchAddCpuOneThreeSlopeRange", "BenchAddCpuOneSevenFiveSlopeRange",
        "BenchAddCpuOneSixFourSlopeRange", "BenchAddCpuNineFourSlopeRange", "BenchAddCpuNineSevenSlopeRange",
        "BenchOtwoMinusPlainSZeroMs",
        "BenchRestNonExSATwoN", "BenchRestNonExSubN", "BenchRestNonExFlatN", "BenchRestNonExNegN", "BenchRestNonExMixN",
        "BenchAllPtExcessFailN", "BenchAllPtRoneInflN", "BenchAllPtNonRegFailN", "BenchPosEighteen", "BenchPosFourFour",
        "BenchPOnePilotNeffTipN", "BenchSAThreeCrossFrameP",
        "BenchOZeroAgree", "BenchOZeroMiss", "BenchOZeroCapped", "BenchOZeroTotalTriples",
        "BenchOZeroOracleAbort", "BenchOZeroOverlayFix", "BenchOZeroInfraMiss", "BenchOZeroCapOtwoAgree",
        "BenchShamAgree", "BenchShamMiss", "BenchShamCapped", "BenchShamTotalPairs",
        "BenchShamOracleAbort", "BenchShamOverlayFix", "BenchShamInfraMiss",
        "BenchCpuCapEvents", "BenchCpuCapPos", "BenchTickCapEvents", "BenchTickCapPos",
        "BenchCpuCapOZeroOnlyPts", "BenchCpuCapTotalPts",
        "BenchOracleUpstreamN", "BenchOracleUpstreamPct", "BenchOracleUpstreamCI",
        "BenchOracleUpstreamTgtN", "BenchOracleUpstreamRefN",
        "BenchOraclePlainN", "BenchOraclePlainTgtN", "BenchOraclePlainRefN",
        "BenchOracleUBSanOnlyN", "BenchOracleUBTgtN", "BenchOracleUBRefN",
        "BenchOracleRestoredN", "BenchOracleShamN", "BenchOracleMultiEvtN",
        "BenchOracleCoordN", "BenchOracleCoordPct",
        "BenchFitQZeroN", "BenchFitBothZeroN", "BenchFitTickCapN",
        "BenchCensorCondN", "BenchCensorDenom", "BenchCensorCondPct", "BenchCensorCondCI",
        "BenchCensorWorstN", "BenchCensorWorstPct", "BenchCensorWorstCI", "BenchCensorWorstFisherP",
        "BenchCensorWorstFisherFourTwelveP", "BenchCensorWorstFisherConservP",
        "BenchCensorCpuCapExclFlatN", "BenchCensorCpuCapExclFlatPct", "BenchCensorCpuCapExclFlatP", "BenchCensorCpuCapExclFlatConservP",
        "BenchCensorCpuCapTotalN", "BenchCensorCpuCapPct", "BenchCensorCpuCapFourTwelveP", "BenchCensorCpuCapConservP",
        "BenchJointConservHolmPOne", "BenchJointConservHolmPThree",
        "BenchWaveOnePin", "BenchWaveTwoPin", "BenchFDWrapOverheadMs",
        "BenchPlainSubCoreN", "BenchOtwoSubCoreN",
        "BenchPosThirteenPlainZeroSubRange", "BenchPosThirteenOtwoSubSlopeRange", "BenchPosOneSevenFiveOtwoSubSlopeRange",
        "BenchPosThirteenPlainDeltaMsRange", "BenchPosOneSevenFivePlainDeltaMsRange",
        "BenchPosFourSevenCOneStream", "BenchPosElevenCOneStream",
        "BenchPosThreeCooksDSThreeMax",
        "BenchRegimeExactEqN", "BenchRegimeFlatLowN", "BenchRegimeFlatHighN", "BenchRegimeZeroFlatSumN",
        "BenchRegimeNegAllN", "BenchRegimeMixedN", "BenchRegimeSubPosN", "BenchRegimeRevSubSumN", "BenchBetaGridDropAlerts",
        "BenchCorpusPieAlertFrac", "BenchCorpusCodeAlertFrac", "BenchCorpusAlertFisherP",
        "BenchCorpusPieExecFrac", "BenchCorpusCodeExecFrac", "BenchCorpusExecFisherP",
        "BenchContestExecPct", "BenchContestExecCI", "BenchContestExecLo",
        "BenchSAFourFisherP", "BenchSAThreeDenom", "BenchSAThreeAllSPass", "BenchSAThreeAllSPassCI",
        "BenchPosThreeRSq", "BenchPosThreeCooksD", "BenchPosThreeCooksDSThree",
        "BenchPosThreeSOneLOO", "BenchPosThreeSThreeLOO", "BenchPosThreeSOneCI", "BenchPosThreeSThreeCI",
        "BenchCoreMinCILo", "BenchPosThirteenCZeroSlope", "BenchPosThirteenTotSlope",
        "BenchPosSevenSevenLogRSq", "BenchPosOneSixFourRatio", "BenchPosOneSixFourTotP",
        "BenchPosOneSixFourTotSlope", "BenchPosOneSixFourTotRSq",
        "BenchPosSevenNine", "BenchPosSevenNineSlopeRange", "BenchPosSevenNineRatioRange",
        "BenchQuarSourceN", "BenchQuarHeldN", "BenchQuarIndetN",
        "BenchTotalFittedStreamsN",
        "BenchDistinctThreeN", "BenchDistinctThreePct", "BenchDistinctTwoN", "BenchDistinctTwoPct",
        "BenchDistinctOneN", "BenchDistinctOnePct", "BenchDistinctOneCOneVarN", "BenchDistinctOneOblivN",
        "BenchZeroVarStreamsN", "BenchDefinedRTwoStreamsN", "BenchAllStreamsMedianRTwo", "BenchAlertMedianRTwo",
        "BenchZeroVarPairsN", "BenchDefinedRTwoPairsN", "BenchPairMedianRTwo", "BenchAlertPairMedianRTwo", "BenchConstZeroVarPairsN",
        "BenchPThreePilotClustFisherP", "BenchPThreePilotClustConservP", "BenchPOnePilotNeffThirtyP", "BenchPOnePilotNeffFiftyP", "BenchSAOnePilotNeffRangeP",
        "BenchSAThreeInclCompileN", "BenchSAThreeInclCompilePct", "BenchSAThreeInclCompileP",
        "BenchCensorCpuCapFisherP", "BenchRestCOneMaskN", "BenchSANinePThreeCI",
        "BenchOZeroRelaxCapPtsN", "BenchOZeroRelaxPairsN", "BenchOZeroRelaxDeltaN",
        "BenchRealizedCpuCoreN", "BenchPosOneSixFourCpuRatio",
        "BenchSubCpuOneSevenFiveSlopeRange", "BenchSubCpuOneThreeSlopeRange", "BenchSubCpuOneSixFourSlopeRange", "BenchSubCpuNineFourSlopeRange", "BenchSubCpuNineSevenSlopeRange",
        "BenchPosSevenOne", "BenchPosNineNine", "BenchPosOneZeroSeven", "BenchPosOneOneSix",
        "BenchPosOneThreeNine", "BenchPosOneFourOne", "BenchPosOneSixSeven",
        "BenchSASevenCount", "BenchSASevenPct", "BenchSASevenCI", "BenchSASevenOnlyN",
        "BenchSAEightAdmittedN", "BenchSAEightAlertsN", "BenchSAEightPct", "BenchSAEightCI",
        "BenchSAEightAnyAlertsN", "BenchSAEightAnyPct", "BenchSAEightAnyCI",
        "BenchCoreFourN", "BenchCoreFourPct", "BenchCoreFourCI",
        "BenchBOneAlertsN", "BenchBOnePct", "BenchBOneCI", "BenchBOneFPN",
        "BenchBOneFlatN", "BenchBOneSubN", "BenchBOneNegN", "BenchBOneSelN", "BenchBOneMcNemarP", "BenchBOneHolmP",
        "BenchBTwoAlertsN", "BenchBTwoPct", "BenchBTwoCI",
        "BenchBThreeAlertsN", "BenchBThreePct", "BenchBThreeCI",
        "BenchBThreeAllExecN", "BenchBThreeAllExecDenom", "BenchBThreeAllExecPct",
        "BenchBFourAlertsN", "BenchBFourPct", "BenchBFourCI", "BenchBFourMcNemarP", "BenchBFourHolmP",
        "BenchBFiveAlertsN", "BenchBFivePct", "BenchBFiveCI", "BenchBFiveTPN", "BenchBFiveFPN",
        "BenchBFiveMcNemarP", "BenchBFiveHolmP", "BenchBFiveCoreTPN", "BenchBFiveCorePrecPct", "BenchBFiveCoreRecPct",
        "BenchRestPassAllN", "BenchRestNoExAllN", "BenchRestFailAllN", "BenchRestUnmeasAllN",
        "BenchRestExecPassN", "BenchRestExecNoExN", "BenchRestExecFailN", "BenchRestExecUnmeasN",
        "BenchRestFitPassN", "BenchRestFitNoExN", "BenchRestFitFailN", "BenchRestFitExcessN",
        "BenchRestFitFailPct", "BenchRestFitFailCI",
        "BenchRestExactCopyN", "BenchRestExactCopyPct", "BenchRestNonExactPassN", "BenchRestSurgicalN", "BenchRestMildOverN", "BenchRestHighOverN", "BenchRestCOneInflN",
        "BenchRestTotPassN", "BenchRestTotNoExN", "BenchRestTotFailN", "BenchRestTotExcessN", "BenchRestTotFailPct", "BenchRestTotFailCI", "BenchRestTotNewTestN",
        "BenchConfDeskPairsN", "BenchFinHolmPOne", "BenchFinHolmPThree",
        "BenchCOneOnlyCount", "BenchPosEleven", "BenchPosElevenCOneRatio", "BenchQOneZeroCount", "BenchEnvSAThirteenShort",
        "BenchPfStderrN", "BenchPfSigabrtN", "BenchPfSigsegvN",
        "BenchPosNineFourOtwoNsRange", "BenchPosNineFourPlainNsRange", "BenchPosNineFourOtwoMsRange",
        "BenchPosOneSevenFiveOtwoNsRange", "BenchPosOneSevenFivePlainNsRange",
        "BenchPosThree", "BenchPosThirteen", "BenchPosTwoSeven", "BenchPosFourSeven", "BenchPosFiveFive",
        "BenchPosFiveNine", "BenchPosSevenSeven", "BenchPosSevenNine", "BenchPosNineZero", "BenchPosNineOne", "BenchPosNineFour",
        "BenchPosNineSeven", "BenchPosOneZeroZero", "BenchPosOneZeroSix", "BenchPosOneTwoNine",
        "BenchPosOneThreeOne", "BenchPosOneFourZero", "BenchPosOneFourFive", "BenchPosOneFiveEight",
        "BenchPosOneSixZero", "BenchPosOneSixFour", "BenchPosOneSevenFour", "BenchPosOneSevenFive",
        "BenchPosSevenSevenRatio", "BenchPosNineZeroRatio", "BenchPosOneFourFiveRatio",
        "BenchPosFourSevenCOneRatio", "BenchPosNineFourTicksM",
        "BenchPosOneSixFourTotRatio", "BenchPosOneZeroZeroMaxSlope", "BenchPosBothZeroMaxSlope",
        "BenchRestOverNineOneRange", "BenchRestOverOneTwoNineRange",
        "BenchEnvPOneRange", "BenchEnvPThreeRange", "BenchEnvSAFourRange", "BenchEnvSAThirteenRange",
        "BenchQuarStopPct", "BenchQuarStopCI", "BenchQuarClustStopFrac", "BenchQuarClustStopCI",
        "BenchPinAnon", "BenchPinForensics",
    }
    author_macros = {
        "BenchTableFourRows",
        "BenchAuthExactPct", "BenchAuthExactK", "BenchAuthExactCI",
        "BenchAuthBucketPct", "BenchAuthBucketK", "BenchAuthBucketCI",
        "BenchAuthBucketKappaMax", "BenchAuthBucketACOne",
        "BenchAuthBinPct", "BenchAuthBinK", "BenchAuthBinPABAK", "BenchAuthBinACOne",
        "BenchAuthBinBI", "BenchAuthBinPI", "BenchAuthBowkerQ",
        "BenchAuthMcNemarP", "BenchAuthBowkerP",
        "BenchAuthConfN", "BenchAuthQuarN", "BenchAuthQuarClustersN", "BenchAuthTotalClustersN",
        "BenchAuthLLMPassFrac", "BenchAuthAuthorPassFrac",
        "BenchAuthConfPct", "BenchAuthConfKappa", "BenchAuthConfBinK",
        "BenchAuthConfBucketKCI", "BenchAuthConfBinKCI", "BenchAuthConfPABAKCI", "BenchAuthConfACOneCI",
        "BenchAuthConfAllStopRev", "BenchAuthConfAllStopRevCI",
        "BenchAuthConfPassStopN", "BenchAuthConfStopPassN", "BenchAuthConfMcNemarP",
        "BenchAuthConfBowkerQ", "BenchAuthConfBowkerP", "BenchAuthConfBowkerExactP", "BenchAuthAllBowkerExactP",
        "BenchAuthQuarPct", "BenchAuthQuarKappa", "BenchAuthQuarBinK", "BenchAuthQuarRev",
        "BenchAuthCohortFisherP", "BenchCohortClustSensP",
        "BenchAuthConfContractRev", "BenchAuthConfContractRevCI",
        "BenchAuthRejExec", "BenchAuthRejExecCI",
        "BenchAuthStopPassN", "BenchAuthPassStopN", "BenchAuthRejTotalN", "BenchManskiTipNum",
        "BenchManskiTipRate", "BenchManskiPlugInTheta", "BenchManskiPlugInThetaCI",
        "BenchManskiPlugJointRectCI", "BenchManskiPlugJointJeffCI",
        "BenchManskiPlugInSAThirteen", "BenchManskiPlugInTwoStepSAThirteen",
        "BenchManskiPlugInPOne", "BenchManskiFullFlipTheta",
        "BenchManskiTwoStepTipTheta", "BenchManskiTwoStepTipPfn",
        "BenchManskiYOneStepHalfPP", "BenchManskiYTwoStepHalfPP", "BenchManskiYDeltaSEDiffPP",
        "BenchPThreeOracleTipN", "BenchPThreeOracleTipPct", "BenchPThreeOracleTipResultPct",
        "BenchPThreeOracleTipConservN", "BenchPThreeOracleTipConservPct",
        "BenchPThreeOracleAdvTipN", "BenchPThreeOracleAdvTipPct",
        "BenchPThreeOracleAdvTipConservN", "BenchPThreeOracleAdvTipConservPct",
        "BenchPThreeSOneTipN", "BenchPThreeSOneTipPct", "BenchPThreeSOneTipResultPct",
        "BenchPThreeSOneTipConservN", "BenchPThreeSOneTipConservPct",
        "BenchSAThirteenFpTipN", "BenchSAThirteenFpTipPct", "BenchSAThirteenFpTipDelta", "BenchSAThirteenFpTipP",
        "BenchAuthConfFitRejFrac",
        "BenchPThreeFpTipConservN", "BenchPThreeFpTipConservPct", "BenchPThreeFpTipConservP",
        "BenchPThreeFpTipFullN", "BenchPThreeFpTipFullPct", "BenchPThreeFpTipFullP",
    }

    base_pins = [p for p in (manifest_sha, protocol_sha, HELD_SHA, amendment_sha) if p]
    stat_pins = [p for p in (agg_sha, anon_sha, forensics_sha) if p]
    auth_pins = [p for p in (author_sha, AUTHOR_DRAW_SHA, forensics_sha) if p]

    claims: list[dict[str, Any]] = []
    for raw_ln in slots_tex.splitlines():
        ln = raw_ln.strip()
        if not ln.startswith(r"\newcommand{\Bench"):
            continue
        m = _re.match(r"^\\newcommand\{\\(Bench[A-Za-z0-9]+)\}(?:\[\d+\])?\{(.*)\}$", ln)
        if not m:
            continue
        name, val = m.group(1), m.group(2)
        if name in ("BenchSlot", "BenchCell"):
            continue
        if name in frozen_consts:
            ev_cls = "protocol-constant"
            inst = "frozen_manifest_and_protocol_constant"
            srcs = base_pins
        elif name in pilot_archived_macros:
            ev_cls = "replay-only"
            inst = "archived_147_pair_pilot_outcome"
            srcs = [protocol_sha]
        elif name in manifest_reexec_macros:
            ev_cls = "re-executable"
            inst = "frozen_manifest_intake_and_quarantine_replay"
            srcs = [manifest_sha, protocol_sha]
        elif name in trace_forensics_macros:
            ev_cls = "replay-only"
            inst = "single_workflow_llm_s1_plus_recorded_gate1_trace_replay"
            srcs = base_pins + stat_pins
        elif name in author_macros:
            ev_cls = "replay-only"
            inst = "blind_single_author_s1_vs_primary_workflow"
            srcs = base_pins + auth_pins + ([agg_sha] if agg_sha else [])
        else:
            ev_cls = "replay-only"
            inst = "single_workflow_llm_s1_plus_deterministic_gate1"
            srcs = base_pins + stat_pins + ([author_sha] if author_sha else [])
        claims.append({
            "macro": name,
            "evidence_class": ev_cls,
            "instrument": inst,
            "source_sha256": list(dict.fromkeys(srcs)),
            "rendered_tex": val,
        })

    grouped_srcs = [grouped_sha] if grouped_sha else [protocol_sha]
    for g_name, g_val in (
        ("GroupedQuadraticFalse", "5/5 = 100.0\\%"),
        ("GroupedLinearFalse", "0/5 = 0.0\\%"),
        ("GroupedAppropriateFalse", "10/10 = 100.0\\%"),
    ):
        claims.append({
            "macro": g_name,
            "evidence_class": "replay-only",
            "instrument": "archived_pilot_deterministic_specificity_replay",
            "source_sha256": grouped_srcs,
            "rendered_tex": g_val,
        })

    return {
        "schema": "eapg.expansion.paper_claims.v1",
        "manifest_sha256": manifest_sha,
        "protocol_sha256": protocol_sha,
        "amendment_sha256": amendment_sha,
        "held_out_used": False,
        "claim_count": len(claims),
        "claims": claims,
    }


def render_benchmark_slots(
    report: dict[str, Any],
    *,
    s1_complete: bool = False,
    execution_complete: bool = False,
    author_check: dict[str, Any] | None = None,
    forensics: dict[str, Any] | None = None,
    manifest: dict[str, Any] | None = None,
) -> str:
    """Emit atomic receipt-bound benchmark_slots.tex macros and table rows."""
    flow = report["flow_table"]
    prim = report["primary_all_post_s0"]
    s13 = report["S13_without_desk_unrateable"]
    inv = report["fixture_inventory"]
    amendment_sha = report.get("amendment_sha256") or AMENDMENT_5_SHA
    if forensics is None:
        forensics = report.get("forensics")

    def _ci_br(r: dict[str, Any] | None) -> str:
        if not r or not r.get("clopper_pearson_95pct_percent"):
            return "n/a"
        lo, hi = r["clopper_pearson_95pct_percent"]
        return f"[{lo:.1f}\\%, {hi:.1f}\\%]"

    def _ci_num(r: dict[str, Any] | None) -> str:
        if not r or not r.get("clopper_pearson_95pct_percent"):
            return "n/a"
        lo, hi = r["clopper_pearson_95pct_percent"]
        return f"[{lo:.1f}, {hi:.1f}]\\%"

    def _boot_br(ci: list[float] | None, unit: str = "~pp") -> str:
        if not ci or len(ci) < 2:
            return "n/a"
        return f"[{_tex_s1(ci[0])}, {_tex_s1(ci[1])}]{unit}"

    def _pct_str(r: dict[str, Any] | None) -> str:
        if not r or r.get("percent") is None:
            return "0.0\\%"
        return f"{r['percent']:.1f}\\%"

    def flow_macro(name: str, field: str, available: bool) -> list[str]:
        if not available:
            return [
                f"\\newcommand{{\\BenchFlow{name}C}}{{\\BenchCell}}",
                f"\\newcommand{{\\BenchFlow{name}R}}{{\\BenchCell}}",
                f"\\newcommand{{\\BenchFlow{name}U}}{{\\BenchCell}}",
            ]
        return [
            f"\\newcommand{{\\BenchFlow{name}C}}{{{_tex_int(flow['Contest'][field])}}}",
            f"\\newcommand{{\\BenchFlow{name}R}}{{{_tex_int(flow['Repository'][field])}}}",
            f"\\newcommand{{\\BenchFlow{name}U}}{{{_tex_int(flow['Union'][field])}}}",
        ]

    lines = [
        "% Auto-generated from verified expansion analysis receipt (do not hand-edit).",
        f"% Manifest SHA-256: {report['manifest_sha256']}",
        f"% Amendment 5 SHA-256: {amendment_sha}",
        r"\newcommand{\BenchPairs}{1{,}000}",
        r"\newcommand{\BenchPIE}{728}",
        r"\newcommand{\BenchVal}{500}",
        r"\newcommand{\BenchTrain}{228}",
        r"\newcommand{\BenchCodeNet}{228}",
        r"\newcommand{\BenchGitHub}{44}",
        r"\newcommand{\BenchContestPairs}{956}",
        r"\newcommand{\BenchGCC}{15.2.0}",
        r"\newcommand{\BenchMinClusters}{200}",
        r"\newcommand{\BenchMinFits}{30}",
        r"\newcommand{\BenchMinSizes}{4}",
        r"\newcommand{\BenchMinSpan}{8}",
        r"\newcommand{\BenchMinSlope}{0.50}",
        r"\newcommand{\BenchMinRatio}{1.50}",
        r"\newcommand{\BenchRecovery}{80\%}",
        r"\newcommand{\BenchAuthorSample}{50}",
        r"\newcommand{\BenchPilotPairs}{147}",
        r"\newcommand{\BenchPilotDeskN}{103}",
        r"\newcommand{\BenchPilotDeskPct}{70.1\%}",
        r"\newcommand{\BenchPilotExecN}{14}",
        r"\newcommand{\BenchPilotExecPct}{9.5\%}",
        r"\newcommand{\BenchPilotFitN}{13}",
        r"\newcommand{\BenchPilotAlertN}{4}",
        r"\newcommand{\BenchPilotAlertPct}{30.8\%}",
        r"\newcommand{\BenchPilotIntakeAlertPct}{2.7\%}",
        r"\newcommand{\BenchPilotPrepN}{12}",
        r"\newcommand{\BenchPilotPrepDenom}{26}",
        r"\newcommand{\BenchPilotPrepPct}{46.2\%}",
        r"\newcommand{\BenchPilotOracleN}{1}",
        r"\newcommand{\BenchPilotOraclePct}{7.1\%}",
        r"\newcommand{\BenchPilotSAFiveDelta}{$-33.3$~pp}",
        r"\newcommand{\BenchCpuCapSec}{8\,s}",
        r"\newcommand{\BenchStackCapMB}{8\,\text{MiB}}",
        r"\newcommand{\BenchFileCapMB}{8\,\text{MiB}}",
        r"\newcommand{\BenchTickCeiling}{$\max(2\times 10^{6},\,5N^{2})$}",
        r"\newcommand{\BenchCpuFloorMs}{10\,\text{ms}}",
        r"\newcommand{\BenchSpawnFloorMs}{0.5\,\text{ms}}",
        r"\newcommand{\BenchCensorTolPct}{10\%}",
        r"\newcommand{\BenchBwrapVer}{0.11.1}",
        r"\newcommand{\BenchPilotFitClustersN}{12}",
        r"\newcommand{\BenchPilotFitClustersFrac}{4/12}",
        r"\newcommand{\BenchPilotConservFrac}{3/12}",
        r"\newcommand{\BenchPilotNeffThirty}{30}",
        r"\newcommand{\BenchPilotNeffFifty}{50}",
        r"\newcommand{\BenchPilotNeffRange}{30\text{--}75}",
        r"\newcommand{\BenchPosSevenOne}{71}",
        r"\newcommand{\BenchPosNineNine}{99}",
        r"\newcommand{\BenchPosOneZeroSeven}{107}",
        r"\newcommand{\BenchPosOneOneSix}{116}",
        r"\newcommand{\BenchPosOneThreeNine}{139}",
        r"\newcommand{\BenchPosOneFourOne}{141}",
        r"\newcommand{\BenchPosOneSixSeven}{167}",
        r"\newcommand{\BenchNumVariants}{4}",
        r"\newcommand{\BenchNumModes}{5}",
        r"\newcommand{\BenchNumStreams}{3}",
        r"\newcommand{\BenchFDWire}{3}",
        r"\newcommand{\BenchUbuntuVer}{26.04}",
        r"\newcommand{\BenchMemCapMiB}{768\,\text{MiB}}",
        r"\newcommand{\BenchTasksCap}{24}",
        r"\newcommand{\BenchAsCapMiB}{512\,\text{MiB}}",
        r"\newcommand{\BenchWallCapSec}{12\,\text{s}}",
        r"\newcommand{\BenchCompileTimeoutSec}{25\,\text{s}}",
        r"\newcommand{\BenchTickExitCode}{85}",
        r"\newcommand{\BenchPilotExecUpperPct}{15.5\%}",
        r"\newcommand{\BenchOLSMinRSq}{0.6584}",
        r"\newcommand{\BenchRestTwoSidedBand}{80--120\%}",
        r"\newcommand{\BenchCensorSlopeMin}{0.45}",
        r"\newcommand{\BenchWaveOnePin}{\texttt{04f1a1b2}}",
        r"\newcommand{\BenchWaveTwoPin}{\texttt{b598ea21}}",
        r"\newcommand{\BenchBetaGridMin}{0.20}",
        r"\newcommand{\BenchBetaGridDrop}{0.10}",
        r"\newcommand{\BenchRestSurgicalBand}{80--105\%}",
        r"\newcommand{\BenchRestMildBand}{105--120\%}",
        r"\newcommand{\BenchRestHighBand}{$>120\%$}",
        f"\\newcommand{{\\BenchPinManifest}}{{\\texttt{{{report['manifest_sha256'][:8]}}}}}",
        f"\\newcommand{{\\BenchPinProtocol}}{{\\texttt{{{PROTOCOL_SHA[:8]}}}}}",
        f"\\newcommand{{\\BenchPinHolds}}{{\\texttt{{{HELD_SHA[:8]}}}}}",
        f"\\newcommand{{\\BenchPinAmendFive}}{{\\texttt{{{amendment_sha[:8]}}}}}",
        f"\\newcommand{{\\BenchPinAnon}}{{\\texttt{{{ANON_MEASUREMENTS_SHA[:8]}}}}}",
        f"\\newcommand{{\\BenchPinForensics}}{{\\texttt{{{FORENSICS_AGG_SHA[:8]}}}}}",
        r"\newcommand{\BenchSlot}[1]{\textnormal{[\emph{#1}:~\rule{1.3em}{0.35pt}]}}",
        r"\newcommand{\BenchCell}{\textnormal{[\rule{1.3em}{0.35pt}]}}",
    ]

    # Manifest / S0 / Cluster geometry counts — recomputed directly from manifest when supplied
    sec = prim["secondary"]
    s12 = sec["S12_quarantined"]
    s10 = sec["S10_per_frame"]
    if manifest is not None and isinstance(manifest.get("pairs"), list):
        m_pairs = manifest["pairs"]
        drawn_u = len(m_pairs)
        s0_u = sum(1 for r in m_pairs if r.get("intake_stop"))
        s0_c = sum(1 for r in m_pairs if r.get("intake_stop") and r.get("frame") == "Contest")
        s0_r = sum(1 for r in m_pairs if r.get("intake_stop") and r.get("frame") == "Repository")
        s0_dup = sum(1 for r in m_pairs if r.get("intake_stop") == "intake_duplicate")
        s0_unret = sum(1 for r in m_pairs if r.get("intake_stop") == "intake_unretrievable")
        s0_pass_u = drawn_u - s0_u
        m_quar = [r for r in m_pairs if not r.get("intake_stop") and r.get("quarantined")]
        m_conf = [r for r in m_pairs if not r.get("intake_stop") and not r.get("quarantined")]
        quar_pairs_n = len(m_quar)
        quar_cl_n = len({r["cluster_id"] for r in m_quar})
        conf_pairs_n = len(m_conf)
        conf_cl_counts = Counter(r["cluster_id"] for r in m_conf)
        conf_cl_n = len(conf_cl_counts)
        conf_c_cl_counts = Counter(r["cluster_id"] for r in m_conf if r.get("frame") == "Contest")
        conf_r_cl_counts = Counter(r["cluster_id"] for r in m_conf if r.get("frame") == "Repository")
        conf_c_cl_n = len(conf_c_cl_counts)
        conf_r_cl_n = len(conf_r_cl_counts)
        conf_r_p_n = sum(conf_r_cl_counts.values())
        conf_singletons = sum(1 for cnt in conf_cl_counts.values() if cnt == 1)
        conf_repo_singletons = sum(1 for cnt in conf_r_cl_counts.values() if cnt == 1)
        m_conf_c_drawn = sum(1 for r in m_pairs if r.get("frame") == "Contest" and not r.get("quarantined"))
        m_conf_c_s0 = sum(1 for r in m_pairs if r.get("frame") == "Contest" and not r.get("quarantined") and r.get("intake_stop"))
        m_quar_s0 = sum(1 for r in m_pairs if r.get("quarantined") and r.get("intake_stop"))
        if drawn_u != int(flow["Union"]["drawn"]) or s0_u != int(flow["Union"]["s0_intake_stop"]):
            raise ValueError("Manifest S0 counts disagree with report flow_table")
        if conf_cl_n != int(prim["confirmatory_clusters_past_s0"]) or conf_pairs_n != int(prim["confirmatory_pairs_past_s0"]):
            raise ValueError("Manifest confirmatory cluster counts disagree with report")
        if quar_cl_n != int(s12["clusters_past_s0"]) or quar_pairs_n != int(s12["pairs_past_s0"]):
            raise ValueError("Manifest quarantined cluster counts disagree with report")
    else:
        drawn_u = int(flow["Union"]["drawn"])
        s0_u = int(flow["Union"]["s0_intake_stop"])
        s0_c = int(flow["Contest"]["s0_intake_stop"])
        s0_r = int(flow["Repository"]["s0_intake_stop"])
        s0_dup = int(flow["Union"].get("s0_intake_duplicate", 0))
        s0_unret = int(flow["Union"].get("s0_intake_unretrievable", 0))
        s0_pass_u = drawn_u - s0_u
        quar_pairs_n = int(s12["pairs_past_s0"])
        quar_cl_n = int(s12["clusters_past_s0"])
        conf_pairs_n = int(prim["confirmatory_pairs_past_s0"])
        conf_cl_n = int(prim["confirmatory_clusters_past_s0"])
        conf_c_cl_n = int(s10["Contest"]["clusters_past_s0"])
        conf_r_cl_n = int(s10["Repository"]["clusters_past_s0"])
        conf_r_p_n = int(s10["Repository"]["pairs_past_s0"])
        conf_singletons = conf_cl_n - max(0, conf_pairs_n - conf_cl_n)
        conf_repo_singletons = max(0, conf_singletons - conf_c_cl_n)
        m_conf_c_drawn = None
        m_conf_c_s0 = None
        m_quar_s0 = None

    lines.extend([
        f"\\newcommand{{\\BenchIntakeStopsN}}{{{_tex_int(s0_u)}}}",
        f"\\newcommand{{\\BenchIntakeDupN}}{{{_tex_int(s0_dup)}}}",
        f"\\newcommand{{\\BenchIntakeUnretN}}{{{_tex_int(s0_unret)}}}",
        f"\\newcommand{{\\BenchIntakeContestN}}{{{_tex_int(s0_c)}}}",
        f"\\newcommand{{\\BenchIntakeRepoN}}{{{_tex_int(s0_r)}}}",
        f"\\newcommand{{\\BenchSOPassN}}{{{_tex_int(s0_pass_u)}}}",
        f"\\newcommand{{\\BenchQuarPairsN}}{{{_tex_int(quar_pairs_n)}}}",
        f"\\newcommand{{\\BenchQuarClustersN}}{{{_tex_int(quar_cl_n)}}}",
        f"\\newcommand{{\\BenchConfPairsN}}{{{_tex_int(conf_pairs_n)}}}",
        f"\\newcommand{{\\BenchConfClustersN}}{{{_tex_int(conf_cl_n)}}}",
        f"\\newcommand{{\\BenchConfContestClustersN}}{{{_tex_int(conf_c_cl_n)}}}",
        f"\\newcommand{{\\BenchConfRepoClustersN}}{{{_tex_int(conf_r_cl_n)}}}",
        f"\\newcommand{{\\BenchConfRepoPairsN}}{{{_tex_int(conf_r_p_n)}}}",
        f"\\newcommand{{\\BenchConfSingletonN}}{{{_tex_int(conf_singletons)}}}",
        f"\\newcommand{{\\BenchConfRepoSingletonN}}{{{_tex_int(conf_repo_singletons)}}}",
    ])

    if s1_complete or execution_complete:
        held_all = int(flow["Union"]["s1_desk_unrateable"])
        held_r = int(flow["Repository"]["s1_desk_unrateable"])
        held_conf_cl = conf_cl_n - int(s13["confirmatory_clusters_past_s0"])
        held_c_conf = max(0, held_conf_cl - conf_r_cl_n)
        held_conf_pairs = max(0, held_all - int(s12["pair_dispositions"].get("desk_unrateable", 0)))
        rateable_n = int(inv["total_rateable"])
        s1_batches = int(report.get("s1_batches", 96))
        s1_win = (forensics or {}).get("s1_run_window") or {}
        s1_att = int(s1_win.get("total_attempts", s1_batches))
        s1_ret = int(s1_win.get("failed_retried_attempts", 0))
        s1_win_str = (
            f"{s1_win['first_date_utc']}, {s1_win['first_timestamp_utc'][11:16]}--{s1_win['last_timestamp_utc'][11:16]}~UTC"
            if s1_win.get("first_date_utc")
            else "frozen batch window"
        )
        lines.extend([
            f"\\newcommand{{\\BenchHeldUnratAllN}}{{{_tex_int(held_all)}}}",
            f"\\newcommand{{\\BenchRepoDeskUnratN}}{{{_tex_int(held_r)}}}",
            f"\\newcommand{{\\BenchContestUnbundledConfN}}{{{_tex_int(held_c_conf)}}}",
            f"\\newcommand{{\\BenchHeldUnratConfClustN}}{{{_tex_int(held_conf_cl)}}}",
            f"\\newcommand{{\\BenchHeldConfPairsN}}{{{_tex_int(held_conf_pairs)}}}",
            f"\\newcommand{{\\BenchRateablePairsN}}{{{_tex_int(rateable_n)}}}",
            f"\\newcommand{{\\BenchSOneBatchesN}}{{{_tex_int(s1_batches)}}}",
            f"\\newcommand{{\\BenchSOneAttemptsN}}{{{_tex_int(s1_att)}}}",
            f"\\newcommand{{\\BenchSOneRetriesN}}{{{_tex_int(s1_ret)}}}",
            f"\\newcommand{{\\BenchSOneDateWindow}}{{{s1_win_str}}}",
        ])
    else:
        for m_name, lbl in (
            ("BenchHeldUnratAllN", "held unrateable"),
            ("BenchRepoDeskUnratN", "repo unrateable"),
            ("BenchContestUnbundledConfN", "unbundled contest"),
            ("BenchHeldUnratConfClustN", "held clusters"),
            ("BenchHeldConfPairsN", "held conf pairs"),
            ("BenchRateablePairsN", "rateable pairs"),
            ("BenchSOneBatchesN", "batches"),
            ("BenchSOneAttemptsN", "attempts"),
            ("BenchSOneRetriesN", "retries"),
            ("BenchSOneDateWindow", "S1 window"),
        ):
            lines.append(f"\\newcommand{{\\{m_name}}}{{\\BenchSlot{{{lbl}}}}}")

    if execution_complete:
        p1_r = prim["P1"]["rate"]
        p2c = prim["P2"]["contrast"]
        p2_delta = float(p2c.get("group_weighted_delta_pp") or 0.0)
        p2_ci = p2c.get("bootstrap_95pct_delta_pp")
        p3_r = prim["P3"]["rate"]
        sa1_r = sec["S1_desk_stop"]
        sa2_r = sec["S2_alerts_per_selected"]
        sa3_r = sec["S3_preprocessing_stops_after_desk"]
        sa4_r = sec["S4_oracle_failures_among_executed"]
        sa5_c = sec["S5_alert_minus_no_alert_among_fits"]
        sa6_r = sec["S6_P1_without_infra"]
        sa7_r = sec["S7_any_stream_alerts"]
        sa8_r = sec["S8_drop_largest_refit"]
        sa9_p1 = sec["S9_all_pair_equal_cluster"]["P1_equal_cluster"]
        sa9_p3 = sec["S9_all_pair_equal_cluster"]["P3_equal_cluster"]
        sa14_r = sec["S14_fixture_stops_after_s1_pass"]

        cb = sa1_r.get("bucket_counts_reps") or {}
        rated_stops_n = sum(int(cb.get(b, 0)) for b in ("contract", "source", "route", "indeterminate"))
        total_desk_n = int(sa1_r["count"])
        conf_s1_pass_n = int(sa14_r["total"])
        cond_exec_r = rate_summary(int(p1_r["count"]), conf_s1_pass_n) if conf_s1_pass_n > 0 else rate_summary(0, 1)
        orig_comp_n = int((sa14_r.get("reason_counts_reps") or {}).get("original_compile_failure", 0))
        orig_comp_r = rate_summary(orig_comp_n, conf_s1_pass_n) if conf_s1_pass_n > 0 else rate_summary(0, 1)

        s13_p1 = s13["P1"]["rate"]
        s13_p2c = s13["P2"]["contrast"]
        s13_desk = s13["secondary"]["S1_desk_stop"]
        s13_d = float(s13_p2c.get("group_weighted_delta_pp") or 0.0)
        s13_p = s13["P2"].get("p_unadjusted")

        def _p_na(p: float | None, *, prefix: str = "p = ") -> str:
            return _tex_p(p, prefix=prefix) if p is not None else "n/a"

        def _rate_or_na(r: dict[str, Any]) -> str:
            return _tex_rate(r) if r.get("total") else "0/0 (n/a)"

        p3_str = _rate_or_na(p3_r) + ("" if prim["P3"]["gate_met"] else " (descriptive only)")

        ex_comp = (forensics or {}).get("exact_comparisons") or {}
        fish = ex_comp.get("fisher_two_sided") or {}
        mcn_scr = ex_comp.get("mcnemar_screens_vs_b0") or {}
        mcn_s13 = ex_comp.get("mcnemar_s13_p2") or {}
        fin_holm = ex_comp.get("holm_primary_finite_sample") or {"P1": fish.get("P1", 1.0), "P2": prim["P2"]["p_unadjusted"], "P3": fish.get("P3", 1.0)}
        p2_str = (
            f"{_tex_s1(p2_delta)}~pp across {_tex_int(p2c['clusters'])} clusters "
            f"(95\\% cluster bootstrap {_tex_s1(p2_ci[0])} to {_tex_s1(p2_ci[1])}~pp, Holm {_p_na(fin_holm.get('P2', prim['P2']['p_holm']), prefix='p_H = ')})"
            if p2_ci
            else f"{_tex_s1(p2_delta)}~pp"
        )
        p2_dec = ex_comp.get("p2_decomposition") or {
            "unrateable_holds_pp": round(100.0 * (conf_cl_n - int(s13["confirmatory_clusters_past_s0"])) / max(1, conf_cl_n), 1),
            "rateable_contrib_pp": round(p2_delta - 100.0 * (conf_cl_n - int(s13["confirmatory_clusters_past_s0"])) / max(1, conf_cl_n), 1),
            "holds_share_pct": round(100.0 * (conf_cl_n - int(s13["confirmatory_clusters_past_s0"])) / max(1, total_desk_n - int(p1_r["count"])), 1),
        }

        raw_a5 = report.get("raw_a5_disclosures") or {}
        pins_d = raw_a5.get("pins") or {}
        disc_d = raw_a5.get("disclosures") or {}
        overlay_pos_list = disc_d.get("overlay_positions") or []
        if overlay_pos_list:
            overlay_fix_cnt = sum(1 for item in overlay_pos_list if item.get("owner_terminal") == "fixture_stop")
        elif disc_d:
            overlay_fix_cnt = int((disc_d.get("actual_overlay_wave_split") or {}).get("wave3", 0))
        else:
            overlay_fix_cnt = 0
        pre_runner_fix_n = max(0, int(sa14_r["count"]) - overlay_fix_cnt)
        runner_s1_n = max(1, conf_s1_pass_n - pre_runner_fix_n)
        overlay_fix_n = max(0, int(sa14_r["count"]) - pre_runner_fix_n)

        p164_cpu_vals = [
            float(s["cpu_usage_usec"]["plain"]["largest_ratio"])
            for al_i in (forensics or {}).get("six_alerts", [])
            if int(al_i.get("position", 0)) == 164
            for s in al_i.get("streams", [])
            if (s.get("cpu_usage_usec") or {}).get("plain", {}).get("largest_ratio") is not None
        ]
        lines.extend([
            f"\\newcommand{{\\BenchFittedClusters}}{{{_tex_int(p3_r['total'])}}}",
            f"\\newcommand{{\\BenchExecRate}}{{{_rate_or_na(p1_r)}}}",
            f"\\newcommand{{\\BenchDeskContrast}}{{{p2_str}}}",
            f"\\newcommand{{\\BenchPOneCount}}{{{_tex_int(p1_r['count'])}}}",
            f"\\newcommand{{\\BenchPOnePct}}{{{_pct_str(p1_r)}}}",
            f"\\newcommand{{\\BenchPOneCI}}{{{_ci_num(p1_r)}}}",
            f"\\newcommand{{\\BenchPOneHolmP}}{{{_p_na(prim['P1']['p_holm'])}}}",
            f"\\newcommand{{\\BenchPOneFisherP}}{{{_p_na(fish.get('P1', prim['P1']['p_unadjusted']))}}}",
            f"\\newcommand{{\\BenchPTwoDelta}}{{{_tex_s1(p2_delta)}~pp}}",
            f"\\newcommand{{\\BenchPTwoHolmP}}{{{_p_na(prim['P2']['p_holm'])}}}",
            f"\\newcommand{{\\BenchPTwoHoldsPP}}{{{_tex_s1(p2_dec['unrateable_holds_pp'])}~pp}}",
            f"\\newcommand{{\\BenchPTwoHoldsShare}}{{{p2_dec['holds_share_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchPTwoRateableContribPP}}{{{_tex_s1(p2_dec['rateable_contrib_pp'])}~pp}}",
            f"\\newcommand{{\\BenchPThreeCount}}{{{_tex_int(p3_r['count'])}}}",
            f"\\newcommand{{\\BenchPThreePct}}{{{_pct_str(p3_r)}}}",
            f"\\newcommand{{\\BenchPThreeCI}}{{{_ci_num(p3_r)}}}",
            f"\\newcommand{{\\BenchPThreeHolmP}}{{{_p_na(prim['P3']['p_holm'])}}}",
            f"\\newcommand{{\\BenchPThreeFisherP}}{{{_p_na(fish.get('P3', prim['P3']['p_unadjusted']))}}}",
            f"\\newcommand{{\\BenchSAFiveSignP}}{{{_p_na(sa5_c.get('nominal_p'))}}}",
            f"\\newcommand{{\\BenchSATwoPct}}{{{_pct_str(sa2_r)}}}",
            f"\\newcommand{{\\BenchSATwoCI}}{{{_ci_num(sa2_r)}}}",
            f"\\newcommand{{\\BenchSATwoFisherP}}{{{_p_na(fish.get('S2', sa2_r.get('nominal_p_vs_4_147')))}}}",
            f"\\newcommand{{\\BenchRateableClustersN}}{{{_tex_int(s13['confirmatory_clusters_past_s0'])}}}",
            f"\\newcommand{{\\BenchRateableExecPct}}{{{_pct_str(s13_p1)}}}",
            f"\\newcommand{{\\BenchRateableExecCI}}{{{_ci_num(s13_p1)}}}",
            f"\\newcommand{{\\BenchRateableDeskPct}}{{{_pct_str(s13_desk)}}}",
            f"\\newcommand{{\\BenchSAThirteenDelta}}{{{_tex_s1(s13_d)}~pp}}",
            f"\\newcommand{{\\BenchSAThirteenBootCI}}{{{_boot_br(s13_p2c.get('bootstrap_95pct_delta_pp'))}}}",
            f"\\newcommand{{\\BenchSAThirteenP}}{{{_p_na(s13_p)}}}",
            f"\\newcommand{{\\BenchConfSTwoPassN}}{{{_tex_int(conf_s1_pass_n)}}}",
            f"\\newcommand{{\\BenchRatedDeskStopRepsN}}{{{_tex_int(rated_stops_n)}}}",
            f"\\newcommand{{\\BenchTotalDeskStopRepsN}}{{{_tex_int(total_desk_n)}}}",
            f"\\newcommand{{\\BenchConfContractStopRepsN}}{{{_tex_int(cb.get('contract', 0))}}}",
            f"\\newcommand{{\\BenchConfSourceStopRepsN}}{{{_tex_int(cb.get('source', 0))}}}",
            f"\\newcommand{{\\BenchConfRouteStopRepsN}}{{{_tex_int(cb.get('route', 0))}}}",
            f"\\newcommand{{\\BenchConfIndetRepsN}}{{{_tex_int(cb.get('indeterminate', 0))}}}",
            f"\\newcommand{{\\BenchFixtureStopN}}{{{_tex_int(sa14_r['count'])}}}",
            f"\\newcommand{{\\BenchFixtureStopPct}}{{{_pct_str(sa14_r)}}}",
            f"\\newcommand{{\\BenchFixtureStopCI}}{{{_ci_num(sa14_r)}}}",
            f"\\newcommand{{\\BenchCondExecPct}}{{{_pct_str(cond_exec_r)}}}",
            f"\\newcommand{{\\BenchOrigCompileFailN}}{{{_tex_int(orig_comp_n)}}}",
            f"\\newcommand{{\\BenchOrigCompileFailPct}}{{{_pct_str(orig_comp_r)}}}",
            f"\\newcommand{{\\BenchOrigCompileFailCI}}{{{_ci_num(orig_comp_r)}}}",
            f"\\newcommand{{\\BenchRunnerSOnePassN}}{{{_tex_int(runner_s1_n)}}}",
            f"\\newcommand{{\\BenchRunnerPreFixtureN}}{{{_tex_int(pre_runner_fix_n)}}}",
            f"\\newcommand{{\\BenchRunnerOverlayFixtureN}}{{{_tex_int(overlay_fix_n)}}}",
            f"\\newcommand{{\\BenchOracleFailN}}{{{_tex_int(sa4_r['count'])}}}",
            f"\\newcommand{{\\BenchOracleFailPct}}{{{_pct_str(sa4_r)}}}",
            f"\\newcommand{{\\BenchOracleFailCI}}{{{_ci_num(sa4_r)}}}",
            f"\\newcommand{{\\BenchNoFitN}}{{{_tex_int(max(0, p1_r['count'] - p3_r['total'] - sa4_r['count']))}}}",
            f"\\newcommand{{\\BenchNoAlertN}}{{{_tex_int(max(0, p3_r['total'] - p3_r['count']))}}}",
            f"\\newcommand{{\\BenchInfraFailN}}{{{_tex_int(max(0, conf_cl_n - sa6_r['total']))}}}",
            f"\\newcommand{{\\BenchQuarUnrunN}}{{{_tex_int(s12['pair_dispositions'].get('not_executed', 0))}}}",
            f"\\newcommand{{\\BenchPinLedger}}{{\\texttt{{{pins_d.get('analysis-ledger.json', 'aggregate')[:8]}}}}}",
            f"\\newcommand{{\\BenchPinRepPlan}}{{\\texttt{{{pins_d.get('representative-plan.json', 'aggregate')[:8]}}}}}",
        ])

        # Stratified Flow Columns (Table 1)
        q_disp = s12.get("pair_dispositions") or {}
        u_flow = flow["Union"]
        c_flow = flow["Contest"]
        r_flow = flow["Repository"]
        q_s1_tot = sum(int(q_disp.get(k, 0)) for k in ("desk_excluded", "desk_blocked", "desk_unrateable", "indeterminate"))
        conf_c_drawn = m_conf_c_drawn if m_conf_c_drawn is not None else (int(c_flow["drawn"]) - quar_pairs_n)
        conf_c_s0 = m_conf_c_s0 if m_conf_c_s0 is not None else int(c_flow["s0_intake_stop"])
        quar_s0_n = m_quar_s0 if m_quar_s0 is not None else 0
        conf_c_s1 = int(c_flow["s1_desk_stop_total"]) - q_s1_tot
        conf_c_fix = int(c_flow["s2_fixture_stop"]) - int(q_disp.get("fixture_stop", 0))
        conf_c_prep = int(c_flow["s2_preprocessing_stop"]) - int(q_disp.get("support_boundary_closed", 0))
        conf_c_inf = int(c_flow["s3_infra_failure"]) - int(q_disp.get("execution_infrastructure_failure", 0))
        conf_c_unr = int(c_flow["not_executed"]) - int(q_disp.get("not_executed", 0))
        conf_c_ora = int(c_flow["s3_oracle_failure"]) - int(q_disp.get("execution_oracle_failure", 0))
        conf_c_nof = int(c_flow["s4_no_fit"]) - int(q_disp.get("insufficient_fit", 0))
        conf_c_noa = int(c_flow["s5_no_alert"]) - int(q_disp.get("no_alert", 0))
        conf_c_al = int(c_flow["s5_alert"]) - int(q_disp.get("alert", 0))

        lines.extend([
            f"\\newcommand{{\\BenchConfContestDrawn}}{{{_tex_int(conf_c_drawn)}}}",
            f"\\newcommand{{\\BenchConfContestIntake}}{{{_tex_int(conf_c_s0)}}}",
            f"\\newcommand{{\\BenchQuarIntakeN}}{{{_tex_int(quar_s0_n)}}}",
            f"\\newcommand{{\\BenchQuarPostSOneZeroN}}{{{_tex_int(0)}}}",
            f"\\newcommand{{\\BenchConfContestDesk}}{{{_tex_int(conf_c_s1)}}}",
            f"\\newcommand{{\\BenchConfContestFix}}{{{_tex_int(conf_c_fix)}}}",
            f"\\newcommand{{\\BenchConfContestPrep}}{{{_tex_int(conf_c_prep)}}}",
            f"\\newcommand{{\\BenchConfContestInfra}}{{{_tex_int(conf_c_inf)}}}",
            f"\\newcommand{{\\BenchConfContestUnrun}}{{{_tex_int(conf_c_unr)}}}",
            f"\\newcommand{{\\BenchConfContestOracle}}{{{_tex_int(conf_c_ora)}}}",
            f"\\newcommand{{\\BenchConfContestNoFit}}{{{_tex_int(conf_c_nof)}}}",
            f"\\newcommand{{\\BenchConfContestNoAlert}}{{{_tex_int(conf_c_noa)}}}",
            f"\\newcommand{{\\BenchConfContestAlert}}{{{_tex_int(conf_c_al)}}}",
            f"\\newcommand{{\\BenchQuarContestDesk}}{{{_tex_int(q_s1_tot)}}}",
        ])

        # Forensics macros (with clean fallbacks when forensics=None in synthetic unit tests)
        ofb = (forensics or {}).get("oracle_failure_breakdown") or {}
        ifb = (forensics or {}).get("insufficient_fit_breakdown") or {}
        miss_d = (forensics or {}).get("missing_decomposition") or {}
        cap_d = (forensics or {}).get("cap_mode_breakdown") or {}
        tax = (forensics or {}).get("fit_124_taxonomy") or {}
        six_d = (forensics or {}).get("six_alerts_robust_diagnostics") or {}
        rest_f = (forensics or {}).get("restoration_forensics_124") or {}
        rest_tot = (forensics or {}).get("restoration_total_ticks_124") or {"pass": 0, "no_excess": 0, "fail": 0, "excess_total": 1, "newly_testable_from_c0_no_excess": 0}
        rest_tot_fail_r = rest_tot.get("fail_rate") or rate_summary(int(rest_tot.get("fail", 0)), max(1, int(rest_tot.get("excess_total", 1))))
        # fin_holm computed above next to p2_str
        c1_hits_list = tax.get("c1_only_hits") or []
        pos11_hit = next((h for h in c1_hits_list if int(h["position"]) == 11), {"max_c1_ratio": 0.0, "stream": "W3"})
        pos47_hit = next((h for h in c1_hits_list if int(h["position"]) == 47), {"max_c1_ratio": 0.0, "stream": "W2"})
        q1_zero_list = tax.get("q1_zero_t0_eq_q0_positions") or []
        conf_desk_pairs_n = max(0, int(flow["Union"]["s1_desk_stop_total"]) - int(q_s1_tot))
        exec_chk = prim.get("execution_checks") or {}
        o_ag = exec_chk.get("o0_o2_o3_agreement") or {"agree": 0, "capped_or_missing": 0}
        s_ag = exec_chk.get("target_vs_sham") or {"agree": 0, "capped_or_missing": 0}
        caps_cnt = exec_chk.get("caps") or {}
        cap_pos_cnt = exec_chk.get("positions_with_cap") or {}
        rest_all = exec_chk.get("restoration") or {"passed": 0, "no_excess": 0, "failed": 0, "unmeasured": 0}
        fit_rest = exec_chk.get("fitted_restoration") or {"passed": 0, "no_excess": 0, "failed": 0}
        fit_ex_n = int(fit_rest.get("passed", 0)) + int(fit_rest.get("failed", 0))
        fit_fail_r = rate_summary(int(fit_rest.get("failed", 0)), max(1, fit_ex_n))
        up_or_r = ofb.get("upstream_rate") or sa4_r

        n_fit = int(p3_r["total"])
        f124 = (forensics or {}).get("fitted_124_forensics") or {}
        sd_all = (f124.get("stream_distinctness_c0") or {}).get("all_124") or {"3_distinct": 0, "2_distinct": 0, "1_distinct": 0}
        r2s = f124.get("r_squared_c0") or {}
        r2_all = r2s.get("all_streams_372") or {"n_zero_var": 0, "n_defined": 0, "median": 0.0}
        r2_al = r2s.get("alert_streams_18") or {"median": 0.0}
        pair_r2 = tax.get("pair_level_r2") or {"all_zero_var_pairs": 0, "defined_r2_pairs": 0, "worst_stream_median_r2": 0.0, "alert_worst_stream_median_r2": 0.0}
        sa9_p3_ci = sa9_p3.get("bootstrap_95pct_pct")
        sa9_p3_ci_str = f"[{sa9_p3_ci[0]:.1f}, {sa9_p3_ci[1]:.1f}]\\%" if sa9_p3_ci else "n/a"
        neff_s = ex_comp.get("pilot_neff_sensitivity") or {}
        ne30 = neff_s.get("n_eff_30") or {"p1_p": 1.0, "sa1_p": 1.0}
        ne50 = neff_s.get("n_eff_50") or {"p1_p": 1.0, "sa1_p": 1.0}
        ne75 = neff_s.get("n_eff_75") or {"p1_p": 1.0, "sa1_p": 1.0}
        sa1_neff_ps = [float(d.get("sa1_p", 1.0)) for d in (ne30, ne50, ne75)]
        o0_rlx = (forensics or {}).get("o0_cpu_cap_relaxation") or {"o0_only_cap_points_n": 0, "affected_pairs_n": 0, "p3_delta": 0, "sa7_delta": 0}
        sub_cpu_al = six_d.get("spawn_floor_subtracted") or {}
        def _sub_range_str(pos_key: str, *, allow_neg_math: bool = False) -> str:
            d = sub_cpu_al.get(pos_key) or {"slope_min": 0.0, "slope_max": 0.0}
            lo, hi = float(d["slope_min"]), float(d["slope_max"])
            if allow_neg_math:
                s_lo = f"$-{abs(lo):.2f}$" if lo < 0 else f"{lo:.2f}"
                s_hi = f"$-{abs(hi):.2f}$" if hi < 0 else f"{hi:.2f}"
                return f"{s_lo} to {s_hi}"
            return f"{lo:.2f}--{hi:.2f}" 
        bs = f124.get("baseline_screens_124") or {}
        b1_dec = (forensics or {}).get("b1_fp_decomposition") or {}
        b1_n = int((bs.get("B1_c0_ratio_ge_1_5_only") or {}).get("alerts", 0))
        b2_n = int((bs.get("B2_c0_slope_ge_0_5_only") or {}).get("alerts", 0))
        b3_n = int((bs.get("B3_total_ticks_c0_plus_c1_dual") or {}).get("alerts", 0))
        b4_n = int((bs.get("B4_plain_cpu_usec_dual_ge_10ms") or {}).get("alerts", 0))
        b5_obj = bs.get("B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms") or {"alerts": 0, "tp_vs_primary": 0, "fp_vs_primary": 0}
        b1_r = rate_summary(b1_n, max(1, n_fit))
        b2_r = rate_summary(b2_n, max(1, n_fit))
        b3_r = rate_summary(b3_n, max(1, n_fit))
        b4_r = rate_summary(b4_n, max(1, n_fit))
        b5_r = rate_summary(int(b5_obj["alerts"]), max(1, n_fit))
        core_r = six_d.get("core_rate") or rate_summary(min(int(p3_r["count"]), int(b3_n)), max(1, n_fit))
        sa8_adm_n = int(sa8_r.get("admitted_count") or 0)
        sa8_al_r = sa8_r.get("alerts_among_admitted") or rate_summary(0, 1)
        sa8_any_r = tax.get("s8_any_stream_alerts_among_admitted") or sa8_r.get("any_stream_alerts_among_admitted") or rate_summary(0, 1)
        censor_r = ifb.get("censoring_upper_p3") or p3_r
        censor_w = ifb.get("censoring_worst_p3") or censor_r
        b3_all_exec = ifb.get("b3_all_non_oracle_exec") or rate_summary(b3_n, max(1, n_fit + int(ifb.get("total", 0))))
        ns_map = six_d.get("ns_per_tick_o2_by_position") or {}
        ns_stats = six_d.get("ns_per_tick_stats") or {}
        p3_diag = ((six_d.get("per_position") or {}).get("3") or {})
        p13_diag = ((six_d.get("per_position") or {}).get("13") or {})
        p3_lev = float(p3_diag.get("c0_max_lev", 0.524))
        regimes = tax.get("regimes") or {}
        b_grid = tax.get("beta_min_grid") or {}
        ex_m = six_d.get("exemplars") or {}
        q_s1_r = s12["pair_rates"]["S1_desk_stop"]
        cs_map = (forensics or {}).get("confirmatory_corpus_split") or {}
        pie_cs = cs_map.get("pie-train") or {}
        cod_cs = cs_map.get("codenet") or {}
        q_pd = s12.get("pair_dispositions") or {}
        q_blk = int(q_pd.get("desk_blocked", 0))
        q_hld = int(q_pd.get("desk_unrateable", 0))
        q_ind = int(q_pd.get("indeterminate", 0))
        q_src_n = int(ex_m.get("quar_source_stops", q_blk))
        z_flat_sum = int(regimes.get("exact_identity_T_eq_Q", 0)) + int(regimes.get("flat_near_1_lt_1.5", 0)) + int(regimes.get("flat_constant_factor_ge_1.5", 0))
        rev_sub_sum = int(regimes.get("negative_slope_all_streams", 0)) + int(regimes.get("mixed_or_reversed", 0)) + int(regimes.get("positive_sub50_regime", 0))
        p3_max_p_val = float(p3_diag.get("c0_max_p", 0.0))
        p3_cooks_s = p3_diag.get("c0_stream_cooks_d") or [0.0, 0.0, 0.0]
        p3_max_cooks_s = p3_diag.get("c0_stream_max_cooks_d") or p3_cooks_s
        p3_loos_s = p3_diag.get("c0_stream_loos") or [0.0, 0.0, 0.0]
        p3_ci_los_s = p3_diag.get("c0_stream_ci_los") or [0.0, 0.0, 0.0]
        p3_ci_his_s = p3_diag.get("c0_stream_ci_his") or [0.0, 0.0, 0.0]
        p164_c0_r = 0.0
        p13_c0_sl = 0.0
        p13_tot_sl = 0.0
        p3_s3_r2 = 0.0
        for item_al in (forensics or {}).get("six_alerts") or []:
            if int(item_al.get("position", 0)) == 3 and len(item_al.get("streams", [])) > 2:
                p3_s3_r2 = float(item_al["streams"][2]["primary_c0"].get("r_squared") or 0.0)
            if int(item_al.get("position", 0)) == 13 and item_al.get("streams"):
                p13_c0_sl = float(item_al["streams"][0]["primary_c0"]["slope"])
                p13_tot_sl = float(item_al["streams"][0]["total_ticks_c0_plus_c1"]["slope"])
            if int(item_al.get("position", 0)) == 164 and item_al.get("streams"):
                p164_c0_r = float(item_al["streams"][0]["primary_c0"]["largest_ratio"])

        cr = (author_check or {}).get("execution_policy_checks") or (author_check or {}).get("camera_ready_checks") or {}
        w1_sens = (cr.get("wave1_stderr_sensitivity") or {}).get("oracle_failure_as_fixture_stop") or {}
        w1_cnt = int((cr.get("wave1_stderr_sensitivity") or {}).get("changed_wave1_positions_count", 0))
        sa = (raw_a5.get("sensitivity") or {}).get("a") or {}
        sb = (raw_a5.get("sensitivity") or {}).get("b") or {}
        sc = (raw_a5.get("sensitivity") or {}).get("c") or {}
        sub_ub = (raw_a5.get("sensitivity") or {}).get("wave3_UB_as_infrastructure") or {}
        sub_cq = (raw_a5.get("sensitivity") or {}).get("wave3_capped_quality_as_insufficient_fit") or {}
        w3_rb = (cr.get("cpu_cap_attribution") or {}).get("wave3_mapping_rollback") or {}

        # Dynamic sensitivity table rows & min/max envelopes over all 10 scenarios
        sa4_baseline_total = int(sa4_r["total"])
        sa4_baseline_count = int(sa4_r["count"])
        s13_total_cl = int(s13["confirmatory_clusters_past_s0"])
        s13_desk_cl = int(s13_desk["count"])
        conf_s1_tot = max(1, conf_s1_pass_n)

        app_scenarios: list[tuple[str, dict[str, Any], dict[str, Any], float, dict[str, Any], dict[str, Any], dict[str, Any], float | None]] = []
        if raw_a5.get("sensitivity") and cr.get("cpu_cap_attribution") and cr.get("wave1_stderr_sensitivity"):
            assert int(s10["Contest"]["clusters_past_s0"]) == int(s10["Contest"]["pairs_past_s0"])
            w1_s = w1_sens
            # Helper to build uniform scenario metrics from terminal counts
            def _scen_from_exec(name: str, exec_n: int, ora_n: int, fix_n: int, fit_n_s: int, al_n_s: int, s13_p: float | None = None):
                p1_s = rate_summary(exec_n, conf_cl_n)
                p2_d_s = round(100.0 * (total_desk_n - exec_n) / conf_cl_n, 1)
                s13_d_s = round(100.0 * (s13_desk_cl - (exec_n)) / s13_total_cl, 1)
                p3_s = rate_summary(al_n_s, fit_n_s)
                sa4_s = rate_summary(ora_n, exec_n)
                sa14_s = rate_summary(fix_n, conf_s1_tot)
                p_use = s13_p if s13_p is not None else _mcnemar_exact(s13_desk_cl, exec_n)
                app_scenarios.append((name, p1_s, {"delta": p2_d_s}, s13_d_s, p3_s, sa4_s, sa14_s, p_use))

            # 1. Baseline
            _scen_from_exec(
                f"Primary protocol baseline (SHA \\texttt{{{pins_d.get('analysis-ledger.json', '')[:8]}}})",
                int(p1_r["count"]), sa4_baseline_count, int(sa14_r["count"]), n_fit, int(p3_r["count"]), s13_p,
            )
            # 2. Pre-patch cpu_cap exit-137 unpatched (2 pairs)
            tc_a = sa.get("terminal_counts_qualified") or {}
            _scen_from_exec(
                f"Pre-patch \\texttt{{cpu\\_cap}} exit-137 (2 pairs; \\texttt{{{pins_d.get('runner_sha256_original', '')[:8]}}})",
                int(sa["P1"]["count"]), int(tc_a.get("execution_oracle_failure", sa4_baseline_count)),
                int(tc_a.get("fixture_stop", sa14_r["count"])), int(sa["P3"]["total"]), int(sa["P3"]["count"]),
            )
            # 3. All cpu_cap exit-137 unpatched (3 pairs incl. Case 139)
            w3_diff = 1 if w3_rb.get("P1_numerator_changes") else 0
            ex_3 = int(sa["P1"]["count"]) - w3_diff
            fit_3 = int(sa["P3"]["total"]) - w3_diff
            _scen_from_exec(
                f"All \\texttt{{cpu\\_cap}} exit-137 unpatched (3 pairs; incl.\\ Case~{w3_rb.get('affected_positions', [139])[0]})",
                ex_3, sa4_baseline_count, int(tc_a.get("fixture_stop", sa14_r["count"])), fit_3, int(sa["P3"]["count"]),
            )
            # 4. 8 MiB stack policy (2 pairs, rc=139) as fixture_stop
            tc_b = sb.get("terminal_counts_qualified") or {}
            _scen_from_exec(
                "8\\,MiB stack policy (2 pairs, \\texttt{rc=139}) as \\texttt{fixture\\_stop}",
                int(sb["P1"]["count"]), int(tc_b.get("execution_oracle_failure", sa4_baseline_count)),
                int(tc_b.get("fixture_stop", sa14_r["count"])), int(sb["P3"]["total"]), int(sb["P3"]["count"]),
            )
            # 5. Non-empty stderr diagnostic pairs (2 pairs) as executed
            tc_c = sc.get("terminal_counts_qualified") or {}
            _scen_from_exec(
                "Non-empty \\texttt{stderr} diagnostic pairs (2 pairs) as executed",
                int(sc["P1"]["count"]), int(tc_c.get("execution_oracle_failure", sa4_baseline_count)),
                int(tc_c.get("fixture_stop", sa14_r["count"])), int(sc["P3"]["total"]), int(sc["P3"]["count"]),
            )
            # 6. Residual UB/crash traps (rc=134/139, 2 pairs) as infra
            tc_ub = sub_ub.get("terminal_counts_qualified") or {}
            _scen_from_exec(
                "Residual UB/crash traps (2 pairs, \\texttt{rc=134/139}) as infra",
                int(sub_ub["P1"]["count"]), int(tc_ub.get("execution_oracle_failure", sa4_baseline_count)),
                int(tc_ub.get("fixture_stop", sa14_r["count"])), int(sub_ub["P3"]["total"]), int(sub_ub["P3"]["count"]),
            )
            # 7. Capped-point quality toggle (1 pair as insufficient_fit)
            tc_cq = sub_cq.get("terminal_counts_qualified") or {}
            _scen_from_exec(
                "Capped-point quality toggle (1 pair as \\texttt{insufficient\\_fit})",
                int(sub_cq["P1"]["count"]), int(tc_cq.get("execution_oracle_failure", sa4_baseline_count)),
                int(tc_cq.get("fixture_stop", sa14_r["count"])), int(sub_cq["P3"]["total"]), int(sub_cq["P3"]["count"]),
            )
            # 8. Initial-batch oracle overrides (6 pairs) as fixture_stop
            _scen_from_exec(
                f"Initial-batch oracle overrides ({w1_cnt} pairs) as \\texttt{{fixture\\_stop}}",
                int(w1_s["P1"]["count"]), int(w1_s["S4"]["count"]),
                int(w1_s["S14"]["fixture_stop_per_S1_pass_pairs"]["count"]), n_fit, int(p3_r["count"]),
            )

        if app_scenarios:
            env_p1_lo = min(float(s[1]["percent"]) for s in app_scenarios)
            env_p1_hi = max(float(s[1]["percent"]) for s in app_scenarios)
            env_p3_lo = min(float(s[4]["percent"]) for s in app_scenarios)
            env_p3_hi = max(float(s[4]["percent"]) for s in app_scenarios)
            env_sa4_lo = min(float(s[5]["percent"]) for s in app_scenarios)
            env_sa4_hi = max(float(s[5]["percent"]) for s in app_scenarios)
            s13_lo_row = min(app_scenarios, key=lambda s: s[3])
            s13_hi_row = max(app_scenarios, key=lambda s: s[3])
        else:
            env_p1_lo = env_p1_hi = float(p1_r.get("percent") or 0.0)
            env_p3_lo = env_p3_hi = float(p3_r.get("percent") or 0.0)
            env_sa4_lo = env_sa4_hi = float(sa4_r.get("percent") or 0.0)
            s13_lo_row = ("", p1_r, {"delta": p2_delta}, s13_d, p3_r, sa4_r, sa14_r, s13_p)
            s13_hi_row = s13_lo_row

        coord_or_n = w1_cnt if cr else 0
        s10_contest = s10["Contest"]["P1_exec_yield"]
        b5_core_d = six_d.get("b5_vs_core") or {"tp": 0, "precision": rate_summary(0, 1), "recall": rate_summary(0, 1)}
        mcn_holm = ex_comp.get("mcnemar_screens_vs_b0_holm5") or {}
        b2_only_d = ex_m.get("b2_only") or {"position": 0, "slope_range": [0.0, 0.0], "ratio_range": [0.0, 0.0]}
        p94_st = ns_stats.get("94") or {"o2_min": 0.0, "o2_max": 0.0, "plain_min": 0.0, "plain_max": 0.0, "o2_ms_diff_min": 0.0, "o2_ms_diff_max": 0.0}
        p175_st = ns_stats.get("175") or {"o2_min": 0.0, "o2_max": 0.0, "plain_min": 0.0, "plain_max": 0.0}
        rest_exec_d = (forensics or {}).get("restoration_executed_149") or {"pass": 0, "no_excess": 0, "fail": 0, "unmeasured": 0}
        p94_pl_min = float(p94_st["plain_min"])
        p94_pl_lo_str = f"$-{abs(p94_pl_min):.2f}$" if p94_pl_min < 0 else f"{p94_pl_min:.2f}"
        p94_pl_hi = float(p94_st["plain_max"])
        p94_pl_hi_str = f"{p94_pl_hi:+.2f}"
        tax_d1_c1 = int(tax.get("distinct1_c1_varying", 0))
        tax_d1_ob = int(tax.get("distinct1_fully_oblivious", 0))
        sa3_all_s1 = sa3_r.get("all_s1_passes") or rate_summary(sa3_r["count"], conf_s1_tot)
        s12_cl = s12["cluster_rates"]["S1_desk_stop"]
        s12_cl_frac = f"{_tex_int(s12_cl['count'])}/{_tex_int(s12_cl['total'])} = {_pct_str(s12_cl)}" if s12_cl.get("count") is not None else "n/a"
        o0_ag_n = int((miss_d.get("O0_O2_O3") or {}).get("agree", o_ag["agree"]))
        o0_ms_n = int((miss_d.get("O0_O2_O3") or {}).get("missing_total", o_ag["capped_or_missing"]))
        sh_ag_n = int((miss_d.get("target_vs_sham") or {}).get("agree", s_ag["agree"]))
        sh_ms_n = int((miss_d.get("target_vs_sham") or {}).get("missing_total", s_ag["capped_or_missing"]))
        zv_n = int(r2_all.get("n_zero_var", 0))
        df_n = int(r2_all.get("n_defined", 0))
        p164_tot_p_val = float(((six_d.get("per_position") or {}).get("164") or {}).get("tot_max_p", 1.0))
        p164_item = next((it for it in (forensics or {}).get("six_alerts", []) if int(it["position"]) == 164), None)
        p164_tot_sl = float(p164_item["streams"][0]["total_ticks_c0_plus_c1"]["slope"]) if p164_item else 0.0
        p164_tot_r2 = float(p164_item["streams"][0]["total_ticks_c0_plus_c1"]["r_squared"]) if p164_item else 0.0
        rest_exact_copy_r = rate_summary(int(rest_f.get("pass_exact_copy", 0)), max(1, int(fit_rest.get("passed", 0))))
        fd_ow_d = six_d.get("fd_wrapper_overhead_ms") or {"median": 0.0, "iqr": [0.0, 0.0]}
        fd_iqr_vals = fd_ow_d.get("iqr") or [0.0, 0.0]
        fd_iqr_lo = float(fd_iqr_vals[0]) if len(fd_iqr_vals) >= 1 else 0.0
        fd_iqr_hi = float(fd_iqr_vals[1]) if len(fd_iqr_vals) >= 2 else 0.0
        fd_lo_s = f"$-{abs(fd_iqr_lo):.2f}$" if fd_iqr_lo < 0 else f"{fd_iqr_lo:.2f}"
        fd_sep = " to " if fd_iqr_lo < 0 else "--"
        fd_ow_str = f"{float(fd_ow_d.get('median', 0.0)):.2f}\\,\\text{{ms}} median, IQR {fd_lo_s}{fd_sep}{fd_iqr_hi:.2f}\\,\\text{{ms}}"
        s0_ow_d = six_d.get("o2_minus_plain_s0_ms") or {"median": 0.0, "iqr": [0.0, 0.0]}
        s0_iqr_vals = s0_ow_d.get("iqr") or [0.0, 0.0]
        s0_iqr_lo = float(s0_iqr_vals[0]) if len(s0_iqr_vals) >= 1 else 0.0
        s0_iqr_hi = float(s0_iqr_vals[1]) if len(s0_iqr_vals) >= 2 else 0.0
        s0_lo_s = f"$-{abs(s0_iqr_lo):.2f}$" if s0_iqr_lo < 0 else f"{s0_iqr_lo:.2f}"
        s0_sep = " to " if s0_iqr_lo < 0 else "--"
        s0_ow_str = f"{float(s0_ow_d.get('median', 0.0)):.2f}\\,\\text{{ms}} median, IQR {s0_lo_s}{s0_sep}{s0_iqr_hi:.2f}\\,\\text{{ms}}"

        def _fmt_add_sl(pos_s: str) -> str:
            d = sub_cpu_al.get(pos_s) or {}
            lo_v = float(d.get("add_delta_pl_slope_min", 0.0))
            hi_v = float(d.get("add_delta_pl_slope_max", 0.0))
            s_lo = f"$-{abs(lo_v):.2f}$" if lo_v < 0 else f"{lo_v:.2f}"
            s_hi = f"$-{abs(hi_v):.2f}$" if hi_v < 0 else f"{hi_v:.2f}"
            sep = " to " if lo_v < 0 else "--"
            return f"{s_lo}{sep}{s_hi}"

        non_ex_reg = rest_f.get("non_exact_pass_regimes") or {}
        non_ex_flat_n = int(non_ex_reg.get("flat_constant_factor_ge_1.5", 0)) + int(non_ex_reg.get("flat_near_1_lt_1.5", 0))
        allpt_nonreg_pos = rest_f.get("all_point_nonreg_r0_fail_positions") or []
        p94_upper_ns = f"{math.ceil(float(p94_st.get('plain_max', 0.336)) * 20.0) / 20.0:.2f}" if p94_st.get("plain_max") else "0.35"
        neff_tip_val = int((ex_comp.get("pilot_neff_sensitivity") or {}).get("p1_tip_neff_ge_05", 19))
        chron_d = (forensics or {}).get("chronological_failure_audit") or {}
        max_cnt_i = int(chron_d.get("max_parsed_counter", 0))
        if max_cnt_i > 0:
            mc_exp = int(math.floor(math.log10(max_cnt_i)))
            mc_mant = max_cnt_i / (10 ** mc_exp)
            max_cnt_str = f"${mc_mant:.2f} \\times 10^{{{mc_exp}}}$"
        else:
            max_cnt_str = "$0$"
        unconf_rest_or_n = max(0, int(ofb.get("restored_variant_failure", 0)) - (1 if ofb.get("pos27_o0_sigabrt_o2_clean") else 0))
        fitted_masked_n = int(chron_d.get("fitted_masked_failure_count", 0))
        p3_worst_ts_v = float(((six_d.get("per_position") or {}).get("3") or {}).get("c0_min_ts", 0.0))

        lines.extend([
            r"\newcommand{\BenchBwrapOverheadMs}{14--22\,\text{ms}}",
            f"\\newcommand{{\\BenchWaveOneOverrideN}}{{{_tex_int(w1_cnt)}}}",
            f"\\newcommand{{\\BenchPinWaveTwoCap}}{{\\texttt{{{pins_d.get('runner_sha256_original', 'aggregate')[:8]}}}}}",
            f"\\newcommand{{\\BenchPosNineFourPlainUpperNs}}{{{p94_upper_ns}}}",
            f"\\newcommand{{\\BenchPosTwoNine}}{{{_tex_int(int(ofb.get('plain_segv_and_ubsan_pos', 29)))}}}",
            f"\\newcommand{{\\BenchPosNineZeroOZeroOnlyPts}}{{{_tex_int(int(((o0_rlx.get('per_position') or {}).get('90') or {}).get('o0_only_points', 2)))}}}",
            f"\\newcommand{{\\BenchPosNineSevenOtwoStreamsN}}{{{_tex_int(int((sub_cpu_al.get('97') or {}).get('o2_streams_dual_pass', 1)))}}}",
            f"\\newcommand{{\\BenchPosNineSevenPlainStreamsN}}{{{_tex_int(int((sub_cpu_al.get('97') or {}).get('streams_dual_pass', 0)))}}}",
            f"\\newcommand{{\\BenchPosThirteenPlainStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('13') or {}).get('streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosThirteenOtwoStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('13') or {}).get('o2_streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosOneSevenFivePlainStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('175') or {}).get('streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosOneSevenFiveOtwoStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('175') or {}).get('o2_streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosOneSixFourPlainStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('164') or {}).get('streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosOneSixFourOtwoStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('164') or {}).get('o2_streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosNineFourPlainStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('94') or {}).get('streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosNineFourOtwoStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('94') or {}).get('o2_streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchPosNineSevenPlainStreamsFrac}}{{{_tex_int(int((sub_cpu_al.get('97') or {}).get('streams_dual_pass', 0)))}/3}}",
            f"\\newcommand{{\\BenchMaxCounterVal}}{{{max_cnt_str}}}",
            f"\\newcommand{{\\BenchUnconfRestoredOracleN}}{{{_tex_int(unconf_rest_or_n)}}}",
            f"\\newcommand{{\\BenchFittedMaskedFailN}}{{{_tex_int(fitted_masked_n)}}}",
            f"\\newcommand{{\\BenchPosOneSixFourTotSlopeTwoDec}}{{{abs(p164_tot_sl):.2f}}}",
            f"\\newcommand{{\\BenchPosThreeWorstTS}}{{{abs(p3_worst_ts_v):.2f}}}",
            f"\\newcommand{{\\BenchAllPtMaxBoundFailN}}{{{_tex_int(int(rest_f.get('all_point_max_bound_fail_n', 0)))}}}",
            f"\\newcommand{{\\BenchMinRefPlainCoreN}}{{{_tex_int(int(six_d.get('min_ref_plain_core_n', 2)))}}}",
            f"\\newcommand{{\\BenchMinRefOtwoCoreN}}{{{_tex_int(int(six_d.get('min_ref_o2_core_n', 2)))}}}",
            f"\\newcommand{{\\BenchMedRefPlainCoreN}}{{{_tex_int(int(six_d.get('med_ref_plain_core_n', 1)))}}}",
            f"\\newcommand{{\\BenchMedRefOtwoCoreN}}{{{_tex_int(int(six_d.get('med_ref_o2_core_n', 2)))}}}",
            f"\\newcommand{{\\BenchAddCpuOneThreeSlopeRange}}{{{_fmt_add_sl('13')}}}",
            f"\\newcommand{{\\BenchAddCpuOneSevenFiveSlopeRange}}{{{_fmt_add_sl('175')}}}",
            f"\\newcommand{{\\BenchAddCpuOneSixFourSlopeRange}}{{{_fmt_add_sl('164')}}}",
            f"\\newcommand{{\\BenchAddCpuNineFourSlopeRange}}{{{_fmt_add_sl('94')}}}",
            f"\\newcommand{{\\BenchAddCpuNineSevenSlopeRange}}{{{_fmt_add_sl('97')}}}",
            f"\\newcommand{{\\BenchOtwoMinusPlainSZeroMs}}{{{s0_ow_str}}}",
            f"\\newcommand{{\\BenchRestNonExSATwoN}}{{{_tex_int(int(non_ex_reg.get('s7_stream_selective', 0)))}}}",
            f"\\newcommand{{\\BenchRestNonExSubN}}{{{_tex_int(int(non_ex_reg.get('positive_sub50_regime', 0)))}}}",
            f"\\newcommand{{\\BenchRestNonExFlatN}}{{{_tex_int(non_ex_flat_n)}}}",
            f"\\newcommand{{\\BenchRestNonExNegN}}{{{_tex_int(int(non_ex_reg.get('negative_slope_all_streams', 0)))}}}",
            f"\\newcommand{{\\BenchRestNonExMixN}}{{{_tex_int(int(non_ex_reg.get('mixed_or_reversed', 0)))}}}",
            f"\\newcommand{{\\BenchAllPtExcessFailN}}{{{_tex_int(int(rest_f.get('all_point_excess_fail_n', 0)))}}}",
            f"\\newcommand{{\\BenchAllPtRoneInflN}}{{{_tex_int(int(rest_f.get('all_point_r1_infl_n', 0)))}}}",
            f"\\newcommand{{\\BenchAllPtNonRegFailN}}{{{_tex_int(len(allpt_nonreg_pos))}}}",
            f"\\newcommand{{\\BenchPosEighteen}}{{{_tex_int(int(allpt_nonreg_pos[0]) if len(allpt_nonreg_pos) >= 1 else 18)}}}",
            f"\\newcommand{{\\BenchPosFourFour}}{{{_tex_int(int(allpt_nonreg_pos[1]) if len(allpt_nonreg_pos) >= 2 else 44)}}}",
            f"\\newcommand{{\\BenchPOnePilotNeffTipN}}{{{_tex_int(neff_tip_val)}}}",
            f"\\newcommand{{\\BenchOZeroAgree}}{{{_tex_int(o0_ag_n)}}}",
            f"\\newcommand{{\\BenchOZeroMiss}}{{{_tex_int(o0_ms_n)}}}",
            f"\\newcommand{{\\BenchOZeroTotalTriples}}{{{_tex_int(o0_ag_n + o0_ms_n)}}}",
            f"\\newcommand{{\\BenchOZeroCapped}}{{{_tex_int((miss_d.get('O0_O2_O3') or {}).get('capped', 0))}}}",
            f"\\newcommand{{\\BenchOZeroOracleAbort}}{{{_tex_int((miss_d.get('O0_O2_O3') or {}).get('oracle_abort', 0))}}}",
            f"\\newcommand{{\\BenchOZeroOverlayFix}}{{{_tex_int((miss_d.get('O0_O2_O3') or {}).get('overlay_fixture_stop', 0))}}}",
            f"\\newcommand{{\\BenchOZeroInfraMiss}}{{{_tex_int((miss_d.get('O0_O2_O3') or {}).get('infra_failure', 0))}}}",
            f"\\newcommand{{\\BenchOZeroCapOtwoAgree}}{{{_tex_int((miss_d.get('O0_O2_O3') or {}).get('o2_o3_agree_on_o0_capped', 0))}}}",
            f"\\newcommand{{\\BenchShamAgree}}{{{_tex_int(sh_ag_n)}}}",
            f"\\newcommand{{\\BenchShamMiss}}{{{_tex_int(sh_ms_n)}}}",
            f"\\newcommand{{\\BenchShamTotalPairs}}{{{_tex_int(sh_ag_n + sh_ms_n)}}}",
            f"\\newcommand{{\\BenchShamCapped}}{{{_tex_int((miss_d.get('target_vs_sham') or {}).get('capped', 0))}}}",
            f"\\newcommand{{\\BenchShamOracleAbort}}{{{_tex_int((miss_d.get('target_vs_sham') or {}).get('oracle_abort', 0))}}}",
            f"\\newcommand{{\\BenchShamOverlayFix}}{{{_tex_int((miss_d.get('target_vs_sham') or {}).get('overlay_fixture_stop', 0))}}}",
            f"\\newcommand{{\\BenchShamInfraMiss}}{{{_tex_int((miss_d.get('target_vs_sham') or {}).get('infra_failure', 0))}}}",
            f"\\newcommand{{\\BenchCpuCapEvents}}{{{_tex_int(caps_cnt.get('cpu_cap', 0))}}}",
            f"\\newcommand{{\\BenchCpuCapPos}}{{{_tex_int(cap_pos_cnt.get('cpu_cap', 0))}}}",
            f"\\newcommand{{\\BenchTickCapEvents}}{{{_tex_int(caps_cnt.get('tick_cap', 0))}}}",
            f"\\newcommand{{\\BenchTickCapPos}}{{{_tex_int(cap_pos_cnt.get('tick_cap', 0))}}}",
            f"\\newcommand{{\\BenchCpuCapOZeroOnlyPts}}{{{_tex_int(cap_d.get('cpu_cap_o0_only_points', 0))}}}",
            f"\\newcommand{{\\BenchCpuCapTotalPts}}{{{_tex_int(cap_d.get('cpu_cap_total_points', 0))}}}",
            f"\\newcommand{{\\BenchOracleUpstreamN}}{{{_tex_int(ofb.get('upstream_total', sa4_r['count']))}}}",
            f"\\newcommand{{\\BenchOracleUpstreamPct}}{{{_pct_str(up_or_r)}}}",
            f"\\newcommand{{\\BenchOracleUpstreamCI}}{{{_ci_num(up_or_r)}}}",
            f"\\newcommand{{\\BenchOracleUpstreamTgtN}}{{{_tex_int(ofb.get('plain_target', 0) + ofb.get('ubsan_invalid_target', ofb.get('ubsan_only_target', 0)))}}}",
            f"\\newcommand{{\\BenchOracleUpstreamRefN}}{{{_tex_int(ofb.get('plain_reference', 0) + ofb.get('ubsan_invalid_reference', ofb.get('ubsan_only_reference', 0)))}}}",
            f"\\newcommand{{\\BenchOraclePlainN}}{{{_tex_int(ofb.get('plain_invalid_total', ofb.get('plain_target', 0) + ofb.get('plain_reference', 0) + ofb.get('restored_variant_failure', 0)))}}}",
            f"\\newcommand{{\\BenchOraclePlainUpstreamN}}{{{_tex_int(ofb.get('plain_target', 0) + ofb.get('plain_reference', 0))}}}",
            f"\\newcommand{{\\BenchOraclePlainTgtN}}{{{_tex_int(ofb.get('plain_target', 0))}}}",
            f"\\newcommand{{\\BenchOraclePlainRefN}}{{{_tex_int(ofb.get('plain_reference', 0))}}}",
            f"\\newcommand{{\\BenchOracleUBAllN}}{{{_tex_int(ofb.get('ubsan_invalid_total', ofb.get('ubsan_only_target', 0) + ofb.get('ubsan_only_reference', 0)))}}}",
            f"\\newcommand{{\\BenchOracleUBSanOnlyN}}{{{_tex_int(ofb.get('ubsan_only_target', 0) + ofb.get('ubsan_only_reference', 0))}}}",
            f"\\newcommand{{\\BenchOracleUBTgtN}}{{{_tex_int(ofb.get('ubsan_invalid_target', ofb.get('ubsan_only_target', 0)))}}}",
            f"\\newcommand{{\\BenchOracleUBRefN}}{{{_tex_int(ofb.get('ubsan_invalid_reference', ofb.get('ubsan_only_reference', 0)))}}}",
            f"\\newcommand{{\\BenchOraclePlainSegvUBN}}{{{_tex_int(ofb.get('plain_segv_and_ubsan_count', 0))}}}",
            f"\\newcommand{{\\BenchOracleRestoredN}}{{{_tex_int(ofb.get('restored_variant_failure', 0))}}}",
            f"\\newcommand{{\\BenchOracleShamN}}{{{_tex_int(ofb.get('sham_variant_failure', 0))}}}",
            f"\\newcommand{{\\BenchOracleMultiEvtN}}{{{_tex_int(ofb.get('multi_event_count', 0))}}}",
            f"\\newcommand{{\\BenchOracleCoordN}}{{{_tex_int(coord_or_n)}}}",
            f"\\newcommand{{\\BenchOracleCoordPct}}{{{(100.0 * coord_or_n / max(1, sa4_r['count'])) if cr else 0.0:.1f}\\%}}",
            f"\\newcommand{{\\BenchFitQZeroN}}{{{_tex_int(ifb.get('q_zero_complete_elim', 0))}}}",
            f"\\newcommand{{\\BenchFitBothZeroN}}{{{_tex_int(ifb.get('both_zero_c0', 0))}}}",
            f"\\newcommand{{\\BenchFitTickCapN}}{{{_tex_int(ifb.get('tick_cap_censored', 0))}}}",
            f"\\newcommand{{\\BenchCensorCondN}}{{{_tex_int(censor_r['count'])}}}",
            f"\\newcommand{{\\BenchCensorDenom}}{{{_tex_int(censor_r['total'])}}}",
            f"\\newcommand{{\\BenchCensorCondPct}}{{{_pct_str(censor_r)}}}",
            f"\\newcommand{{\\BenchCensorCondCI}}{{{_ci_num(censor_r)}}}",
            f"\\newcommand{{\\BenchCensorWorstN}}{{{_tex_int(censor_w['count'])}}}",
            f"\\newcommand{{\\BenchCensorWorstPct}}{{{_pct_str(censor_w)}}}",
            f"\\newcommand{{\\BenchCensorWorstCI}}{{{_ci_num(censor_w)}}}",
            f"\\newcommand{{\\BenchCensorWorstFisherP}}{{{_tex_p(float(ifb.get('censoring_worst_fisher_4_13', _fisher_two_sided_exact(int(censor_w['count']), int(censor_w['total']) - int(censor_w['count']), 4, 13 - 4))))}}}",
            f"\\newcommand{{\\BenchCensorWorstFisherFourTwelveP}}{{{_tex_p(float(ifb.get('censoring_worst_fisher_4_12', _fisher_two_sided_exact(int(censor_w['count']), int(censor_w['total']) - int(censor_w['count']), 4, 12 - 4))))}}}",
            f"\\newcommand{{\\BenchCensorWorstFisherConservP}}{{{_tex_p(float(ifb.get('censoring_worst_fisher_conserv', _fisher_two_sided_exact(int(censor_w['count']), int(censor_w['total']) - int(censor_w['count']), 3, 12 - 3))))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapExclFlatN}}{{{_tex_int(int(ifb.get('censoring_plus_cpucap_excl_flat_n', int(censor_w['count']))))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapExclFlatPct}}{{{_pct_str(ifb.get('censoring_plus_cpucap_excl_flat_rate') or censor_w)}}}",
            f"\\newcommand{{\\BenchCensorCpuCapExclFlatP}}{{{_tex_p(float(ifb.get('censoring_plus_cpucap_excl_flat_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapExclFlatConservP}}{{{_tex_p(float(ifb.get('censoring_plus_cpucap_excl_flat_conserv_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapTotalN}}{{{_tex_int(int(censor_w['count']) + len(ifb.get('cpu_cap_fitted_positions') or []))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapPct}}{{{_pct_str(rate_summary(int(censor_w['count']) + len(ifb.get('cpu_cap_fitted_positions') or []), int(censor_w['total'])))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapFourTwelveP}}{{{_tex_p(float(ifb.get('censoring_plus_cpucap_fisher_4_12_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapConservP}}{{{_tex_p(float(ifb.get('censoring_plus_cpucap_fisher_conserv_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchJointConservHolmPOne}}{{{_p_na((ex_comp.get('joint_conserv_holm_3') or {}).get('P1'), prefix='p_H = ')}}}",
            f"\\newcommand{{\\BenchJointConservHolmPThree}}{{{_p_na((ex_comp.get('joint_conserv_holm_3') or {}).get('P3'), prefix='p_H = ')}}}",
            f"\\newcommand{{\\BenchDistinctThreeN}}{{{_tex_int(sd_all.get('3_distinct', 0))}}}",
            f"\\newcommand{{\\BenchDistinctThreePct}}{{{100.0 * sd_all.get('3_distinct', 0) / max(1, n_fit):.1f}\\%}}",
            f"\\newcommand{{\\BenchDistinctTwoN}}{{{_tex_int(sd_all.get('2_distinct', 0))}}}",
            f"\\newcommand{{\\BenchDistinctTwoPct}}{{{100.0 * sd_all.get('2_distinct', 0) / max(1, n_fit):.1f}\\%}}",
            f"\\newcommand{{\\BenchDistinctOneN}}{{{_tex_int(sd_all.get('1_distinct', 0))}}}",
            f"\\newcommand{{\\BenchDistinctOnePct}}{{{100.0 * sd_all.get('1_distinct', 0) / max(1, n_fit):.1f}\\%}}",
            f"\\newcommand{{\\BenchDistinctOneCOneVarN}}{{{_tex_int(tax_d1_c1)}}}",
            f"\\newcommand{{\\BenchDistinctOneOblivN}}{{{_tex_int(tax_d1_ob)}}}",
            f"\\newcommand{{\\BenchZeroVarStreamsN}}{{{_tex_int(zv_n)}}}",
            f"\\newcommand{{\\BenchDefinedRTwoStreamsN}}{{{_tex_int(df_n)}}}",
            f"\\newcommand{{\\BenchTotalFittedStreamsN}}{{{_tex_int(zv_n + df_n)}}}",
            f"\\newcommand{{\\BenchAllStreamsMedianRTwo}}{{{float(r2_all.get('median') or 0.0):.3f}}}",
            f"\\newcommand{{\\BenchAlertMedianRTwo}}{{{float(r2_al.get('median') or 0.0):.4f}}}",
            f"\\newcommand{{\\BenchZeroVarPairsN}}{{{_tex_int(int(pair_r2.get('all_zero_var_pairs', 0)))}}}",
            f"\\newcommand{{\\BenchDefinedRTwoPairsN}}{{{_tex_int(int(pair_r2.get('defined_r2_pairs', 0)))}}}",
            f"\\newcommand{{\\BenchPairMedianRTwo}}{{{float(pair_r2.get('worst_stream_median_r2') or 0.0):.3f}}}",
            f"\\newcommand{{\\BenchAlertPairMedianRTwo}}{{{float(pair_r2.get('alert_worst_stream_median_r2') or 0.0):.4f}}}",
            f"\\newcommand{{\\BenchPThreePilotClustFisherP}}{{{_tex_p(fish.get('P3_pilot_12cl', fish.get('P3', 1.0)))}}}",
            f"\\newcommand{{\\BenchPThreePilotClustConservP}}{{{_tex_p(fish.get('P3_pilot_12cl_conserv', fish.get('P3', 1.0)))}}}",
            f"\\newcommand{{\\BenchPOnePilotNeffThirtyP}}{{{_tex_p(float(ne30.get('p1_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchPOnePilotNeffFiftyP}}{{{_tex_p(float(ne50.get('p1_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchSAOnePilotNeffRangeP}}{{$p = {min(sa1_neff_ps):.3f}\\text{{--}}{max(sa1_neff_ps):.3f}$}}",
            f"\\newcommand{{\\BenchSAThreeInclCompileN}}{{{_tex_int(orig_comp_n)}}}",
            f"\\newcommand{{\\BenchSAThreeInclCompilePct}}{{{_pct_str(orig_comp_r)}}}",
            f"\\newcommand{{\\BenchSAThreeInclCompileP}}{{{_tex_p(fish.get('SA3_incl_orig_compile_fail', _fisher_two_sided_exact(orig_comp_n, max(0, conf_s1_pass_n - orig_comp_n), 12, 14)))}}}",
            f"\\newcommand{{\\BenchSAThreeCrossFrameP}}{{{_tex_p(fish.get('S3', _fisher_two_sided_exact(sa3_r['count'], sa3_r['total'] - sa3_r['count'], 12, 14)))}}}",
            f"\\newcommand{{\\BenchConstZeroVarPairsN}}{{{_tex_int(max(0, int(pair_r2.get('all_zero_var_pairs', 0)) - int(regimes.get('exact_identity_T_eq_Q', 0))))}}}",
            f"\\newcommand{{\\BenchCensorCpuCapFisherP}}{{{_tex_p(ifb.get('censoring_plus_cpucap_fisher_p', 1.0))}}}",
            f"\\newcommand{{\\BenchRestCOneMaskN}}{{{_tex_int(int(rest_tot.get('c0_fail_to_tot_pass', 0)))}}}",
            f"\\newcommand{{\\BenchSANinePThreeCI}}{{{sa9_p3_ci_str}}}",
            f"\\newcommand{{\\BenchOZeroRelaxCapPtsN}}{{{_tex_int(int(o0_rlx.get('o0_only_cap_points_n', 0)))}}}",
            f"\\newcommand{{\\BenchOZeroRelaxPairsN}}{{{_tex_int(int(o0_rlx.get('affected_pairs_n', 0)))}}}",
            f"\\newcommand{{\\BenchOZeroRelaxDeltaN}}{{{_tex_int(abs(int(o0_rlx.get('p3_delta', 0))) + abs(int(o0_rlx.get('sa7_delta', 0))))}}}",
            f"\\newcommand{{\\BenchRealizedCpuCoreN}}{{{_tex_int(int(six_d.get('realized_cpu_core_n', 2)))}}}",
            f"\\newcommand{{\\BenchPlainSubCoreN}}{{{_tex_int(int(six_d.get('plain_sub_500_core_n', 1)))}}}",
            f"\\newcommand{{\\BenchOtwoSubCoreN}}{{{_tex_int(int(six_d.get('o2_sub_500_core_n', 2)))}}}",
            f"\\newcommand{{\\BenchFDWrapOverheadMs}}{{{fd_ow_str}}}",
            f"\\newcommand{{\\BenchPosOneSixFourCpuRatio}}{{{_fmt_ratio_range(p164_cpu_vals) if p164_cpu_vals else '0.00'}}}",
            f"\\newcommand{{\\BenchSubCpuOneSevenFiveSlopeRange}}{{{_sub_range_str('175')}}}",
            f"\\newcommand{{\\BenchSubCpuOneThreeSlopeRange}}{{{_sub_range_str('13')}}}",
            f"\\newcommand{{\\BenchPosThirteenPlainZeroSubRange}}{{{float((sub_cpu_al.get('13') or {}).get('pl0_slope_min', 0.0)):.2f}--{float((sub_cpu_al.get('13') or {}).get('pl0_slope_max', 0.0)):.2f}}}",
            f"\\newcommand{{\\BenchPosThirteenOtwoSubSlopeRange}}{{{float((sub_cpu_al.get('13') or {}).get('o2_slope_min', 0.0)):.2f}--{float((sub_cpu_al.get('13') or {}).get('o2_slope_max', 0.0)):.2f}}}",
            f"\\newcommand{{\\BenchPosOneSevenFiveOtwoSubSlopeRange}}{{{float((sub_cpu_al.get('175') or {}).get('o2_slope_min', 0.0)):.2f}--{float((sub_cpu_al.get('175') or {}).get('o2_slope_max', 0.0)):.2f}}}",
            f"\\newcommand{{\\BenchPosThirteenPlainDeltaMsRange}}{{{float((sub_cpu_al.get('13') or {}).get('pl_delta_ms_min', 0.0)):.1f}--{float((sub_cpu_al.get('13') or {}).get('pl_delta_ms_max', 0.0)):.1f}\\,\\text{{ms}}}}",
            f"\\newcommand{{\\BenchPosOneSevenFivePlainDeltaMsRange}}{{{float((sub_cpu_al.get('175') or {}).get('pl_delta_ms_min', 0.0)):.1f}--{float((sub_cpu_al.get('175') or {}).get('pl_delta_ms_max', 0.0)):.1f}\\,\\text{{ms}}}}",
            f"\\newcommand{{\\BenchSubCpuOneSixFourSlopeRange}}{{{_sub_range_str('164', allow_neg_math=True)}}}",
            f"\\newcommand{{\\BenchSubCpuNineFourSlopeRange}}{{{_sub_range_str('94', allow_neg_math=True)}}}",
            f"\\newcommand{{\\BenchSubCpuNineSevenSlopeRange}}{{{_sub_range_str('97')}}}",
            f"\\newcommand{{\\BenchSASevenCount}}{{{_tex_int(sa7_r.get('count') or 0)}}}",
            f"\\newcommand{{\\BenchSASevenPct}}{{{_pct_str(sa7_r)}}}",
            f"\\newcommand{{\\BenchSASevenCI}}{{{_ci_num(sa7_r)}}}",
            f"\\newcommand{{\\BenchSASevenOnlyN}}{{{_tex_int(max(0, int(sa7_r.get('count') or 0) - int(p3_r['count'])))}}}",
            f"\\newcommand{{\\BenchSAEightAdmittedN}}{{{_tex_int(sa8_adm_n)}}}",
            f"\\newcommand{{\\BenchSAEightAlertsN}}{{{_tex_int(sa8_al_r.get('count') or 0)}}}",
            f"\\newcommand{{\\BenchSAEightPct}}{{{_pct_str(sa8_al_r)}}}",
            f"\\newcommand{{\\BenchSAEightCI}}{{{_ci_num(sa8_al_r)}}}",
            f"\\newcommand{{\\BenchSAEightAnyAlertsN}}{{{_tex_int(sa8_any_r.get('count') or 0)}}}",
            f"\\newcommand{{\\BenchSAEightAnyPct}}{{{_pct_str(sa8_any_r)}}}",
            f"\\newcommand{{\\BenchSAEightAnyCI}}{{{_ci_num(sa8_any_r)}}}",
            f"\\newcommand{{\\BenchCoreFourN}}{{{_tex_int(core_r['count'])}}}",
            f"\\newcommand{{\\BenchCoreFourPct}}{{{_pct_str(core_r)}}}",
            f"\\newcommand{{\\BenchCoreFourCI}}{{{_ci_num(core_r)}}}",
            f"\\newcommand{{\\BenchCoreMinCILo}}{{{float(six_d.get('core_min_ci_lo', 0.0)):.2f}}}",
            f"\\newcommand{{\\BenchBOneAlertsN}}{{{_tex_int(b1_n)}}}",
            f"\\newcommand{{\\BenchBOnePct}}{{{_pct_str(b1_r)}}}",
            f"\\newcommand{{\\BenchBOneCI}}{{{_ci_num(b1_r)}}}",
            f"\\newcommand{{\\BenchBOneFPN}}{{{_tex_int(int((bs.get('B1_c0_ratio_ge_1_5_only') or {}).get('fp_vs_primary', 0)))}}}",
            f"\\newcommand{{\\BenchBOneFlatN}}{{{_tex_int(int(b1_dec.get('flat_constant_factor', 0)))}}}",
            f"\\newcommand{{\\BenchBOneSubN}}{{{_tex_int(int(b1_dec.get('positive_subthreshold', 0)))}}}",
            f"\\newcommand{{\\BenchBOneNegN}}{{{_tex_int(int(b1_dec.get('negative_slope_precomp', 0)))}}}",
            f"\\newcommand{{\\BenchBOneSelN}}{{{_tex_int(int(b1_dec.get('s7_stream_selective', 0)))}}}",
            f"\\newcommand{{\\BenchBOneMcNemarP}}{{{_tex_p(mcn_scr.get('B1', 1.0))}}}",
            f"\\newcommand{{\\BenchBOneHolmP}}{{{_tex_p(mcn_holm.get('B1', 1.0))}}}",
            f"\\newcommand{{\\BenchBTwoAlertsN}}{{{_tex_int(b2_n)}}}",
            f"\\newcommand{{\\BenchBTwoPct}}{{{_pct_str(b2_r)}}}",
            f"\\newcommand{{\\BenchBTwoCI}}{{{_ci_num(b2_r)}}}",
            f"\\newcommand{{\\BenchBThreeAlertsN}}{{{_tex_int(b3_n)}}}",
            f"\\newcommand{{\\BenchBThreePct}}{{{_pct_str(b3_r)}}}",
            f"\\newcommand{{\\BenchBThreeCI}}{{{_ci_num(b3_r)}}}",
            f"\\newcommand{{\\BenchBThreeAllExecN}}{{{_tex_int(b3_all_exec['count'])}}}",
            f"\\newcommand{{\\BenchBThreeAllExecDenom}}{{{_tex_int(b3_all_exec['total'])}}}",
            f"\\newcommand{{\\BenchBThreeAllExecPct}}{{{_pct_str(b3_all_exec)}}}",
            f"\\newcommand{{\\BenchBFourAlertsN}}{{{_tex_int(b4_n)}}}",
            f"\\newcommand{{\\BenchBFourPct}}{{{_pct_str(b4_r)}}}",
            f"\\newcommand{{\\BenchBFourCI}}{{{_ci_num(b4_r)}}}",
            f"\\newcommand{{\\BenchBFourMcNemarP}}{{{_tex_p(mcn_scr.get('B4', 1.0))}}}",
            f"\\newcommand{{\\BenchBFourHolmP}}{{{_tex_p(mcn_holm.get('B4', 1.0))}}}",
            f"\\newcommand{{\\BenchBFiveAlertsN}}{{{_tex_int(int(b5_obj['alerts']))}}}",
            f"\\newcommand{{\\BenchBFivePct}}{{{_pct_str(b5_r)}}}",
            f"\\newcommand{{\\BenchBFiveCI}}{{{_ci_num(b5_r)}}}",
            f"\\newcommand{{\\BenchBFiveTPN}}{{{_tex_int(int(b5_obj['tp_vs_primary']))}}}",
            f"\\newcommand{{\\BenchBFiveFPN}}{{{_tex_int(int(b5_obj['fp_vs_primary']))}}}",
            f"\\newcommand{{\\BenchBFiveMcNemarP}}{{{_tex_p(mcn_scr.get('B5', 1.0))}}}",
            f"\\newcommand{{\\BenchBFiveHolmP}}{{{_tex_p(mcn_holm.get('B5', 1.0))}}}",
            f"\\newcommand{{\\BenchBFiveCoreTPN}}{{{_tex_int(int(b5_core_d.get('tp', 0)))}}}",
            f"\\newcommand{{\\BenchBFiveCorePrecPct}}{{{_pct_str(b5_core_d.get('precision'))}}}",
            f"\\newcommand{{\\BenchBFiveCoreRecPct}}{{{_pct_str(b5_core_d.get('recall'))}}}",
            f"\\newcommand{{\\BenchRestPassAllN}}{{{_tex_int(int(rest_all.get('passed', 0)))}}}",
            f"\\newcommand{{\\BenchRestNoExAllN}}{{{_tex_int(int(rest_all.get('no_excess', 0)))}}}",
            f"\\newcommand{{\\BenchRestFailAllN}}{{{_tex_int(int(rest_all.get('failed', 0)))}}}",
            f"\\newcommand{{\\BenchRestUnmeasAllN}}{{{_tex_int(int(rest_all.get('unmeasured', 0)))}}}",
            f"\\newcommand{{\\BenchRestExecPassN}}{{{_tex_int(int(rest_exec_d.get('pass', 0)))}}}",
            f"\\newcommand{{\\BenchRestExecNoExN}}{{{_tex_int(int(rest_exec_d.get('no_excess', 0)))}}}",
            f"\\newcommand{{\\BenchRestExecFailN}}{{{_tex_int(int(rest_exec_d.get('fail', 0)))}}}",
            f"\\newcommand{{\\BenchRestExecUnmeasN}}{{{_tex_int(int(rest_exec_d.get('unmeasured', 0)))}}}",
            f"\\newcommand{{\\BenchRestFitPassN}}{{{_tex_int(int(fit_rest.get('passed', 0)))}}}",
            f"\\newcommand{{\\BenchRestFitNoExN}}{{{_tex_int(int(fit_rest.get('no_excess', 0)))}}}",
            f"\\newcommand{{\\BenchRestFitFailN}}{{{_tex_int(int(fit_rest.get('failed', 0)))}}}",
            f"\\newcommand{{\\BenchRestFitExcessN}}{{{_tex_int(fit_ex_n)}}}",
            f"\\newcommand{{\\BenchRestFitFailPct}}{{{_pct_str(fit_fail_r)}}}",
            f"\\newcommand{{\\BenchRestFitFailCI}}{{{_ci_num(fit_fail_r)}}}",
            f"\\newcommand{{\\BenchRestExactCopyN}}{{{_tex_int(int(rest_f.get('pass_exact_copy', 0)))}}}",
            f"\\newcommand{{\\BenchRestExactCopyPct}}{{{_pct_str(rest_exact_copy_r)}}}",
            f"\\newcommand{{\\BenchRestNonExactPassN}}{{{_tex_int(int(rest_f.get('non_exact_pass', max(0, int(fit_rest.get('passed', 0)) - int(rest_f.get('pass_exact_copy', 0))))))}}}",
            f"\\newcommand{{\\BenchRestSurgicalN}}{{{_tex_int(int(rest_f.get('pass_surgical_80_105', 0)))}}}",
            f"\\newcommand{{\\BenchRestMildOverN}}{{{_tex_int(int(rest_f.get('pass_mild_over_105_120', 0)))}}}",
            f"\\newcommand{{\\BenchRestHighOverN}}{{{_tex_int(int(rest_f.get('pass_over_gt_120', 0)))}}}",
            f"\\newcommand{{\\BenchRestTotPassN}}{{{_tex_int(int(rest_tot.get('pass', 0)))}}}",
            f"\\newcommand{{\\BenchRestTotNoExN}}{{{_tex_int(int(rest_tot.get('no_excess', 0)))}}}",
            f"\\newcommand{{\\BenchRestTotFailN}}{{{_tex_int(int(rest_tot.get('fail', 0)))}}}",
            f"\\newcommand{{\\BenchRestTotExcessN}}{{{_tex_int(int(rest_tot.get('excess_total', 0)))}}}",
            f"\\newcommand{{\\BenchRestTotFailPct}}{{{_pct_str(rest_tot_fail_r)}}}",
            f"\\newcommand{{\\BenchRestTotFailCI}}{{{_ci_num(rest_tot_fail_r)}}}",
            f"\\newcommand{{\\BenchRestTotNewTestN}}{{{_tex_int(int(rest_tot.get('newly_testable_from_c0_no_excess', 0)))}}}",
            f"\\newcommand{{\\BenchConfDeskPairsN}}{{{_tex_int(conf_desk_pairs_n)}}}",
            f"\\newcommand{{\\BenchFinHolmPOne}}{{{_p_na(fin_holm.get('P1'), prefix='p_H = ')}}}",
            f"\\newcommand{{\\BenchFinHolmPThree}}{{{_p_na(fin_holm.get('P3'), prefix='p_H = ')}}}",
            f"\\newcommand{{\\BenchCOneOnlyCount}}{{{_tex_int(int(tax.get('c1_only_hit_count', len(c1_hits_list))))}}}",
            f"\\newcommand{{\\BenchPosEleven}}{{11}}",
            f"\\newcommand{{\\BenchPosElevenCOneStream}}{{\\texttt{{{pos11_hit.get('stream', 'W3')}}}}}",
            f"\\newcommand{{\\BenchPosFourSevenCOneStream}}{{\\texttt{{{pos47_hit.get('stream', 'W2')}}}}}",
            f"\\newcommand{{\\BenchPosElevenCOneRatio}}{{{float(pos11_hit.get('max_c1_ratio', 0.0)):.1f}$\\times$}}",
            f"\\newcommand{{\\BenchQOneZeroCount}}{{{_tex_int(len(q1_zero_list))}}}",
            f"\\newcommand{{\\BenchPosThreeLev}}{{{p3_lev:.3f}}}",
            f"\\newcommand{{\\BenchPosThreeCooksD}}{{{float(p3_cooks_s[0]):.2f}}}",
            f"\\newcommand{{\\BenchPosThreeCooksDSThree}}{{{float(p3_cooks_s[2]):.2f}}}",
            f"\\newcommand{{\\BenchPosThreeCooksDSThreeMax}}{{{float(p3_max_cooks_s[2]):.2f}}}",
            f"\\newcommand{{\\BenchPosThreeSOneLOO}}{{{float(p3_loos_s[0]):.2f}}}",
            f"\\newcommand{{\\BenchPosThreeSThreeLOO}}{{{f'$-{abs(float(p3_loos_s[2])):.2f}$' if float(p3_loos_s[2]) < 0 else f'{float(p3_loos_s[2]):.2f}'}}}",
            f"\\newcommand{{\\BenchPosThreeSOneCI}}{{[{float(p3_ci_los_s[0]):.2f}, {float(p3_ci_his_s[0]):.2f}]}}",
            f"\\newcommand{{\\BenchPosThreeSThreeCI}}{{[{float(p3_ci_los_s[2]):.2f}, {float(p3_ci_his_s[2]):.2f}]}}",
            f"\\newcommand{{\\BenchPosThirteenCZeroSlope}}{{{p13_c0_sl:.2f}}}",
            f"\\newcommand{{\\BenchPosThirteenTotSlope}}{{{p13_tot_sl:.2f}}}",
            f"\\newcommand{{\\BenchPosNineFourOtwoNsRange}}{{{p94_st['o2_min']:.2f}--{p94_st['o2_max']:.2f}}}",
            f"\\newcommand{{\\BenchPosNineFourPlainNsRange}}{{{p94_pl_lo_str} to {p94_pl_hi_str}}}",
            f"\\newcommand{{\\BenchPosNineFourOtwoMsRange}}{{{p94_st['o2_ms_diff_min']:.1f}--{p94_st['o2_ms_diff_max']:.1f}\\,\\text{{ms}}}}",
            f"\\newcommand{{\\BenchPosOneSevenFiveOtwoNsRange}}{{{p175_st['o2_min']:.1f}--{p175_st['o2_max']:.1f}}}",
            f"\\newcommand{{\\BenchPosOneSevenFivePlainNsRange}}{{{p175_st['plain_min']:.1f}--{p175_st['plain_max']:.1f}}}",
            f"\\newcommand{{\\BenchEnvPOneRange}}{{{env_p1_lo:.1f}--{env_p1_hi:.1f}\\%}}",
            f"\\newcommand{{\\BenchEnvPThreeRange}}{{{env_p3_lo:.1f}--{env_p3_hi:.1f}\\%}}",
            f"\\newcommand{{\\BenchEnvSAFourRange}}{{{env_sa4_lo:.1f}--{env_sa4_hi:.1f}\\%}}",
            f"\\newcommand{{\\BenchEnvSAThirteenRange}}{{{_tex_s1(s13_lo_row[3])}~pp ({_p_na(s13_lo_row[7])}) to {_tex_s1(s13_hi_row[3])}~pp ({_p_na(s13_hi_row[7])})}}",
            f"\\newcommand{{\\BenchEnvSAThirteenShort}}{{{_tex_s1(s13_lo_row[3])} to {_tex_s1(s13_hi_row[3])}~pp, {f'$p = {min(float(s13_lo_row[7]), float(s13_hi_row[7])):.3f}\\text{{--}}{max(float(s13_lo_row[7]), float(s13_hi_row[7])):.3f}$' if (s13_lo_row[7] is not None and s13_hi_row[7] is not None) else _p_na(s13_hi_row[7])}}}",
            f"\\newcommand{{\\BenchPfStderrN}}{{{_tex_int(int(((forensics or {}).get('chronological_failure_audit') or {}).get('rc_0_stderr_count', 0)))}}}",
            f"\\newcommand{{\\BenchPfSigabrtN}}{{{_tex_int(int(((forensics or {}).get('chronological_failure_audit') or {}).get('rc_134_sigabrt_count', 0)))}}}",
            f"\\newcommand{{\\BenchPfSigsegvN}}{{{_tex_int(int(((forensics or {}).get('chronological_failure_audit') or {}).get('rc_139_sigsegv_count', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeExactEqN}}{{{_tex_int(int(regimes.get('exact_identity_T_eq_Q', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeFlatLowN}}{{{_tex_int(int(regimes.get('flat_near_1_lt_1.5', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeFlatHighN}}{{{_tex_int(int(regimes.get('flat_constant_factor_ge_1.5', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeZeroFlatSumN}}{{{_tex_int(z_flat_sum)}}}",
            f"\\newcommand{{\\BenchRegimeNegAllN}}{{{_tex_int(int(regimes.get('negative_slope_all_streams', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeMixedN}}{{{_tex_int(int(regimes.get('mixed_or_reversed', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeSubPosN}}{{{_tex_int(int(regimes.get('positive_sub50_regime', 0)))}}}",
            f"\\newcommand{{\\BenchRegimeRevSubSumN}}{{{_tex_int(rev_sub_sum)}}}",
            f"\\newcommand{{\\BenchBetaGridDropAlerts}}{{{_tex_int(int(b_grid.get('0.1', p3_r['count'])))}}}",
            f"\\newcommand{{\\BenchCorpusPieAlertFrac}}{{{_tex_int(int(pie_cs.get('alert', 0)))}/{_tex_int(int(pie_cs.get('fitted', 0)))}}}",
            f"\\newcommand{{\\BenchCorpusCodeAlertFrac}}{{{_tex_int(int(cod_cs.get('alert', 0)))}/{_tex_int(int(cod_cs.get('fitted', 0)))}}}",
            f"\\newcommand{{\\BenchCorpusAlertFisherP}}{{{_tex_p(_fisher_two_sided_exact(int(pie_cs.get('alert', 0)), max(0, int(pie_cs.get('fitted', 0)) - int(pie_cs.get('alert', 0))), int(cod_cs.get('alert', 0)), max(0, int(cod_cs.get('fitted', 0)) - int(cod_cs.get('alert', 0)))))}}}",
            f"\\newcommand{{\\BenchCorpusPieExecFrac}}{{{_tex_int(int(pie_cs.get('executed', 0)))}/{_tex_int(int(pie_cs.get('s0_pass', 0)))} = {100.0 * int(pie_cs.get('executed', 0)) / max(1, int(pie_cs.get('s0_pass', 1))):.1f}\\%}}",
            f"\\newcommand{{\\BenchCorpusCodeExecFrac}}{{{_tex_int(int(cod_cs.get('executed', 0)))}/{_tex_int(int(cod_cs.get('s0_pass', 0)))} = {100.0 * int(cod_cs.get('executed', 0)) / max(1, int(cod_cs.get('s0_pass', 1))):.1f}\\%}}",
            f"\\newcommand{{\\BenchCorpusExecFisherP}}{{{_tex_p(float((forensics or {}).get('corpus_exec_fisher_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchContestExecPct}}{{{_pct_str(s10_contest)}}}",
            f"\\newcommand{{\\BenchContestExecCI}}{{{_ci_num(s10_contest)}}}",
            f"\\newcommand{{\\BenchContestExecLo}}{{{(s10_contest.get('clopper_pearson_95pct_percent') or [0.0])[0]:.1f}\\%}}",
            f"\\newcommand{{\\BenchSAFourFisherP}}{{{_tex_p(fish.get('S4', 1.0))}}}",
            f"\\newcommand{{\\BenchSAThreeDenom}}{{{_tex_int(int(sa3_r.get('total', 154)))}}}",
            f"\\newcommand{{\\BenchSAThreeAllSPass}}{{{_tex_int(sa3_all_s1['count'])}/{_tex_int(sa3_all_s1['total'])} = {_pct_str(sa3_all_s1)}}}",
            f"\\newcommand{{\\BenchSAThreeAllSPassCI}}{{{_ci_num(sa3_all_s1)}}}",
            f"\\newcommand{{\\BenchPosThreeRSq}}{{{p3_s3_r2:.3f}}}",
            f"\\newcommand{{\\BenchPosSevenSevenLogRSq}}{{{float(ex_m.get('pos_77_log_r2', 0.0)):.3f}}}",
            f"\\newcommand{{\\BenchPosOneSixFourRatio}}{{{_tex_int(round(p164_c0_r))}$\\times$}}",
            f"\\newcommand{{\\BenchPosOneSixFourTotP}}{{{_tex_p(p164_tot_p_val)}}}",
            f"\\newcommand{{\\BenchPosOneSixFourTotSlope}}{{{p164_tot_sl:.4f}}}",
            f"\\newcommand{{\\BenchPosOneSixFourTotRSq}}{{{p164_tot_r2:.3f}}}",
            f"\\newcommand{{\\BenchPosSevenNine}}{{{_tex_int(int(b2_only_d.get('position', 0)))}}}",
            f"\\newcommand{{\\BenchPosSevenNineSlopeRange}}{{{b2_only_d['slope_range'][0]:.2f}--{b2_only_d['slope_range'][1]:.2f}}}",
            f"\\newcommand{{\\BenchPosSevenNineRatioRange}}{{{b2_only_d['ratio_range'][0]:.2f}--{b2_only_d['ratio_range'][1]:.2f}$\\times$}}",
            f"\\newcommand{{\\BenchQuarSourceN}}{{{_tex_int(q_src_n)}}}",
            f"\\newcommand{{\\BenchQuarHeldN}}{{{_tex_int(q_hld)}}}",
            f"\\newcommand{{\\BenchQuarIndetN}}{{{_tex_int(q_ind)}}}",
            f"\\newcommand{{\\BenchRestCOneInflN}}{{{_tex_int(int(ex_m.get('rest_c1_inflation_events', 0)))}}}",
            r"\newcommand{\BenchPosThree}{3}",
            r"\newcommand{\BenchPosThirteen}{13}",
            r"\newcommand{\BenchPosTwoSeven}{27}",
            r"\newcommand{\BenchPosFourSeven}{47}",
            r"\newcommand{\BenchPosFiveFive}{55}",
            r"\newcommand{\BenchPosFiveNine}{59}",
            r"\newcommand{\BenchPosSevenSeven}{77}",
            r"\newcommand{\BenchPosNineZero}{90}",
            r"\newcommand{\BenchPosNineOne}{91}",
            r"\newcommand{\BenchPosNineFour}{94}",
            r"\newcommand{\BenchPosNineSeven}{97}",
            r"\newcommand{\BenchPosOneZeroZero}{100}",
            r"\newcommand{\BenchPosOneZeroSix}{106}",
            r"\newcommand{\BenchPosOneTwoNine}{129}",
            r"\newcommand{\BenchPosOneThreeOne}{131}",
            r"\newcommand{\BenchPosOneFourZero}{140}",
            r"\newcommand{\BenchPosOneFourFive}{145}",
            r"\newcommand{\BenchPosOneFiveEight}{158}",
            r"\newcommand{\BenchPosOneSixZero}{160}",
            r"\newcommand{\BenchPosOneSixFour}{164}",
            r"\newcommand{\BenchPosOneSevenFour}{174}",
            r"\newcommand{\BenchPosOneSevenFive}{175}",
            f"\\newcommand{{\\BenchPosSevenSevenRatio}}{{{float(ex_m.get('pos_77_c0_ratio', 0.0)):.2f}$\\times$}}",
            f"\\newcommand{{\\BenchPosNineZeroRatio}}{{{_tex_int(int(ex_m.get('pos_90_c0_ratio', 0)))}$\\times$}}",
            f"\\newcommand{{\\BenchPosOneFourFiveRatio}}{{{_tex_int(int(ex_m.get('pos_145_c0_ratio', 0)))}$\\times$}}",
            f"\\newcommand{{\\BenchPosFourSevenCOneRatio}}{{{_tex_int(round(float(ex_m.get('pos_47_c1_ratio', 0.0))))}$\\times$}}",
            f"\\newcommand{{\\BenchPosNineFourTicksM}}{{{float(ex_m.get('pos_94_ticks_m', 0.0)):.1f}}}",
            f"\\newcommand{{\\BenchPosOneSixFourTotRatio}}{{{float(ex_m.get('pos_164_tot_ratio', 0.0)):.2f}$\\times$}}",
            f"\\newcommand{{\\BenchPosOneZeroZeroMaxSlope}}{{{float(ex_m.get('pos_100_131_max_tot_slope', 0.0)):.3f}}}",
            f"\\newcommand{{\\BenchPosBothZeroMaxSlope}}{{{float(ex_m.get('both_zero_max_tot_slope', 0.0)):.3f}}}",
            f"\\newcommand{{\\BenchRestOverNineOneRange}}{{{int((ex_m.get('pos_91_rec_pct_range') or [0, 0])[0])}--{int((ex_m.get('pos_91_rec_pct_range') or [0, 0])[1])}\\%}}",
            f"\\newcommand{{\\BenchRestOverOneTwoNineRange}}{{{int((ex_m.get('pos_129_rec_pct_range') or [0, 0])[0])}--{int((ex_m.get('pos_129_rec_pct_range') or [0, 0])[1])}\\%}}",
            f"\\newcommand{{\\BenchQuarStopPct}}{{{_pct_str(q_s1_r)}}}",
            f"\\newcommand{{\\BenchQuarStopCI}}{{{_ci_num(q_s1_r)}}}",
            f"\\newcommand{{\\BenchQuarClustStopFrac}}{{{s12_cl_frac}}}",
            f"\\newcommand{{\\BenchQuarClustStopCI}}{{{_ci_num(s12_cl)}}}",
        ])

        # Author IRR & Manski macros
        ex_a = (author_check or {}).get("exact") or {"n_pairs": 50, "n_clusters": 38, "raw_agreement_count": 0, "raw_agreement_pct": 0.0, "cohens_kappa": 0.0, "cluster_bootstrap_95pct_kappa": [0.0, 0.0]}
        bk_a = (author_check or {}).get("bucket") or {"n_pairs": 50, "n_clusters": 38, "raw_agreement_count": 0, "raw_agreement_pct": 0.0, "cohens_kappa": 0.0, "cluster_bootstrap_95pct_kappa": [0.0, 0.0]}
        irr_s = (forensics or {}).get("s1_irr_stratified") or {}
        ov_i = irr_s.get("overall") or {"n": 50, "binary_agree_pct": 0.0, "binary_kappa": 0.0, "binary_pabak": 0.0, "binary_gwet_ac1": 0.0, "binary_bias_index": 0.0, "binary_prevalence_index": 0.0, "bowker_q_df3": 0.0, "binary_mcnemar_p": 1.0, "bowker_p": 1.0, "bucket_kappa_max": 0.0, "bucket_gwet_ac1": 0.0, "binary_matrix": [[0, 0], [0, 1]]}
        cf_i = irr_s.get("confirmatory") or {"n": 20, "bucket_agree_pct": 0.0, "bucket_kappa": 0.0, "binary_kappa": 0.0, "binary_matrix": [[0, 0], [0, 1]], "contract_to_author_pass_count": 0, "contract_total": 1, "bucket_kappa_boot_ci": [0.0, 0.0], "binary_kappa_boot_ci": [0.0, 0.0], "binary_pabak_boot_ci": [0.0, 0.0], "binary_ac1_boot_ci": [0.0, 0.0], "binary_mcnemar_p": 1.0}
        qr_i = irr_s.get("quarantined") or {"n": 30, "bucket_agree_pct": 0.0, "bucket_kappa": 0.0, "binary_kappa": 0.0, "contract_to_author_pass_count": 0, "contract_total": 1}
        cf_stop_rev = irr_s.get("confirmatory_all_stop_reversal_ci") or rate_summary(0, 1)
        qr_bm = qr_i.get("binary_matrix") or [[0, 0], [0, 1]]
        qr_c2p = int(qr_i.get("contract_to_author_pass_count", 0))
        qr_ctot = max(1, int(qr_i.get("contract_total", 1)))
        qr_contract_rev_r = rate_summary(qr_c2p, qr_ctot)
        mk_b = irr_s.get("manski_bounds") or {"tipping_theta_sa13_pct": 0.0, "plugin_theta_pct": 0.0, "plugin_theta_ci_pct": [0.0, 0.0], "plugin_sa13_delta_pp": 0.0, "plugin_sa13_two_step_delta_pp": 0.0, "plugin_rateable_p1_pct": 0.0, "tipping_theta_full_p2_pct": 0.0}
        rev_ci = irr_s.get("confirmatory_contract_reversal_ci") or rate_summary(0, 1)
        rej_ci = irr_s.get("author_rejected_pass_exec_ci") or rate_summary(0, 1)
        ex_ci_l = ex_a.get("cluster_bootstrap_95pct_kappa") or [0.0, 0.0]
        bk_ci_l = bk_a.get("cluster_bootstrap_95pct_kappa") or [0.0, 0.0]
        ov_bm = ov_i.get("binary_matrix") or [[0, 0], [0, 0]]
        cf_bm = cf_i.get("binary_matrix") or [[0, 0], [0, 0]]
        llm_pass_tot = int(ov_bm[0][0]) + int(ov_bm[0][1])
        auth_pass_tot = int(ov_bm[0][0]) + int(ov_bm[1][0])
        ov_n = max(1, int(ov_i.get("n", 50)))
        llm_pass_r = rate_summary(llm_pass_tot, ov_n)
        auth_pass_r = rate_summary(auth_pass_tot, ov_n)
        n_cl_tot = int(ex_a.get("n_clusters", 38))
        n_cl_conf = int(cf_i.get("n", 20))
        n_cl_quar = max(0, n_cl_tot - n_cl_conf)
        mk_ci = mk_b.get("plugin_theta_ci_pct") or [0.0, 0.0]
        cf_bk_ci = cf_i.get("bucket_kappa_boot_ci") or [0.0, 0.0]
        cf_bn_ci = cf_i.get("binary_kappa_boot_ci") or [0.0, 0.0]
        cf_pb_ci = cf_i.get("binary_pabak_boot_ci") or [0.0, 0.0]
        cf_ac_ci = cf_i.get("binary_ac1_boot_ci") or [0.0, 0.0]

        mk_rect = mk_b.get("plugin_theta_joint_rect_ci_pct") or mk_ci
        mk_jeff = mk_b.get("plugin_theta_joint_jeffreys_ci_pct") or mk_ci
        p3t = mk_b.get("p3_tipping") or {}
        p3t_or = p3t.get("oracle_vs_4_13") or {"min_k": 0, "pct": 0.0, "resulting_pct": 0.0}
        p3t_orc = p3t.get("oracle_vs_3_12_conserv") or {"min_k": 0, "pct": 0.0}
        p3t_s1 = p3t.get("s1_vs_4_13") or {"min_k": 0, "pct": 0.0, "resulting_pct": 0.0}
        p3t_s1c = p3t.get("s1_vs_3_12_conserv") or {"min_k": 0, "pct": 0.0}
        lines.extend([
            f"\\newcommand{{\\BenchAuthExactPct}}{{{ex_a['raw_agreement_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthExactK}}{{{_tex_k3(float(ex_a.get('cohens_kappa') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthExactCI}}{{[{_tex_k3(ex_ci_l[0])}, {_tex_k3(ex_ci_l[1])}]}}",
            f"\\newcommand{{\\BenchAuthBucketPct}}{{{bk_a['raw_agreement_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthBucketK}}{{{_tex_k3(float(bk_a.get('cohens_kappa') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthBucketCI}}{{[{_tex_k3(bk_ci_l[0])}, {_tex_k3(bk_ci_l[1])}]}}",
            f"\\newcommand{{\\BenchAuthBucketKappaMax}}{{{_tex_k3(float(ov_i.get('bucket_kappa_max') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthBucketACOne}}{{{_tex_k3(float(ov_i.get('bucket_gwet_ac1') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthBinPct}}{{{ov_i['binary_agree_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthBinK}}{{{_tex_k3(ov_i['binary_kappa'])}}}",
            f"\\newcommand{{\\BenchAuthBinPABAK}}{{{_tex_k3(ov_i['binary_pabak'])}}}",
            f"\\newcommand{{\\BenchAuthBinACOne}}{{{_tex_k3(ov_i['binary_gwet_ac1'])}}}",
            f"\\newcommand{{\\BenchAuthBinBI}}{{{float(ov_i.get('binary_bias_index') or 0.0):.2f}}}",
            f"\\newcommand{{\\BenchAuthBinPI}}{{{float(ov_i.get('binary_prevalence_index') or 0.0):.2f}}}",
            f"\\newcommand{{\\BenchAuthBowkerQ}}{{{float(ov_i.get('bowker_q_df3') or 0.0):.2f}}}",
            f"\\newcommand{{\\BenchAuthMcNemarP}}{{{_tex_p(ov_i['binary_mcnemar_p'])}}}",
            f"\\newcommand{{\\BenchAuthBowkerP}}{{{_tex_p(ov_i['bowker_p'])}}}",
            f"\\newcommand{{\\BenchAuthAllBowkerExactP}}{{{_tex_p(float(ov_i.get('bowker_exact_p', ov_i['bowker_p'])))}}}",
            f"\\newcommand{{\\BenchAuthConfN}}{{{_tex_int(int(cf_i.get('n', 20)))}}}",
            f"\\newcommand{{\\BenchAuthQuarN}}{{{_tex_int(int(qr_i.get('n', 30)))}}}",
            f"\\newcommand{{\\BenchAuthQuarClustersN}}{{{_tex_int(n_cl_quar)}}}",
            f"\\newcommand{{\\BenchAuthTotalClustersN}}{{{_tex_int(n_cl_tot)}}}",
            f"\\newcommand{{\\BenchAuthLLMPassFrac}}{{{_tex_int(llm_pass_tot)}/{_tex_int(ov_n)} = {_pct_str(llm_pass_r)}}}",
            f"\\newcommand{{\\BenchAuthAuthorPassFrac}}{{{_tex_int(auth_pass_tot)}/{_tex_int(ov_n)} = {_pct_str(auth_pass_r)}}}",
            f"\\newcommand{{\\BenchAuthConfPct}}{{{cf_i['bucket_agree_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthConfKappa}}{{{_tex_k3(float(cf_i.get('bucket_kappa') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthConfBinK}}{{{_tex_k3(cf_i['binary_kappa'])}}}",
            f"\\newcommand{{\\BenchAuthConfBucketKCI}}{{[{_tex_k3(cf_bk_ci[0])}, {_tex_k3(cf_bk_ci[1])}]}}",
            f"\\newcommand{{\\BenchAuthConfBinKCI}}{{[{_tex_k3(cf_bn_ci[0])}, {_tex_k3(cf_bn_ci[1])}]}}",
            f"\\newcommand{{\\BenchAuthConfPABAKCI}}{{[{_tex_k3(cf_pb_ci[0])}, {_tex_k3(cf_pb_ci[1])}]}}",
            f"\\newcommand{{\\BenchAuthConfACOneCI}}{{[{_tex_k3(cf_ac_ci[0])}, {_tex_k3(cf_ac_ci[1])}]}}",
            f"\\newcommand{{\\BenchAuthConfAllStopRev}}{{{_tex_int(cf_stop_rev['count'])}/{_tex_int(cf_stop_rev['total'])} = {cf_stop_rev['percent']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthConfAllStopRevCI}}{{{_ci_num(cf_stop_rev)}}}",
            f"\\newcommand{{\\BenchAuthConfPassStopN}}{{{_tex_int(int(cf_bm[0][1]))}}}",
            f"\\newcommand{{\\BenchAuthConfStopPassN}}{{{_tex_int(int(cf_bm[1][0]))}}}",
            f"\\newcommand{{\\BenchAuthConfMcNemarP}}{{{_tex_p(float(cf_i.get('binary_mcnemar_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchAuthConfBowkerQ}}{{{float(cf_i.get('bowker_q_df3') or 0.0):.2f}}}",
            f"\\newcommand{{\\BenchAuthConfBowkerP}}{{{_tex_p(float(cf_i.get('bowker_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchAuthConfBowkerExactP}}{{{_tex_p(float(cf_i.get('bowker_exact_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchAuthQuarPct}}{{{qr_i['bucket_agree_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthQuarKappa}}{{{_tex_k3(float(qr_i.get('bucket_kappa') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthQuarBinK}}{{{_tex_k3(float(qr_i.get('binary_kappa') or 0.0))}}}",
            f"\\newcommand{{\\BenchAuthQuarRev}}{{{_tex_int(qr_c2p)}/{_tex_int(qr_ctot)} = {qr_contract_rev_r['percent']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthCohortFisherP}}{{{_tex_p(irr_s.get('cohort_bucket_fisher_p', 1.0))}}}",
            f"\\newcommand{{\\BenchCohortClustSensP}}{{$p = {float((irr_s.get('cohort_bucket_fisher_18cl_range') or [0.0, 0.0])[0]):.3f}\\text{{--}}{float((irr_s.get('cohort_bucket_fisher_18cl_range') or [0.0, 0.0])[1]):.3f}$}}",
            f"\\newcommand{{\\BenchAuthConfContractRev}}{{{_tex_int(cf_i['contract_to_author_pass_count'])}/{_tex_int(cf_i['contract_total'])} = {rev_ci['percent']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthConfContractRevCI}}{{{_ci_num(rev_ci)}}}",
            f"\\newcommand{{\\BenchAuthRejExec}}{{{_tex_int(rej_ci['count'])}/{_tex_int(rej_ci['total'])}~=~{rej_ci['percent']:.1f}\\%}}",
            f"\\newcommand{{\\BenchAuthRejExecCI}}{{{_ci_num(rej_ci)}}}",
            f"\\newcommand{{\\BenchAuthPassStopN}}{{{_tex_int(int(ov_bm[0][1]))}}}",
            f"\\newcommand{{\\BenchAuthStopPassN}}{{{_tex_int(int(ov_bm[1][0]))}}}",
            f"\\newcommand{{\\BenchAuthRejTotalN}}{{{_tex_int(int(rej_ci['total']))}}}",
            f"\\newcommand{{\\BenchManskiTipNum}}{{{_tex_int(max(0, int(s13_desk['count']) - int(s13_p1['count'])) // 2)}}}",
            f"\\newcommand{{\\BenchManskiTipRate}}{{{mk_b['tipping_theta_sa13_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchManskiPlugInTheta}}{{{mk_b['plugin_theta_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchManskiPlugInThetaCI}}{{[{mk_ci[0]:.1f}, {mk_ci[1]:.1f}]\\%}}",
            f"\\newcommand{{\\BenchManskiPlugJointRectCI}}{{[{mk_rect[0]:.1f}, {mk_rect[1]:.1f}]\\%}}",
            f"\\newcommand{{\\BenchManskiPlugJointJeffCI}}{{[{mk_jeff[0]:.1f}, {mk_jeff[1]:.1f}]\\%}}",
            f"\\newcommand{{\\BenchManskiPlugInSAThirteen}}{{{_tex_s1(mk_b['plugin_sa13_delta_pp'])}~pp}}",
            f"\\newcommand{{\\BenchManskiPlugInTwoStepSAThirteen}}{{{_tex_s1(mk_b.get('plugin_sa13_two_step_delta_pp', mk_b['plugin_sa13_delta_pp']))}~pp}}",
            f"\\newcommand{{\\BenchManskiPlugInPOne}}{{{mk_b['plugin_rateable_p1_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchManskiFullFlipTheta}}{{{mk_b['tipping_theta_full_p2_pct']:.1f}\\%}}",
            f"\\newcommand{{\\BenchManskiTwoStepTipTheta}}{{{float(mk_b.get('tipping_theta_two_step_pct', mk_b['tipping_theta_sa13_pct'])):.1f}\\%}}",
            f"\\newcommand{{\\BenchManskiTwoStepTipPfn}}{{{float(mk_b.get('tipping_pfn_two_step_pct', mk_b['tipping_theta_sa13_pct'])):.1f}\\%}}",
            f"\\newcommand{{\\BenchManskiYOneStepHalfPP}}{{{float(mk_b.get('plugin_sa13_y_half_width_pp', 0.0)):.1f}~pp}}",
            f"\\newcommand{{\\BenchManskiYTwoStepHalfPP}}{{{float(mk_b.get('plugin_sa13_two_step_y_half_width_pp', 0.0)):.1f}~pp}}",
            f"\\newcommand{{\\BenchManskiYDeltaSEDiffPP}}{{{float(mk_b.get('plugin_theta_delta_se_diff_pp', 0.0)):.2f}~pp}}",
            f"\\newcommand{{\\BenchPThreeOracleTipN}}{{{_tex_int(int(p3t_or['min_k']))}}}",
            f"\\newcommand{{\\BenchPThreeOracleTipPct}}{{{float(p3t_or['pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeOracleTipResultPct}}{{{float(p3t_or['resulting_pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeOracleTipConservN}}{{{_tex_int(int(p3t_orc['min_k']))}}}",
            f"\\newcommand{{\\BenchPThreeOracleTipConservPct}}{{{float(p3t_orc['pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeOracleAdvTipN}}{{{_tex_int(int((p3t.get('oracle_adv_vs_4_13') or p3t_or)['min_k']))}}}",
            f"\\newcommand{{\\BenchPThreeOracleAdvTipPct}}{{{float((p3t.get('oracle_adv_vs_4_13') or p3t_or)['pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeOracleAdvTipConservN}}{{{_tex_int(int((p3t.get('oracle_adv_vs_3_12_conserv') or p3t_orc)['min_k']))}}}",
            f"\\newcommand{{\\BenchPThreeOracleAdvTipConservPct}}{{{float((p3t.get('oracle_adv_vs_3_12_conserv') or p3t_orc)['pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeSOneTipN}}{{{_tex_int(int(p3t_s1['min_k']))}}}",
            f"\\newcommand{{\\BenchPThreeSOneTipPct}}{{{float(p3t_s1['pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeSOneTipResultPct}}{{{float(p3t_s1['resulting_pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeSOneTipConservN}}{{{_tex_int(int(p3t_s1c['min_k']))}}}",
            f"\\newcommand{{\\BenchPThreeSOneTipConservPct}}{{{float(p3t_s1c['pct']):.1f}\\%}}",
            f"\\newcommand{{\\BenchSAThirteenFpTipN}}{{{_tex_int(int((mk_b.get('sa13_fp_tipping') or {}).get('min_k', 0)))}}}",
            f"\\newcommand{{\\BenchSAThirteenFpTipPct}}{{{float((mk_b.get('sa13_fp_tipping') or {}).get('pct', 0.0)):.1f}\\%}}",
            f"\\newcommand{{\\BenchSAThirteenFpTipDelta}}{{{_tex_s1(float((mk_b.get('sa13_fp_tipping') or {}).get('delta_pp', 0.0)))}~pp}}",
            f"\\newcommand{{\\BenchSAThirteenFpTipP}}{{{_tex_p(float((mk_b.get('sa13_fp_tipping') or {}).get('sign_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchAuthConfFitRejFrac}}{{{_tex_int(int((irr_s.get('author_rejected_conf_fits_ci') or {}).get('count', 0)))}/{_tex_int(int((irr_s.get('author_rejected_conf_fits_ci') or {}).get('total', 1)))} = {float((irr_s.get('author_rejected_conf_fits_ci') or {}).get('percent') or 0.0):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeFpTipConservN}}{{{_tex_int(int(((mk_b.get('p3_fp_tipping') or {}).get('vs_3_12_conserv') or {}).get('min_k', 0)))}}}",
            f"\\newcommand{{\\BenchPThreeFpTipConservPct}}{{{float(((mk_b.get('p3_fp_tipping') or {}).get('vs_3_12_conserv') or {}).get('pct', 0.0)):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeFpTipConservP}}{{{_tex_p(float(((mk_b.get('p3_fp_tipping') or {}).get('vs_3_12_conserv') or {}).get('fisher_p', 1.0)))}}}",
            f"\\newcommand{{\\BenchPThreeFpTipFullN}}{{{_tex_int(int(((mk_b.get('p3_fp_tipping') or {}).get('vs_4_13') or {}).get('min_k', 0)))}}}",
            f"\\newcommand{{\\BenchPThreeFpTipFullPct}}{{{float(((mk_b.get('p3_fp_tipping') or {}).get('vs_4_13') or {}).get('pct', 0.0)):.1f}\\%}}",
            f"\\newcommand{{\\BenchPThreeFpTipFullP}}{{{_tex_p(float(((mk_b.get('p3_fp_tipping') or {}).get('vs_4_13') or {}).get('fisher_p', 1.0)))}}}",
        ])

        # Structured Table Macros
        # Table 2 rows: 7 columns (Test separated from aligned Finite p; denominators inside Estimate)
        s12_cl = s12["cluster_rates"]["S1_desk_stop"]
        s12_cl_str = f"{_tex_int(s12_cl['count'])}/{_tex_int(s12_cl['total'])} ({_pct_str(s12_cl)})" if s12_cl.get("count") is not None else "n/a"
        held_conf_cl_n = max(0, conf_cl_n - int(s13["confirmatory_clusters_past_s0"]))
        env_sa4_str = f"{env_sa4_lo:.1f}--{env_sa4_hi:.1f}\\%"
        s13_p_vals = [float(s[7]) for s in app_scenarios if s[7] is not None]
        s13_p_lo = min(s13_p_vals) if s13_p_vals else float(s13_p if s13_p is not None else 1.0)
        s13_p_hi = max(s13_p_vals) if s13_p_vals else float(s13_p if s13_p is not None else 1.0)
        s13_tog_note = f"toggles {s13_p_lo:.3f}--{s13_p_hi:.3f}" if app_scenarios else "exact sign"
        sa9_p3_note = f"boot.; P3 {sa9_p3_ci_str}" if sa9_p3_ci else ("boot." if sa9_p3.get("equal_cluster_pct") is None else f"P3 {sa9_p3['equal_cluster_pct']:.1f}\\%")
        t2_rows = [
            f"\\textbf{{P1}}\\,$^{{\\ddagger}}$ & Execution yield (conf.\\ reps) & {_tex_int(p1_r['count'])}/{_tex_int(p1_r['total'])} ({_pct_str(p1_r)}) & {_ci_num(p1_r)} & Holm & {_p_na(fin_holm.get('P1'), prefix='')} & 1-S {_p_na(prim['P1']['p_holm'], prefix='')} \\\\",
            f"\\textbf{{P2}} & Desk stop $-$ execution & {_tex_s1(p2_delta)}~pp ({_tex_int(conf_cl_n)} cl.) & {_boot_br(p2_ci)} & Holm & {_p_na(fin_holm.get('P2'), prefix='')} & exact sign; hold+WF \\\\",
            f"\\quad $\\hookrightarrow$ & Unrateable holds share & {_tex_s1(p2_dec['unrateable_holds_pp'])}~pp ({p2_dec['holds_share_pct']:.1f}\\%) & --- & --- & --- & --- \\\\",
            f"\\quad $\\hookrightarrow$ & Rateable Contest contrib. & {_tex_s1(p2_dec['rateable_contrib_pp'])}~pp ({max(0.0, 100.0 - float(p2_dec['holds_share_pct'])):.1f}\\%) & --- & --- & --- & --- \\\\",
            f"\\textbf{{P3}} & All-stream alerts / fits & {_tex_int(p3_r['count'])}/{_tex_int(p3_r['total'])} ({_pct_str(p3_r)}) & {_ci_num(p3_r)} & Holm & {_p_na(fin_holm.get('P3'), prefix='')} & 1-S {_p_na(prim['P3']['p_holm'], prefix='')} \\\\",
            r"\midrule",
            f"\\textbf{{SA1}} & Desk stops (conf.\\ reps) & {_tex_int(sa1_r['count'])}/{_tex_int(sa1_r['total'])} ({_pct_str(sa1_r)}) & {_ci_num(sa1_r)} & Fisher\\,$^\\dagger$ & {_p_na(fish.get('S1', 1.0), prefix='')} & 1-S {_p_na(sa1_r.get('nominal_p_vs_103_147'), prefix='')} \\\\",
            f"\\textbf{{SA2}} & Alerts / post-S0 conf.\\ reps & {_tex_int(sa2_r['count'])}/{_tex_int(sa2_r['total'])} ({_pct_str(sa2_r)}) & {_ci_num(sa2_r)} & Fisher\\,$^\\dagger$ & {_p_na(fish.get('S2', 1.0), prefix='')} & 1-S {_p_na(sa2_r.get('nominal_p_vs_4_147'), prefix='')} \\\\",
            f"\\textbf{{SA3}}\\,$^{{\\ddagger}}$ & S2 preprocessing stops & {_tex_int(sa3_r['count'])}/{_tex_int(sa3_r['total'])} ({_pct_str(sa3_r)}) & {_ci_num(sa3_r)} & --- & --- & x-frame ({_tex_int(orig_comp_n)}/{_tex_int(sa14_r['total'])} comp.) \\\\",
            f"\\textbf{{SA4}} & Oracle / UBSan failures & {_tex_int(sa4_r['count'])}/{_tex_int(sa4_r['total'])} ({_pct_str(sa4_r)}) & {_ci_num(sa4_r)} & Fisher\\,$^\\dagger$ & {_p_na(fish.get('S4', 1.0), prefix='')} & env.\\ {env_sa4_str} \\\\",
            f"\\textbf{{SA5}} & Alert $-$ no-alert (vs.\\ 50\\%) & {_tex_s1(float(sa5_c.get('group_weighted_delta_pp') or 0.0))}~pp ({_tex_int(n_fit)} fits) & {_boot_br(sa5_c.get('bootstrap_95pct_delta_pp'))} & Sign & {_p_na(sa5_c.get('nominal_p'), prefix='')} & vs.\\ $-33.3$~pp pilot \\\\",
            f"\\textbf{{SA6}} & P1 excl.\\ infra stops & {_tex_int(sa6_r['count'])}/{_tex_int(sa6_r['total'])} ({_pct_str(sa6_r)}) & {_ci_num(sa6_r)} & --- & --- & 2 infra excl. \\\\",
            f"\\textbf{{SA7}} & Any-stream alerts / fits & {_tex_int(sa7_r.get('count') or 0)}/{_tex_int(n_fit)} ({_pct_str(sa7_r)}) & {_ci_num(sa7_r)} & --- & --- & any-stream \\\\",
            f"\\textbf{{SA8}} & Drop-largest all-stream & {_tex_int(sa8_al_r.get('count') or 0)}/{_tex_int(sa8_adm_n)} ({_pct_str(sa8_al_r)}) & {_ci_num(sa8_al_r)} & --- & --- & 1 range-lim. \\\\",
            f"\\textbf{{SA9}} & Equal-cluster P1 (all pairs) & {sa9_p1['equal_cluster_pct']:.1f}\\% ({_tex_int(sa9_p1['clusters'])} cl.) & [{sa9_p1['bootstrap_95pct_pct'][0]:.1f}, {sa9_p1['bootstrap_95pct_pct'][1]:.1f}]\\% & --- & --- & {sa9_p3_note} \\\\",
            f"\\textbf{{SA10}} & Contest P1 (within-Contest) & {_tex_int(s10_contest['count'])}/{_tex_int(s10_contest['total'])} ({_pct_str(s10_contest)}) & {_ci_num(s10_contest)} & --- & --- & {_tex_int(s10['Repository']['clusters_past_s0'])} Repo held at S1 \\\\",
            f"\\textbf{{SA12}} & Quarantined S1 stops (cl.) & {s12_cl_str} & {_ci_num(s12_cl)} & --- & --- & {_pct_str(q_s1_r)} pairs; {_tex_int(s12['pair_dispositions'].get('not_executed', 0))} unrun \\\\",
            f"\\textbf{{SA13a}} & Rateable Contest P1 & {_tex_int(s13_p1['count'])}/{_tex_int(s13_p1['total'])} ({_pct_str(s13_p1)}) & {_ci_num(s13_p1)} & --- & --- & excl.\\ {_tex_int(held_conf_cl_n)} holds \\\\",
            f"\\textbf{{SA13b}} & Rateable Contest P2 & {_tex_s1(s13_d)}~pp ({_tex_int(s13['confirmatory_clusters_past_s0'])} cl.) & {_boot_br(s13_p2c.get('bootstrap_95pct_delta_pp'))} & Sign & {_p_na(s13_p, prefix='')} & {s13_tog_note} \\\\",
            f"\\textbf{{SA14}} & Pre-S3 fixture stops & {_tex_int(sa14_r['count'])}/{_tex_int(sa14_r['total'])} ({_pct_str(sa14_r)}) & {_ci_num(sa14_r)} & --- & --- & cond.\\ {_pct_str(cond_exec_r)} \\\\",
        ]
        lines.append("\\newcommand{\\BenchTableTwoRows}{" + " ".join(t2_rows) + "}")

        # Table 4 rows: 6-alert forensics separating logical-counter core (Log.) from >=1.5x plain CPU (CPU)
        if forensics is not None:
            alert_rows = []
            per_pos = six_d.get("per_position") or {}
            for item in forensics["six_alerts"]:
                pos = int(item["position"])
                src = item["source"]
                dt = int(item["distinct_c0_trajectories"])
                s0 = item["streams"][0]
                n_lo, n_hi = int(s0["sizes"][0]), int(s0["sizes"][-1])
                c0_slopes = [float(s["primary_c0"]["slope"]) for s in item["streams"]]
                c0_ratios = [float(s["primary_c0"]["largest_ratio"]) for s in item["streams"]]
                tot_slopes = [float(s["total_ticks_c0_plus_c1"]["slope"]) for s in item["streams"]]
                tot_ratios = [float(s["total_ticks_c0_plus_c1"]["largest_ratio"]) for s in item["streams"]]
                cpu_ratios = [float(s["cpu_usage_usec"]["plain"]["largest_ratio"]) for s in item["streams"] if s["cpu_usage_usec"]["plain"]["largest_ratio"] is not None]
                diag_p = per_pos.get(str(pos)) or {}
                c0_min_ci = float(diag_p.get("c0_min_ci_lo", 0.0))
                ts_min = float(diag_p.get("c0_min_ts", 0.0))
                dl_verd = "Retain" if item["drop_largest_case_verdict"] == "retained_alert" else "Flip"
                log_mark = r"\checkmark" if diag_p.get("robust_4check_pass") else r"$\times$"
                cpu_mark = r"\checkmark" if (cpu_ratios and min(cpu_ratios) >= 1.50) else r"$\times$"
                ci_txt = f"$-{abs(c0_min_ci):.2f}$" if c0_min_ci < 0 else f"{c0_min_ci:.2f}"
                alert_rows.append(
                    f"{_tex_int(pos)} ({src}) & {_tex_int(n_lo)}--{_tex_int(n_hi)} ({dt}/3) & "
                    f"{_fmt_range(c0_slopes, 2)} & {ci_txt}/{ts_min:.2f} & {_fmt_ratio_range(c0_ratios)} & "
                    f"{_fmt_range(tot_slopes, 2)} & {_fmt_ratio_range(tot_ratios)} & {dl_verd} & {_fmt_ratio_range(cpu_ratios)} & {log_mark} & {cpu_mark} \\\\"
                )
            lines.append("\\newcommand{\\BenchAlertForensicsRows}{" + " ".join(alert_rows) + "}")
        else:
            lines.append(
                f"\\newcommand{{\\BenchAlertForensicsRows}}{{1--{_tex_int(max(1, int(p3_r['count'])))} & 4--6 sizes & $\\ge 0.50$ & $>0.50$ / $\\ge 0.50$ & $\\ge 1.50\\times$ & $\\ge 0.50$ & $\\ge 1.50\\times$ & Retain & $\\ge 1.0\\times$ & \\checkmark & \\checkmark \\\\}}"
            )

        # Table 5 rows: Stratified S1 Blind Author Check matching prose precision (3 decimals)
        if irr_s:
            def _ci3(lo: float, hi: float) -> str:
                s_lo = f"$-{abs(lo):.3f}$" if lo < 0 else f"{lo:.3f}"
                s_hi = f"$-{abs(hi):.3f}$" if hi < 0 else f"{hi:.3f}"
                return f"[{s_lo}, {s_hi}]"

            t4_rows = [
                (
                    f"Overall ({_tex_int(n_cl_tot)} cl.) & {_tex_int(ov_i['n'])} & {ov_i['bucket_agree_pct']:.1f}\\% ({_tex_k3(bk_a['cohens_kappa'])}; {_ci3(bk_ci_l[0], bk_ci_l[1])}) & "
                    f"{ov_i['binary_agree_pct']:.1f}\\% ({_tex_k3(ov_i['binary_kappa'])}) & {_tex_k3(ov_i['binary_pabak'])} & "
                    f"{_tex_k3(ov_i['binary_gwet_ac1'])} & {ov_bm[0][0]}/{ov_bm[0][1]}/{ov_bm[1][0]}/{ov_bm[1][1]} & "
                    f"{_tex_int(ov_i['contract_to_author_pass_count'])}/{_tex_int(ov_i['contract_total'])} & ({_tex_p(ov_i['binary_mcnemar_p'], prefix='')})\\,$^\\dagger$ \\\\"
                ),
                (
                    f"Conf.\\ (sing.) & {_tex_int(cf_i['n'])} & {cf_i['bucket_agree_pct']:.1f}\\% ({_tex_k3(cf_i['bucket_kappa'])}; {_ci3(cf_bk_ci[0], cf_bk_ci[1])}) & "
                    f"{cf_i['binary_agree_pct']:.1f}\\% ({_tex_k3(cf_i['binary_kappa'])}) & {_tex_k3(cf_i['binary_pabak'])} & "
                    f"{_tex_k3(cf_i['binary_gwet_ac1'])} & {cf_bm[0][0]}/{cf_bm[0][1]}/{cf_bm[1][0]}/{cf_bm[1][1]} & "
                    f"{_tex_int(cf_i['contract_to_author_pass_count'])}/{_tex_int(cf_i['contract_total'])} & {_tex_p(cf_i['binary_mcnemar_p'], prefix='')}\\phantom{{$\\,^\\dagger$}} \\\\"
                ),
                (
                    f"Quar.\\ ({_tex_int(n_cl_quar)} cl.) & {_tex_int(qr_i['n'])} & {qr_i['bucket_agree_pct']:.1f}\\% ({_tex_k3(qr_i['bucket_kappa'])}; ---) & "
                    f"{qr_i['binary_agree_pct']:.1f}\\% ({_tex_k3(qr_i['binary_kappa'])}) & {_tex_k3(qr_i['binary_pabak'])} & "
                    f"{_tex_k3(qr_i['binary_gwet_ac1'])} & {qr_bm[0][0]}/{qr_bm[0][1]}/{qr_bm[1][0]}/{qr_bm[1][1]} & "
                    f"{_tex_int(qr_c2p)}/{_tex_int(qr_ctot)} & ({_tex_p(qr_i['binary_mcnemar_p'], prefix='')})\\,$^\\dagger$ \\\\"
                ),
            ]
            lines.append("\\newcommand{\\BenchTableFourRows}{" + " ".join(t4_rows) + "}")
        else:
            lines.append(
                r"\newcommand{\BenchTableFourRows}{Overall & 50 & --- & --- & --- & --- & --- & --- & --- \\}"
            )

        # Corpus split rows (Confirmatory Contest PIE-train vs CodeNet + Repository + Total, 13 columns incl. Infra)
        cs = (forensics or {}).get("confirmatory_corpus_split") or {}
        if cs:
            c_rows = []
            tot_c = Counter()
            for cname, lbl in (("pie-train", "PIE-train (Contest)"), ("codenet", "CodeNet (Contest)"), ("github-performance-fix", "GitHub (Repository)")):
                d = cs.get(cname) or {}
                s1_p_n = int(d.get("s1_pass", 0))
                fx_n = int(d.get("fixture_stop", 0))
                ex_n = int(d.get("executed", 0))
                inf_n = max(0, s1_p_n - fx_n - ex_n)
                or_n = int(d.get("oracle_failure", 0))
                ft_n = int(d.get("fitted", 0))
                nf_n = max(0, ex_n - or_n - ft_n)
                vals = {
                    "drawn": int(d.get("drawn", 0)),
                    "s0_pass": int(d.get("s0_pass", 0)),
                    "held": int(d.get("s1_unrateable", 0)),
                    "rated_stop": int(d.get("s1_stop", 0)) - int(d.get("s1_unrateable", 0)),
                    "s1_pass": s1_p_n,
                    "fix_stop": fx_n,
                    "infra": inf_n,
                    "executed": ex_n,
                    "oracle": or_n,
                    "no_fit": nf_n,
                    "fitted": ft_n,
                    "alert": int(d.get("alert", 0)),
                }
                for k, v in vals.items():
                    tot_c[k] += v
                c_rows.append(
                    f"{lbl} & {_tex_int(vals['drawn'])} & {_tex_int(vals['s0_pass'])} & "
                    f"{_tex_int(vals['held'])} & {_tex_int(vals['rated_stop'])} & "
                    f"{_tex_int(vals['s1_pass'])} & {_tex_int(vals['fix_stop'])} & {_tex_int(vals['infra'])} & "
                    f"{_tex_int(vals['executed'])} & {_tex_int(vals['oracle'])} & "
                    f"{_tex_int(vals['no_fit'])} & {_tex_int(vals['fitted'])} & {_tex_int(vals['alert'])} \\\\"
                )
            c_rows.append(
                r"\midrule "
                f"\\textbf{{Total}} & {_tex_int(tot_c['drawn'])} & {_tex_int(tot_c['s0_pass'])} & "
                f"{_tex_int(tot_c['held'])} & {_tex_int(tot_c['rated_stop'])} & "
                f"{_tex_int(tot_c['s1_pass'])} & {_tex_int(tot_c['fix_stop'])} & {_tex_int(tot_c['infra'])} & "
                f"{_tex_int(tot_c['executed'])} & {_tex_int(tot_c['oracle'])} & "
                f"{_tex_int(tot_c['no_fit'])} & {_tex_int(tot_c['fitted'])} & {_tex_int(tot_c['alert'])} \\\\"
            )
            lines.append("\\newcommand{\\BenchTableCorpusRows}{" + " ".join(c_rows) + "}")
        else:
            lines.append(
                r"\newcommand{\BenchTableCorpusRows}{Contest + Repository & \BenchPairs & \BenchSOPassN & --- & --- & --- & --- & --- & --- & --- & --- & --- & --- \\}"
            )

        # Appendix Table A1 rows: 100% dynamically derived from scenario tuple list
        if app_scenarios:
            app_rows = [
                f"{lbl} & {_pct_str(p1s)} & {_tex_s1(p2s['delta'])}~pp & {_tex_s1(s13d)}~pp ({_tex_p(s13p, prefix='')}) & {_pct_str(p3s)} & {_pct_str(s4s)} & {_pct_str(s14s)} \\\\"
                for lbl, p1s, p2s, s13d, p3s, s4s, s14s, s13p in app_scenarios
            ]
            lines.append("\\newcommand{\\BenchTableAppRows}{" + " ".join(app_rows) + "}")
        else:
            lines.append(
                f"\\newcommand{{\\BenchTableAppRows}}{{Primary baseline & {_pct_str(p1_r)} & {_tex_s1(p2_delta)}~pp & {_tex_s1(s13_d)}~pp & {_pct_str(p3_r)} & {_pct_str(sa4_r)} & {_pct_str(sa14_r)} \\\\}}"
            )
    else:
        for slot_macro, label in (
            ("BenchFittedClusters", "fitted clusters"),
            ("BenchExecRate", "P1 execution yield"),
            ("BenchDeskContrast", "P2 contrast"),
            ("BenchPOneCount", "P1 count"),
            ("BenchPOnePct", "P1 pct"),
            ("BenchPOneCI", "P1 CI"),
            ("BenchPOneHolmP", "P1 Holm p"),
            ("BenchPOneFisherP", "P1 Fisher p"),
            ("BenchPTwoDelta", "P2 delta"),
            ("BenchPTwoHolmP", "P2 Holm p"),
            ("BenchPTwoHoldsPP", "P2 holds pp"),
            ("BenchPTwoHoldsShare", "P2 holds share"),
            ("BenchPTwoRateableContribPP", "P2 rateable contrib"),
            ("BenchPThreeCount", "P3 count"),
            ("BenchPThreePct", "P3 pct"),
            ("BenchPThreeCI", "P3 CI"),
            ("BenchPThreeHolmP", "P3 Holm p"),
            ("BenchPThreeFisherP", "P3 Fisher p"),
            ("BenchSAFiveSignP", "SA5 sign p"),
            ("BenchSATwoPct", "SA2 pct"),
            ("BenchSATwoCI", "SA2 CI"),
            ("BenchSATwoFisherP", "SA2 Fisher p"),
            ("BenchRateableClustersN", "rateable clusters"),
            ("BenchRateableExecPct", "rateable exec pct"),
            ("BenchRateableExecCI", "rateable exec CI"),
            ("BenchRateableDeskPct", "rateable desk pct"),
            ("BenchSAThirteenDelta", "SA13 delta"),
            ("BenchSAThirteenBootCI", "SA13 boot CI"),
            ("BenchSAThirteenP", "SA13 p"),
            ("BenchConfSTwoPassN", "conf S1 pass"),
            ("BenchRatedDeskStopRepsN", "rated stops"),
            ("BenchTotalDeskStopRepsN", "total desk stops"),
            ("BenchConfContractStopRepsN", "contract stops"),
            ("BenchConfSourceStopRepsN", "source stops"),
            ("BenchConfRouteStopRepsN", "route stops"),
            ("BenchConfIndetRepsN", "indet stops"),
            ("BenchFixtureStopN", "fixture stops"),
            ("BenchFixtureStopPct", "fixture stop pct"),
            ("BenchFixtureStopCI", "fixture stop CI"),
            ("BenchCondExecPct", "cond exec pct"),
            ("BenchOrigCompileFailN", "orig compile fail"),
            ("BenchOrigCompileFailPct", "orig compile fail pct"),
            ("BenchOrigCompileFailCI", "orig compile fail CI"),
            ("BenchRunnerSOnePassN", "runner S1 pass"),
            ("BenchRunnerPreFixtureN", "pre-runner fixture stop"),
            ("BenchRunnerOverlayFixtureN", "overlay fixture stop"),
            ("BenchOracleFailN", "oracle fail"),
            ("BenchOracleFailPct", "oracle fail pct"),
            ("BenchOracleFailCI", "oracle fail CI"),
            ("BenchNoFitN", "no fit"),
            ("BenchNoAlertN", "no alert"),
            ("BenchInfraFailN", "infra fail"),
            ("BenchQuarUnrunN", "quar unrun"),
            ("BenchPinLedger", "ledger pin"),
            ("BenchPinRepPlan", "rep plan pin"),
            ("BenchConfContestDrawn", "conf contest drawn"),
            ("BenchConfContestIntake", "conf contest S0"),
            ("BenchQuarIntakeN", "quar S0"),
            ("BenchQuarPostSOneZeroN", "quar post-S1 zero"),
            ("BenchConfContestDesk", "conf contest S1"),
            ("BenchConfContestFix", "conf contest fix"),
            ("BenchConfContestPrep", "conf contest prep"),
            ("BenchConfContestInfra", "conf contest infra"),
            ("BenchConfContestUnrun", "conf contest unrun"),
            ("BenchConfContestOracle", "conf contest oracle"),
            ("BenchConfContestNoFit", "conf contest nofit"),
            ("BenchConfContestNoAlert", "conf contest noalert"),
            ("BenchConfContestAlert", "conf contest alert"),
            ("BenchQuarContestDesk", "quar contest S1"),
            ("BenchBwrapOverheadMs", "container spawn floor ms"),
            ("BenchWaveOneOverrideN", "stderr override N"),
            ("BenchPinWaveTwoCap", "pre-patch runner pin"),
            ("BenchPosNineFourPlainUpperNs", "pos 94 plain ns upper"),
            ("BenchPosTwoNine", "pos 29"),
            ("BenchPosNineZeroOZeroOnlyPts", "pos 90 O0-only pts"),
            ("BenchPosNineSevenOtwoStreamsN", "pos 97 O2 streams"),
            ("BenchPosNineSevenPlainStreamsN", "pos 97 plain streams"),
            ("BenchPosThirteenPlainStreamsFrac", "pos 13 plain streams"),
            ("BenchPosThirteenOtwoStreamsFrac", "pos 13 O2 streams"),
            ("BenchPosOneSevenFivePlainStreamsFrac", "pos 175 plain streams"),
            ("BenchPosOneSevenFiveOtwoStreamsFrac", "pos 175 O2 streams"),
            ("BenchPosOneSixFourPlainStreamsFrac", "pos 164 plain streams"),
            ("BenchPosOneSixFourOtwoStreamsFrac", "pos 164 O2 streams"),
            ("BenchPosNineFourPlainStreamsFrac", "pos 94 plain streams"),
            ("BenchPosNineFourOtwoStreamsFrac", "pos 94 O2 streams"),
            ("BenchPosNineSevenPlainStreamsFrac", "pos 97 plain streams"),
            ("BenchMaxCounterVal", "max parsed counter"),
            ("BenchUnconfRestoredOracleN", "unconf restored oracle N"),
            ("BenchFittedMaskedFailN", "fitted masked fail N"),
            ("BenchPosOneSixFourTotSlopeTwoDec", "pos 164 tot slope 2dec"),
            ("BenchPosThreeWorstTS", "pos 3 worst TS"),
            ("BenchAllPtMaxBoundFailN", "all-pt R0>max(T0,Q0) N"),
            ("BenchMinRefPlainCoreN", "min-ref plain core N"),
            ("BenchMinRefOtwoCoreN", "min-ref O2 core N"),
            ("BenchMedRefPlainCoreN", "med-ref plain core N"),
            ("BenchMedRefOtwoCoreN", "med-ref O2 core N"),
            ("BenchAddCpuOneThreeSlopeRange", "pos 13 add CPU slope"),
            ("BenchAddCpuOneSevenFiveSlopeRange", "pos 175 add CPU slope"),
            ("BenchAddCpuOneSixFourSlopeRange", "pos 164 add CPU slope"),
            ("BenchAddCpuNineFourSlopeRange", "pos 94 add CPU slope"),
            ("BenchAddCpuNineSevenSlopeRange", "pos 97 add CPU slope"),
            ("BenchOtwoMinusPlainSZeroMs", "O2-plain s0 diff ms"),
            ("BenchRestNonExSATwoN", "non-exact SA7 rest N"),
            ("BenchRestNonExSubN", "non-exact sub-0.50 rest N"),
            ("BenchRestNonExFlatN", "non-exact flat rest N"),
            ("BenchRestNonExNegN", "non-exact neg rest N"),
            ("BenchRestNonExMixN", "non-exact mix rest N"),
            ("BenchAllPtExcessFailN", "all-pt excess fail N"),
            ("BenchAllPtRoneInflN", "all-pt c1 infl N"),
            ("BenchAllPtNonRegFailN", "all-pt non-reg R0>T0 N"),
            ("BenchPosEighteen", "pos 18"),
            ("BenchPosFourFour", "pos 44"),
            ("BenchPOnePilotNeffTipN", "P1 n_eff tipping N"),
            ("BenchSAThreeCrossFrameP", "SA3 cross-frame Fisher p"),
            ("BenchOraclePlainUpstreamN", "plain upstream oracle fails"),
            ("BenchOracleUBAllN", "ubsan total oracle fails"),
            ("BenchOraclePlainSegvUBN", "plain SIGSEGV + ubsan fail"),
            ("BenchOZeroAgree", "O0 agree"),
            ("BenchOZeroMiss", "O0 miss"),
            ("BenchOZeroTotalTriples", "O0 total triples"),
            ("BenchOZeroCapped", "O0 capped"),
            ("BenchOZeroOracleAbort", "O0 oracle abort"),
            ("BenchOZeroOverlayFix", "O0 overlay fix"),
            ("BenchOZeroInfraMiss", "O0 infra miss"),
            ("BenchOZeroCapOtwoAgree", "O2==O3 on O0-capped"),
            ("BenchShamAgree", "sham agree"),
            ("BenchShamMiss", "sham miss"),
            ("BenchShamTotalPairs", "sham total pairs"),
            ("BenchShamCapped", "sham capped"),
            ("BenchShamOracleAbort", "sham oracle abort"),
            ("BenchShamOverlayFix", "sham overlay fix"),
            ("BenchShamInfraMiss", "sham infra miss"),
            ("BenchCpuCapEvents", "cpu cap events"),
            ("BenchCpuCapPos", "cpu cap pos"),
            ("BenchTickCapEvents", "tick cap events"),
            ("BenchTickCapPos", "tick cap pos"),
            ("BenchCpuCapOZeroOnlyPts", "cpu cap O0-only pts"),
            ("BenchCpuCapTotalPts", "cpu cap total pts"),
            ("BenchOracleUpstreamN", "upstream oracle fails"),
            ("BenchOracleUpstreamPct", "upstream oracle pct"),
            ("BenchOracleUpstreamCI", "upstream oracle CI"),
            ("BenchOracleUpstreamTgtN", "upstream oracle target"),
            ("BenchOracleUpstreamRefN", "upstream oracle ref"),
            ("BenchOraclePlainN", "plain oracle fails"),
            ("BenchOraclePlainTgtN", "plain oracle target"),
            ("BenchOraclePlainRefN", "plain oracle ref"),
            ("BenchOracleUBSanOnlyN", "ubsan oracle fails"),
            ("BenchOracleUBTgtN", "ubsan oracle target"),
            ("BenchOracleUBRefN", "ubsan oracle ref"),
            ("BenchOracleRestoredN", "restored oracle fails"),
            ("BenchOracleShamN", "sham oracle fails"),
            ("BenchOracleMultiEvtN", "multi-event oracle fails"),
            ("BenchOracleCoordN", "audited oracle overrides"),
            ("BenchOracleCoordPct", "audited oracle override pct"),
            ("BenchFitQZeroN", "Q==0 insufficient"),
            ("BenchFitBothZeroN", "both-zero insufficient"),
            ("BenchFitTickCapN", "tick-cap insufficient"),
            ("BenchCensorCondN", "censor cond num"),
            ("BenchCensorDenom", "censor denom"),
            ("BenchCensorCondPct", "censor cond pct"),
            ("BenchCensorCondCI", "censor cond CI"),
            ("BenchCensorWorstN", "censor worst num"),
            ("BenchCensorWorstPct", "censor worst pct"),
            ("BenchCensorWorstCI", "censor worst CI"),
            ("BenchCensorWorstFisherP", "censor worst Fisher p"),
            ("BenchCensorWorstFisherFourTwelveP", "censor worst Fisher 4/12 p"),
            ("BenchCensorWorstFisherConservP", "censor worst Fisher 3/12 p"),
            ("BenchCensorCpuCapExclFlatN", "censor+cpucap excl flat count"),
            ("BenchCensorCpuCapExclFlatPct", "censor+cpucap excl flat pct"),
            ("BenchCensorCpuCapExclFlatP", "censor+cpucap excl flat p"),
            ("BenchCensorCpuCapExclFlatConservP", "censor+cpucap excl flat 3/12 p"),
            ("BenchCensorCpuCapTotalN", "censor+cpucap count"),
            ("BenchCensorCpuCapPct", "censor+cpucap pct"),
            ("BenchCensorCpuCapFourTwelveP", "censor+cpucap 4/12 p"),
            ("BenchCensorCpuCapConservP", "censor+cpucap 3/12 p"),
            ("BenchJointConservHolmPOne", "joint conservative P1 Holm p"),
            ("BenchJointConservHolmPThree", "joint conservative P3 Holm p"),
            ("BenchDistinctThreeN", "3 distinct"),
            ("BenchDistinctThreePct", "3 distinct pct"),
            ("BenchDistinctTwoN", "2 distinct"),
            ("BenchDistinctTwoPct", "2 distinct pct"),
            ("BenchDistinctOneN", "1 distinct"),
            ("BenchDistinctOnePct", "1 distinct pct"),
            ("BenchDistinctOneCOneVarN", "1 distinct c1-varying"),
            ("BenchDistinctOneOblivN", "1 distinct oblivious"),
            ("BenchZeroVarStreamsN", "zero-var streams"),
            ("BenchDefinedRTwoStreamsN", "defined R2 streams"),
            ("BenchTotalFittedStreamsN", "total fitted streams"),
            ("BenchAllStreamsMedianRTwo", "median R2"),
            ("BenchAlertMedianRTwo", "alert median R2"),
            ("BenchZeroVarPairsN", "zero-var pairs"),
            ("BenchDefinedRTwoPairsN", "defined R2 pairs"),
            ("BenchPairMedianRTwo", "pair worst-stream median R2"),
            ("BenchAlertPairMedianRTwo", "alert pair worst-stream median R2"),
            ("BenchConstZeroVarPairsN", "constant-factor zero-var pairs"),
            ("BenchPThreePilotClustFisherP", "P3 12-cluster pilot Fisher p"),
            ("BenchPThreePilotClustConservP", "P3 conservative 3/12 cluster Fisher p"),
            ("BenchPOnePilotNeffThirtyP", "P1 n_eff=30 Fisher p"),
            ("BenchPOnePilotNeffFiftyP", "P1 n_eff=50 Fisher p"),
            ("BenchSAOnePilotNeffRangeP", "SA1 n_eff range Fisher p"),
            ("BenchSAThreeInclCompileN", "SA3 original compile failures"),
            ("BenchSAThreeInclCompilePct", "SA3 incl compile pct"),
            ("BenchSAThreeInclCompileP", "SA3 incl compile Fisher p"),
            ("BenchCensorCpuCapFisherP", "censoring+cpucap Fisher p"),
            ("BenchRestCOneMaskN", "c0 fail to total pass mask count"),
            ("BenchSANinePThreeCI", "SA9 P3 bootstrap CI"),
            ("BenchOZeroRelaxCapPtsN", "O0-only cpu_cap pts"),
            ("BenchOZeroRelaxPairsN", "O0-only cpu_cap pairs"),
            ("BenchOZeroRelaxDeltaN", "O0 relaxation verdict deltas"),
            ("BenchRealizedCpuCoreN", "realized CPU core count"),
            ("BenchPlainSubCoreN", "plain spawn-sub core count"),
            ("BenchOtwoSubCoreN", "O2 spawn-sub core count"),
            ("BenchFDWrapOverheadMs", "FD wrapper overhead ms"),
            ("BenchPosOneSixFourCpuRatio", "pos 164 plain CPU ratio"),
            ("BenchSubCpuOneSevenFiveSlopeRange", "pos 175 sub CPU slope"),
            ("BenchSubCpuOneThreeSlopeRange", "pos 13 sub CPU slope"),
            ("BenchPosThirteenPlainZeroSubRange", "pos 13 plain zero-sub slope"),
            ("BenchPosThirteenOtwoSubSlopeRange", "pos 13 O2 sub slope"),
            ("BenchPosOneSevenFiveOtwoSubSlopeRange", "pos 175 O2 sub slope"),
            ("BenchPosThirteenPlainDeltaMsRange", "pos 13 plain delta ms"),
            ("BenchPosOneSevenFivePlainDeltaMsRange", "pos 175 plain delta ms"),
            ("BenchSubCpuOneSixFourSlopeRange", "pos 164 sub CPU slope"),
            ("BenchSubCpuNineFourSlopeRange", "pos 94 sub CPU slope"),
            ("BenchSubCpuNineSevenSlopeRange", "pos 97 sub CPU slope"),
            ("BenchSASevenCount", "SA7 count"),
            ("BenchSASevenPct", "SA7 pct"),
            ("BenchSASevenCI", "SA7 CI"),
            ("BenchSASevenOnlyN", "SA7-only count"),
            ("BenchSAEightAdmittedN", "SA8 admitted"),
            ("BenchSAEightAlertsN", "SA8 alerts"),
            ("BenchSAEightPct", "SA8 pct"),
            ("BenchSAEightCI", "SA8 CI"),
            ("BenchSAEightAnyAlertsN", "SA8 any alerts"),
            ("BenchSAEightAnyPct", "SA8 any pct"),
            ("BenchSAEightAnyCI", "SA8 any CI"),
            ("BenchCoreFourN", "core 4 count"),
            ("BenchCoreFourPct", "core 4 pct"),
            ("BenchCoreFourCI", "core 4 CI"),
            ("BenchCoreMinCILo", "core min CI lower"),
            ("BenchBOneAlertsN", "B1 count"),
            ("BenchBOnePct", "B1 pct"),
            ("BenchBOneCI", "B1 CI"),
            ("BenchBOneFPN", "B1 FP"),
            ("BenchBOneFlatN", "B1 flat"),
            ("BenchBOneSubN", "B1 sub"),
            ("BenchBOneNegN", "B1 neg"),
            ("BenchBOneSelN", "B1 sel"),
            ("BenchBOneMcNemarP", "B1 McNemar p"),
            ("BenchBOneHolmP", "B1 Holm p"),
            ("BenchBTwoAlertsN", "B2 count"),
            ("BenchBTwoPct", "B2 pct"),
            ("BenchBTwoCI", "B2 CI"),
            ("BenchBThreeAlertsN", "B3 count"),
            ("BenchBThreePct", "B3 pct"),
            ("BenchBThreeCI", "B3 CI"),
            ("BenchBThreeAllExecN", "B3 all exec count"),
            ("BenchBThreeAllExecDenom", "B3 all exec denom"),
            ("BenchBThreeAllExecPct", "B3 all exec pct"),
            ("BenchBFourAlertsN", "B4 count"),
            ("BenchBFourPct", "B4 pct"),
            ("BenchBFourCI", "B4 CI"),
            ("BenchBFourMcNemarP", "B4 McNemar p"),
            ("BenchBFourHolmP", "B4 Holm p"),
            ("BenchBFiveAlertsN", "B5 count"),
            ("BenchBFivePct", "B5 pct"),
            ("BenchBFiveCI", "B5 CI"),
            ("BenchBFiveTPN", "B5 TP"),
            ("BenchBFiveFPN", "B5 FP"),
            ("BenchBFiveMcNemarP", "B5 McNemar p"),
            ("BenchBFiveHolmP", "B5 Holm p"),
            ("BenchBFiveCoreTPN", "B5 core TP"),
            ("BenchBFiveCorePrecPct", "B5 core precision"),
            ("BenchBFiveCoreRecPct", "B5 core recall"),
            ("BenchRestPassAllN", "rest pass all"),
            ("BenchRestNoExAllN", "rest no excess all"),
            ("BenchRestFailAllN", "rest fail all"),
            ("BenchRestUnmeasAllN", "rest unmeas all"),
            ("BenchRestExecPassN", "rest pass exec"),
            ("BenchRestExecNoExN", "rest no excess exec"),
            ("BenchRestExecFailN", "rest fail exec"),
            ("BenchRestExecUnmeasN", "rest unmeas exec"),
            ("BenchRestFitPassN", "rest fit pass"),
            ("BenchRestFitNoExN", "rest fit no excess"),
            ("BenchRestFitFailN", "rest fit fail"),
            ("BenchRestFitExcessN", "rest fit excess"),
            ("BenchRestFitFailPct", "rest fit fail pct"),
            ("BenchRestFitFailCI", "rest fit fail CI"),
            ("BenchRestExactCopyN", "rest exact copy"),
            ("BenchRestExactCopyPct", "rest exact copy pct"),
            ("BenchRestNonExactPassN", "rest non-exact pass"),
            ("BenchRestSurgicalN", "rest surgical"),
            ("BenchRestMildOverN", "rest mild over"),
            ("BenchRestHighOverN", "rest high over"),
            ("BenchRestTotPassN", "tot rest pass"),
            ("BenchRestTotNoExN", "tot rest no excess"),
            ("BenchRestTotFailN", "tot rest fail"),
            ("BenchRestTotExcessN", "tot rest excess"),
            ("BenchRestTotFailPct", "tot rest fail pct"),
            ("BenchRestTotFailCI", "tot rest fail CI"),
            ("BenchRestTotNewTestN", "tot rest newly testable"),
            ("BenchConfDeskPairsN", "conf desk pairs"),
            ("BenchFinHolmPOne", "finite Holm P1"),
            ("BenchFinHolmPThree", "finite Holm P3"),
            ("BenchCOneOnlyCount", "c1-only pos Q1 hits"),
            ("BenchPosEleven", "pos 11"),
            ("BenchPosElevenCOneStream", "pos 11 c1 stream"),
            ("BenchPosFourSevenCOneStream", "pos 47 c1 stream"),
            ("BenchPosElevenCOneRatio", "pos 11 c1 ratio"),
            ("BenchQOneZeroCount", "Q1==0 count"),
            ("BenchPosThreeLev", "Pos 3 leverage"),
            ("BenchPosThreeCooksD", "Pos 3 Cook D"),
            ("BenchPosThreeCooksDSThree", "Pos 3 S3 Cook D"),
            ("BenchPosThreeCooksDSThreeMax", "Pos 3 S3 max Cook D"),
            ("BenchPosThreeSOneLOO", "Pos 3 S1 LOO"),
            ("BenchPosThreeSThreeLOO", "Pos 3 S3 LOO"),
            ("BenchPosThreeSOneCI", "Pos 3 S1 CI"),
            ("BenchPosThreeSThreeCI", "Pos 3 S3 CI"),
            ("BenchPosThirteenCZeroSlope", "Pos 13 c0 slope"),
            ("BenchPosThirteenTotSlope", "Pos 13 tot slope"),
            ("BenchPosNineFourOtwoNsRange", "Pos 94 O2 ns/tick range"),
            ("BenchPosNineFourPlainNsRange", "Pos 94 plain ns/tick range"),
            ("BenchPosNineFourOtwoMsRange", "Pos 94 O2 ms diff range"),
            ("BenchPosOneSevenFiveOtwoNsRange", "Pos 175 O2 ns/tick range"),
            ("BenchPosOneSevenFivePlainNsRange", "Pos 175 plain ns/tick range"),
            ("BenchEnvPOneRange", "P1 envelope"),
            ("BenchEnvPThreeRange", "P3 envelope"),
            ("BenchEnvSAFourRange", "SA4 envelope"),
            ("BenchEnvSAThirteenRange", "SA13 envelope"),
            ("BenchEnvSAThirteenShort", "SA13 short envelope"),
            ("BenchPfStderrN", "process_failure stderr count"),
            ("BenchPfSigabrtN", "process_failure SIGABRT count"),
            ("BenchPfSigsegvN", "process_failure SIGSEGV count"),
            ("BenchRegimeExactEqN", "exact identity count"),
            ("BenchRegimeFlatLowN", "flat <1.5 count"),
            ("BenchRegimeFlatHighN", "flat >=1.5 count"),
            ("BenchRegimeZeroFlatSumN", "zero/flat sum"),
            ("BenchRegimeNegAllN", "neg all-stream count"),
            ("BenchRegimeMixedN", "mixed/reversed count"),
            ("BenchRegimeSubPosN", "positive sub-0.50 count"),
            ("BenchRegimeRevSubSumN", "rev/sub sum"),
            ("BenchBetaGridDropAlerts", "beta 0.10 alerts"),
            ("BenchCorpusPieAlertFrac", "PIE alerts frac"),
            ("BenchCorpusCodeAlertFrac", "CodeNet alerts frac"),
            ("BenchCorpusAlertFisherP", "Corpus alert Fisher p"),
            ("BenchCorpusPieExecFrac", "PIE exec frac"),
            ("BenchCorpusCodeExecFrac", "CodeNet exec frac"),
            ("BenchCorpusExecFisherP", "Corpus exec Fisher p"),
            ("BenchContestExecPct", "Contest exec pct"),
            ("BenchContestExecCI", "Contest exec CI"),
            ("BenchContestExecLo", "Contest exec CP lo"),
            ("BenchSAFourFisherP", "SA4 Fisher p"),
            ("BenchSAThreeDenom", "SA3 denom"),
            ("BenchSAThreeAllSPass", "SA3 all S1-pass"),
            ("BenchSAThreeAllSPassCI", "SA3 all S1-pass CI"),
            ("BenchPosThreeRSq", "pos 3 R2"),
            ("BenchPosSevenSevenLogRSq", "pos 77 log R2"),
            ("BenchPosOneSixFourRatio", "pos 164 ratio"),
            ("BenchPosOneSixFourTotP", "pos 164 tot p"),
            ("BenchPosOneSixFourTotSlope", "pos 164 tot slope"),
            ("BenchPosOneSixFourTotRSq", "pos 164 tot R2"),
            ("BenchPosSevenNine", "pos 79"),
            ("BenchPosSevenNineSlopeRange", "pos 79 slope range"),
            ("BenchPosSevenNineRatioRange", "pos 79 ratio range"),
            ("BenchQuarSourceN", "quar source stops"),
            ("BenchQuarHeldN", "quar held stops"),
            ("BenchQuarIndetN", "quar indet stops"),
            ("BenchRestCOneInflN", "restored c1 inflation"),
            ("BenchPosThree", "pos 3"),
            ("BenchPosThirteen", "pos 13"),
            ("BenchPosTwoSeven", "pos 27"),
            ("BenchPosFourSeven", "pos 47"),
            ("BenchPosFiveFive", "pos 55"),
            ("BenchPosFiveNine", "pos 59"),
            ("BenchPosSevenSeven", "pos 77"),
            ("BenchPosNineZero", "pos 90"),
            ("BenchPosNineOne", "pos 91"),
            ("BenchPosNineFour", "pos 94"),
            ("BenchPosNineSeven", "pos 97"),
            ("BenchPosOneZeroZero", "pos 100"),
            ("BenchPosOneZeroSix", "pos 106"),
            ("BenchPosOneTwoNine", "pos 129"),
            ("BenchPosOneThreeOne", "pos 131"),
            ("BenchPosOneFourZero", "pos 140"),
            ("BenchPosOneFourFive", "pos 145"),
            ("BenchPosOneFiveEight", "pos 158"),
            ("BenchPosOneSixZero", "pos 160"),
            ("BenchPosOneSixFour", "pos 164"),
            ("BenchPosOneSevenFour", "pos 174"),
            ("BenchPosOneSevenFive", "pos 175"),
            ("BenchPosSevenSevenRatio", "pos 77 ratio"),
            ("BenchPosNineZeroRatio", "pos 90 ratio"),
            ("BenchPosOneFourFiveRatio", "pos 145 ratio"),
            ("BenchPosFourSevenCOneRatio", "pos 47 c1 ratio"),
            ("BenchPosNineFourTicksM", "pos 94 ticks M"),
            ("BenchPosOneSixFourTotRatio", "pos 164 tot ratio"),
            ("BenchPosOneZeroZeroMaxSlope", "pos 100/131 max slope"),
            ("BenchPosBothZeroMaxSlope", "both-zero max slope"),
            ("BenchRestOverNineOneRange", "pos 91 rec range"),
            ("BenchRestOverOneTwoNineRange", "pos 129 rec range"),
            ("BenchQuarStopPct", "quarantined stop pct"),
            ("BenchQuarStopCI", "quarantined stop CI"),
            ("BenchQuarClustStopFrac", "quar cluster stop frac"),
            ("BenchQuarClustStopCI", "quar cluster stop CI"),
            ("BenchAuthExactPct", "auth exact pct"),
            ("BenchAuthExactK", "auth exact kappa"),
            ("BenchAuthExactCI", "auth exact CI"),
            ("BenchAuthBucketPct", "auth bucket pct"),
            ("BenchAuthBucketK", "auth bucket kappa"),
            ("BenchAuthBucketCI", "auth bucket CI"),
            ("BenchAuthBucketKappaMax", "auth bucket kmax"),
            ("BenchAuthBucketACOne", "auth bucket AC1"),
            ("BenchAuthBinPct", "auth binary pct"),
            ("BenchAuthBinK", "auth binary kappa"),
            ("BenchAuthBinPABAK", "auth binary PABAK"),
            ("BenchAuthBinACOne", "auth binary AC1"),
            ("BenchAuthBinBI", "auth binary BI"),
            ("BenchAuthBinPI", "auth binary PI"),
            ("BenchAuthBowkerQ", "auth Bowker Q"),
            ("BenchAuthMcNemarP", "auth McNemar p"),
            ("BenchAuthBowkerP", "auth Bowker p"),
            ("BenchAuthAllBowkerExactP", "auth overall Bowker exact p"),
            ("BenchAuthConfN", "auth conf n"),
            ("BenchAuthQuarN", "auth quar n"),
            ("BenchAuthQuarClustersN", "auth quar cl"),
            ("BenchAuthTotalClustersN", "auth total cl"),
            ("BenchAuthLLMPassFrac", "auth LLM pass frac"),
            ("BenchAuthAuthorPassFrac", "auth human pass frac"),
            ("BenchAuthConfPct", "auth conf pct"),
            ("BenchAuthConfKappa", "auth conf kappa"),
            ("BenchAuthConfBinK", "auth conf bin kappa"),
            ("BenchAuthConfBucketKCI", "auth conf bucket kappa CI"),
            ("BenchAuthConfBinKCI", "auth conf bin kappa CI"),
            ("BenchAuthConfPABAKCI", "auth conf PABAK CI"),
            ("BenchAuthConfACOneCI", "auth conf AC1 CI"),
            ("BenchAuthConfAllStopRev", "auth conf all-stop rev"),
            ("BenchAuthConfAllStopRevCI", "auth conf all-stop rev CI"),
            ("BenchAuthConfPassStopN", "auth conf pass-stop"),
            ("BenchAuthConfStopPassN", "auth conf stop-pass"),
            ("BenchAuthConfMcNemarP", "auth conf McNemar p"),
            ("BenchAuthConfBowkerQ", "auth conf Bowker Q"),
            ("BenchAuthConfBowkerP", "auth conf Bowker p"),
            ("BenchAuthConfBowkerExactP", "auth conf Bowker exact p"),
            ("BenchAuthQuarPct", "auth quar pct"),
            ("BenchAuthQuarKappa", "auth quar kappa"),
            ("BenchAuthQuarBinK", "auth quar bin kappa"),
            ("BenchAuthQuarRev", "auth quar rev"),
            ("BenchAuthCohortFisherP", "auth cohort Fisher p"),
            ("BenchCohortClustSensP", "auth 18-cl cohort sensitivity"),
            ("BenchAuthConfContractRev", "conf contract reversals"),
            ("BenchAuthConfContractRevCI", "conf contract rev CI"),
            ("BenchAuthRejExec", "author rejected exec"),
            ("BenchAuthRejExecCI", "author rejected exec CI"),
            ("BenchAuthStopPassN", "author stop-pass disagree"),
            ("BenchAuthPassStopN", "author pass-stop disagree"),
            ("BenchAuthRejTotalN", "author rejected total"),
            ("BenchManskiTipNum", "Manski tip numerator"),
            ("BenchManskiTipRate", "Manski tipping rate"),
            ("BenchManskiPlugInTheta", "Manski plugin theta"),
            ("BenchManskiPlugInThetaCI", "Manski plugin theta CI"),
            ("BenchManskiPlugJointRectCI", "Manski joint rect CI"),
            ("BenchManskiPlugJointJeffCI", "Manski joint Jeffreys CI"),
            ("BenchManskiPlugInSAThirteen", "Manski plugin SA13"),
            ("BenchManskiPlugInTwoStepSAThirteen", "Manski plugin SA13 two-step"),
            ("BenchManskiPlugInPOne", "Manski plugin P1"),
            ("BenchManskiFullFlipTheta", "Manski full flip"),
            ("BenchManskiTwoStepTipTheta", "Manski two-step tip theta"),
            ("BenchManskiTwoStepTipPfn", "Manski two-step tip pfn"),
            ("BenchManskiYOneStepHalfPP", "Manski 1-step y sensitivity"),
            ("BenchManskiYTwoStepHalfPP", "Manski 2-step y sensitivity"),
            ("BenchManskiYDeltaSEDiffPP", "Manski delta SE diff"),
            ("BenchPThreeOracleTipN", "P3 oracle tipping k"),
            ("BenchPThreeOracleTipPct", "P3 oracle tipping pct"),
            ("BenchPThreeOracleTipResultPct", "P3 oracle tipping result pct"),
            ("BenchPThreeOracleTipConservN", "P3 oracle conservative k"),
            ("BenchPThreeOracleTipConservPct", "P3 oracle conservative pct"),
            ("BenchPThreeOracleAdvTipN", "P3 oracle adv tipping k"),
            ("BenchPThreeOracleAdvTipPct", "P3 oracle adv tipping pct"),
            ("BenchPThreeOracleAdvTipConservN", "P3 oracle adv conservative k"),
            ("BenchPThreeOracleAdvTipConservPct", "P3 oracle adv conservative pct"),
            ("BenchPThreeSOneTipN", "P3 S1 tipping k"),
            ("BenchPThreeSOneTipPct", "P3 S1 tipping pct"),
            ("BenchPThreeSOneTipResultPct", "P3 S1 tipping result pct"),
            ("BenchPThreeSOneTipConservN", "P3 S1 conservative k"),
            ("BenchPThreeSOneTipConservPct", "P3 S1 conservative pct"),
            ("BenchSAThirteenFpTipN", "SA13b FP tipping k"),
            ("BenchSAThirteenFpTipPct", "SA13b FP tipping pct"),
            ("BenchSAThirteenFpTipDelta", "SA13b FP tipping delta"),
            ("BenchSAThirteenFpTipP", "SA13b FP tipping p"),
            ("BenchAuthConfFitRejFrac", "author rejected conf fits"),
            ("BenchPThreeFpTipConservN", "P3 FP conserv k"),
            ("BenchPThreeFpTipConservPct", "P3 FP conserv pct"),
            ("BenchPThreeFpTipConservP", "P3 FP conserv p"),
            ("BenchPThreeFpTipFullN", "P3 FP full k"),
            ("BenchPThreeFpTipFullPct", "P3 FP full pct"),
            ("BenchPThreeFpTipFullP", "P3 FP full p"),
            ("BenchTableTwoRows", "Table 2 rows"),
            ("BenchAlertForensicsRows", "Table 4 rows"),
            ("BenchTableFourRows", "Table 5 rows"),
            ("BenchTableCorpusRows", "Corpus split rows"),
            ("BenchTableAppRows", "Appendix Table A1 rows"),
        ):
            lines.append(f"\\newcommand{{\\{slot_macro}}}{{\\BenchSlot{{{label}}}}}")

    lines.extend(flow_macro("Intake", "s0_intake_stop", s1_complete or execution_complete))
    lines.extend(flow_macro("Desk", "s1_desk_stop_total", s1_complete or execution_complete))
    lines.extend(flow_macro("Fixture", "s2_fixture_stop", execution_complete))
    lines.extend(flow_macro("Prep", "s2_preprocessing_stop", execution_complete))
    lines.extend(flow_macro("Infra", "s3_infra_failure", execution_complete))
    lines.extend(flow_macro("Unrun", "not_executed", execution_complete))
    lines.extend(flow_macro("Oracle", "s3_oracle_failure", execution_complete))
    lines.extend(flow_macro("NoFit", "s4_no_fit", execution_complete))
    lines.extend(flow_macro("NoAlert", "s5_no_alert", execution_complete))
    lines.extend(flow_macro("Alert", "s5_alert", execution_complete))
    return "\n".join(lines) + "\n"

def load_ledger(path: Path) -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    """Parse --ledger supporting both pretty-printed JSON and JSONL."""
    text = path.read_text(encoding="utf-8-sig").strip()
    if not text:
        return {}, {}

    records: list[dict[str, Any]] = []
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError:
        for lineno, line in enumerate(text.splitlines(), 1):
            s = line.strip()
            if not s:
                continue
            obj = json.loads(s)
            if not isinstance(obj, dict):
                raise ValueError(f"Invalid JSONL object on line {lineno}")
            records.append(obj)
    else:
        if isinstance(parsed, list):
            records = parsed
        elif isinstance(parsed, dict):
            if ("id" in parsed or "pair_id" in parsed) and any(
                k in parsed for k in ("terminal", "disposition", "final_disposition")
            ):
                records = [parsed]
            elif any(
                isinstance(parsed.get(k), list)
                for k in ("rows", "records", "entries", "pairs", "checkpoints", "items", "ledger")
            ):
                for k in ("rows", "records", "entries", "pairs", "checkpoints", "items", "ledger"):
                    if isinstance(parsed.get(k), list):
                        records = parsed[k]
                        break
            elif isinstance(parsed.get("dispositions"), dict):
                disps = {}
                rows = {}
                for k, v in parsed["dispositions"].items():
                    if v is None:
                        raise ValueError(f"Unresolved terminal disposition (None) for {k}")
                    if isinstance(v, dict):
                        term = v.get("terminal", v.get("disposition", v.get("final_disposition")))
                        if term is None:
                            raise ValueError(f"Unresolved terminal disposition (None) for {k}")
                        disps[str(k)] = str(term)
                        rows[str(k)] = v
                    else:
                        disps[str(k)] = str(v)
                return disps, rows
            else:
                disps: dict[str, str] = {}
                rows: dict[str, dict[str, Any]] = {}
                for k, v in parsed.items():
                    if v is None:
                        raise ValueError(f"Unresolved terminal disposition (None) for {k}")
                    if isinstance(v, str):
                        disps[k] = v
                    elif isinstance(v, dict):
                        term = v.get("terminal", v.get("disposition", v.get("final_disposition")))
                        if term is None:
                            raise ValueError(f"Unresolved terminal disposition (None) for {k}")
                        disps[k] = str(term)
                        rows[k] = v
                return disps, rows
        else:
            raise ValueError("Unsupported ledger JSON root type")

    dispositions: dict[str, str] = {}
    ledger_rows: dict[str, dict[str, Any]] = {}
    for obj in records:
        if not isinstance(obj, dict):
            raise ValueError("Ledger entry must be a JSON object")
        if "terminal" not in obj and "disposition" not in obj and "final_disposition" not in obj:
            continue
        raw_id = obj.get("id") or obj.get("pair_id")
        if not raw_id:
            raise ValueError("Ledger record missing id/pair_id")
        key = f'{obj["corpus"]}:{raw_id}' if (":" not in str(raw_id) and obj.get("corpus")) else str(raw_id)
        term = obj.get("terminal") if "terminal" in obj else obj.get("disposition", obj.get("final_disposition"))
        if term is None:
            raise ValueError(f"Unresolved terminal disposition (None) for {key}")
        dispositions[key] = str(term)
        ledger_rows[key] = obj
    return dispositions, ledger_rows


def _load_author_check_cli(
    author_path: Path,
    *,
    draw_path: Path | None,
    manifest: dict[str, Any] | None,
    s1_summary: dict[str, dict[str, Any]] | None,
) -> dict[str, Any]:
    raw = json.loads(author_path.read_bytes())
    if isinstance(raw, dict) and isinstance(raw.get("author_check"), dict):
        top_ep = raw.get("execution_policy_checks") or raw.get("camera_ready_checks")
        raw = dict(raw["author_check"])
        if top_ep is not None:
            raw["execution_policy_checks"] = top_ep
    if isinstance(raw, dict) and "exact" in raw and "bucket" in raw:
        return raw
    if manifest is None or s1_summary is None:
        raise SystemExit("--author-check with raw labels requires --manifest and --s1-summary")
    if draw_path is not None:
        draw_raw = draw_path.read_bytes()
        if digest(draw_raw) != AUTHOR_DRAW_SHA:
            raise SystemExit("author draw SHA-256 mismatch")
        draw_pairs = json.loads(draw_raw)
    elif isinstance(raw, dict) and isinstance(raw.get("draw"), list):
        draw_pairs = raw["draw"]
    else:
        labels_src = raw.get("author_labels", raw.get("labels", raw))
        draw_pairs = [
            {"corpus": k.split(":", 1)[0], "pair_id": k.split(":", 1)[1]}
            for k in sorted(labels_src)
        ]

    if isinstance(raw, dict) and ("author_labels" in raw or "labels" in raw):
        author_labels = raw.get("author_labels") or raw["labels"]
        unblinded = set(raw.get("unblinded_keys") or [])
    else:
        author_labels = raw
        unblinded = set()
    manifest_by_key = {pair_key(r): r for r in manifest["pairs"]}
    return author_check_agreement(
        draw_pairs,
        manifest_by_key,
        s1_summary,
        author_labels,
        unblinded_keys=unblinded,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, help="Frozen manifest-expanded.json")
    parser.add_argument("--holds", type=Path, help="Frozen s1_hold_list.json")
    parser.add_argument("--s1-summary", type=Path, help="JSON mapping corpus:pair_id -> {status,bucket,reason}")
    parser.add_argument("--ledger", type=Path, help="Optional terminal dispositions JSON/JSONL; defaults to S1-only + not_executed")
    parser.add_argument("--aggregate-json", type=Path, help="Ingest de-identified aggregate JSON (e.g., final-a5-stats-agg.json) directly")
    parser.add_argument("--author-check", type=Path, help="Optional sealed author-check labels or precomputed summary JSON")
    parser.add_argument("--author-draw", type=Path, help="Optional pinned s1_author_check_draw.json for --author-check")
    parser.add_argument("--forensics-json", type=Path, help="Optional de-identified alert/fit forensics JSON (alert-and-fit-forensics-agg.json)")
    parser.add_argument("--anon-measurements", type=Path, help="Optional de-identified per-point counter JSON (anonymous-measurements.json)")
    parser.add_argument("--write-slots", type=Path, help="Optional output path for rendered benchmark_slots.tex")
    parser.add_argument("--write-claims", type=Path, help="Optional output path for paper_claims.json")
    parser.add_argument("--grouped-macros", type=Path, help="Optional grouped_statistics_macros.tex path for provenance hashing")
    parser.add_argument(
        "--execution-complete",
        action=argparse.BooleanOptionalAction,
        default=None,
        help="Override execution_complete flag when rendering benchmark_slots.tex",
    )
    parser.add_argument("--out", type=Path, help="Optional JSON receipt output path")
    args = parser.parse_args()

    author_res: dict[str, Any] | None = None
    cli_manifest: dict[str, Any] | None = None
    if args.aggregate_json:
        agg = json.loads(args.aggregate_json.read_bytes())
        report = analyze_aggregate(agg)
        if args.manifest:
            m_raw = args.manifest.read_bytes()
            if digest(m_raw) != MANIFEST_SHA:
                raise SystemExit("manifest SHA-256 mismatch")
            cli_manifest = json.loads(m_raw)
        elif (cand_man := args.aggregate_json.parent / "freeze" / "manifest-expanded.json").is_file():
            m_raw = cand_man.read_bytes()
            if digest(m_raw) != MANIFEST_SHA:
                raise SystemExit("sibling manifest SHA-256 mismatch")
            cli_manifest = json.loads(m_raw)
        if args.author_check:
            cli_s1 = json.loads(args.s1_summary.read_bytes()) if (cli_manifest and args.s1_summary) else None
            author_res = _load_author_check_cli(
                args.author_check,
                draw_path=args.author_draw,
                manifest=cli_manifest,
                s1_summary=cli_s1,
            )
            report["author_check"] = author_res
        else:
            author_res = report.get("author_check")
        if args.execution_complete is not None:
            exec_complete = bool(args.execution_complete)
        elif "execution_complete" in report:
            exec_complete = bool(report["execution_complete"])
        else:
            u = report["flow_table"]["Union"]
            exec_complete = (
                u["s2_fixture_stop"]
                + u["s2_preprocessing_stop"]
                + u["s3_infra_failure"]
                + u["s3_oracle_failure"]
                + u["s4_no_fit"]
                + u["s5_no_alert"]
                + u["s5_alert"]
            ) > 0
        s1_complete = report["fixture_inventory"]["total_rateable"] > 0
    else:
        if not (args.manifest and args.holds and args.s1_summary):
            parser.error("Either --aggregate-json OR all of --manifest, --holds, and --s1-summary are required")

        manifest_raw = args.manifest.read_bytes()
        if digest(manifest_raw) != MANIFEST_SHA:
            raise SystemExit("manifest SHA-256 mismatch")
        holds_raw = args.holds.read_bytes()
        if digest(holds_raw) != HELD_SHA:
            raise SystemExit("hold list SHA-256 mismatch")

        manifest = json.loads(manifest_raw)
        cli_manifest = manifest
        holds = json.loads(holds_raw)
        s1_summary = json.loads(args.s1_summary.read_bytes())

        inventory = fixture_readiness_inventory(manifest, s1_summary, holds)
        hold_map = {f'{h["corpus"]}:{h["pair_id"]}': "desk_unrateable" for h in holds}

        dispositions: dict[str, str] = {}
        ledger_rows: dict[str, dict[str, Any]] = {}
        if args.ledger:
            dispositions, ledger_rows = load_ledger(args.ledger)
            for row in manifest["pairs"]:
                key = pair_key(row)
                if row.get("intake_stop") and key not in dispositions:
                    dispositions[key] = row["intake_stop"]
                elif key in hold_map and key not in dispositions:
                    dispositions[key] = "desk_unrateable"
                elif key in s1_summary and key not in dispositions and s1_summary[key].get("status") != "pass":
                    dispositions[key] = s1_summary[key]["status"]
        else:
            for row in manifest["pairs"]:
                key = pair_key(row)
                if row.get("intake_stop"):
                    dispositions[key] = row["intake_stop"]
                elif key in hold_map:
                    dispositions[key] = "desk_unrateable"
                else:
                    st = s1_summary[key]["status"]
                    dispositions[key] = "not_executed" if st == "pass" else st

        report = {
            "schema": "eapg.expansion.analysis.v1",
            "amendment_sha256": AMENDMENT_5_SHA,
            "manifest_sha256": MANIFEST_SHA,
            "held_list_sha256": HELD_SHA,
            "held_out_used": manifest["held_out_used"],
            "s1_batches": 96,
            "flow_table": flow_table(manifest["pairs"], dispositions),
            "primary_all_post_s0": analyze_cohort(
                manifest, dispositions, desk_meta=s1_summary, ledger_rows=ledger_rows, drop_unrateable=False
            ),
            "S13_without_desk_unrateable": analyze_cohort(
                manifest, dispositions, desk_meta=s1_summary, ledger_rows=ledger_rows, drop_unrateable=True
            ),
            "fixture_inventory": inventory,
        }
        if args.author_check:
            author_res = _load_author_check_cli(
                args.author_check,
                draw_path=args.author_draw,
                manifest=manifest,
                s1_summary=s1_summary,
            )
            report["author_check"] = author_res
        s1_complete = True
        exec_complete = bool(args.execution_complete) if args.execution_complete is not None else bool(args.ledger)

    forensics_res: dict[str, Any] | None = None
    agg_sha = digest(args.aggregate_json.read_bytes()) if args.aggregate_json and args.aggregate_json.is_file() else None
    author_sha = digest(args.author_check.read_bytes()) if args.author_check and args.author_check.is_file() else None
    forensics_sha: str | None = None
    anon_sha: str | None = None
    if args.forensics_json:
        f_bytes = args.forensics_json.read_bytes()
        forensics_sha = digest(f_bytes)
        f_raw = json.loads(f_bytes)
        anon_rows = None
        if args.anon_measurements:
            a_bytes = args.anon_measurements.read_bytes()
            anon_sha = digest(a_bytes)
            if anon_sha != ANON_MEASUREMENTS_SHA:
                raise SystemExit(f"anonymous-measurements SHA-256 mismatch: {anon_sha} != {ANON_MEASUREMENTS_SHA}")
            anon_rows = json.loads(a_bytes)
        forensics_res = verify_anon_and_forensics(f_raw, anon_rows, report, author_res, manifest=cli_manifest)
        report["forensics"] = forensics_res
        sec_s8 = ((report.get("primary_all_post_s0") or {}).get("secondary") or {}).get("S8_drop_largest_refit")
        s8_any = (forensics_res.get("fit_124_taxonomy") or {}).get("s8_any_stream_alerts_among_admitted")
        if isinstance(sec_s8, dict) and sec_s8.get("any_stream_alerts_among_admitted") is None and s8_any is not None:
            sec_s8["any_stream_alerts_among_admitted"] = s8_any
    else:
        forensics_res = report.get("forensics")

    slots_tex: str | None = None
    if args.write_slots or args.write_claims:
        slots_tex = render_benchmark_slots(
            report,
            s1_complete=s1_complete,
            execution_complete=exec_complete,
            author_check=author_res,
            forensics=forensics_res,
            manifest=cli_manifest,
        )
    if args.write_slots and slots_tex is not None:
        args.write_slots.parent.mkdir(parents=True, exist_ok=True)
        args.write_slots.write_bytes(slots_tex.encode("utf-8"))
    if args.write_claims and slots_tex is not None:
        grouped_path = args.grouped_macros or (Path(__file__).resolve().parents[1] / "manuscript" / "grouped_statistics_macros.tex")
        grouped_sha = digest(grouped_path.read_bytes()) if grouped_path.is_file() else None
        claims_obj = build_paper_claims(
            slots_tex,
            manifest_sha=report.get("manifest_sha256", MANIFEST_SHA),
            amendment_sha=report.get("amendment_sha256", AMENDMENT_5_SHA),
            agg_sha=agg_sha,
            author_sha=author_sha,
            forensics_sha=forensics_sha,
            anon_sha=anon_sha,
            grouped_sha=grouped_sha,
        )
        args.write_claims.parent.mkdir(parents=True, exist_ok=True)
        args.write_claims.write_bytes((json.dumps(claims_obj, indent=2, sort_keys=True) + "\n").encode("utf-8"))

    text = json.dumps(report, indent=2, sort_keys=True)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_bytes((text + "\n").encode("utf-8"))
    elif not args.write_slots and not args.write_claims:
        print(text)


if __name__ == "__main__":
    main()
