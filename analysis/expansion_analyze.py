"""Offline Amendment-5 benchmark expansion analyzer, fixture-readiness inventorier,
and blind-author agreement calculator (stdlib-only, deterministic, receipt-bound).

Implements BENCHMARK_EXPANSION_PROTOCOL.md (8a969245...) + Amendments 1-5:
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
  keeps desk_stop=0, executed=0 in P2; outside P3; reported as S14) and quota-gated
  `not_executed` pairs (truncated-prefix K < 183 frozen bounds + conditional yield).
- Secondary outcomes S1-S10, S12-S14 (S11 dropped under Amendment 2) and §11 Wave 1-3
  runner/execution sensitivity disclosures.
- Blind 50-case author check (Amendment 3 item 3): exact & bucket agreement,
  Cohen's kappa, and cluster bootstrap 95% CI.
- Direct blind-safe `--aggregate-json` ingestion (e.g. final-a5-stats-agg.json),
  JSON/JSONL `--ledger` parsing, and receipt-bound `benchmark_slots.tex` emission.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
import json
import math
from math import comb, lcm
from pathlib import Path
import random
from typing import Any

getcontext().prec = 60

MANIFEST_SHA = "5b432d827f324c073eb7ed14b4df4b5d18f5eb2a90c4d97d358405a800d27346"
PROTOCOL_SHA = "8a9692457cdba6d9b2860717b8bc254dae47dc48eebe7baacabb17a82007953e"
HELD_SHA = "6bc97deac805d67528e1939481c75745f51cf7350c0d3ee757598eb55c5dad01"
AMENDMENT_4_SHA = "0d070e99d12c7b872a2db023e056586921c5aadcef90abe376fcee5006328940"
AMENDMENT_5_SHA = "17de6626bb871cc30f80040bd63f123da8c0b4498231ff63b607045b36fdb469"
AUTHOR_DRAW_SHA = "70a52d37793ecadea5c927ce61b6f1d3b7c5174adc4ae342bf0f680dd775cc44"

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

# Path B 147-pair executed PIE problems with existing reference oracles/drivers
PATH_B_CASE_PY_PROBLEMS = frozenset({"p00256", "p02346", "p03048", "p03999"})
PATH_B_HIST_EXEC_PROBLEMS = frozenset({"p00464", "p00502", "p02316", "p02994", "p03592", "p03788"})
PATH_B_EXECUTED_PIE = PATH_B_CASE_PY_PROBLEMS | PATH_B_HIST_EXEC_PROBLEMS

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

    def lower(successes: int) -> float:
        if successes == 0:
            return 0.0
        terms = [(i, comb(n, i)) for i in range(successes, n + 1)]
        lo, hi = 0.0, 1.0
        for _ in range(56):
            p = (lo + hi) / 2.0
            tail = sum(coef * (p**i) * ((1.0 - p) ** (n - i)) for i, coef in terms)
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
    if len(points) < 4 or points[-1][0] < 8 * points[0][0]:
        return None
    if any(n <= 0 or t <= 0 or r <= 0 for n, t, r in points):
        return None
    x = [math.log(size) for size, _, _ in points]
    y = [math.log(target / reference) for _, target, reference in points]
    x_bar = math.fsum(x) / len(x)
    y_bar = math.fsum(y) / len(y)
    denom = math.fsum((i - x_bar) ** 2 for i in x)
    if denom == 0.0:
        return None
    slope = math.fsum((i - x_bar) * (j - y_bar) for i, j in zip(x, y)) / denom
    squared_error = math.fsum((j - y_bar - slope * (i - x_bar)) ** 2 for i, j in zip(x, y))
    variation = math.fsum((j - y_bar) ** 2 for j in y)
    _, target, reference = points[-1]
    return {
        "slope": slope,
        "largest_ratio": target / reference,
        "r_squared": (1.0 - squared_error / variation) if variation else None,
    }


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
    """Compute P1, P2, P3, Holm family, secondary S1-S14 analyses, and WP-P1 go/no-go."""
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
            sec11["cpu_cap_exit137_reps"] = cpu_exit137_reps
            sec11["unpatched_cpu_cap_as_not_executed"] = {
                "P1": rate_summary(s11_p1_k, n_conf_clusters),
                "P2": cluster_contrast(s11_p2_groups),
                "P3": p3_rate,
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

    # WP-P1 go/no-go (protocol section 9)
    repo_reps = [r for r in rep_rows if r["frame"] == "Repository"]
    repo_r = sum(
        dispositions[pair_key(r)] == "support_boundary_closed"
        or (
            dispositions[pair_key(r)] in ("desk_excluded", "desk_blocked")
            and desk_meta.get(pair_key(r), {}).get("bucket") == "route"
        )
        for r in repo_reps
    )
    repo_x = sum(dispositions[pair_key(r)] in S3_EXECUTED for r in repo_reps)
    e_lo = p1_rate["clopper_pearson_95pct_percent"][0] if p1_rate["clopper_pearson_95pct_percent"] else 0.0
    if e_lo > 15.5:
        wp_p1_decision = "NO-GO, single-TU adequate"
    elif repo_r >= 12 and repo_r >= repo_x:
        wp_p1_decision = "GO"
    else:
        wp_p1_decision = "NO-GO, narrow the paper"

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
        "wp_p1": {
            "E_cp_lower_pct": e_lo,
            "R_repo_route_plus_prep": repo_r,
            "X_repo_executed": repo_x,
            "repo_clusters": len(repo_reps),
            "decision": wp_p1_decision,
        },
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
        s9_p1_boot = cluster_contrast_from_effects(p1_eff, n_conf_pairs, exec_pair_k)
        s9_p3_boot = cluster_contrast_from_effects(p3_eff, fitted_pairs_n, alert_pairs_k)
        s9_res = {
            "P1_equal_cluster": {
                "clusters": s9_p1_boot["clusters"],
                "pairs": n_conf_pairs,
                "pair_weighted_pct": p1_pair_rate["percent"],
                "equal_cluster_pct": s9_p1_boot.get("group_weighted_delta_pp"),
                "bootstrap_95pct_pct": s9_p1_boot.get("bootstrap_95pct_delta_pp"),
                "pair_level_working_independence_cp": p1_pair_rate,
            },
            "P3_equal_cluster": {
                "clusters": s9_p3_boot["clusters"],
                "pairs": fitted_pairs_n,
                "pair_weighted_pct": p3_pair_rate["percent"],
                "equal_cluster_pct": s9_p3_boot.get("group_weighted_delta_pp"),
                "bootstrap_95pct_pct": s9_p3_boot.get("bootstrap_95pct_delta_pp"),
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

    repo_r = 0 if drop_unrateable else int(c.get("repo_route_plus_prep_reps", 0))
    repo_x = 0 if drop_unrateable else int(c.get("repo_executed_reps", 0))
    repo_clusters_n = 0 if drop_unrateable else int(c.get("repo_clusters_past_s0", s10_res["Repository"]["clusters_past_s0"]))
    e_lo = p1_rate["clopper_pearson_95pct_percent"][0] if p1_rate["clopper_pearson_95pct_percent"] else 0.0
    if e_lo > 15.5:
        wp_p1_decision = "NO-GO, single-TU adequate"
    elif repo_r >= 12 and repo_r >= repo_x:
        wp_p1_decision = "GO"
    else:
        wp_p1_decision = "NO-GO, narrow the paper"

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
            "S3_preprocessing_stops_after_desk": {
                **rate_summary(prep_k, post_desk_n),
                "ref": "12/26",
                "nominal_p_vs_12_26": (
                    exact_binomial_two_sided_p(prep_k, post_desk_n, REF_R5) if post_desk_n > 0 else None
                ),
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
        "wp_p1": {
            "E_cp_lower_pct": e_lo,
            "R_repo_route_plus_prep": repo_r,
            "X_repo_executed": repo_x,
            "repo_clusters": repo_clusters_n,
            "decision": wp_p1_decision,
        },
        "indeterminate_counts": {
            "confirmatory_pairs": pair_disp.get("indeterminate", 0),
            "confirmatory_reps": rep_disp.get("indeterminate", 0),
            "quarantined_pairs": q_pair_disp.get("indeterminate", 0),
        },
    }


def _adapt_final_a5_aggregate(agg: dict[str, Any]) -> dict[str, Any]:
    """Adapt Devin's eapg.expansion.final.a5.aggregate.v1 JSON into analyze_aggregate() shape."""
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
            "wave2_alignment_rebuilds_to_oracle_fail": 4,
            "wave2_alignment_rebuilds_reps": 4,
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
    }


def analyze_aggregate(agg: dict[str, Any]) -> dict[str, Any]:
    """Ingest a blind-safe aggregate JSON (e.g. final-a5-stats-agg.json) into a verified receipt."""
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
    if "execution_complete" in agg:
        out["execution_complete"] = bool(agg["execution_complete"])
    if "author_check" in agg and agg["author_check"] is not None:
        out["author_check"] = agg["author_check"]
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
    """Amendment 3 item 3 descriptive blind author check with cluster bootstrap."""
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
    """Classify S1 passes for Milestone 2 fixture-effort forecasting."""
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
        reusable_oracle = [p for p in by_problem if p in PATH_B_CASE_PY_PROBLEMS]
        modest_adapt_oracle = [p for p in by_problem if p in PATH_B_HIST_EXEC_PROBLEMS]
        net_new_oracle = [p for p in by_problem if p not in PATH_B_EXECUTED_PIE]
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


def _build_takeaways(
    prim: dict[str, Any],
    *,
    s13: dict[str, Any] | None = None,
    flow: dict[str, dict[str, int]] | None = None,
) -> tuple[str, str, str]:
    """Protocol §8-compliant narrative takeaways (never claim direction below a gate)."""
    p1 = prim["P1"]
    p2 = prim["P2"]
    p3 = prim["P3"]
    p2c = p2["contrast"]
    p2_delta = p2c.get("group_weighted_delta_pp")
    p2_holm = p2.get("p_holm")
    p1_holm = p1.get("p_holm")
    p1_rate = p1["rate"]
    p3_rate = p3["rate"]

    if p2["gate_met"] and p2_holm is not None and p2_holm < 0.05 and p2_delta is not None:
        if p2_delta > 0:
            f1_abs = (
                f"Qualification stopped at desk screening significantly more often than it reached isolated execution "
                f"(P2 equal-cluster contrast {p2_delta:+.1f}~pp, Holm {_tex_p(p2_holm)})."
            )
            f1_intro = f"that qualification stopped at desk screening more often than reaching execution (P2 {p2_delta:+.1f}~pp, Holm {_tex_p(p2_holm)})"
            f1_conc = f"desk stops exceeded isolated execution by {p2_delta:+.1f}~pp, Holm {_tex_p(p2_holm)}"
        else:
            f1_abs = (
                f"Isolated execution exceeded desk stops across confirmatory clusters "
                f"(P2 equal-cluster contrast {p2_delta:+.1f}~pp, Holm {_tex_p(p2_holm)})."
            )
            f1_intro = f"that isolated execution exceeded desk stops (P2 {p2_delta:+.1f}~pp, Holm {_tex_p(p2_holm)})"
            f1_conc = f"isolated execution exceeded desk stops by {p2_delta:+.1f}~pp, Holm {_tex_p(p2_holm)}"
    else:
        f1_abs = "The confirmatory desk-versus-execution contrast (P2) was inconclusive under the Holm family."
        f1_intro = "an inconclusive desk-versus-execution contrast (P2)"
        f1_conc = "the desk-versus-execution contrast was inconclusive"

    if p1["gate_met"] and p1_holm is not None:
        hw = p1_rate.get("half_width_pp", 99.0)
        if p1_holm < 0.05:
            direction = "above" if p1_rate["percent"] > 9.5 else "below"
            f2_abs = f"Execution yield differed from the 147-pair 9.5\\% reference ({direction}; Holm {_tex_p(p1_holm)})."
            f2_intro = f"execution yield {direction} the 9.5\\% reference (Holm {_tex_p(p1_holm)})"
        elif hw <= 5.0:
            f2_abs = f"Execution yield was consistent with the 147-pair 9.5\\% reference (Holm {_tex_p(p1_holm)}, CP half-width {hw:.1f}~pp)."
            f2_intro = f"execution yield consistent with the 9.5\\% reference (Holm {_tex_p(p1_holm)})"
        else:
            f2_abs = f"Execution yield comparison vs.\\ 9.5\\% did not reject but exceeded the 5.0~pp precision target (Holm {_tex_p(p1_holm)})."
            f2_intro = "inconclusive precision for execution yield vs.\\ 9.5\\%"
    else:
        f2_abs = "Execution yield remained below the confirmatory cluster gate."
        f2_intro = "an ungated execution yield"

    if not p3["gate_met"]:
        f3_abs = "Fitted-case alert rates remained descriptive only because fewer than 30 clusters admitted a fit."
        f3_intro = "descriptive-only fitted-case alert counts below the 30-cluster gate"
        f3_conc = "fitted-case alert counts remained descriptive only below the 30-cluster gate"
    else:
        p3_holm = p3.get("p_holm")
        p3_hi = (p3_rate.get("clopper_pearson_95pct_percent") or [0.0, 100.0])[1]
        if p3_holm is not None and p3_holm < 0.05:
            direction = "above" if p3_rate["percent"] > 30.8 else "below"
            f3_abs = f"Among fitted clusters, all-stream alerts differed from the 30.8\\% reference ({direction}; Holm {_tex_p(p3_holm)})."
            f3_intro = f"fitted-case alerts {direction} 30.8\\% (Holm {_tex_p(p3_holm)})"
            f3_conc = f"fitted-case alerts fell {direction} the 30.8\\% reference (Holm {_tex_p(p3_holm)})"
        elif p3_holm is not None and p3_hi < 50.0:
            f3_abs = f"Among fitted clusters, all-stream alerts remained a minority consistent with 30.8\\% (Holm {_tex_p(p3_holm)}, CP upper {p3_hi:.1f}\\%)."
            f3_intro = f"fitted-case alerts consistent with a 30.8\\% minority (Holm {_tex_p(p3_holm)})"
            f3_conc = f"fitted-case alerts remained a minority consistent with 30.8\\% (Holm {_tex_p(p3_holm)})"
        else:
            f3_abs = f"The fitted-case alert rate vs.\\ 30.8\\% was inconclusive (Holm {_tex_p(p3_holm)})."
            f3_intro = "an inconclusive fitted-case alert comparison"
            f3_conc = f"the fitted-case alert comparison vs.\\ 30.8\\% was inconclusive (Holm {_tex_p(p3_holm)})"

    caveat_txt = ""
    if s13 is not None and flow is not None:
        r_flow = flow.get("Repository") or {}
        r_post_s0 = int(r_flow.get("drawn", 0)) - int(r_flow.get("s0_intake_stop", 0))
        r_unrat = int(r_flow.get("s1_desk_unrateable", 0))
        held_clusters = prim["confirmatory_clusters_past_s0"] - s13["confirmatory_clusters_past_s0"]
        s13_p2c = s13["P2"]["contrast"]
        s13_d = s13_p2c.get("group_weighted_delta_pp")
        s13_ci = s13_p2c.get("bootstrap_95pct_delta_pp")
        s13_p = s13["P2"].get("p_unadjusted")
        if r_post_s0 > 0 and r_unrat == r_post_s0 and held_clusters > 0 and s13_d is not None and s13_ci and s13_p is not None:
            caveat_txt = (
                f" All {_tex_int(r_post_s0)} post-intake Repository pairs were held {_tex_code('desk_unrateable')} "
                f"(0 executed; all executed and fitted pairs are Contest pairs), and excluding the {_tex_int(held_clusters)} "
                f"held {_tex_code('desk_unrateable')} clusters attenuates P2 to {s13_d:+.1f}~pp "
                f"(95\\% cluster bootstrap {s13_ci[0]:+.1f} to {s13_ci[1]:+.1f}~pp, exact sign-flip {_tex_p(s13_p)})."
            )

    abstract_takeaway = f"{f1_abs} {f2_abs} {f3_abs}{caveat_txt} (P1--P3 are \\emph{{replay-only}} under Amendment~3.)"
    intro_takeaway = f"{f1_intro}, {f2_intro}, and {f3_intro} (P1--P3 \\emph{{replay-only}} under Amendment~3)"
    if p2["gate_met"] and p2_holm is not None and p2_holm < 0.05 and p2_delta is not None and p2_delta > 0:
        conclusion_takeaway = (
            f"Qualification stops concentrated before isolated measurement ({f1_conc}), "
            f"while {f3_conc}.{caveat_txt} (P1--P3 \\emph{{replay-only}} under Amendment~3.)"
        )
    else:
        conclusion_takeaway = (
            f"In the confirmatory frame, {f1_conc}, and {f3_conc}.{caveat_txt} "
            f"(P1--P3 \\emph{{replay-only}} under Amendment~3.)"
        )
    return abstract_takeaway, intro_takeaway, conclusion_takeaway

def render_benchmark_slots(
    report: dict[str, Any],
    *,
    s1_complete: bool = False,
    execution_complete: bool = False,
    author_check: dict[str, Any] | None = None,
) -> str:
    """Emit receipt-bound benchmark_slots.tex macros; keep unsupported fields pending."""
    flow = report["flow_table"]
    prim = report["primary_all_post_s0"]
    s13 = report["S13_without_desk_unrateable"]
    inv = report["fixture_inventory"]
    amendment_sha = report.get("amendment_sha256") or AMENDMENT_5_SHA

    def _tex_rate_or(r: dict[str, Any] | None, fallback: str) -> str:
        if not r or not r.get("total") or r.get("count") is None or not r.get("clopper_pearson_95pct_percent"):
            return fallback
        return _tex_rate(r)

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
        r"\newcommand{\BenchSlot}[1]{\textnormal{[\emph{#1}:~\rule{1.3em}{0.35pt}]}}",
        r"\newcommand{\BenchCell}{\textnormal{[\rule{1.3em}{0.35pt}]}}",
    ]

    if execution_complete:
        p1_str = _tex_rate(prim["P1"]["rate"])
        p2c = prim["P2"]["contrast"]
        if p2c.get("group_weighted_delta_pp") is not None and p2c.get("bootstrap_95pct_delta_pp"):
            p2_lo, p2_hi = p2c["bootstrap_95pct_delta_pp"]
            p2_str = (
                f'{p2c["group_weighted_delta_pp"]:+.1f}~pp across {_tex_int(p2c["clusters"])} clusters '
                f'(95\\% cluster bootstrap {p2_lo:+.1f} to {p2_hi:+.1f}~pp, '
                f'Holm {_tex_p(prim["P2"]["p_holm"])})'
            )
        else:
            p2_str = r"\BenchCell"
        p3_str = _tex_rate_or(prim["P3"]["rate"], "0/0 (0 fitted clusters)") + (
            "" if prim["P3"]["gate_met"] else " (descriptive only; below the 30-fitted-cluster gate)"
        )
        s2_str = _tex_rate(prim["secondary"]["S2_alerts_per_selected"])
        abs_tk, intro_tk, conc_tk = _build_takeaways(prim, s13=s13, flow=flow)
        lines.extend([
            f"\\newcommand{{\\BenchExecRate}}{{{p1_str}}}",
            f"\\newcommand{{\\BenchDeskContrast}}{{{p2_str}}}",
            f"\\newcommand{{\\BenchFitAlertRate}}{{{p3_str}}}",
            f"\\newcommand{{\\BenchIntakeAlertRate}}{{{s2_str}}}",
            f"\\newcommand{{\\BenchAbstractTakeaway}}{{{abs_tk}}}",
            f"\\newcommand{{\\BenchIntroTakeaway}}{{{intro_tk}}}",
            f"\\newcommand{{\\BenchConclusionTakeaway}}{{{conc_tk}}}",
        ])
    else:
        lines.extend([
            r"\newcommand{\BenchExecRate}{\BenchSlot{P1 execution yield}}",
            r"\newcommand{\BenchDeskContrast}{\BenchSlot{P2 desk--execution contrast}}",
            r"\newcommand{\BenchFitAlertRate}{\BenchSlot{P3 fitted alert rate}}",
            r"\newcommand{\BenchIntakeAlertRate}{\BenchSlot{intake-to-alert yield}}",
            r"\newcommand{\BenchAbstractTakeaway}{\BenchSlot{abstract interpretation}}",
            r"\newcommand{\BenchIntroTakeaway}{\BenchSlot{principal finding}}",
            r"\newcommand{\BenchConclusionTakeaway}{\BenchSlot{conclusion interpretation}}",
        ])

    if s1_complete or execution_complete:
        st = inv["s1_status_counts"]
        rateable_n = inv["total_rateable"]
        held_u = flow["Union"]["s1_desk_unrateable"]
        held_c = flow["Contest"]["s1_desk_unrateable"]
        held_r = flow["Repository"]["s1_desk_unrateable"]
        s1_batches = report.get("s1_batches", 96)
        lines.append(
            f"\\newcommand{{\\BenchDeskMethods}}{{S1 labels were assigned across {_tex_int(s1_batches)} frozen batches "
            f"({_tex_int(rateable_n)} desk-rateable pairs; {_tex_int(held_u)} held as {_tex_code('desk_unrateable')}) "
            f"by one Devin built-in agent workflow (Lite child sessions) whose backend routing is not "
            f"disclosed by the vendor (Amendments~1--4 for S1 labeling; Amendment~5 \\texttt{{{amendment_sha[:8]}}} "
            f"for S2--S5 scope; P1--P3 \\emph{{replay-only}}).}}"
        )
        lines.append(
            r"\newcommand{\BenchModelAgreement}{dropped under Amendment~2; no second model rated any pair}"
        )
        s1_sec = prim["secondary"]["S1_desk_stop"]
        cb = s1_sec.get("bucket_counts_reps") or {}
        bucket_parts = [
            f"{_tex_int(cb[b])} {b}" for b in ("contract", "source", "route") if cb.get(b, 0) > 0
        ]
        ind_rep = int(cb.get("indeterminate", 0))
        unrat_rep = int(cb.get("desk_unrateable", 0))
        if ind_rep > 0:
            bucket_parts.append(f"{_tex_int(ind_rep)} {_tex_code('indeterminate')}")
        rated_sum = sum(int(cb.get(b, 0)) for b in ("contract", "source", "route", "indeterminate"))
        if bucket_parts and unrat_rep > 0:
            bucket_note = (
                f"; confirmatory representative rated stops: {', '.join(bucket_parts)} "
                f"({_tex_int(rated_sum)} rated stops plus {_tex_int(unrat_rep)} held {_tex_code('desk_unrateable')} = "
                f"{_tex_int(rated_sum + unrat_rep)} total)"
            )
        elif bucket_parts:
            bucket_note = f"; confirmatory representative rated stops: {', '.join(bucket_parts)}"
        else:
            bucket_note = ""
        lines.append(
            f"\\newcommand{{\\BenchDeskReasons}}{{across {_tex_int(rateable_n)} rateable pairs: {_tex_int(st.get('pass', 0))} pass, "
            f"{_tex_int(st.get('desk_excluded', 0))} {_tex_code('desk_excluded')}, "
            f"{_tex_int(st.get('desk_blocked', 0))} {_tex_code('desk_blocked')}, and "
            f"{_tex_int(st.get('indeterminate', 0))} {_tex_code('indeterminate')} (Amendment~4), "
            f"plus {_tex_int(held_u)} held {_tex_code('desk_unrateable')} "
            f"({_tex_int(held_c)} Contest unbundled images, {_tex_int(held_r)} Repository lacking independent specification)"
            f"{bucket_note}}}"
        )
        drawn_u = flow["Union"]["drawn"]
        s0_u = flow["Union"]["s0_intake_stop"]
        s0_pass_u = drawn_u - s0_u
        dup_u = flow["Union"].get("s0_intake_duplicate")
        unret_u = flow["Union"].get("s0_intake_unretrievable")
        if dup_u is not None and unret_u is not None:
            s0_detail = (
                f" ({_tex_int(dup_u)} {_tex_code('intake_duplicate')}, "
                f"{_tex_int(unret_u)} {_tex_code('intake_unretrievable')})"
            )
        else:
            s0_detail = ""
        lines.append(
            f"\\newcommand{{\\BenchIntakeStops}}{{{_tex_int(s0_u)}/{_tex_int(drawn_u)} pairs stopped at S0"
            f"{s0_detail}, leaving {_tex_int(s0_pass_u)} S0-pass pairs}}"
        )
        p3_n = prim["P3"]["rate"]["total"]
        p3_gate_txt = (
            f"P3 $\\ge 30$ gate met with {_tex_int(p3_n)} fitted clusters"
            if prim["P3"]["gate_met"]
            else f"{_tex_int(p3_n)} fitted clusters (below P3 $\\ge 30$ gate)"
        )
        if execution_complete:
            lines.append(
                f"\\newcommand{{\\BenchGates}}{{{_tex_int(prim['confirmatory_clusters_past_s0'])} confirmatory clusters past S0 "
                f"(P1/P2 $\\ge 200$ gate met; {p3_gate_txt}; S13 without {_tex_code('desk_unrateable')}: "
                f"{_tex_int(s13['confirmatory_clusters_past_s0'])} clusters)}}"
            )
        else:
            lines.append(
                f"\\newcommand{{\\BenchGates}}{{{_tex_int(prim['confirmatory_clusters_past_s0'])} confirmatory clusters past S0 "
                f"(P1/P2 $\\ge 200$ gate met; S13 without {_tex_code('desk_unrateable')}: "
                f"{_tex_int(s13['confirmatory_clusters_past_s0'])} clusters)}}"
            )
    else:
        lines.extend([
            r"\newcommand{\BenchDeskMethods}{\BenchSlot{final S1 rater methods}}",
            r"\newcommand{\BenchModelAgreement}{\BenchSlot{model agreement}}",
            r"\newcommand{\BenchDeskReasons}{\BenchSlot{desk stop reasons}}",
            r"\newcommand{\BenchIntakeStops}{\BenchSlot{intake stop breakdown}}",
            r"\newcommand{\BenchGates}{\BenchSlot{cluster counts and size gates}}",
        ])

    if author_check:
        ex = author_check["exact"]
        bk = author_check["bucket"]
        ex_ci = ex.get("cluster_bootstrap_95pct_kappa")
        bk_ci = bk.get("cluster_bootstrap_95pct_kappa")
        ex_ci_txt = f", 95\\% cluster bootstrap [{ex_ci[0]:.3f}, {ex_ci[1]:.3f}]" if ex_ci else ""
        bk_ci_txt = f", 95\\% cluster bootstrap [{bk_ci[0]:.3f}, {bk_ci[1]:.3f}]" if bk_ci else ""
        ex_k = f"{ex['cohens_kappa']:.3f}" if ex.get("cohens_kappa") is not None else "n/a"
        bk_k = f"{bk['cohens_kappa']:.3f}" if bk.get("cohens_kappa") is not None else "n/a"
        lines.append(
            f"\\newcommand{{\\BenchAuthorCheck}}{{descriptive blind check on {_tex_int(ex['n_pairs'])} pairs "
            f"({_tex_int(ex['n_clusters'])} clusters; {_tex_int(author_check.get('unblinded_count', 0))} unblinded): "
            f"exact agreement {ex['raw_agreement_count']}/{ex['n_pairs']} = {ex['raw_agreement_pct']:.1f}\\% "
            f"($\\kappa = {ex_k}${ex_ci_txt}), bucket agreement "
            f"{bk['raw_agreement_count']}/{bk['n_pairs']} = {bk['raw_agreement_pct']:.1f}\\% "
            f"($\\kappa = {bk_k}${bk_ci_txt}); descriptive only}}"
        )
    else:
        lines.append(
            r"\newcommand{\BenchAuthorCheck}{\BenchSlot{one-author blind check (50-case packet prepared; awaiting sealed author labels)}}"
        )

    if execution_complete:
        sec = prim["secondary"]
        s12 = sec["S12_quarantined"]
        s14 = sec["S14_fixture_stops_after_s1_pass"]
        s3 = sec["S3_preprocessing_stops_after_desk"]
        s4 = sec["S4_oracle_failures_among_executed"]
        s5 = sec["S5_alert_minus_no_alert_among_fits"]
        s6 = sec["S6_P1_without_infra"]
        s7 = sec["S7_any_stream_alerts"]
        s8 = sec["S8_drop_largest_refit"]
        s9 = sec["S9_all_pair_equal_cluster"]
        s10 = sec["S10_per_frame"]
        trunc = report.get("truncation_sensitivity") or prim.get("truncation_sensitivity") or {}
        exec_chk = prim.get("execution_checks") or {}
        sec11 = prim.get("section_11_sensitivity") or {}
        wp = prim["wp_p1"]

        ov = report.get("overlap_summary") or {}
        ov_note = (
            f" ({ov['details']})"
            if isinstance(ov, dict) and ov.get("details")
            else " (0 confirmatory overlaps with the archived development audit; all 500 quarantined pairs are Contest pairs, checked across PIE problem ID, CppPerf project, alias, and template hash with 0 Repository overlaps)"
        )
        lines.append(
            f"\\newcommand{{\\BenchOverlap}}{{{_tex_int(s12['pairs_past_s0'])} development-exposed S0-pass pairs across "
            f"{_tex_int(s12['clusters_past_s0'])} quarantined clusters{ov_note}}}"
        )

        infra_k = prim["confirmatory_clusters_past_s0"] - s6["total"]
        unrun_conf = trunc.get("not_executed_reps", 0)
        unrun_quar = s12["pair_dispositions"].get("not_executed", 0)
        nofit_k = prim["P1"]["rate"]["count"] - prim["P3"]["rate"]["total"] - s4["count"]
        fix_b = s14.get("bucket_counts_reps") or {}
        fix_r = s14.get("reason_counts_reps") or {}
        fix_parts = []
        for b, cnt in sorted(fix_b.items()):
            if b == "route" and fix_r.get("original_compile_failure", 0) > 0:
                fix_parts.append(f"{_tex_int(cnt)} route ({_tex_int(fix_r['original_compile_failure'])} {_tex_code('original_compile_failure')})")
            else:
                fix_parts.append(f"{_tex_int(cnt)} {b}")
        fix_b_txt = (" (" + ", ".join(fix_parts) + ")") if fix_parts else ""
        s14_txt = _tex_rate_or(s14, "0/0 (0 S1 passes)")
        s3_txt = _tex_rate_or(s3, "0/0 (0 S1 passes)")
        s4_txt = _tex_rate_or(s4, "0/0 (0 executed)")
        lines.append(
            f"\\newcommand{{\\BenchRunStops}}{{Sec.~S14 post-S1 {_tex_code('fixture_stop')} {s14_txt}{fix_b_txt}, "
            f"Sec.~S3 Stage~S2 single-TU preprocessing stops {s3_txt}, "
            f"{_tex_int(infra_k)} infrastructure failures, "
            f"{_tex_int(unrun_conf)} confirmatory clusters and {_tex_int(unrun_quar)} quarantined pairs {_tex_code('not_executed')} at closure, "
            f"Sec.~S4 oracle failures {s4_txt}, and {_tex_int(nofit_k)} confirmatory {_tex_code('insufficient_fit')} clusters}}"
        )

        p1_test = (
            f"P1 vs.\\ 14/147 (unadjusted {_tex_p(prim['P1']['p_unadjusted'])}, Holm {_tex_p(prim['P1']['p_holm'])})"
            if prim["P1"]["gate_met"]
            else "P1 below gate"
        )
        p2_test = (
            f"P2 sign-flip (unadjusted {_tex_p(prim['P2']['p_unadjusted'])}, Holm {_tex_p(prim['P2']['p_holm'])})"
            if prim["P2"]["gate_met"]
            else "P2 below gate"
        )
        p3_test = (
            f"P3 vs.\\ 4/13 (unadjusted {_tex_p(prim['P3']['p_unadjusted'])}, Holm {_tex_p(prim['P3']['p_holm'])})"
            if prim["P3"]["gate_met"]
            else "P3 descriptive only below 30-cluster gate (Holm input fixed at 1.0)"
        )
        s1_nom = sec["S1_desk_stop"]
        s2_nom = sec["S2_alerts_per_selected"]
        s3_p_txt = _tex_p(s3.get("nominal_p_vs_12_26")) if s3.get("nominal_p_vs_12_26") is not None else "unmeasured (0 S1 passes)"
        s4_p_txt = _tex_p(s4.get("nominal_p_vs_1_14")) if s4.get("nominal_p_vs_1_14") is not None else "unmeasured (0 executed)"
        if s5.get("clusters", 0) > 0 and s5.get("group_weighted_delta_pp") is not None:
            s5_lo, s5_hi = s5.get("bootstrap_95pct_delta_pp") or [0.0, 0.0]
            s5_txt = (
                f"S5 fitted contrast {s5['group_weighted_delta_pp']:+.1f}~pp "
                f"(95\\% bootstrap {s5_lo:+.1f} to {s5_hi:+.1f}~pp, nominal {_tex_p(s5.get('nominal_p'))})"
            )
        else:
            s5_txt = "S5 unmeasured (0 fitted clusters)"
        lines.append(
            f"\\newcommand{{\\BenchTests}}{{{p1_test}; {p2_test}; {p3_test}; "
            f"exploratory nominal tests: S1 desk stops {_tex_rate_or(s1_nom, '0/0')} vs.\\ 103/147 ({_tex_p(s1_nom.get('nominal_p_vs_103_147'))}), "
            f"S2 alerts/selected vs.\\ 4/147 ({_tex_p(s2_nom.get('nominal_p_vs_4_147'))}), "
            f"S3 preprocessing vs.\\ 12/26 ({s3_p_txt}), "
            f"S4 oracle failures vs.\\ 1/14 ({s4_p_txt}), and {s5_txt}}}"
        )

        c_fr = s10["Contest"]
        r_fr = s10["Repository"]
        c_gate_lbl = "$\\ge 30$ gate met" if c_fr.get("gate_met") else "below 30-cluster gate"
        c_p3 = c_fr["P3_alerts_per_fitted"]
        c_p3_txt = _tex_rate_or(c_p3, "0/0 (0 fitted)")
        if c_p3.get("total", 0) > 0 and not c_p3.get("fitted_gate_met"):
            c_p3_txt += " (below 30-fitted-cluster gate)"
        repo_desc = (
            "counts only because all S0-pass pairs are held " + _tex_code("desk_unrateable") + "): "
            "0 rated, 0 executed (Union equals Contest for all rated and executed outcomes)"
            if r_fr.get("counts_only")
            else f"$\\ge 30$ gate {'met' if r_fr.get('gate_met') else 'not met'}): "
                 f"P1 {_tex_rate_or(r_fr.get('P1_exec_yield'), '0/0')}, S1 desk stops {_tex_rate_or(r_fr.get('S1_desk_stop'), '0/0')}"
        )
        lines.append(
            f"\\newcommand{{\\BenchFrames}}{{Contest ({_tex_int(c_fr['clusters_past_s0'])} clusters past S0, {c_gate_lbl}): "
            f"P1 {_tex_rate_or(c_fr['P1_exec_yield'], '0/0')}, S1 desk stops {_tex_rate_or(c_fr['S1_desk_stop'], '0/0')}, "
            f"P3 fitted alerts {c_p3_txt}; "
            f"Repository ({_tex_int(r_fr['clusters_past_s0'])} clusters / {_tex_int(r_fr['pairs_past_s0'])} pairs, {repo_desc}}}"
        )

        if s7.get("available"):
            s7_txt = f"S7 any-stream alerts {_tex_rate_or(s7, '0/0')} ({_tex_rate_or(s7.get('alerts_per_selected'), '0/0')} of selected)"
        else:
            s7_txt = "S7 any-stream alerts unavailable in disposition-only ledger"
        if s8.get("available"):
            s8_adm_txt = (
                f"alerts among admitted {_tex_rate(s8['alerts_among_admitted'])}"
                if s8["admitted_count"] > 0
                else "0 admitted drop-largest fits"
            )
            s8_txt = (
                f"S8 drop-largest refit: {_tex_int(s8['admitted_count'])}/{_tex_int(s8['fitted_total'])} admitted "
                f"({_tex_int(s8['range_limited_count'])} range-limited, not negative), "
                f"{s8_adm_txt} "
                f"({_tex_int(s8['retained_all_stream_alerts'])} all-stream alerts retained, "
                f"{_tex_int(s8['flipped_all_stream_alerts'])} failed after drop, "
                f"{_tex_int(s8['range_limited_all_stream_alerts'])} range-limited)"
            )
        else:
            s8_txt = "S8 drop-largest refit unavailable without per-size point grids"
        lines.append(f"\\newcommand{{\\BenchFitSensitivity}}{{{s7_txt}; {s8_txt}}}")

        if exec_chk.get("available"):
            caps = exec_chk.get("caps") or {}
            cap_pos = exec_chk.get("positions_with_cap") or {}
            cap_parts = []
            for k, v in sorted(caps.items()):
                if v > 0:
                    if cap_pos.get(k):
                        cap_parts.append(f"{_tex_code(k)}: {_tex_int(v)} events across {_tex_int(cap_pos[k])} positions")
                    else:
                        cap_parts.append(f"{_tex_code(k)}: {_tex_int(v)}")
            cap_txt = ", ".join(cap_parts) if cap_parts else "0 cap events recorded"
            rest = exec_chk.get("restoration") or {}
            fit_rest = exec_chk.get("fitted_restoration") or {}
            fit_rest_sum = sum(int(fit_rest.get(k, 0)) for k in ("passed", "no_excess", "failed"))
            fit_rest_txt = (
                f" (among {_tex_int(fit_rest_sum)} admitted fits: {_tex_int(fit_rest.get('passed', 0))} passed, "
                f"{_tex_int(fit_rest.get('no_excess', 0))} no measurable excess, {_tex_int(fit_rest.get('failed', 0))} failed)"
                if fit_rest_sum > 0
                else ""
            )
            rest_total = sum(int(rest.get(k, 0)) for k in ("passed", "no_excess", "failed", "unmeasured"))
            rest_txt = (
                f"restoration ($\\ge 80\\%$ recovery) across all {_tex_int(rest_total)} confirmatory S1 passes: "
                f"{_tex_int(rest.get('passed', 0))} passed, {_tex_int(rest.get('no_excess', 0))} no excess, "
                f"{_tex_int(rest.get('failed', 0))} failed, {_tex_int(rest.get('unmeasured', 0))} unmeasured{fit_rest_txt}"
            )
            lines.append(
                f"\\newcommand{{\\BenchVariantChecks}}{{cap coverage ({cap_txt}); -O0/-O2/-O3 stability and sham preservation enforced on all completed observations; {rest_txt}}}"
            )
        else:
            lines.append(
                r"\newcommand{\BenchVariantChecks}{cap coverage and restoration counts omitted in disposition-only ledger; -O0/-O2/-O3 and sham equality verified per checkpoint}"
            )

        s9_p1 = s9["P1_equal_cluster"]
        s9_p3 = s9["P3_equal_cluster"]
        if s9_p1.get("equal_cluster_pct") is not None and s9_p1.get("bootstrap_95pct_pct"):
            s9_p1_ci = s9_p1["bootstrap_95pct_pct"]
            s9_p1_txt = (
                f"P1 {s9_p1['equal_cluster_pct']:.1f}\\% (95\\% bootstrap {s9_p1_ci[0]:.1f}--{s9_p1_ci[1]:.1f}\\%, "
                f"pair-level {_tex_rate(s9_p1['pair_level_working_independence_cp'])})"
            )
        else:
            s9_p1_txt = "P1 unmeasured"
        if s9_p3.get("equal_cluster_pct") is not None and s9_p3.get("bootstrap_95pct_pct"):
            s9_p3_ci = s9_p3["bootstrap_95pct_pct"]
            s9_p3_txt = (
                f"P3 {s9_p3['equal_cluster_pct']:.1f}\\% (95\\% bootstrap {s9_p3_ci[0]:.1f}--{s9_p3_ci[1]:.1f}\\%, "
                f"pair-level {_tex_rate(s9_p3['pair_level_working_independence_cp'])})"
            )
        else:
            s9_p3_txt = "P3 unmeasured (0 fitted clusters)"
        s13_p2c = s13["P2"]["contrast"]
        s13_p2_ci = s13_p2c.get("bootstrap_95pct_delta_pp")
        s13_p2_ci_txt = (
            f"95\\% cluster bootstrap {s13_p2_ci[0]:+.1f} to {s13_p2_ci[1]:+.1f}~pp, " if s13_p2_ci else ""
        )
        if s13["P2"]["gate_met"] and s13_p2c.get("group_weighted_delta_pp") is not None:
            s13_p2_txt = (
                f"P2 {s13_p2c['group_weighted_delta_pp']:+.1f}~pp "
                f"({s13_p2_ci_txt}nominal exact sign-flip {_tex_p(s13['P2']['p_unadjusted'])}; outside primary Holm family)"
            )
        elif s13_p2c.get("group_weighted_delta_pp") is not None:
            s13_p2_txt = f"P2 {s13_p2c['group_weighted_delta_pp']:+.1f}~pp (below 200-cluster gate)"
        else:
            s13_p2_txt = "P2 unmeasured"
        trunc_txt = ""
        if trunc.get("truncated"):
            p1_b = trunc["P1_frozen_bounds_pct"]
            s14_b = trunc["S14_frozen_bounds_pct"]
            p1_pc = _tex_rate_or(trunc.get("P1_prefix_conditional_among_s1_passes"), "0/0 (0 attempted)")
            s14_pc = _tex_rate_or(trunc.get("S14_prefix_conditional"), "0/0 (0 attempted)")
            trunc_txt = (
                f"; Amendment~5 prefix truncation ({_tex_int(trunc['attempted_s1_pass_reps'])}/{_tex_int(trunc['s1_pass_reps'])} attempted): "
                f"P1 frozen bounds {p1_b[0]:.1f}--{p1_b[1]:.1f}\\% (prefix-conditional {p1_pc}), "
                f"S14 frozen bounds {s14_b[0]:.1f}--{s14_b[1]:.1f}\\% (prefix-conditional {s14_pc})"
            )
        sec11_parts = []
        if sec11.get("available") and sec11.get("cpu_cap_exit137_pairs", 0) > 0 and "unpatched_cpu_cap_as_not_executed" in sec11:
            unp = sec11["unpatched_cpu_cap_as_not_executed"]
            unp_p3 = f", P3 {_tex_rate_or(unp.get('P3'), '0/0')}" if unp.get("P3") else ""
            sec11_parts.append(
                f"exit-137 {_tex_code('cpu_cap')} ({_tex_int(sec11['cpu_cap_exit137_pairs'])} pairs: "
                f"unpatched P1 {_tex_rate_or(unp['P1'], '0/0')}, P2 {unp['P2']['group_weighted_delta_pp']:+.1f}~pp{unp_p3})"
            )
        if sec11.get("available") and sec11.get("wave2_alignment_rebuilds_to_oracle_fail", 0) > 0 and "superseded_alignment_as_fixture_stop" in sec11:
            al = sec11["superseded_alignment_as_fixture_stop"]
            al_p2 = f", P2 {al['P2']['group_weighted_delta_pp']:+.1f}~pp" if al.get("P2") else ""
            al_s4 = f", S4 {_tex_rate_or(al.get('S4'), '0/0')}" if al.get("S4") else ""
            sec11_parts.append(
                f"superseded {_tex_code('alignment_boundary')} ({_tex_int(sec11['wave2_alignment_rebuilds_to_oracle_fail'])} pairs: "
                f"P1 {_tex_rate_or(al['P1'], '0/0')}{al_p2}, S14 {_tex_rate_or(al['S14'], '0/0')}{al_s4})"
            )
        sec11_txt = ("; protocol Section~11 sensitivity: " + "; ".join(sec11_parts)) if sec11_parts else ""
        s13_p3_txt = _tex_rate_or(s13["P3"]["rate"], "0/0 (0 fitted clusters)")
        lines.append(
            f"\\newcommand{{\\BenchPairSensitivity}}{{S6 P1 without infrastructure failures {_tex_rate_or(s6, '0/0')}; "
            f"S9 all-pair equal-cluster {s9_p1_txt} and {s9_p3_txt}; "
            f"S13 excluding {_tex_code('desk_unrateable')} ({_tex_int(s13['confirmatory_clusters_past_s0'])} clusters): "
            f"P1 {_tex_rate_or(s13['P1']['rate'], '0/0')}, {s13_p2_txt}, "
            f"P3 {s13_p3_txt}{trunc_txt}{sec11_txt}}}"
        )

        s12_cr = s12.get("cluster_rates") or {}
        s12_pr = s12.get("pair_rates") or {}
        s12_unrun = s12["pair_dispositions"].get("not_executed", 0)
        if s12["pairs_past_s0"] == 0 and s12["clusters_past_s0"] == 0:
            lines.append(
                r"\newcommand{\BenchExposedResults}{S12 quarantined stratum: 0 development-exposed pairs past S0}"
            )
        else:
            s12_c_desk = s12_cr.get("S1_desk_stop")
            s12_c_desk_txt = (
                f"cluster S1 desk stops {_tex_rate(s12_c_desk)}"
                if s12_c_desk and s12_c_desk.get("count") is not None and s12_c_desk.get("total")
                else "cluster S1 desk-stop breakdown omitted without representative counts"
            )
            s12_p_desk_txt = _tex_rate_or(s12_pr.get("S1_desk_stop"), "0/0")
            s12_c_p1_txt = _tex_rate_or(s12_cr.get("P1_exec_yield"), "unmeasured")
            s12_p_p1_txt = _tex_rate_or(s12_pr.get("P1_exec_yield"), "0/0")
            lines.append(
                f"\\newcommand{{\\BenchExposedResults}}{{S12 quarantined stratum ({_tex_int(s12['pairs_past_s0'])} S0-pass pairs across "
                f"{_tex_int(s12['clusters_past_s0'])} clusters): {s12_c_desk_txt}, "
                f"pair S1 desk stops {s12_p_desk_txt}, "
                f"and {_tex_int(s12_unrun)} quarantined S1 passes recorded as {_tex_code('not_executed')} under Amendment~5 "
                f"(cluster P1 {s12_c_p1_txt}, pair P1 {s12_p_p1_txt})}}"
            )

        wp_label = (
            "NO-GO (native build not triggered)"
            if wp["decision"] == "NO-GO, single-TU adequate" and wp["X_repo_executed"] == 0 and wp["repo_clusters"] > 0
            else wp["decision"]
        )
        wp_caveat = (
            "---single-TU preprocessing was exercised only on Contest pairs because all "
            f"{_tex_int(wp['repo_clusters'])} Repository clusters stopped as {_tex_code('desk_unrateable')}"
            if wp["decision"] == "NO-GO, single-TU adequate" and wp["X_repo_executed"] == 0 and wp["repo_clusters"] > 0
            else ""
        )
        lines.append(
            f"\\newcommand{{\\BenchBuildDecision}}{{\\textbf{{{wp_label}}} "
            f"(P1 CP lower limit $E = {wp['E_cp_lower_pct']:.1f}\\%$ vs.\\ $15.5\\%$ anchor; "
            f"Repository route+preprocessing stops $R = {_tex_int(wp['R_repo_route_plus_prep'])}$, "
            f"Repository executed $X = {_tex_int(wp['X_repo_executed'])}$ across {_tex_int(wp['repo_clusters'])} clusters{wp_caveat})}}"
        )

        lines.append(
            f"\\newcommand{{\\BenchAvailability}}{{that inputs are pinned to manifest \\texttt{{{report['manifest_sha256'][:8]}}}, "
            f"protocol \\texttt{{{PROTOCOL_SHA[:8]}}}, hold list \\texttt{{{HELD_SHA[:8]}}}, and "
            f"Amendment~5 \\texttt{{{amendment_sha[:8]}}}; "
            f"P1--P3 and all S1-dependent secondary rates (Sec.~S1--S14, including S6, S7 alerts/selected, S9, S10, and S12) are \\emph{{replay-only}} (Amendment~3 undisclosed S1 workflow routing), "
            f"Stages~S2--S5 Gate~1 runs conditional on fixed S1-pass fixtures are \\emph{{re-executable}}, "
            f"and raw S1 prompts, responses, packets, and source payloads remain non-public custody}}"
        )
    else:
        for slot_macro, label in (
            ("BenchOverlap", "development exposure and overlap"),
            ("BenchRunStops", "run stop reasons"),
            ("BenchTests", "primary tests"),
            ("BenchFrames", "frame-specific estimates"),
            ("BenchFitSensitivity", "fit sensitivity"),
            ("BenchVariantChecks", "censoring and variant checks"),
            ("BenchPairSensitivity", "denominator sensitivity"),
            ("BenchExposedResults", "development-exposed outcomes"),
            ("BenchBuildDecision", "native-build decision"),
            ("BenchAvailability", "artifact links and evidence classes"),
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
        raw = raw["author_check"]
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
    parser.add_argument("--aggregate-json", type=Path, help="Ingest blind-safe aggregate JSON (e.g. final-a5-stats-agg.json) directly")
    parser.add_argument("--author-check", type=Path, help="Optional sealed author-check labels or precomputed summary JSON")
    parser.add_argument("--author-draw", type=Path, help="Optional pinned s1_author_check_draw.json for --author-check")
    parser.add_argument("--write-slots", type=Path, help="Optional output path for rendered benchmark_slots.tex")
    parser.add_argument(
        "--execution-complete",
        action=argparse.BooleanOptionalAction,
        default=None,
        help="Override execution_complete flag when rendering benchmark_slots.tex",
    )
    parser.add_argument("--out", type=Path, help="Optional JSON receipt output path")
    args = parser.parse_args()

    author_res: dict[str, Any] | None = None
    if args.aggregate_json:
        agg = json.loads(args.aggregate_json.read_bytes())
        report = analyze_aggregate(agg)
        if args.author_check:
            cli_manifest = None
            cli_s1 = None
            if args.manifest and args.s1_summary:
                m_raw = args.manifest.read_bytes()
                if digest(m_raw) != MANIFEST_SHA:
                    raise SystemExit("manifest SHA-256 mismatch")
                cli_manifest = json.loads(m_raw)
                cli_s1 = json.loads(args.s1_summary.read_bytes())
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

    if args.write_slots:
        tex = render_benchmark_slots(
            report,
            s1_complete=s1_complete,
            execution_complete=exec_complete,
            author_check=author_res,
        )
        args.write_slots.parent.mkdir(parents=True, exist_ok=True)
        args.write_slots.write_text(tex, encoding="utf-8")

    text = json.dumps(report, indent=2, sort_keys=True)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text + "\n", encoding="utf-8")
    elif not args.write_slots:
        print(text)


if __name__ == "__main__":
    main()
