"""Unit tests for expansion_analyze.py covering Amendment 5 fixture_stop and
truncation bounds, Amendment 4 indeterminate rules, 147-pair reference sanity checks,
below-gate P3 behavior, secondary analyses S1-S14, §11 sensitivity, blind author check
kappa, JSON/JSONL ledger loading, --aggregate-json CLI mode, and LaTeX macro emission.
"""

from __future__ import annotations

from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "analysis"))
import expansion_analyze as ea


def _make_manifest(n_conf: int = 205, n_quar: int = 4) -> tuple[dict, list[dict]]:
    pairs = []
    # 1 S0 stop
    pairs.append({
        "corpus": "codenet", "id": "s0_dup", "cluster_id": "c_s0", "problem_id": "p_s0",
        "frame": "Contest", "quarantined": False, "intake_stop": "intake_duplicate",
        "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
    })
    holds = []
    for i in range(n_conf):
        is_repo = i < 5
        corpus = "github-performance-fix" if is_repo else "codenet"
        frame = "Repository" if is_repo else "Contest"
        pid = f"p_conf_{i}"
        pairs.append({
            "corpus": corpus, "id": f"id_{i}", "cluster_id": f"cl_{i:04d}", "problem_id": pid,
            "frame": frame, "quarantined": False,
            "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
        })
        if is_repo:
            holds.append({"corpus": corpus, "pair_id": f"id_{i}", "reason": "no_independent_repository_spec"})
    for j in range(n_quar):
        pairs.append({
            "corpus": "pie-validation", "id": f"q_{j}", "cluster_id": "cl_q_synth", "problem_id": "prob_q_synth",
            "frame": "Contest", "quarantined": True,
            "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
        })
    return {"held_out_used": False, "pairs": pairs}, holds


def test_clopper_pearson_matches_147_reference_values():
    r1 = ea.rate_summary(103, 147)
    assert r1["percent"] == 70.1
    assert r1["clopper_pearson_95pct_percent"] == [62.0, 77.3]
    r2 = ea.rate_summary(14, 147)
    assert r2["percent"] == 9.5
    assert r2["clopper_pearson_95pct_percent"] == [5.3, 15.5]
    r3 = ea.rate_summary(4, 13)
    assert r3["percent"] == 30.8
    assert r3["clopper_pearson_95pct_percent"] == [9.1, 61.4]


def test_exact_binomial_and_holm():
    assert ea.exact_binomial_two_sided_p(5, 10, Fraction(1, 2)) == pytest.approx(1.0)
    assert ea.exact_binomial_two_sided_p(0, 10, Fraction(1, 2)) == pytest.approx(2 / 1024)
    adj = ea.holm({"P1": 0.01, "P2": 0.04, "P3": 0.02})
    assert adj["P1"] == pytest.approx(0.03)
    assert adj["P3"] == pytest.approx(0.04)
    assert adj["P2"] == pytest.approx(0.04)


def test_amendment4_indeterminate_and_below_gate_p3():
    manifest, holds = _make_manifest(205, 4)
    disps = {"codenet:s0_dup": "intake_duplicate"}
    for i in range(205):
        if i < 5:
            disps[f"github-performance-fix:id_{i}"] = "desk_unrateable"
        elif i == 5:
            disps[f"codenet:id_{i}"] = "indeterminate"
        elif i < 120:
            disps[f"codenet:id_{i}"] = "desk_excluded"
        elif i < 180:
            disps[f"codenet:id_{i}"] = "not_executed"
        elif i < 190:
            disps[f"codenet:id_{i}"] = "alert"
        else:
            disps[f"codenet:id_{i}"] = "no_alert"
    for j in range(4):
        disps[f"pie-validation:q_{j}"] = "not_executed"

    flow = ea.flow_table(manifest["pairs"], disps)
    assert flow["Union"]["drawn"] == 210
    assert flow["Union"]["s0_intake_stop"] == 1
    assert flow["Union"]["s0_intake_duplicate"] == 1
    assert flow["Union"]["s0_intake_unretrievable"] == 0
    assert flow["Union"]["s1_indeterminate"] == 1
    assert flow["Union"]["s1_desk_unrateable"] == 5
    assert flow["Union"]["s1_desk_stop_total"] == 120  # 5 unrateable + 1 indeterminate + 114 excluded
    assert flow["Union"]["not_executed"] == 64

    res = ea.analyze_cohort(manifest, disps)
    assert res["confirmatory_clusters_past_s0"] == 205
    # P1: 25 executed (10 alert + 15 no_alert) / 205; indeterminate & not_executed count as not executed
    assert res["P1"]["gate_met"] is True
    assert res["P1"]["rate"]["count"] == 25
    assert res["P1"]["rate"]["total"] == 205
    # P2: 120 desk stops (including 1 indeterminate + 5 unrateable) - 25 executed = +95 / 205
    assert res["P2"]["gate_met"] is True
    assert res["P2"]["contrast"]["group_weighted_delta_pp"] == round(100 * 95 / 205, 1)
    assert res["P2"]["p_holm"] < 1e-10
    # P3: only 25 fitted (< 30 gate) -> descriptive only, indeterminate NOT in fitted denominator
    assert res["P3"]["gate_met"] is False
    assert res["P3"]["rate"]["count"] == 10
    assert res["P3"]["rate"]["total"] == 25
    assert res["P3"]["p_unadjusted"] is None
    assert res["P3"]["reporting_mode"] == "descriptive_only_below_30_fitted_clusters"
    assert res["indeterminate_counts"]["confirmatory_reps"] == 1

    # S13 drops the 5 desk_unrateable pairs but retains indeterminate in denominator (200 clusters)
    s13 = ea.analyze_cohort(manifest, disps, drop_unrateable=True)
    assert s13["confirmatory_clusters_past_s0"] == 200
    assert s13["indeterminate_counts"]["confirmatory_reps"] == 1


def test_author_check_kappa_and_fixture_inventory(monkeypatch: pytest.MonkeyPatch):
    synth_h = ea.digest(b"prob_q_synth")[:16]
    monkeypatch.setattr(ea, "PATH_B_CASE_PY_HASHES", frozenset({synth_h}))
    monkeypatch.setattr(ea, "PATH_B_EXECUTED_PIE_HASHES", ea.PATH_B_HIST_EXEC_HASHES | {synth_h})
    manifest, holds = _make_manifest(10, 4)
    s1 = {}
    for row in manifest["pairs"]:
        if row.get("intake_stop"):
            continue
        k = ea.pair_key(row)
        if any(f'{h["corpus"]}:{h["pair_id"]}' == k for h in holds):
            continue
        if row["quarantined"]:
            s1[k] = {"status": "pass", "bucket": None, "reason": None}
        elif row["id"] == "id_5":
            s1[k] = {"status": "indeterminate", "bucket": None, "reason": None}
        elif row["id"] in ("id_6", "id_7"):
            s1[k] = {"status": "pass", "bucket": None, "reason": None}
        else:
            s1[k] = {"status": "desk_excluded", "bucket": "contract", "reason": "fixed_contract"}

    inv = ea.fixture_readiness_inventory(manifest, s1, holds)
    assert inv["confirmatory_passes"]["total_pass_pairs"] == 2
    assert inv["confirmatory_passes"]["oracle_workload_readiness"]["net_new_oracle_and_workload_needed"]["problems"] == 2
    assert inv["quarantined_passes"]["total_pass_pairs"] == 4
    assert inv["quarantined_passes"]["oracle_workload_readiness"]["reusable_path_b_cases_py"]["problems"] == 1

    # Author check agreement on 4 synthetic pairs
    draw = [{"corpus": "codenet", "pair_id": f"id_{i}"} for i in range(5, 9)]
    m_map = {ea.pair_key(r): r for r in manifest["pairs"]}
    author = {f"codenet:id_{i}": s1[f"codenet:id_{i}"] for i in range(5, 9)}
    ag = ea.author_check_agreement(draw, m_map, s1, author)
    assert ag["descriptive_only"] is True
    assert ag["exact"]["raw_agreement_pct"] == 100.0
    assert ag["exact"]["cohens_kappa"] == 1.0


def test_render_benchmark_slots_keeps_unexecuted_fields_pending():
    manifest, holds = _make_manifest(10, 4)
    disps = {"codenet:s0_dup": "intake_duplicate"}
    s1 = {}
    for row in manifest["pairs"]:
        if row.get("intake_stop"):
            continue
        k = ea.pair_key(row)
        if any(f'{h["corpus"]}:{h["pair_id"]}' == k for h in holds):
            disps[k] = "desk_unrateable"
            continue
        s1[k] = {"status": "pass" if row["quarantined"] else "desk_excluded", "bucket": None if row["quarantined"] else "contract", "reason": None if row["quarantined"] else "fixed_contract"}
        disps[k] = "not_executed" if row["quarantined"] else "desk_excluded"
    report = {
        "manifest_sha256": ea.MANIFEST_SHA,
        "amendment_sha256": ea.AMENDMENT_5_SHA,
        "flow_table": ea.flow_table(manifest["pairs"], disps),
        "primary_all_post_s0": ea.analyze_cohort(manifest, disps),
        "S13_without_desk_unrateable": ea.analyze_cohort(manifest, disps, drop_unrateable=True),
        "fixture_inventory": ea.fixture_readiness_inventory(manifest, s1, holds),
    }
    tex = ea.render_benchmark_slots(report, s1_complete=True, execution_complete=False)
    assert r"\BenchSlot{P1 execution yield}" in tex
    assert r"\newcommand{\BenchFlowDeskU}{10}" in tex
    assert r"\newcommand{\BenchFlowFixtureU}{\BenchCell}" in tex
    assert r"\newcommand{\BenchFlowAlertU}{\BenchCell}" in tex
    assert r"\newcommand{\BenchSOneBatchesN}{" in tex
    assert f"% Amendment 5 SHA-256: {ea.AMENDMENT_5_SHA}" in tex
    assert "Amendment 4 SHA-256" not in tex
    # Dynamic flow values instead of hardcoded 23/1,000 and 844
    assert r"\newcommand{\BenchIntakeStopsN}{1}" in tex
    assert r"\newcommand{\BenchSOPassN}{14}" in tex
    assert r"\newcommand{\BenchRateablePairsN}{9}" in tex
    assert r"\newcommand{\BenchRepoDeskUnratN}{5}" in tex


def test_amendment5_fixture_stop_accounting():
    manifest, _ = _make_manifest(205, 0)
    disps = {"codenet:s0_dup": "intake_duplicate"}
    for i in range(205):
        if i < 5:
            disps[f"github-performance-fix:id_{i}"] = "desk_unrateable"
        elif i < 120:
            disps[f"codenet:id_{i}"] = "desk_excluded"
        elif i < 150:
            disps[f"codenet:id_{i}"] = "fixture_stop"
        elif i < 165:
            disps[f"codenet:id_{i}"] = "not_executed"
        elif i < 180:
            disps[f"codenet:id_{i}"] = "alert"
        else:
            disps[f"codenet:id_{i}"] = "no_alert"

    flow = ea.flow_table(manifest["pairs"], disps)
    assert flow["Union"]["s2_fixture_stop"] == 30
    assert flow["Union"]["s1_desk_stop_total"] == 120

    res = ea.analyze_cohort(manifest, disps)
    # P1: 40 executed (15 alert + 25 no_alert) / 205; fixture_stop & not_executed count as not executed
    assert res["P1"]["rate"]["count"] == 40
    assert res["P1"]["rate"]["total"] == 205
    # P2: primary desk stops (120) - executed (40) = +80 / 205 (fixture_stop keeps desk=0, exec=0)
    assert res["P2"]["contrast"]["group_weighted_delta_pp"] == round(100 * 80 / 205, 1)
    # P3: 15 alerts / 40 fitted (fixture_stop excluded from fitted denominator)
    assert res["P3"]["rate"]["count"] == 15
    assert res["P3"]["rate"]["total"] == 40
    assert res["P3"]["gate_met"] is True
    # S14: 30 fixture_stops / 85 post-desk S1 passes (30 + 15 + 40) with truncated prefix K=70 < 85
    s14 = res["secondary"]["S14_fixture_stops_after_s1_pass"]
    assert s14["count"] == 30
    assert s14["total"] == 85
    assert s14["truncated"] is True
    assert s14["attempted_count"] == 70
    assert s14["not_executed_count"] == 15
    assert s14["prefix_conditional"]["count"] == 30
    assert s14["prefix_conditional"]["total"] == 70
    assert s14["frozen_bounds_pct"] == [round(100 * 30 / 85, 1), round(100 * 45 / 85, 1)]

def test_secondary_analyses_s1_to_s14_and_section11():
    # Build manifest with multi-pair confirmatory clusters so S9 equal-cluster differs from pair-level
    pairs = [
        {
            "corpus": "codenet", "id": "s0_unret", "cluster_id": "c_s0", "problem_id": "p_s0",
            "frame": "Contest", "quarantined": False, "intake_stop": "intake_unretrievable",
            "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
        }
    ]
    holds = []
    # 5 Repository held pairs across 4 clusters (cl_repo_0 has 2 pairs)
    for i in range(5):
        cid = "cl_repo_0" if i < 2 else f"cl_repo_{i}"
        pairs.append({
            "corpus": "github-performance-fix", "id": f"repo_{i}", "cluster_id": cid, "problem_id": f"pr_{i}",
            "frame": "Repository", "quarantined": False,
            "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
        })
        holds.append({"corpus": "github-performance-fix", "pair_id": f"repo_{i}", "reason": "no_independent_repository_spec"})

    # 200 Contest confirmatory clusters (cl_0000 has 3 pairs -> multi-pair S9 test!)
    for i in range(200):
        n_m = 3 if i == 0 else 1
        for m in range(n_m):
            pairs.append({
                "corpus": "codenet", "id": f"c_{i}_{m}", "cluster_id": f"cl_{i:04d}", "problem_id": f"pc_{i}",
                "frame": "Contest", "quarantined": False,
                "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
            })
    # 6 quarantined pairs across 3 clusters (2 pairs per cluster)
    for q in range(6):
        pairs.append({
            "corpus": "pie-validation", "id": f"q_{q}", "cluster_id": f"qcl_{q // 2}", "problem_id": f"pq_{q // 2}",
            "frame": "Contest", "quarantined": True,
            "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
        })
    manifest = {"held_out_used": False, "pairs": pairs}

    disps = {"codenet:s0_unret": "intake_unretrievable"}
    desk_meta = {}
    ledger_rows = {}
    for i in range(5):
        disps[f"github-performance-fix:repo_{i}"] = "desk_unrateable"

    # Full 6-point ladder (admitted drop-largest) vs 4-point ladder (range-limited drop-largest)
    pts_alert_keep = [[1, 10, 10], [2, 30, 10], [4, 90, 10], [8, 270, 10], [16, 810, 10], [32, 2430, 10]]
    pts_alert_range_limited = [[1, 10, 10], [2, 30, 10], [4, 90, 10], [8, 270, 10]]
    pts_no_alert = [[1, 10, 10], [2, 11, 10], [4, 12, 10], [8, 13, 10], [16, 14, 10], [32, 15, 10]]
    pts_any_only = [[1, 10, 10], [2, 25, 10], [4, 60, 10], [8, 150, 10], [16, 400, 10], [32, 1000, 10]]

    cl0_rep = ea.select_representatives([r for r in pairs if r["cluster_id"] == "cl_0000"])["cl_0000"]["id"]
    for i in range(200):
        n_m = 3 if i == 0 else 1
        for m in range(n_m):
            k = f"codenet:c_{i}_{m}"
            if i == 0:
                # Representative of cl_0000 is alert, while its 2 siblings are desk_excluded
                if f"c_{i}_{m}" == cl0_rep:
                    disps[k] = "alert"
                    ledger_rows[k] = {
                        "id": k, "terminal": "alert",
                        "fits": {"s1": {"slope": 1.6, "largest_ratio": 243.0}, "s2": {"slope": 1.6, "largest_ratio": 243.0}},
                        "points": {"s1": pts_alert_keep, "s2": pts_alert_keep},
                        "restoration": {"s1": [{"size": 32, "passes": True}]},
                    }
                else:
                    disps[k] = "desk_excluded"
                    desk_meta[k] = {"status": "desk_excluded", "bucket": "contract", "reason": "fixed_contract"}
            elif i <= 90:
                disps[k] = "desk_excluded"
                bkt = "source" if i <= 20 else ("route" if i <= 25 else "contract")
                desk_meta[k] = {"status": "desk_excluded", "bucket": bkt, "reason": "test_reason"}
            elif i <= 105:
                disps[k] = "fixture_stop"
                ledger_rows[k] = {"id": k, "terminal": "fixture_stop", "fixture_stop": {"bucket": "contract", "reason": "alignment_boundary"}}
            elif i <= 115:
                disps[k] = "support_boundary_closed"
            elif i <= 120:
                disps[k] = "execution_oracle_failure"
            elif i <= 122:
                disps[k] = "insufficient_fit"
                ledger_rows[k] = {
                    "id": k, "terminal": "insufficient_fit",
                    "measurements": [{"step": ["execute", 0, "target", "O2"], "status": "capped", "caps": ["cpu_cap"], "exit": 137}],
                }
            elif i <= 125:
                # 3 alerts with only 4 sizes -> range-limited on drop-largest
                disps[k] = "alert"
                ledger_rows[k] = {
                    "id": k, "terminal": "alert",
                    "fits": {"s1": {"slope": 1.6, "largest_ratio": 27.0}},
                    "points": {"s1": pts_alert_range_limited},
                    "restoration": {"s1": [{"size": 8, "passes": True}]},
                }
            elif i <= 135:
                disps[k] = "alert"
                ledger_rows[k] = {
                    "id": k, "terminal": "alert",
                    "fits": {"s1": {"slope": 1.6, "largest_ratio": 243.0}},
                    "points": {"s1": pts_alert_keep},
                    "restoration": {"s1": [{"size": 32, "passes": True}]},
                }
            elif i <= 145:
                # Any-stream alert (s1 passes, s2 flat) -> terminal no_alert
                disps[k] = "no_alert"
                ledger_rows[k] = {
                    "id": k, "terminal": "no_alert",
                    "fits": {"s1": {"slope": 1.3, "largest_ratio": 100.0}, "s2": {"slope": 0.1, "largest_ratio": 1.5}},
                    "points": {"s1": pts_any_only, "s2": pts_no_alert},
                    "restoration": {"s1": []},
                }
            elif i <= 190:
                disps[k] = "no_alert"
                ledger_rows[k] = {
                    "id": k, "terminal": "no_alert",
                    "fits": {"s1": {"slope": 0.1, "largest_ratio": 1.5}},
                    "points": {"s1": pts_no_alert},
                    "restoration": {"s1": []},
                }
            else:
                disps[k] = "not_executed"

    for q in range(6):
        qk = f"pie-validation:q_{q}"
        if q < 3:
            disps[qk] = "desk_excluded"
            desk_meta[qk] = {"status": "desk_excluded", "bucket": "contract", "reason": "fixed_contract"}
        else:
            disps[qk] = "not_executed"

    res = ea.analyze_cohort(manifest, disps, desk_meta=desk_meta, ledger_rows=ledger_rows)
    sec = res["secondary"]

    # S1: 4 repo reps + 90 contest reps = 94 / 204 clusters + nominal p vs 103/147 + bucket split
    s1 = sec["S1_desk_stop"]
    assert s1["count"] == 94
    assert s1["total"] == 204
    assert s1["ref"] == "103/147"
    assert s1["nominal_p_vs_103_147"] == pytest.approx(ea.exact_binomial_two_sided_p(94, 204, Fraction(103, 147)))
    assert s1["bucket_counts_reps"] == {"contract": 65, "desk_unrateable": 4, "route": 5, "source": 20}

    # S3: 10 preprocessing stops / 110 post_desk reps, nominal p vs 12/26
    s3 = sec["S3_preprocessing_stops_after_desk"]
    assert s3["count"] == 10
    assert s3["total"] == 110
    assert s3["nominal_p_vs_12_26"] == pytest.approx(ea.exact_binomial_two_sided_p(10, 110, Fraction(12, 26)))

    # S4: 5 oracle failures / (5 oracle + 2 insufficient_fit + 69 fitted = 76 executed), nominal p vs 1/14
    s4 = sec["S4_oracle_failures_among_executed"]
    assert s4["count"] == 5
    assert s4["total"] == 76
    assert s4["nominal_p_vs_1_14"] == pytest.approx(ea.exact_binomial_two_sided_p(5, 76, Fraction(1, 14)))

    # S5: 14 alerts - 55 no_alert across 69 fitted clusters
    s5 = sec["S5_alert_minus_no_alert_among_fits"]
    assert s5["clusters"] == 69
    assert s5["gate_met"] is True
    assert s5["group_weighted_delta_pp"] == round(100 * (14 - 55) / 69, 1)
    assert s5["nominal_p"] < 1e-5

    # S7: 14 all-stream + 10 any-stream-only = 24 / 69 fitted
    s7 = sec["S7_any_stream_alerts"]
    assert s7["available"] is True
    assert s7["count"] == 24
    assert s7["total"] == 69

    # S8: 66 admitted (69 - 3 range-limited), 3 range-limited (the 3 4-point alerts), 11 retained
    s8 = sec["S8_drop_largest_refit"]
    assert s8["available"] is True
    assert s8["fitted_total"] == 69
    assert s8["admitted_count"] == 66
    assert s8["range_limited_count"] == 3
    assert s8["retained_all_stream_alerts"] == 11
    assert s8["range_limited_all_stream_alerts"] == 3
    assert s8["flipped_all_stream_alerts"] == 0

    # S9: cl_0000 has 1/3 executed (0.3333) while pair-level has 76/207 (vs rep 76/204)
    s9 = sec["S9_all_pair_equal_cluster"]
    assert s9["P1_equal_cluster"]["clusters"] == 204
    assert s9["P1_equal_cluster"]["pairs"] == 207
    assert s9["P1_equal_cluster"]["equal_cluster_pct"] == round(100 * (75 + 1 / 3) / 204, 1)
    assert s9["P1_equal_cluster"]["pair_level_working_independence_cp"]["total"] == 207

    # S10: Contest vs Repository
    assert sec["S10_per_frame"]["Contest"]["clusters_past_s0"] == 200
    assert sec["S10_per_frame"]["Repository"]["clusters_past_s0"] == 4
    assert sec["S10_per_frame"]["Repository"]["counts_only"] is True

    # S12: Quarantined cluster + pair rates
    s12 = sec["S12_quarantined"]
    assert s12["pairs_past_s0"] == 6
    assert s12["clusters_past_s0"] == 3
    assert s12["cluster_rates"]["S1_desk_stop"]["total"] == 3
    assert s12["pair_rates"]["S1_desk_stop"]["count"] == 3
    assert s12["pair_rates"]["S1_desk_stop"]["total"] == 6
    assert s12["pair_rates"]["S1_desk_stop"]["equal_cluster"]["equal_cluster_pct"] == 50.0

    # §11 exit-137 cpu_cap sensitivity (2 pairs)
    sec11 = res["section_11_sensitivity"]
    assert sec11["available"] is True
    assert sec11["cpu_cap_exit137_pairs"] == 2
    assert sec11["unpatched_cpu_cap_as_not_executed"]["P1"]["count"] == 74

    # Truncation bounds (9 not_executed i=191..199 out of 110 post-desk)
    tr = res["truncation_sensitivity"]
    assert tr["truncated"] is True
    assert tr["not_executed_reps"] == 9
    assert tr["P1_prefix_conditional_among_s1_passes"]["total"] == 101


def test_latex_scientific_p_values_and_macro_completeness(tmp_path: Path):
    assert ea._tex_p(1.57e-6) == r"$p = 1.57 \times 10^{-6}$"
    assert ea._tex_p(4.94e-14, prefix="") == r"$4.94 \times 10^{-14}$"
    assert ea._tex_p(0.388) == "$p = 0.388$"
    assert ea._tex_p(0.0015) == "$p = 0.0015$"

    build_dir = Path(__file__).resolve().parents[1] / "manuscript"
    tex_src = (build_dir / "paired_mechanism.tex").read_text(encoding="utf-8")
    grouped_src = (build_dir / "grouped_statistics_macros.tex").read_text(encoding="utf-8")

    # Verify aggregate ingestion + full execution_complete=True slot rendering has 0 missing/orphan macros & 0 raw e-
    agg = {
        "manifest_sha256": ea.MANIFEST_SHA,
        "held_list_sha256": ea.HELD_SHA,
        "held_out_used": False,
        "execution_complete": True,
        "flow_table": {
            "Contest": {"drawn": 956, "s0_intake_stop": 12, "s1_desk_stop_total": 557, "s1_desk_excluded": 411, "s1_desk_blocked": 43, "s1_desk_unrateable": 100, "s1_indeterminate": 3, "s2_fixture_stop": 20, "s2_preprocessing_stop": 0, "s3_infra_failure": 0, "not_executed": 204, "s3_oracle_failure": 20, "s4_no_fit": 6, "s5_no_alert": 120, "s5_alert": 17},
            "Repository": {"drawn": 44, "s0_intake_stop": 11, "s1_desk_stop_total": 33, "s1_desk_excluded": 0, "s1_desk_blocked": 0, "s1_desk_unrateable": 33, "s1_indeterminate": 0, "s2_fixture_stop": 0, "s2_preprocessing_stop": 0, "s3_infra_failure": 0, "not_executed": 0, "s3_oracle_failure": 0, "s4_no_fit": 0, "s5_no_alert": 0, "s5_alert": 0},
            "Union": {"drawn": 1000, "s0_intake_stop": 23, "s0_intake_duplicate": 12, "s0_intake_unretrievable": 11, "s1_desk_stop_total": 590, "s1_desk_excluded": 411, "s1_desk_blocked": 43, "s1_desk_unrateable": 133, "s1_indeterminate": 3, "s2_fixture_stop": 20, "s2_preprocessing_stop": 0, "s3_infra_failure": 0, "not_executed": 204, "s3_oracle_failure": 20, "s4_no_fit": 6, "s5_no_alert": 120, "s5_alert": 17},
        },
        "confirmatory": {
            "clusters_past_s0": 476, "pairs_past_s0": 477,
            "rep_dispositions": {"desk_excluded": 152, "desk_blocked": 21, "desk_unrateable": 118, "indeterminate": 2, "fixture_stop": 20, "execution_oracle_failure": 20, "insufficient_fit": 6, "no_alert": 120, "alert": 17},
            "pair_dispositions": {"desk_excluded": 152, "desk_blocked": 21, "desk_unrateable": 119, "indeterminate": 2, "fixture_stop": 20, "execution_oracle_failure": 20, "insufficient_fit": 6, "no_alert": 120, "alert": 17},
            "s1_buckets_reps": {"contract": 160, "source": 11, "route": 2, "desk_unrateable": 118, "indeterminate": 2},
            "fixture_stop_buckets": {"contract": 12, "source": 7, "route": 1},
            "s7_any_stream_alerts": 22,
            "s8_drop_largest": {"admitted": 130, "range_limited": 7, "alerts_among_admitted": 12, "retained_all_stream_alerts": 12, "range_limited_all_stream_alerts": 2, "flipped_all_stream_alerts": 3},
            "execution_checks": {"available": True, "caps": {"tick_cap": 3, "cpu_cap": 2}, "restoration": {"passed": 55, "no_excess": 60, "failed": 22, "unmeasured": 46}},
            "section_11_disclosures": {"cpu_cap_exit137_pairs": 2, "wave2_alignment_rebuilds_to_oracle_fail": 4},
        },
        "quarantined": {
            "pairs_past_s0": 500, "clusters_past_s0": 54, "unrateable_clusters": 5,
            "pair_dispositions": {"desk_excluded": 259, "desk_blocked": 22, "desk_unrateable": 14, "indeterminate": 1, "not_executed": 204},
        },
    }
    report = ea.analyze_aggregate(agg)
    author = {
        "unblinded_count": 0,
        "exact": {"n_pairs": 50, "n_clusters": 48, "raw_agreement_count": 40, "raw_agreement_pct": 80.0, "cohens_kappa": 0.712, "cluster_bootstrap_95pct_kappa": [0.551, 0.855]},
        "bucket": {"n_pairs": 50, "n_clusters": 48, "raw_agreement_count": 43, "raw_agreement_pct": 86.0, "cohens_kappa": 0.781, "cluster_bootstrap_95pct_kappa": [0.620, 0.910]},
    }
    slots_tex = ea.render_benchmark_slots(report, s1_complete=True, execution_complete=True, author_check=author)
    assert not re.search(r"\d+e[+-]\d+", slots_tex), "Found raw scientific notation in LaTeX macros"
    assert r"\times 10^{" in slots_tex
    body_tex = slots_tex.split(r"\newcommand{\BenchCell}", 1)[1].split("\n", 1)[1]
    assert r"\BenchSlot{" not in body_tex
    assert r"\BenchCell" not in body_tex
    assert f"% Amendment 5 SHA-256: {ea.AMENDMENT_5_SHA}" in slots_tex

    used_bench = set(re.findall(r"\\(Bench[A-Za-z0-9]+)", tex_src))
    def_bench = set(re.findall(r"\\newcommand\{\\(Bench[A-Za-z0-9]+)\}", slots_tex))
    assert used_bench - def_bench == set(), f"Missing macros: {used_bench - def_bench}"
    assert def_bench - used_bench == {"BenchCell", "BenchSlot"}, f"Orphan macros: {def_bench - used_bench}"
    used_grouped = set(re.findall(r"\\(Grouped[A-Za-z0-9]+)", tex_src))
    def_grouped = set(re.findall(r"\\newcommand\{\\(Grouped[A-Za-z0-9]+)\}", grouped_src))
    assert used_grouped - def_grouped == set()

    if shutil.which("pdflatex") and shutil.which("bibtex"):
        tex_tmp = tmp_path / "full_s11_build"
        tex_tmp.mkdir()
        for fname in (
            "paired_mechanism.tex", "paired_mechanism.bib", "grouped_statistics_macros.tex",
            "fig_pipeline_funnel.pdf", "fig_s1_desk_taxonomy.pdf", "fig_scaling_landscape.pdf", "fig_alert_trajectories.pdf", "fig_manski_tipping.pdf",
        ):
            shutil.copy2(build_dir / fname, tex_tmp / fname)
        (tex_tmp / "benchmark_slots.tex").write_bytes(slots_tex.encode("utf-8"))
        for cmd in (
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["bibtex", "paired_mechanism"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
        ):
            subprocess.run(cmd, cwd=tex_tmp, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        log = (tex_tmp / "paired_mechanism.log").read_text(encoding="utf-8", errors="ignore")
        assert "Overfull" not in log
        assert "Undefined" not in log
        assert "Warning" not in log
        assert ".pk" not in log


def test_load_ledger_json_and_jsonl(tmp_path: Path):
    # 1. Pretty-printed JSON list
    p_list = tmp_path / "ledger_pretty.json"
    p_list.write_text(json.dumps([{"id": "codenet:a", "terminal": "alert"}, {"id": "codenet:b", "terminal": "no_alert"}], indent=2), encoding="utf-8")
    d1, r1 = ea.load_ledger(p_list)
    assert d1 == {"codenet:a": "alert", "codenet:b": "no_alert"}
    assert "codenet:a" in r1

    # 2. Pretty-printed JSON object with rows
    p_rows = tmp_path / "ledger_rows.json"
    p_rows.write_text(json.dumps({"rows": [{"corpus": "codenet", "id": "x", "terminal": "fixture_stop"}]}, indent=2), encoding="utf-8")
    d2, _ = ea.load_ledger(p_rows)
    assert d2 == {"codenet:x": "fixture_stop"}

    # 3. JSONL with header line
    p_jsonl = tmp_path / "ledger.jsonl"
    p_jsonl.write_text(
        json.dumps({"schema": "eapg.expansion.checkpoint.v1"}) + "\n"
        + json.dumps({"id": "codenet:c", "terminal": "insufficient_fit"}) + "\n",
        encoding="utf-8",
    )
    d3, _ = ea.load_ledger(p_jsonl)
    assert d3 == {"codenet:c": "insufficient_fit"}

    # 4. Rejects unresolved terminal=None
    p_none = tmp_path / "ledger_none.jsonl"
    p_none.write_text(json.dumps({"id": "codenet:bad", "terminal": None}) + "\n", encoding="utf-8")
    with pytest.raises(ValueError, match="Unresolved terminal disposition"):
        ea.load_ledger(p_none)


def test_cli_aggregate_json_and_author_check_and_write_slots(tmp_path: Path):
    agg = {
        "manifest_sha256": ea.MANIFEST_SHA,
        "held_list_sha256": ea.HELD_SHA,
        "held_out_used": False,
        "flow_table": {
            "Contest": {"drawn": 956, "s0_intake_stop": 12, "s1_desk_stop_total": 557, "s1_desk_excluded": 411, "s1_desk_blocked": 43, "s1_desk_unrateable": 100, "s1_indeterminate": 3, "s2_fixture_stop": 15, "s2_preprocessing_stop": 0, "s3_infra_failure": 0, "not_executed": 204, "s3_oracle_failure": 15, "s4_no_fit": 5, "s5_no_alert": 130, "s5_alert": 18},
            "Repository": {"drawn": 44, "s0_intake_stop": 11, "s1_desk_stop_total": 33, "s1_desk_unrateable": 33},
            "Union": {"drawn": 1000, "s0_intake_stop": 23, "s0_intake_duplicate": 12, "s0_intake_unretrievable": 11, "s1_desk_stop_total": 590, "s1_desk_excluded": 411, "s1_desk_blocked": 43, "s1_desk_unrateable": 133, "s1_indeterminate": 3, "s2_fixture_stop": 15, "s2_preprocessing_stop": 0, "s3_infra_failure": 0, "not_executed": 204, "s3_oracle_failure": 15, "s4_no_fit": 5, "s5_no_alert": 130, "s5_alert": 18},
        },
        "confirmatory": {
            "clusters_past_s0": 476, "pairs_past_s0": 477,
            "rep_dispositions": {"desk_excluded": 152, "desk_blocked": 21, "desk_unrateable": 118, "indeterminate": 2, "fixture_stop": 15, "execution_oracle_failure": 15, "insufficient_fit": 5, "no_alert": 130, "alert": 18},
            "pair_dispositions": {"desk_excluded": 152, "desk_blocked": 21, "desk_unrateable": 119, "indeterminate": 2, "fixture_stop": 15, "execution_oracle_failure": 15, "insufficient_fit": 5, "no_alert": 130, "alert": 18},
            "s1_buckets_reps": {"contract": 160, "source": 11, "route": 2, "desk_unrateable": 118, "indeterminate": 2},
            "s7_any_stream_alerts": 24,
            "s8_drop_largest": {"admitted": 140, "range_limited": 8, "alerts_among_admitted": 16, "retained_all_stream_alerts": 16, "range_limited_all_stream_alerts": 1, "flipped_all_stream_alerts": 1},
        },
        "quarantined": {
            "pairs_past_s0": 500, "clusters_past_s0": 54, "unrateable_clusters": 5,
            "pair_dispositions": {"desk_excluded": 259, "desk_blocked": 22, "desk_unrateable": 14, "indeterminate": 1, "not_executed": 204},
        },
    }
    agg_path = tmp_path / "final-a5-stats-agg.json"
    agg_path.write_text(json.dumps(agg), encoding="utf-8")
    author_path = tmp_path / "author.json"
    author_path.write_text(json.dumps({
        "unblinded_keys": [],
        "unblinded_count": 0,
        "exact": {"n_pairs": 50, "n_clusters": 48, "raw_agreement_count": 41, "raw_agreement_pct": 82.0, "cohens_kappa": 0.740, "cluster_bootstrap_95pct_kappa": [0.580, 0.870]},
        "bucket": {"n_pairs": 50, "n_clusters": 48, "raw_agreement_count": 44, "raw_agreement_pct": 88.0, "cohens_kappa": 0.810, "cluster_bootstrap_95pct_kappa": [0.660, 0.930]},
    }), encoding="utf-8")
    out_json = tmp_path / "receipt.json"
    out_tex = tmp_path / "benchmark_slots.tex"

    script = Path(__file__).resolve().parents[1] / "analysis" / "expansion_analyze.py"
    subprocess.run(
        [
            sys.executable, "-B", str(script),
            "--aggregate-json", str(agg_path),
            "--author-check", str(author_path),
            "--write-slots", str(out_tex),
            "--out", str(out_json),
        ],
        check=True,
    )
    rec = json.loads(out_json.read_text(encoding="utf-8"))
    assert rec["amendment_sha256"] == ea.AMENDMENT_5_SHA
    assert rec["primary_all_post_s0"]["P1"]["rate"]["count"] == 168
    assert rec["primary_all_post_s0"]["secondary"]["S14_fixture_stops_after_s1_pass"]["count"] == 15
    assert rec["author_check"]["exact"]["cohens_kappa"] == 0.740
    tex = out_tex.read_text(encoding="utf-8")
    assert r"\BenchFlowFixtureU}{15}" in tex
    assert r"\BenchAuthExactK}{0.740}" in tex
    assert r"\BenchNoFitN}{5}" in tex
    assert not re.search(r"\d+e[+-]\d+", tex)
    assert r"\BenchConclusionTakeaway" not in tex
    desk_line = [ln for ln in tex.splitlines() if r"\BenchDeskContrast" in ln][0]
    assert r"6.25 \times 10^{-9}" in desk_line

    # Full pdflatex compile smoke check if pdflatex is installed
    if shutil.which("pdflatex") and shutil.which("bibtex"):
        build_src = Path(__file__).resolve().parents[1] / "manuscript"
        tex_tmp = tmp_path / "tex_build"
        tex_tmp.mkdir()
        for fname in (
            "paired_mechanism.tex", "paired_mechanism.bib", "grouped_statistics_macros.tex",
            "fig_pipeline_funnel.pdf", "fig_s1_desk_taxonomy.pdf", "fig_scaling_landscape.pdf", "fig_alert_trajectories.pdf", "fig_manski_tipping.pdf",
        ):
            shutil.copy2(build_src / fname, tex_tmp / fname)
        (tex_tmp / "benchmark_slots.tex").write_bytes(tex.encode("utf-8"))
        for cmd in (
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["bibtex", "paired_mechanism"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paired_mechanism.tex"],
        ):
            subprocess.run(cmd, cwd=tex_tmp, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        log = (tex_tmp / "paired_mechanism.log").read_text(encoding="utf-8", errors="ignore")
        assert "Overfull" not in log
        assert "Undefined" not in log
        assert "Warning" not in log
        assert ".pk" not in log


def test_cli_manifest_ledger_pretty_and_author_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    manifest, holds = _make_manifest(10, 4)
    s1 = {}
    ledger_list = []
    for row in manifest["pairs"]:
        if row.get("intake_stop"):
            continue
        k = ea.pair_key(row)
        if any(f'{h["corpus"]}:{h["pair_id"]}' == k for h in holds):
            continue
        if row["quarantined"]:
            s1[k] = {"status": "pass", "bucket": None, "reason": None}
            ledger_list.append({"id": k, "terminal": "not_executed"})
        elif row["id"] == "id_5":
            s1[k] = {"status": "indeterminate", "bucket": None, "reason": None}
            ledger_list.append({"id": k, "terminal": "indeterminate"})
        elif row["id"] == "id_6":
            s1[k] = {"status": "pass", "bucket": None, "reason": None}
            ledger_list.append({"id": k, "terminal": "fixture_stop", "fixture_stop": {"bucket": "contract", "reason": "fixed_contract"}})
        elif row["id"] == "id_7":
            s1[k] = {"status": "pass", "bucket": None, "reason": None}
            ledger_list.append({"id": k, "terminal": "alert", "fits": {"s1": {"slope": 1.5, "largest_ratio": 20.0}}, "points": {"s1": [[1, 10, 10], [2, 20, 10], [4, 40, 10], [8, 80, 10], [16, 160, 10]]}, "restoration": {"s1": [{"size": 16, "passes": True}]}})
        else:
            s1[k] = {"status": "desk_excluded", "bucket": "contract", "reason": "fixed_contract"}
            ledger_list.append({"id": k, "terminal": "desk_excluded"})

    m_path = tmp_path / "manifest.json"
    h_path = tmp_path / "holds.json"
    s1_path = tmp_path / "s1.json"
    led_path = tmp_path / "ledger_pretty.json"
    auth_path = tmp_path / "author_raw.json"
    draw_path = tmp_path / "author_draw.json"
    out_json = tmp_path / "out.json"
    out_slots = tmp_path / "slots.tex"

    m_bytes = json.dumps(manifest).encode("utf-8")
    h_bytes = json.dumps(holds).encode("utf-8")
    draw_pairs = [{"corpus": "codenet", "pair_id": f"id_{i}"} for i in range(5, 9)]
    d_bytes = json.dumps(draw_pairs).encode("utf-8")

    m_path.write_bytes(m_bytes)
    h_path.write_bytes(h_bytes)
    s1_path.write_text(json.dumps(s1), encoding="utf-8")
    led_path.write_text(json.dumps(ledger_list, indent=2), encoding="utf-8")
    draw_path.write_bytes(d_bytes)
    auth_path.write_text(json.dumps({"author_labels": {f"codenet:id_{i}": s1[f"codenet:id_{i}"] for i in range(5, 9)}, "unblinded_keys": []}), encoding="utf-8")

    monkeypatch.setattr(ea, "MANIFEST_SHA", ea.digest(m_bytes))
    monkeypatch.setattr(ea, "HELD_SHA", ea.digest(h_bytes))
    monkeypatch.setattr(ea, "AUTHOR_DRAW_SHA", ea.digest(d_bytes))
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "expansion_analyze.py",
            "--manifest", str(m_path),
            "--holds", str(h_path),
            "--s1-summary", str(s1_path),
            "--ledger", str(led_path),
            "--author-check", str(auth_path),
            "--author-draw", str(draw_path),
            "--write-slots", str(out_slots),
            "--out", str(out_json),
        ],
    )
    ea.main()
    rep = json.loads(out_json.read_text(encoding="utf-8"))
    assert rep["amendment_sha256"] == ea.AMENDMENT_5_SHA
    assert rep["flow_table"]["Union"]["s2_fixture_stop"] == 1
    assert rep["primary_all_post_s0"]["secondary"]["S8_drop_largest_refit"]["admitted_count"] == 1
    assert rep["author_check"]["exact"]["cohens_kappa"] == 1.0
    tex = out_slots.read_text(encoding="utf-8")
    assert r"\newcommand{\BenchFlowFixtureU}{1}" in tex
    assert r"\newcommand{\BenchAuthExactK}{1.000}" in tex


def test_regressions_aggregate_aliases_s12_honesty_and_zero_denominators(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    # 1. Zero-denominator execution_complete=True must never leak \BenchCell into macro bodies
    manifest, holds = _make_manifest(205, 0)
    disps = {"codenet:s0_dup": "intake_duplicate"}
    s1 = {}
    for row in manifest["pairs"]:
        if row.get("intake_stop"):
            continue
        k = ea.pair_key(row)
        if any(f'{h["corpus"]}:{h["pair_id"]}' == k for h in holds):
            disps[k] = "desk_unrateable"
            continue
        s1[k] = {"status": "desk_excluded", "bucket": "contract", "reason": "fixed_contract"}
        disps[k] = "desk_excluded"
    zero_rep = {
        "manifest_sha256": ea.MANIFEST_SHA,
        "amendment_sha256": ea.AMENDMENT_5_SHA,
        "flow_table": ea.flow_table(manifest["pairs"], disps),
        "primary_all_post_s0": ea.analyze_cohort(manifest, disps),
        "S13_without_desk_unrateable": ea.analyze_cohort(manifest, disps, drop_unrateable=True),
        "fixture_inventory": ea.fixture_readiness_inventory(manifest, s1, holds),
    }
    zero_tex = ea.render_benchmark_slots(zero_rep, s1_complete=True, execution_complete=True)
    zero_body = zero_tex.split(r"\newcommand{\BenchCell}", 1)[1].split("\n", 1)[1]
    assert r"\BenchCell" not in zero_body
    assert r"\newcommand{\BenchQuarPairsN}{0}" in zero_tex

    # 2. Aggregate aliases (Distinct Union, top-level fallback, analyze_cohort-shaped S8, S10 repo_clusters, S12 missing rep_dispositions)
    agg = {
        "manifest_sha256": ea.MANIFEST_SHA,
        "held_list_sha256": ea.HELD_SHA,
        "held_out_used": False,
        "flow_table": {
            "Contest": {"drawn": 956, "intake_duplicate": 12, "intake_unretrievable": 0, "desk_excluded": 411, "desk_blocked": 43, "desk_unrateable": 100, "indeterminate": 3, "fixture_stop": 20, "support_boundary_closed": 0, "execution_infrastructure_failure": 0, "not_executed": 204, "execution_oracle_failure": 20, "insufficient_fit": 6, "no_alert": 120, "alert": 17},
            "Repository": {"drawn": 44, "s0_intake_stop": 11, "s1_desk_stop": 33, "desk_unrateable": 33},
            "Distinct Union": {"drawn": 1000, "s0_intake_stop": 23, "s0_intake_duplicate": 12, "s0_intake_unretrievable": 11, "s1_desk_stop_total": 590, "s1_desk_excluded": 411, "s1_desk_blocked": 43, "s1_desk_unrateable": 133, "s1_indeterminate": 3, "s2_fixture_stop": 20, "s2_preprocessing_stop": 0, "s3_infra_failure": 0, "not_executed": 204, "s3_oracle_failure": 20, "s4_no_fit": 6, "s5_no_alert": 120, "s5_alert": 17},
        },
        "s7_any_stream_alerts": {"count": 22, "total": 137},
        "s8_drop_largest": {"admitted_count": 130, "range_limited_count": 7, "alerts_among_admitted": {"count": 12, "total": 130}, "retained_all_stream_alerts": 12, "range_limited_all_stream_alerts": 2, "flipped_all_stream_alerts": 3},
        "section_11_disclosures": {"cpu_cap_exit137_pairs": 2, "wave2_alignment_rebuilds_to_oracle_fail": 4},
        "confirmatory": {
            "clusters_past_s0": 470, "pairs_past_s0": 477,
            "repo_clusters_past_s0": 32,
            "rep_dispositions": {"desk_excluded": 150, "desk_blocked": 20, "desk_unrateable": 115, "indeterminate": 2, "fixture_stop": 20, "execution_oracle_failure": 20, "insufficient_fit": 6, "no_alert": 120, "alert": 17},
            "pair_dispositions": {"desk_excluded": 152, "desk_blocked": 21, "desk_unrateable": 119, "indeterminate": 2, "fixture_stop": 20, "execution_oracle_failure": 20, "insufficient_fit": 6, "no_alert": 120, "alert": 17},
            "s9_all_pair_equal_cluster": {
                "P1_equal_cluster": {"clusters": 470, "pairs": 477, "pair_weighted_pct": 34.2, "equal_cluster_pct": 34.7, "bootstrap_95pct_pct": [30.0, 39.0], "pair_level_working_independence_cp": ea.rate_summary(163, 477)},
                "P3_equal_cluster": {"clusters": 137, "pairs": 137, "pair_weighted_pct": 12.4, "equal_cluster_pct": 12.4, "bootstrap_95pct_pct": [7.0, 18.0], "pair_level_working_independence_cp": ea.rate_summary(17, 137)},
            },
        },
        "quarantined": {
            "pairs_past_s0": 500, "clusters_past_s0": 54, "unrateable_clusters": 5,
            "pair_dispositions": {"desk_excluded": 259, "desk_blocked": 22, "desk_unrateable": 14, "indeterminate": 1, "not_executed": 204},
        },
    }
    rep = ea.analyze_aggregate(agg)
    prim = rep["primary_all_post_s0"]
    s13 = rep["S13_without_desk_unrateable"]
    # S8 exact analyze_cohort schema worked
    assert prim["secondary"]["S8_drop_largest_refit"]["available"] is True
    assert prim["secondary"]["S8_drop_largest_refit"]["admitted_count"] == 130
    # S10 derived contest_clusters = 470 - 32 = 438
    assert prim["secondary"]["S10_per_frame"]["Contest"]["clusters_past_s0"] == 438
    # S13 recomputed S9 instead of copying 470-cluster S9
    assert s13["secondary"]["S9_all_pair_equal_cluster"]["P1_equal_cluster"]["clusters"] == 355
    # S12 did NOT fabricate 0/54 = 0.0% cluster desk stops when rep_dispositions omitted
    assert prim["secondary"]["S12_quarantined"]["cluster_rates"]["S1_desk_stop"]["count"] is None
    assert prim["secondary"]["S12_quarantined"]["cluster_rates"]["P1_exec_yield"]["count"] == 0
    # §11 alignment rebuild S4 computed
    assert prim["section_11_sensitivity"]["superseded_alignment_as_fixture_stop"]["S4"]["count"] == 16

    # 3. load_ledger rejects None in dispositions wrapper and supports pair_id/final_disposition
    p_bad_disp = tmp_path / "bad_disp.json"
    p_bad_disp.write_text(json.dumps({"dispositions": {"codenet:a": None}}), encoding="utf-8")
    with pytest.raises(ValueError, match="Unresolved terminal disposition"):
        ea.load_ledger(p_bad_disp)
    p_single = tmp_path / "single.json"
    p_single.write_text(json.dumps({"corpus": "codenet", "pair_id": "x1", "final_disposition": "alert"}), encoding="utf-8")
    d_single, _ = ea.load_ledger(p_single)
    assert d_single == {"codenet:x1": "alert"}

    # 4. analyze_cohort multi-pair §11 exit-137 uses representative count + capped points ignored in S8 + ledger["desk"] fallback
    m_multi, _ = _make_manifest(10, 0)
    # Add 1 extra pair inside cl_0005 (non-representative) with cpu_cap exit 137
    m_multi["pairs"].append({
        "corpus": "codenet", "id": "id_5_sib", "cluster_id": "cl_0005", "problem_id": "p_conf_5",
        "frame": "Contest", "quarantined": False,
        "slow": {"files": [{"path": "s.cpp"}]}, "fast": {"files": [{"path": "f.cpp"}]},
    })
    d_multi = {"codenet:s0_dup": "intake_duplicate"}
    l_multi = {}
    for row in m_multi["pairs"]:
        if row.get("intake_stop"):
            continue
        k = ea.pair_key(row)
        if row["frame"] == "Repository":
            d_multi[k] = "desk_unrateable"
        elif row["id"] == "id_5_sib":
            d_multi[k] = "insufficient_fit"
            l_multi[k] = {"id": k, "terminal": "insufficient_fit", "measurements": [{"step": ["execute", 0, "target", "O2"], "caps": ["cpu_cap"], "exit": 137}]}
        elif row["id"] == "id_6":
            d_multi[k] = "alert"
            l_multi[k] = {
                "id": k, "terminal": "alert",
                "points": {"s1": [
                    {"size": 1, "target": 10, "reference": 10},
                    {"size": 2, "target": 30, "reference": 10},
                    {"size": 4, "target": 90, "reference": 10},
                    {"size": 8, "target": 270, "reference": 10},
                    {"size": 16, "target": 810, "reference": 10},
                    {"size": 32, "target": None, "reference": None, "capped": True},
                ]},
                "restoration": {"s1": [{"size": 16, "passes": True}]},
            }
        else:
            d_multi[k] = "desk_excluded"
            l_multi[k] = {"id": k, "terminal": "desk_excluded", "desk": {"status": "desk_excluded", "bucket": "source", "reason": "forced_avx"}}
    # Ensure id_5 (rep of cl_0005) is desk_excluded, while sibling id_5_sib had exit 137
    res_multi = ea.analyze_cohort(m_multi, d_multi, ledger_rows=l_multi)
    assert res_multi["secondary"]["S1_desk_stop"]["bucket_counts_reps"]["source"] > 0
    assert res_multi["secondary"]["S8_drop_largest_refit"]["admitted_count"] == 1
    assert res_multi["section_11_sensitivity"]["cpu_cap_exit137_pairs"] == 1
    assert res_multi["section_11_sensitivity"]["cpu_cap_exit137_reps"] == 0
    assert res_multi["section_11_sensitivity"]["unpatched_cpu_cap_as_not_executed"]["P1"]["count"] == 1

    # 5. CLI --aggregate-json + raw --author-check + --manifest + --s1-summary AND figure generator integration
    m_cli, h_cli = _make_manifest(10, 4)
    s1_cli = {}
    for row in m_cli["pairs"]:
        if row.get("intake_stop"):
            continue
        k = ea.pair_key(row)
        if any(f'{h["corpus"]}:{h["pair_id"]}' == k for h in h_cli):
            continue
        s1_cli[k] = {"status": "pass" if row["id"] in ("id_6", "id_7") or row["quarantined"] else "desk_excluded", "bucket": None if row["id"] in ("id_6", "id_7") or row["quarantined"] else "contract", "reason": None if row["id"] in ("id_6", "id_7") or row["quarantined"] else "fixed_contract"}
    m_b = json.dumps(m_cli).encode("utf-8")
    d_draw = [{"corpus": "codenet", "pair_id": f"id_{i}"} for i in range(5, 9)]
    d_b = json.dumps(d_draw).encode("utf-8")
    m_p, s1_p, agg_p, auth_p, draw_p, out_p = (
        tmp_path / "m.json", tmp_path / "s1.json", tmp_path / "agg.json", tmp_path / "auth.json", tmp_path / "draw.json", tmp_path / "out_cli.json"
    )
    m_p.write_bytes(m_b)
    s1_p.write_text(json.dumps(s1_cli), encoding="utf-8")
    agg["manifest_sha256"] = ea.digest(m_b)
    agg_p.write_text(json.dumps(agg), encoding="utf-8")
    draw_p.write_bytes(d_b)
    auth_p.write_text(json.dumps({"author_labels": {f"codenet:id_{i}": s1_cli[f"codenet:id_{i}"] for i in range(5, 9)}}), encoding="utf-8")
    monkeypatch.setattr(ea, "MANIFEST_SHA", ea.digest(m_b))
    monkeypatch.setattr(ea, "AUTHOR_DRAW_SHA", ea.digest(d_b))
    monkeypatch.setattr(
        sys, "argv",
        [
            "expansion_analyze.py", "--aggregate-json", str(agg_p),
            "--author-check", str(auth_p), "--author-draw", str(draw_p),
            "--manifest", str(m_p), "--s1-summary", str(s1_p), "--out", str(out_p),
        ],
    )
    ea.main()
    cli_rep = json.loads(out_p.read_text(encoding="utf-8"))
    assert cli_rep["author_check"]["exact"]["cohens_kappa"] == 1.0

    # Verify generate_figures.py plot_pipeline_funnel consumes the receipt cleanly
    if importlib.util.find_spec("matplotlib") is not None:
        import generate_figures as gf
        gf.plot_pipeline_funnel(cli_rep, tmp_path / "fig1_test")
        assert (tmp_path / "fig1_test.pdf").is_file()


def test_ingest_live_final_a5_stats_agg():
    """Verify ingestion of final-a5-stats-agg.json and author-check-50-agg.json."""
    here = Path(__file__).resolve().parent
    data_dir = Path(__file__).resolve().parents[1] / "data"
    agg_path = data_dir / "final-a5-stats-agg.json"
    if not agg_path.is_file():
        pytest.skip("final-a5-stats-agg.json not present")
    raw = json.loads(agg_path.read_text(encoding="utf-8"))
    rep = ea.analyze_aggregate(raw)
    prim = rep["primary_all_post_s0"]
    sec = prim["secondary"]
    s13 = rep["S13_without_desk_unrateable"]
    assert rep["amendment_sha256"] == ea.AMENDMENT_5_SHA
    assert prim["P1"]["rate"]["count"] == 149 and prim["P1"]["rate"]["total"] == 476
    assert prim["P2"]["contrast"]["group_weighted_delta_pp"] == 30.3
    assert prim["P2"]["contrast"]["bootstrap_95pct_delta_pp"] == [22.1, 38.4]
    assert prim["P3"]["rate"]["count"] == 6 and prim["P3"]["rate"]["total"] == 124
    assert prim["P3"]["gate_met"] is True
    assert sec["S1_desk_stop"]["count"] == 293 and sec["S1_desk_stop"]["total"] == 476
    assert sec["S4_oracle_failures_among_executed"]["count"] == 17
    assert sec["S7_any_stream_alerts"]["count"] == 11
    assert sec["S8_drop_largest_refit"]["admitted_count"] == 123
    assert sec["S8_drop_largest_refit"]["alerts_among_admitted"]["count"] == 5
    assert sec["S14_fixture_stops_after_s1_pass"]["count"] == 32
    assert s13["P2"]["contrast"]["group_weighted_delta_pp"] == 7.3
    assert "wp_p1" not in prim
    assert sec["S10_per_frame"]["Repository"]["clusters_past_s0"] == 32
    assert sec["S10_per_frame"]["Repository"]["pairs_past_s0"] == 33
    assert sec["S10_per_frame"]["Repository"]["counts_only"] is True

    author_path = data_dir / "author-check-50-agg.json"
    if author_path.is_file():
        auth = ea._load_author_check_cli(author_path, draw_path=None, manifest=None, s1_summary=None)
        assert auth["exact"]["raw_agreement_count"] == 13
        assert auth["exact"]["cohens_kappa"] == 0.163
        assert auth["bucket"]["raw_agreement_count"] == 24
        assert auth["bucket"]["cohens_kappa"] == 0.154
        slots = ea.render_benchmark_slots(rep, s1_complete=True, execution_complete=True, author_check=auth)
        body = slots.split(r"\newcommand{\BenchCell}", 1)[1].split("\n", 1)[1]
        assert r"\BenchSlot" not in body
        assert r"\BenchCell" not in body


def test_forensics_anon_replay_claims_and_literal_guard(tmp_path: Path):
    """Verify full per-point anonymous-measurements replay, paper_claims.json, and literal/citation guards."""
    repo_root = Path(__file__).resolve().parents[1]
    data_dir = repo_root / "data"

    agg_p = data_dir / "final-a5-stats-agg.json"
    auth_p = data_dir / "author-check-50-agg.json"
    for_p = data_dir / "alert-and-fit-forensics-agg.json"
    anon_p = data_dir / "anonymous-measurements.json"
    man_p = data_dir / "freeze" / "manifest-expanded.json"
    assert for_p.is_file() and anon_p.is_file() and man_p.is_file()

    rep = ea.analyze_aggregate(json.loads(agg_p.read_bytes()))
    auth = ea._load_author_check_cli(auth_p, draw_path=None, manifest=None, s1_summary=None)
    man = json.loads(man_p.read_bytes())
    forensics = ea.verify_anon_and_forensics(
        json.loads(for_p.read_bytes()),
        json.loads(anon_p.read_bytes()),
        rep,
        auth,
        manifest=man,
    )
    assert forensics["verified_from_anon_measurements"] is True
    assert len(forensics["six_alerts"]) == 6
    assert forensics["fitted_124_forensics"]["baseline_screens_124"]["B3_total_ticks_c0_plus_c1_dual"]["alerts"] == 5
    assert forensics["b1_fp_decomposition"] == {
        "flat_constant_factor": 12,
        "negative_slope_precomp": 5,
        "positive_subthreshold": 6,
        "s7_stream_selective": 3,
    }
    # Forensic regression assertions: 4-way missing partition, -O0-only caps, SA3, Cook's D, censoring, B1-B5 Holm, IRR direction
    md_o0 = forensics["missing_decomposition"]["O0_O2_O3"]
    assert md_o0["capped"] + md_o0["oracle_abort"] + md_o0["overlay_fixture_stop"] + md_o0["infra_failure"] == md_o0["missing_total"] == 1294
    md_sh = forensics["missing_decomposition"]["target_vs_sham"]
    assert md_sh["capped"] + md_sh["oracle_abort"] + md_sh["overlay_fixture_stop"] + md_sh["infra_failure"] == md_sh["missing_total"] == 967
    assert forensics["cap_mode_breakdown"]["cpu_cap_o0_only_points"] == 5
    assert forensics["cap_mode_breakdown"]["cpu_cap_total_points"] == 7
    assert rep["primary_all_post_s0"]["secondary"]["S3_preprocessing_stops_after_desk"]["total"] == 154
    assert rep["primary_all_post_s0"]["secondary"]["S12_quarantined"]["cluster_rates"]["S1_desk_stop"]["clopper_pearson_95pct_percent"] == [45.0, 72.4]
    assert forensics["insufficient_fit_breakdown"]["censoring_upper_p3"]["total"] == 126
    assert forensics["insufficient_fit_breakdown"]["censoring_worst_p3"]["count"] == 8
    assert forensics["insufficient_fit_breakdown"]["b3_all_non_oracle_exec"]["count"] == 5
    assert forensics["insufficient_fit_breakdown"]["b3_all_non_oracle_exec"]["total"] == 132
    assert forensics["six_alerts_robust_diagnostics"]["per_position"]["3"]["c0_stream_cooks_d"][0] > 2.0
    mcn_h5 = forensics["exact_comparisons"]["mcnemar_screens_vs_b0_holm5"]
    assert mcn_h5["B1"] < 1e-6 and mcn_h5["B5"] > 0.05 and mcn_h5["B4"] > 0.05
    assert forensics["exact_comparisons"]["fisher_two_sided"]["S3"] == pytest.approx(5.8168199e-12, rel=1e-4)
    assert forensics["exact_comparisons"]["holm_primary_finite_sample"]["P3"] == pytest.approx(0.00763127, rel=1e-3)
    cfa = forensics["chronological_failure_audit"]
    assert cfa["oracle_prior_process_failure_positions"] == [27, 29]
    assert cfa["other_noncap_failure_positions"] == [71, 107, 116, 141, 167]
    assert cfa["rc_0_stderr_count"] == 1
    assert cfa["rc_134_sigabrt_count"] == 2
    assert cfa["rc_139_sigsegv_count"] == 4
    assert cfa["counters_ge_2_pow_64"] == 0
    assert cfa["fitted_masked_failure_count"] == 0
    assert md_o0["o2_o3_agree_on_o0_capped"] == 12 and md_o0["o2_o3_disagree_on_o0_capped"] == 0
    pr2 = forensics["fit_124_taxonomy"]["pair_level_r2"]
    assert pr2["all_zero_var_pairs"] == 52 and pr2["defined_r2_pairs"] == 72
    assert pr2["worst_stream_median_r2"] == pytest.approx(0.738, abs=0.002)
    assert pr2["alert_worst_stream_median_r2"] == pytest.approx(0.9994, abs=0.001)
    assert forensics["exact_comparisons"]["fisher_two_sided"]["P3_pilot_12cl"] == pytest.approx(0.00564, rel=1e-2)
    assert forensics["exact_comparisons"]["fisher_two_sided"]["P3_pilot_12cl_conserv"] == pytest.approx(0.03291, rel=1e-2)
    assert forensics["exact_comparisons"]["fisher_two_sided"]["SA3_incl_orig_compile_fail"] == pytest.approx(1.272e-9, rel=1e-2)
    assert forensics["exact_comparisons"]["pilot_neff_sensitivity"]["n_eff_30"]["p1_p"] == pytest.approx(0.0128, rel=2e-2)
    assert forensics["insufficient_fit_breakdown"]["cpu_cap_fitted_positions"] == [90, 99, 139]
    assert forensics["insufficient_fit_breakdown"]["censoring_plus_cpucap_fisher_p"] == pytest.approx(0.03546, rel=1e-2)
    assert forensics["insufficient_fit_breakdown"]["censoring_worst_fisher_conserv"] == pytest.approx(0.05601, rel=1e-2)
    assert forensics["insufficient_fit_breakdown"]["censoring_plus_cpucap_excl_flat_n"] == 9
    assert forensics["insufficient_fit_breakdown"]["censoring_plus_cpucap_fisher_conserv_p"] == pytest.approx(0.10565, rel=1e-2)
    assert forensics["exact_comparisons"]["joint_conserv_holm_3"]["P1"] == pytest.approx(0.02563, rel=1e-2)
    assert forensics["exact_comparisons"]["joint_conserv_holm_3"]["P3"] == pytest.approx(0.03291, rel=1e-2)
    ofb = forensics["oracle_failure_breakdown"]
    assert ofb["invalid_output_mode_exits"] == {"plain:exit_0": 12, "ubsan:exit_1": 5}
    assert ofb["plain_reference"] == 3 and ofb["ubsan_only_reference"] == 2 and ofb["ubsan_invalid_reference"] == 3
    assert ofb["plain_segv_and_ubsan_count"] == 1 and ofb["plain_segv_and_ubsan_pos"] == 29
    assert ofb["pos27_o0_sigabrt_o2_clean"] is True
    o0_rlx = forensics["o0_cpu_cap_relaxation"]
    assert o0_rlx["o0_only_cap_points_n"] == 5 and o0_rlx["affected_pairs_n"] == 3 and o0_rlx["p3_delta"] == 0 and o0_rlx["sa7_delta"] == 0
    assert o0_rlx["per_position"]["90"]["o0_only_points"] == 2
    sub_f = forensics["six_alerts_robust_diagnostics"]["spawn_floor_subtracted"]
    assert forensics["six_alerts_robust_diagnostics"]["realized_cpu_core_n"] == 2
    assert forensics["six_alerts_robust_diagnostics"]["plain_sub_500_core_n"] == 1
    assert forensics["six_alerts_robust_diagnostics"]["o2_sub_500_core_n"] == 2
    assert forensics["six_alerts_robust_diagnostics"]["min_ref_plain_core_n"] == 2
    assert forensics["six_alerts_robust_diagnostics"]["min_ref_o2_core_n"] == 2
    assert forensics["six_alerts_robust_diagnostics"]["o2_minus_plain_s0_ms"]["n"] == 18
    assert sub_f["175"]["all_streams_pass"] is True and sub_f["13"]["all_streams_pass"] is False and sub_f["13"]["streams_dual_pass"] == 2
    assert sub_f["13"]["o2_all_streams_pass"] is True and sub_f["94"]["all_streams_pass"] is False and sub_f["97"]["o2_streams_dual_pass"] == 1
    assert forensics["six_alerts_robust_diagnostics"]["fd_wrapper_overhead_ms"]["n"] == 72
    assert forensics["restoration_forensics_124"]["non_exact_c1_inflation"] == 0
    assert forensics["restoration_forensics_124"]["all_point_excess_fail_n"] == 0
    assert forensics["restoration_forensics_124"]["all_point_r1_infl_n"] == 0
    assert forensics["restoration_forensics_124"]["all_point_nonreg_r0_fail_positions"] == [18, 44]
    assert sum(forensics["restoration_forensics_124"]["non_exact_pass_regimes"].values()) == 14
    assert forensics["exact_comparisons"]["pilot_neff_sensitivity"]["p1_tip_neff_ge_05"] == 19
    rtot = forensics["restoration_total_ticks_124"]
    assert rtot["pass"] == 62 and rtot["no_excess"] == 49 and rtot["fail"] == 13 and rtot["c0_fail_to_tot_pass"] == 2
    q1z = forensics["fit_124_taxonomy"]["q1_zero_t0_eq_q0_positions"]
    assert len(q1z) == 10 and 174 in q1z and 178 in q1z
    assert 91 in forensics["fit_124_taxonomy"]["t1_lt_q1_positions"] and 175 in forensics["fit_124_taxonomy"]["t1_lt_q1_positions"]
    c1h = {h["position"]: h for h in forensics["fit_124_taxonomy"]["c1_only_hits"]}
    assert len(c1h) == 2 and c1h[47]["stream"] == "W2" and c1h[11]["stream"] == "W3"
    irr_s = forensics["s1_irr_stratified"]
    assert irr_s["overall"]["binary_matrix"] == [[3, 19], [3, 25]]
    assert irr_s["confirmatory"]["binary_matrix"] == [[1, 8], [3, 8]]
    assert irr_s["author_rejected_pass_exec_ci"]["count"] == 7 and irr_s["author_rejected_pass_exec_ci"]["total"] == 8
    mb = irr_s["manski_bounds"]
    assert mb["plugin_theta_ci_pct"] == [4.9, 49.6]
    assert mb["plugin_sa13_y_half_width_pp"] == pytest.approx(1.6, abs=0.1)
    assert mb["plugin_sa13_two_step_y_half_width_pp"] == pytest.approx(0.8, abs=0.1)
    assert mb["plugin_theta_delta_se_diff_pp"] < 0.1
    assert mb["plugin_theta_joint_rect_ci_pct"] == [4.5, 52.9]
    assert mb["plugin_theta_joint_jeffreys_ci_pct"] == [6.8, 46.1]
    assert rep["primary_all_post_s0"]["secondary"]["S9_all_pair_equal_cluster"]["P1_equal_cluster"]["bootstrap_95pct_pct"] == [27.1, 35.5]
    assert forensics["restoration_forensics_124"]["all_point_max_bound_fail_n"] == 0
    assert mb["p3_tipping"]["oracle_vs_4_13"]["min_k"] == 9 and mb["p3_tipping"]["s1_vs_4_13"]["min_k"] == 8
    assert mb["p3_tipping"]["oracle_adv_vs_4_13"]["min_k"] == 8 and mb["p3_tipping"]["oracle_adv_vs_3_12_conserv"]["min_k"] == 2
    deg_irr = ea._irr_from_3x3({"pass": {"pass": 5}})
    assert deg_irr["bucket_kappa"] == 1.0 and deg_irr["binary_kappa"] == 1.0

    slots_tex = ea.render_benchmark_slots(
        rep, s1_complete=True, execution_complete=True, author_check=auth, forensics=forensics, manifest=man
    )
    assert "32 Repo held at S1" in slots_tex
    assert r"\newcommand{\BenchPlainSubCoreN}{1}" in slots_tex
    assert r"\newcommand{\BenchOtwoSubCoreN}{2}" in slots_tex
    assert r"\newcommand{\BenchPosFourSevenCOneStream}{\texttt{W2}}" in slots_tex
    assert r"\newcommand{\BenchPosElevenCOneStream}{\texttt{W3}}" in slots_tex
    assert r"\newcommand{\BenchPThreeOracleAdvTipN}{8}" in slots_tex
    assert r"\newcommand{\BenchSAThirteenFpTipN}{6}" in slots_tex
    assert r"\newcommand{\BenchPThreeFpTipConservN}{20}" in slots_tex
    assert r"\newcommand{\BenchPThreeFpTipFullN}{57}" in slots_tex
    assert r"\newcommand{\BenchAuthConfFitRejFrac}{6/7 = 85.7\%}" in slots_tex
    assert r"\newcommand{\BenchOracleCoordN}{6}" in slots_tex
    assert r"\BenchWaveTwoAlignN" not in slots_tex
    assert r"\BenchConclusionTakeaway" not in slots_tex
    assert r"2.03 \times 10^{-11}" in [ln for ln in slots_tex.splitlines() if r"\BenchDeskContrast" in ln][0]
    assert r"\newcommand{\BenchAuthPassStopN}{19}" in slots_tex
    assert r"\newcommand{\BenchAuthStopPassN}{3}" in slots_tex
    assert r"\newcommand{\BenchAuthQuarRev}{0/16 = 0.0\%}" in slots_tex
    assert r"\newcommand{\BenchPosSevenSevenLogRSq}{1.000}" in slots_tex
    assert r"\newcommand{\BenchEnvSAFourRange}{7.7--11.6\%}" in slots_tex
    assert r"\newcommand{\BenchPosOneSixFourTotSlope}{0.0002}" in slots_tex
    assert r"\newcommand{\BenchAuthConfBowkerQ}{8.00}" in slots_tex
    assert r"\newcommand{\BenchAuthConfBowkerExactP}{$p = 0.041$}" in slots_tex
    assert r"\newcommand{\BenchAuthAllBowkerExactP}{$p = 1.55 \times 10^{-4}$}" in slots_tex
    assert r"\newcommand{\BenchCensorWorstFisherP}{$p = 0.015$}" in slots_tex
    assert r"\newcommand{\BenchCorpusAlertFisherP}{$p = 1.000$}" in slots_tex
    assert r"\newcommand{\BenchRestExactCopyPct}{70.2\%}" in slots_tex
    assert r"\newcommand{\BenchFileCapMB}{8\,\text{MiB}}" in slots_tex
    assert r"\newcommand{\BenchOLSMinRSq}{0.6584}" in slots_tex
    assert r"\newcommand{\BenchSAThreeCrossFrameP}{$p = 5.82 \times 10^{-12}$}" in slots_tex
    assert r"x-frame (4/183 comp.)" in slots_tex
    assert r"P3 [1.6, 8.9]\%" in slots_tex
    assert r"toggles 0.082--0.203" in slots_tex
    assert r"\textbf{P1}\,$^{\ddagger}$" in slots_tex
    assert r"\textbf{SA3}\,$^{\ddagger}$" in slots_tex
    assert r"& 2 & 65 &" in slots_tex
    assert r"[$-0.031$, 0.326]" in slots_tex
    assert r"\newcommand{\BenchManskiYOneStepHalfPP}{" in slots_tex
    assert r"\newcommand{\BenchManskiYTwoStepHalfPP}{" in slots_tex
    assert r"\newcommand{\BenchPfStderrN}{1}" in slots_tex
    assert r"\newcommand{\BenchPfSigabrtN}{2}" in slots_tex
    assert r"\newcommand{\BenchPfSigsegvN}{4}" in slots_tex
    assert r"\newcommand{\BenchRestTotPassN}{62}" in slots_tex
    assert r"\newcommand{\BenchFinHolmPThree}{$p_H = 0.0076$}" in slots_tex
    assert r"2.56\text{M}$\times$" in slots_tex
    assert r"\checkmark & \checkmark \\" in slots_tex
    # Zero raw p\d{5}/s\d{9} upstream IDs in analyzer or test suite
    leak_re = re.compile(r"\b(?:p\d{5}|s\d{9})\b")
    assert not leak_re.search(Path(ea.__file__).read_text(encoding="utf-8"))
    assert not leak_re.search(Path(__file__).read_text(encoding="utf-8"))
    final_rec = json.loads((data_dir / "final_receipt.json").read_bytes())
    assert "mcnemar_screens_vs_b0_holm5" in (final_rec.get("forensics") or {}).get("exact_comparisons", {})
    assert final_rec["primary_all_post_s0"]["secondary"]["S8_drop_largest_refit"]["any_stream_alerts_among_admitted"]["count"] == 10
    assert "execution_policy_checks" in (final_rec.get("author_check") or {})
    assert "s1_run_window" in (final_rec.get("forensics") or {})

    if importlib.util.find_spec("matplotlib") is not None:
        import generate_figures as gf
        gf.plot_scaling_landscape(json.loads(anon_p.read_bytes()), forensics, tmp_path / "fig_scaling_landscape")
    grouped_p = repo_root / "manuscript" / "grouped_statistics_macros.tex"
    claims = ea.build_paper_claims(
        slots_tex,
        agg_sha=ea.digest(agg_p.read_bytes()),
        author_sha=ea.digest(auth_p.read_bytes()),
        forensics_sha=ea.digest(for_p.read_bytes()),
        anon_sha=ea.digest(anon_p.read_bytes()),
        grouped_sha=ea.digest(grouped_p.read_bytes()) if grouped_p.is_file() else None,
    )
    claims_by_macro = {c["macro"]: c for c in claims["claims"]}
    for m_name in (
        "BenchAlertForensicsRows", "BenchCoreFourPct", "BenchTableFourRows", "BenchBOneAlertsN",
        "BenchWaveOnePin", "BenchWaveTwoPin", "BenchPinWaveTwoCap", "BenchFDWrapOverheadMs",
        "BenchBwrapOverheadMs", "BenchWaveOneOverrideN", "BenchSAThirteenFpTipN", "BenchPThreeFpTipConservN",
        "BenchPosNineFourPlainUpperNs", "BenchPosTwoNine",
    ):
        assert claims_by_macro[m_name]["evidence_class"] == "replay-only"
    assert claims_by_macro["BenchIntakeStopsN"]["evidence_class"] == "re-executable"
    assert claims_by_macro["BenchConfContestDrawn"]["evidence_class"] == "re-executable"
    assert claims_by_macro["BenchConfContestIntake"]["evidence_class"] == "re-executable"
    assert claims_by_macro["BenchQuarIntakeN"]["evidence_class"] == "re-executable"
    assert claims_by_macro["BenchPosThreeLev"]["evidence_class"] == "protocol-constant"
    assert claims_by_macro["BenchBwrapVer"]["evidence_class"] == "protocol-constant"
    assert claims_by_macro["BenchRateablePairsN"]["evidence_class"] == "replay-only"
    assert claims_by_macro["BenchHeldUnratConfClustN"]["evidence_class"] == "replay-only"
    assert claims_by_macro["BenchMaxCounterVal"]["evidence_class"] == "replay-only"
    assert claims_by_macro["BenchPosThreeWorstTS"]["evidence_class"] == "replay-only"
    assert r"\newcommand{\BenchCensorSlopeMin}{0.45}" in slots_tex
    assert r"\newcommand{\BenchPosOneSevenFiveOtwoSubSlopeRange}{1.12--1.80}" in slots_tex
    assert r"\newcommand{\BenchPosNineZeroRatio}{23{,}899$\times$}" in slots_tex
    assert r"vs.\ $-33.3$~pp pilot" in slots_tex
    assert claims_by_macro["BenchPilotPairs"]["evidence_class"] == "replay-only"
    assert claims_by_macro["BenchPairMedianRTwo"]["evidence_class"] == "replay-only"
    assert claims_by_macro["GroupedQuadraticFalse"]["source_sha256"] == [ea.digest(grouped_p.read_bytes())]
    claims_p = data_dir / "paper_claims.json"
    assert claims_p.is_file()
    assert claims == json.loads(claims_p.read_bytes())

    ms_dir = repo_root / "manuscript"
    if (ms_dir / "paired_mechanism.tex").is_file() and (ms_dir / "paired_mechanism.bib").is_file():
        tex_raw = (ms_dir / "paired_mechanism.tex").read_text(encoding="utf-8")
        bib_raw = (ms_dir / "paired_mechanism.bib").read_text(encoding="utf-8")
        tex_clean = re.sub(r"(?<!\\)%[^\n]*", "", tex_raw)
        bib_keys = set(re.findall(r"^@\w+\{([^,]+),", bib_raw, flags=re.M))
        cited_keys = {k.strip() for m in re.findall(r"\\cite\{([^}]+)\}", tex_clean) for k in m.split(",")}
        assert bib_keys == cited_keys, f"BibTeX mismatch: uncited={bib_keys - cited_keys}, unknown={cited_keys - bib_keys}"
        body = tex_clean.split(r"\begin{document}", 1)[1].split(r"\end{document}", 1)[0]
        assert not re.search(r"\b(?:registered|asymptotic(?:ally)?)\b|github\.com/(?!evalplus\b)", body, re.I)
        assert "`" not in tex_clean.replace("``", "")
        assert not re.search(r"\\texttt\{[^}]*--[^}]*\}", tex_clean)

    if (repo_root / "verify.py").is_file():
        sys.path.insert(0, str(repo_root))
        import verify as vf
        tex_raw = (repo_root / "manuscript/paired_mechanism.tex").read_text(encoding="utf-8")
        grouped_src = (repo_root / "manuscript/grouped_statistics_macros.tex").read_text(encoding="utf-8")
        assert vf.verify_paper_claims(claims, slots_tex, grouped_src, tex_raw) == claims["claim_count"]
        vf.verify_tex_literals_and_banned_terms(tex_raw)

        # Injecting a raw empirical digit or banned term must fail closed
        tampered_digit = tex_raw.replace(r"\BenchFittedClusters{} fits", "124 fits")
        assert tampered_digit != tex_raw
        with pytest.raises(ValueError, match="Unguarded numeric literal"):
            vf.verify_tex_literals_and_banned_terms(tampered_digit)

        tampered_banned = tex_raw.replace("frozen manifest", "registered manifest")
        assert tampered_banned != tex_raw
        with pytest.raises(ValueError, match="Banned overclaim"):
            vf.verify_tex_literals_and_banned_terms(tampered_banned)


def test_pinned_predict_library_and_cli_help():
    """Verify pinned predict.py calculate_fit(), score.validate_committed_draw(), and --help CLI."""
    import subprocess
    from development.paired_study import predict as pred_mod
    from development.paired_study import score as score_mod

    fit = pred_mod.calculate_fit(
        [(10, 100, 10), (20, 400, 20), (40, 1600, 40), (80, 6400, 80)]
    )
    assert fit["slope"] == pytest.approx(1.0, abs=1e-9)
    assert fit["largest_ratio"] == pytest.approx(80.0, abs=1e-9)

    score_mod.validate_committed_draw({"phase": "confirmatory", "pins": {"methods": "0" * 64}, "cases": ["c1"]})
    with pytest.raises(ValueError):
        score_mod.validate_committed_draw({"phase": "confirmatory"})

    repo_root = Path(__file__).resolve().parents[1]
    res = subprocess.run(
        [sys.executable, "-B", "-m", "development.paired_study.predict", "--help"],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0
    assert "--traces" in res.stdout
