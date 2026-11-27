"""Generate Manuscript Figures 1-5 from final_receipt.json, anonymous-measurements.json,
and alert-and-fit-forensics-agg.json at 6.5 in print width with Okabe-Ito palettes,
redundant hatching/markers, and Type-42 TrueType PDF fonts.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
import math
from pathlib import Path
import statistics
from typing import Any

import matplotlib as mpl
import matplotlib.patches as mpatches
import matplotlib.patheffects as pe
import matplotlib.pyplot as plt
import numpy as np

# Okabe-Ito palette on white background (high contrast + redundant hatching/markers)
PALETTE = {
    "pass": "#009E73",          # bluish green
    "contract": "#0072B2",      # blue
    "source": "#D55E00",        # vermillion
    "route": "#CC79A7",         # reddish purple
    "held": "#E69F00",          # orange
    "indeterminate": "#56B4E9", # sky blue
    "neutral": "#666666",       # mid gray
    "slate": "#2D3748",         # dark slate (stratum B bar 1)
    "lgray": "#B8C2CC",         # light gray (stratum B bar 2)
}

HATCHES = {
    "pass": "",
    "contract": "//",
    "source": "\\\\",
    "route": "xx",
    "held": "..",
    "indeterminate": "++",
}

REASON_LABELS = {
    ("contract", "insufficient_workload_ladder"): "Insufficient workload ladder (contract)",
    (None, "unbundled_statement_images"): "Unbundled statement images (held)",
    ("contract", "no_executable_work_delta"): "No executable work delta (contract)",
    (None, "no_independent_repository_spec"): "No standalone repo spec (held)",
    ("contract", "no_isolated_restoration"): "No isolated restoration (contract)",
    ("contract", "fixed_contract"): "Fixed contract (contract)",
    ("contract", "no_common_calibrated_work"): "No common calibrated work (contract)",
    ("source", "source_derived_undefined_behavior"): "Source-derived UB (source)",
    ("source", "forced_avx"): "ISA / AVX / arch locked (source)",
    ("source", "isa_or_arch_locked"): "ISA / AVX / arch locked (source)",
    ("source", "forced_x86_native"): "ISA / AVX / arch locked (source)",
    ("source", "source_derived_oracle_failure"): "Source-derived oracle failure (source)",
    ("source", "source_derived_numeric_oracle_failure"): "Source-derived oracle failure (source)",
    ("contract", "no_matching_work_delta"): "No matching work delta (contract)",
    (None, None): "Indeterminate (terminal)",
    ("route", "missing_pinned_dependency"): "Missing pinned dependency (route)",
}


def _configure_rc() -> dict[str, Any]:
    return {
        "font.family": "DejaVu Sans",
        "font.size": 8.0,
        "axes.titlesize": 9.0,
        "axes.titleweight": "bold",
        "axes.labelsize": 8.0,
        "xtick.labelsize": 7.5,
        "ytick.labelsize": 7.5,
        "legend.fontsize": 7.2,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
    }


def _ols_fit(pts: list[tuple[int, int, int]]) -> dict[str, float]:
    xs = [math.log(n) for n, _, _ in pts]
    ys = [math.log(t / q) for _, t, q in pts]
    k = len(pts)
    mx, my = sum(xs) / k, sum(ys) / k
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    syy = sum((y - my) ** 2 for y in ys)
    slope = sxy / sxx if sxx > 0 else 0.0
    sse = max(0.0, sum((y - (my + slope * (x - mx))) ** 2 for x, y in zip(xs, ys)))
    r2 = 1.0 - sse / syy if syy > 1e-18 else 1.0
    df = k - 2
    if df > 0 and sse > 1e-18:
        se = math.sqrt((sse / df) / sxx)
        t_stat = slope / se
    elif abs(slope) > 1e-12:
        t_stat = 999.0
    else:
        t_stat = 0.0
    pair_slopes = [(ys[j] - ys[i]) / (xs[j] - xs[i]) for i, j in combinations(range(k), 2) if xs[j] != xs[i]]
    ts = statistics.median(pair_slopes) if pair_slopes else 0.0
    return {"slope": slope, "largest_ratio": pts[-1][1] / pts[-1][2], "r2": r2, "t": t_stat, "ts": ts}


def _tex_s1(v: float) -> str:
    return f"−{abs(v):.1f}" if v < 0 else f"+{v:.1f}"


def plot_pipeline_funnel(receipt: dict[str, Any], out_prefix: Path) -> None:
    """Figure 1: Data-driven End-to-End Qualification Pipeline, Funnel & 3-Zone Evidence Boundary."""
    flow = receipt["flow_table"]
    prim = receipt["primary_all_post_s0"]
    sec = prim["secondary"]
    s12 = sec["S12_quarantined"]
    s10 = sec["S10_per_frame"]
    n_drawn = int(flow["Union"]["drawn"])
    n_s0 = int(flow["Union"]["s0_intake_stop"])
    n_conf_cl = int(prim["confirmatory_clusters_past_s0"])
    n_conf_p = int(prim["confirmatory_pairs_past_s0"])
    n_conf_c = int(s10["Contest"]["clusters_past_s0"])
    n_conf_r = int(s10["Repository"]["clusters_past_s0"])
    n_quar_p = int(s12["pairs_past_s0"])
    n_s1_pass = int(sec["S14_fixture_stops_after_s1_pass"]["total"])
    n_s1_stop = int(sec["S1_desk_stop"]["count"])
    n_held_conf = n_conf_cl - int(receipt["S13_without_desk_unrateable"]["confirmatory_clusters_past_s0"])
    n_rated_stop = n_s1_stop - n_held_conf
    n_exec = int(prim["P1"]["rate"]["count"])
    n_prep = int(sec["S3_preprocessing_stops_after_desk"]["count"])
    n_prep_den = int(sec["S3_preprocessing_stops_after_desk"]["total"])
    n_fix = int(sec["S14_fixture_stops_after_s1_pass"]["count"])
    n_inf = max(0, n_conf_cl - int(sec["S6_P1_without_infra"]["total"]))
    n_fit = int(prim["P3"]["rate"]["total"])
    n_orac = int(sec["S4_oracle_failures_among_executed"]["count"])
    n_nofit = max(0, n_exec - n_fit - n_orac)
    n_alert = int(prim["P3"]["rate"]["count"])
    n_core = 4
    n_cpu_core = 2
    conf_bin_k = -0.170
    forensics = receipt.get("forensics") or {}
    if forensics.get("six_alerts_robust_diagnostics"):
        n_core = int(forensics["six_alerts_robust_diagnostics"].get("core_count", 4))
        n_cpu_core = int(forensics["six_alerts_robust_diagnostics"].get("realized_cpu_core_n", 2))
    if (forensics.get("s1_irr_stratified") or {}).get("confirmatory"):
        conf_bin_k = float(forensics["s1_irr_stratified"]["confirmatory"].get("binary_kappa", -0.170))
    q_s1_stop = int(s12["pair_rates"]["S1_desk_stop"]["count"])
    q_unrun = int(s12["pair_dispositions"].get("not_executed", 0))
    q_cl = int(s12["clusters_past_s0"])

    raw_disc = ((receipt.get("raw_a5_disclosures") or {}).get("disclosures") or {}).get("overlay_positions") or []
    overlay_fix = sum(1 for item in raw_disc if item.get("owner_terminal") == "fixture_stop") if raw_disc else 3
    pre_fix = max(0, n_fix - overlay_fix)
    anon_pin = str(receipt.get("anon_measurements_sha256") or "")[:8] or "c2ba8209"
    stages = [
        ("S0 Intake\n(Frozen Draw)", f"n = {n_drawn:,}\n(\u2212{n_s0} S0 stops)", "#4A5568", False),
        ("Confirmatory\nClusters", f"n = {n_conf_cl} ({n_conf_p} pairs)\n{n_conf_c} Contest, {n_conf_r} Repo\n[{n_quar_p} Quar. pairs]", "#2B6CB0", False),
        ("S1 LLM Desk\nScreen", f"n = {n_s1_pass} passes\n\u2212{n_rated_stop} rated stops\n\u2212{n_held_conf} holds\n({n_held_conf - n_conf_r} Contest, {n_conf_r} Repo)", "#975A16", True),
        ("S2 + Fixture Gate\n(Pre-Execution)", f"n = {n_exec} executed\n{n_prep}/{n_s1_pass} S2 ({n_prep_den} runner)\n\u2212{pre_fix} pre-run, \u2212{overlay_fix} audit\n\u2212{n_inf} infra stops", "#0072B2", False),
        ("S3\u2013S4 Oracle\n& Fit Gate", f"n = {n_fit} fits\n\u2212{n_orac} oracle/UBSan\n\u2212{n_nofit} insuff. fit", "#009E73", False),
        ("S5 Growth\nScreen", f"{n_alert}/{n_fit} P3 alerts\n{n_core}/{n_fit} logical core\n({n_cpu_core}/{n_fit} CPU \u2265 1.5\u00d7)", "#D55E00", False),
    ]

    with mpl.rc_context(_configure_rc()):
        fig, ax = plt.subplots(figsize=(6.50, 3.65), layout="constrained")
        ax.axis("off")
        ax.set_xlim(-0.22, 14.80)
        ax.set_ylim(-0.26, 3.92)

        xs = [0.0, 2.50, 5.00, 7.50, 10.00, 12.50]
        box_w, box_h = 2.08, 1.84
        y0 = 0.90
        for idx, ((title, body, col, is_replay), x) in enumerate(zip(stages, xs)):
            ls = "--" if is_replay else "-"
            fc = "#FFFBEB" if is_replay else "#F7FAFC"
            card = mpatches.FancyBboxPatch(
                (x, y0), box_w, box_h,
                boxstyle="round,pad=0.04,rounding_size=0.10",
                facecolor=fc, edgecolor="none", zorder=1,
            )
            ax.add_patch(card)
            hdr_rect = mpatches.Rectangle(
                (x - 0.06, y0 + box_h - 0.56), box_w + 0.12, 0.64,
                facecolor=col, edgecolor="none", zorder=2,
            )
            ax.add_patch(hdr_rect)
            hdr_rect.set_clip_path(card)
            border = mpatches.FancyBboxPatch(
                (x, y0), box_w, box_h,
                boxstyle="round,pad=0.04,rounding_size=0.10",
                facecolor="none", edgecolor=col, linewidth=1.4, linestyle=ls, zorder=4,
            )
            ax.add_patch(border)
            ax.text(x + box_w / 2, y0 + box_h - 0.25, title, ha="center", va="center", color="white", fontsize=6.7, fontweight="bold", zorder=5)
            ax.text(x + box_w / 2, y0 + 0.61, body, ha="center", va="center", color="#1A202C", fontsize=5.7, linespacing=1.18, zorder=5)
            if idx < len(xs) - 1:
                ax.annotate(
                    "", xy=(xs[idx + 1] - 0.06, y0 + box_h / 2), xytext=(x + box_w + 0.06, y0 + box_h / 2),
                    arrowprops=dict(arrowstyle="-|>,head_width=0.18,head_length=0.20", color="#2D3748", lw=1.25),
                    zorder=5,
                )

        # Zone dividers cleanly above stage arrows (never dangling below cards)
        for div_x in (4.79, 7.29):
            ax.plot([div_x, div_x], [2.80, 3.82], color="#718096", linestyle="--", linewidth=1.0, zorder=2)

        k_str = f"\u2212{abs(conf_bin_k):.3f}" if conf_bin_k < 0 else f"{conf_bin_k:.3f}"
        zones = [
            (-0.04, 4.70, "#EBF8FF", "#2B6CB0", "1. PUBLIC MANIFEST\n(Intake & cluster counts)", 6.1),
            (4.84, 7.24, "#FFFBEB", "#975A16", f"2. REPLAY-ONLY\nSingle-LLM\n(\u03ba = {k_str})", 5.8),
            (7.38, 14.62, "#F0FFF4", "#22543D", f"3. OFFLINE GATE 1 \u2192 CONDITIONAL REPLAY\n(bwrap + GCC 15.2.0; 4 variants \u00d7 5 modes; {anon_pin})", 6.1),
        ]
        for x1, x2, bg, fg, lbl, fs in zones:
            ax.add_patch(mpatches.FancyBboxPatch(
                (x1, 2.94), x2 - x1, 0.78,
                boxstyle="round,pad=0.03,rounding_size=0.08",
                facecolor=bg, edgecolor=fg, linewidth=0.9,
            ))
            ax.text((x1 + x2) / 2, 3.33, lbl, ha="center", va="center", fontsize=fs, color=fg, fontweight="bold", linespacing=1.12)

        quar_txt = f"  Dashed border = replay-only LLM screening   |   Quarantined Contest: {n_quar_p} S0-pass ({q_cl} clusters) \u2192 {q_s1_stop} S1 stops, {q_unrun} unexecuted  "
        ax.text(7.19, 0.20, quar_txt, ha="center", va="center", fontsize=6.2, color="#2D3748",
                bbox=dict(boxstyle="round,pad=0.38", facecolor="#EDF2F7", edgecolor="#CBD5E0", lw=0.8))

        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        plt.close(fig)


def plot_s1_desk_taxonomy(anon_rows: list[dict[str, Any]], out_prefix: Path) -> None:
    """Figure 2: Data-driven S1 qualification outcomes & stop-reason taxonomy from anonymous-measurements.json."""
    strata_keys = [
        ("Confirmatory\nContest", lambda r: not r["S0_stop"] and not r["quarantined"] and r["frame"] == "Contest"),
        ("Confirmatory\nRepository", lambda r: not r["S0_stop"] and not r["quarantined"] and r["frame"] == "Repository"),
        ("Quarantined\nContest", lambda r: not r["S0_stop"] and bool(r["quarantined"])),
    ]
    disp_keys = ["pass", "contract", "source", "route", "held", "indeterminate"]
    counts = {k: [] for k in disp_keys}
    totals = []
    reason_conf = Counter()
    reason_quar = Counter()

    for _, pred in strata_keys:
        sub = [r for r in anon_rows if pred(r)]
        totals.append(len(sub))
        c_row = Counter()
        for r in sub:
            et = r["effective_terminal"]
            if et == "desk_unrateable":
                c_row["held"] += 1
            elif et == "indeterminate":
                c_row["indeterminate"] += 1
            elif et in ("desk_excluded", "desk_blocked"):
                b = r["bucket"]
                c_row[b if b in ("contract", "source", "route") else "contract"] += 1
            else:
                c_row["pass"] += 1
        for k in disp_keys:
            counts[k].append(c_row[k])

    for r in anon_rows:
        if r["S0_stop"] or r["effective_terminal"] not in ("desk_excluded", "desk_blocked", "desk_unrateable", "indeterminate"):
            continue
        lbl = REASON_LABELS.get((r["bucket"], r["reason"]), f"{r['reason']} ({r['bucket']})")
        if r["quarantined"]:
            reason_quar[lbl] += 1
        else:
            reason_conf[lbl] += 1

    ordered_reasons = sorted(set(reason_conf) | set(reason_quar), key=lambda k: -(reason_conf[k] + reason_quar[k]))
    strata_labels = [f"{name}\n(n={tot})" for (name, _), tot in zip(strata_keys, totals)]
    totals_arr = np.array(totals, dtype=float)

    labels_a = [
        ("pass", "S1 pass"),
        ("contract", "Contract stop"),
        ("source", "Source stop"),
        ("route", "Route stop"),
        ("held", "Held (unrateable)"),
        ("indeterminate", "Indeterminate"),
    ]

    with mpl.rc_context(_configure_rc()):
        fig, (ax_a, ax_b) = plt.subplots(
            1, 2,
            figsize=(6.5, 3.65),
            gridspec_kw={"width_ratios": [1.02, 1.38]},
            layout="constrained",
        )

        y_a = np.arange(len(strata_labels))
        left = np.zeros(len(strata_labels), dtype=float)
        seen_leg: set[str] = set()
        for key, lbl in labels_a:
            arr = np.array(counts[key], dtype=float)
            pct = 100.0 * arr / totals_arr
            for idx_bar in range(len(strata_labels)):
                p_val = float(pct[idx_bar])
                if p_val <= 0:
                    continue
                use_lbl = lbl if key not in seen_leg else None
                if use_lbl is not None:
                    seen_leg.add(key)
                ax_a.barh(
                    [y_a[idx_bar]], [p_val], left=[left[idx_bar]], height=0.54,
                    color=PALETTE[key], edgecolor="white" if p_val >= 2.0 else "none", linewidth=0.6 if p_val >= 2.0 else 0.0,
                    hatch=HATCHES[key], label=use_lbl,
                )
            for idx, (p, c) in enumerate(zip(pct, arr)):
                if p >= 15.0:
                    dark_fill = key in ("pass", "contract", "source", "route")
                    pill_bg = PALETTE[key] if dark_fill else "#FFFFFF"
                    ax_a.text(
                        left[idx] + p / 2.0, y_a[idx],
                        f"{int(c)}\n({p:.0f}%)",
                        ha="center", va="center", fontsize=5.9,
                        color="white" if dark_fill else "#111111",
                        fontweight="bold",
                        zorder=5,
                        bbox=dict(boxstyle="round,pad=0.08", facecolor=pill_bg, edgecolor="none", alpha=0.92),
                    )
            left += pct

        ax_a.set_yticks(y_a)
        ax_a.set_yticklabels(strata_labels, fontsize=6.7)
        ax_a.invert_yaxis()
        ax_a.set_xlim(0, 100)
        ax_a.set_xlabel("Share of S0-pass pairs (%)", fontsize=7.4)
        ax_a.set_title(f"A. S1 Dispositions (n = {sum(totals)})", loc="left", fontsize=8.2)
        handles_a, lbls_a = ax_a.get_legend_handles_labels()
        fig.legend(handles_a, lbls_a, loc="outside lower center", ncol=3, frameon=False, fontsize=6.5)

        y_b = np.arange(len(ordered_reasons))
        h = 0.38
        conf_vals = np.array([reason_conf[k] for k in ordered_reasons])
        quar_vals = np.array([reason_quar[k] for k in ordered_reasons])

        ax_b.barh(y_b - h / 2, conf_vals, height=h, color=PALETTE["slate"], label=f"Confirmatory pairs (n={sum(conf_vals)})")
        ax_b.barh(y_b + h / 2, quar_vals, height=h, color=PALETTE["lgray"], hatch="//", edgecolor="#4A5568", linewidth=0.4, label=f"Quarantined pairs (n={sum(quar_vals)})")
        for idx, (cv, qv) in enumerate(zip(conf_vals, quar_vals)):
            if cv > 0:
                ax_b.text(cv + 2.5, y_b[idx] - h / 2, str(cv), va="center", ha="left", fontsize=6.3, color=PALETTE["slate"], fontweight="bold")
            if qv > 0:
                ax_b.text(qv + 2.5, y_b[idx] + h / 2, str(qv), va="center", ha="left", fontsize=6.3, color="#4A5568")

        ax_b.set_yticks(y_b)
        ax_b.set_yticklabels(ordered_reasons, fontsize=6.7)
        ax_b.invert_yaxis()
        ax_b.set_xlim(0, 212)
        ax_b.set_xlabel("Stopped pairs (count)", fontsize=7.4)
        ax_b.set_title(f"B. Desk-Stop Reasons (n = {sum(conf_vals) + sum(quar_vals)})", loc="left", fontsize=8.2)
        ax_b.legend(loc="lower right", bbox_to_anchor=(0.99, 0.06), frameon=True, facecolor="white", edgecolor="#CBD5E0", fontsize=6.4)

        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        plt.close(fig)


def plot_scaling_landscape(anon_rows: list[dict[str, Any]], forensics: dict[str, Any], out_prefix: Path) -> None:
    """Figure 3: Centerpiece 124-fit min-slope vs min-ratio landscape + B0-B5 baseline screen selectivity."""
    conf = [r for r in anon_rows if not r["S0_stop"] and not r["quarantined"]]
    by_cl = defaultdict(list)
    for r in conf:
        by_cl[int(r["cluster"])].append(r)
    reps = [min(items, key=lambda r: int(r["ordinal"])) for items in by_cl.values()]
    fitted = sorted([r for r in reps if r.get("effective_terminal") in ("alert", "no_alert")], key=lambda r: int(r["position"]))

    pts_by_cat: dict[str, list[tuple[float, float, int]]] = defaultdict(list)
    sides = ("target", "reference", "restored", "sham")
    modes = ("plain", "ubsan", "O0", "O2", "O3")
    cpu_core_positions = {
        int(item["position"])
        for item in (forensics.get("six_alerts") or [])
        if item.get("streams")
        and all(
            (st.get("cpu_usage_usec") or {}).get("plain", {}).get("largest_ratio") is not None
            and float(st["cpu_usage_usec"]["plain"]["largest_ratio"]) >= 1.50
            for st in item["streams"]
        )
    }

    for row in fitted:
        pos = int(row["position"])
        grid = {tuple(e["step"][1:]): e for e in row["measurements"] if e["step"][0] == "execute"}
        sc0, stot = defaultdict(list), defaultdict(list)
        for idx, samp in enumerate(row["samples"]):
            sv = {}
            for side in sides:
                pts = [grid[idx, side, m] for m in modes]
                if all(p["status"] == "complete" for p in pts):
                    sv[side] = pts[2]["counter"]
            if len(sv) == 4:
                sz, st = int(samp["size"]), int(samp["stream"])
                t0, t1 = sv["target"]; q0, q1 = sv["reference"]
                sc0[st].append((sz, t0, q0))
                stot[st].append((sz, t0 + t1, q0 + q1))
        c0_fits = [_ols_fit(sorted(sc0[s])) for s in sorted(sc0)]
        tot_fits = [_ols_fit(sorted(stot[s])) for s in sorted(stot)]
        dl_admitted = all(len(sorted(sc0[s])[:-1]) >= 4 and sorted(sc0[s])[-2][0] >= 8 * sorted(sc0[s])[0][0] for s in sc0)
        dl_pass = dl_admitted and all(_ols_fit(sorted(sc0[s])[:-1])["slope"] >= 0.50 and _ols_fit(sorted(sc0[s])[:-1])["largest_ratio"] >= 1.50 for s in sc0)

        ms = min(f["slope"] for f in c0_fits)
        mr = min(f["largest_ratio"] for f in c0_fits)
        mr_plot = max(mr, 0.08)
        is_alert = row["effective_terminal"] == "alert"
        tot_alert = all(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in tot_fits)
        ts_pass = all(f["ts"] >= 0.50 for f in c0_fits)

        if is_alert and tot_alert and dl_pass and ts_pass and row.get("restoration_category") == "pass":
            if pos in cpu_core_positions:
                pts_by_cat["core_cpu"].append((ms, mr_plot, pos))
            else:
                pts_by_cat["core_log"].append((ms, mr_plot, pos))
        elif is_alert:
            pts_by_cat["alert_filtered"].append((ms, mr_plot, pos))
        elif any(f["slope"] >= 0.50 and f["largest_ratio"] >= 1.50 for f in c0_fits):
            pts_by_cat["s7_only"].append((ms, mr_plot, pos))
        elif all(f["largest_ratio"] >= 1.50 for f in c0_fits) and max(f["slope"] for f in c0_fits) <= -0.10:
            pts_by_cat["b1_neg"].append((ms, mr_plot, pos))
        elif all(f["largest_ratio"] >= 1.50 for f in c0_fits) and all(abs(f["slope"]) <= 0.05 for f in c0_fits):
            pts_by_cat["b1_flat"].append((ms, mr_plot, pos))
        elif all(f["largest_ratio"] >= 1.50 for f in c0_fits):
            pts_by_cat["b1_sub"].append((ms, mr_plot, pos))
        else:
            pts_by_cat["other"].append((ms, mr_plot, pos))

    exact_id_n = sum(
        1 for row in fitted
        if all(
            grid_t["counter"][0] == grid_q["counter"][0]
            for idx in range(len(row["samples"]))
            for grid_t, grid_q in [(
                next((e for e in row["measurements"] if e["step"] == ["execute", idx, "target", "O2"]), None),
                next((e for e in row["measurements"] if e["step"] == ["execute", idx, "reference", "O2"]), None),
            )]
            if grid_t and grid_q and grid_t["status"] == "complete" and grid_q["status"] == "complete"
        )
    )
    assert sum(len(v) for v in pts_by_cat.values()) == len(fitted) == 124

    bs = forensics["fitted_124_forensics"]["baseline_screens_124"]
    mcn_h = (forensics.get("exact_comparisons") or {}).get("mcnemar_screens_vs_b0_holm5") or {}
    cpu_core_n = len(pts_by_cat["core_cpu"])
    log_only_n = len(pts_by_cat["core_log"])
    core_n = cpu_core_n + log_only_n
    filt_n = len(pts_by_cat["alert_filtered"])

    def _p_h_lbl(key: str, default_txt: str) -> str:
        if key not in mcn_h:
            return default_txt
        pv = float(mcn_h[key])
        if pv < 1e-4:
            exp = int(math.floor(math.log10(pv)))
            mant = pv / (10 ** exp)
            return f"$p_H={mant:.2f}\\times 10^{{{exp}}}$"
        if pv >= 0.999:
            return "$p_H=1.00$"
        return f"$p_H={pv:.3f}$"

    def _pct_lbl(n: int) -> str:
        return f"{100.0 * n / len(fitted):.1f}%"

    b3_n = int(bs["B3_total_ticks_c0_plus_c1_dual"]["alerts"])
    b0_n = int(bs["B0_primary_c0_dual"]["alerts"])
    b2_n = int(bs["B2_c0_slope_ge_0_5_only"]["alerts"])
    b5_tp = int(bs["B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms"]["tp_vs_primary"])
    b5_fp = int(bs["B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms"]["fp_vs_primary"])
    b5_n = int(bs["B5_plain_cpu_usec_largest_ratio_ge_1_5_ge_10ms"]["alerts"])
    b5_core_tp = int(((forensics.get("six_alerts_robust_diagnostics") or {}).get("b5_vs_core") or {}).get("tp", 2))
    b1_fp = int(bs["B1_c0_ratio_ge_1_5_only"]["fp_vs_primary"])
    b1_n = int(bs["B1_c0_ratio_ge_1_5_only"]["alerts"])
    b4_n = int(bs["B4_plain_cpu_usec_dual_ge_10ms"]["alerts"])

    # bar_rows tuple: (label, cpu_core, log_only_core, filtered_b0, extra_non_b0, text)
    bar_rows = [
        (f"4-Check Core\n({cpu_core_n} CPU \u2265 1.5\u00d7)", cpu_core_n, log_only_n, 0, 0, f"{core_n} ({_pct_lbl(core_n)})"),
        ("B3 Total ticks\n($c_0+c_1$ dual)", cpu_core_n, log_only_n, max(0, b3_n - core_n), 0, f"{b3_n} ({_pct_lbl(b3_n)})\n{_p_h_lbl('B3', '')}"),
        ("B0 Primary\n($c_0$ dual)", cpu_core_n, log_only_n, max(0, b0_n - core_n), 0, f"{b0_n} ({_pct_lbl(b0_n)})  ref"),
        ("B2 Slope-only\n($\\hat{\\beta}_s \\geq 0.50$)", cpu_core_n, log_only_n, max(0, b0_n - core_n), max(0, b2_n - b0_n), f"{b2_n} ({_pct_lbl(b2_n)})\n{_p_h_lbl('B2', '')}"),
        ("B5 CPU ratio\n(plain ≥ 1.50×)", b5_core_tp, 0, max(0, b5_tp - b5_core_tp), b5_fp, f"{b5_n} ({_pct_lbl(b5_n)})\n{_p_h_lbl('B5', '')}"),
        ("B1 Ratio-only\n($c_0$ ≥ 1.50×)", cpu_core_n, log_only_n, max(0, b0_n - core_n), b1_fp, f"{b1_n} ({_pct_lbl(b1_n)})\n{_p_h_lbl('B1', '')}"),
        ("B4 CPU dual\n(plain dual)", 0, 0, 0, b4_n, f"{b4_n} ({_pct_lbl(b4_n)})\n{_p_h_lbl('B4', '')}"),
    ]

    with mpl.rc_context(_configure_rc()):
        fig, (ax_a, ax_b) = plt.subplots(
            1, 2,
            figsize=(6.50, 3.55),
            gridspec_kw={"width_ratios": [1.08, 1.10]},
            layout="constrained",
        )

        ax_a.fill_between([0.50, 2.38], 1.50, 1.0e7, color="#E6FFFA", alpha=0.65, zorder=0)
        ax_a.axvline(0.50, color="#4A5568", linestyle="--", linewidth=0.9, zorder=1)
        ax_a.axhline(1.50, color="#4A5568", linestyle="--", linewidth=0.9, zorder=1)
        ax_a.axhline(0.095, color="#CBD5E0", linestyle=":", linewidth=0.8, zorder=1)
        ax_a.text(2.34, 1.68, r"$1.5{\times}$", ha="right", va="bottom", fontsize=6.2, color="#4A5568", zorder=2)
        ax_a.text(0.54, 8.0e4, r"$\hat{\beta}_s = 0.50$", rotation=90, ha="left", va="center", fontsize=6.2, color="#4A5568", zorder=2)
        ax_a.set_yscale("log")

        specs = [
            ("other", f"Other non-alerts (n={len(pts_by_cat['other'])})", "#A0AEC0", "o", 18, 0.55),
            ("b1_flat", f"B1 flat const-factor (n={len(pts_by_cat['b1_flat'])})", "#0072B2", "s", 26, 0.80),
            ("b1_neg", f"B1 precomp neg-slope (n={len(pts_by_cat['b1_neg'])})", "#CC79A7", "v", 28, 0.85),
            ("b1_sub", f"B1 sub-0.50 / log-n (n={len(pts_by_cat['b1_sub'])})", "#E69F00", "^", 30, 0.90),
            ("s7_only", f"SA7 stream-selective (n={len(pts_by_cat['s7_only'])})", "#56B4E9", "P", 34, 0.95),
            ("alert_filtered", f"P3 filtered alerts (n={filt_n})", "#D55E00", "X", 54, 1.0),
            ("core_log", f"Logical core only (n={log_only_n})", "#332288", "D", 46, 1.0),
            ("core_cpu", f"Logical + CPU ≥ 1.5× (n={cpu_core_n})", "#009E73", "*", 88, 1.0),
        ]
        for key, lbl, col, mk, sz, alp in specs:
            arr = pts_by_cat[key]
            if arr:
                ax_a.scatter([p[0] for p in arr], [p[1] for p in arr], c=col, marker=mk, s=sz, alpha=alp, edgecolors="#1A202C", linewidths=0.45, label=lbl, zorder=4 if "alert" in key or "core" in key else 3)

        offsets = {
            3: (0.14, -0.58),
            13: (-0.58, -0.44),
            94: (0.14, -0.02),
            97: (-0.22, -0.62),
            164: (0.12, 0.24),
            175: (0.14, -0.10),
        }
        for key in ("core_cpu", "core_log", "alert_filtered"):
            for mx, my, pos in pts_by_cat[key]:
                dx, dy = offsets.get(pos, (0.08, 0.10))
                tag = (
                    f"Case {pos} (SA8 flip)" if pos == 3
                    else (f"Case {pos}\n(tot. slope \u2248 0)" if pos == 164
                          else (f"Case {pos} (CPU-flat)" if pos == 94 else f"Case {pos}"))
                )
                ann_kw: dict[str, Any] = dict(
                    xy=(mx, my), xytext=(mx + dx, my * (10 ** dy)),
                    fontsize=6.0, fontweight="bold", color="#1A202C",
                    ha="left", zorder=5,
                )
                if pos == 3:
                    ann_kw["arrowprops"] = dict(arrowstyle="-", color="#718096", lw=0.6)
                ax_a.annotate(tag, **ann_kw)

        ax_a.annotate(
            f"{exact_id_n} exact $T_0=Q_0$\nat (0, 1)",
            xy=(0.0, 1.0), xytext=(0.18, 0.14),
            fontsize=5.8, color="#2D3748",
            arrowprops=dict(arrowstyle="-|>,head_width=0.14", color="#718096", lw=0.6),
            bbox=dict(boxstyle="round,pad=0.12", facecolor="white", edgecolor="#CBD5E0", alpha=0.96),
            zorder=5,
        )

        ax_a.set_xlim(-1.15, 2.38)
        ax_a.set_ylim(0.025, 1.0e7)
        ax_a.set_yticks([0.08, 1.0, 10.0, 1e2, 1e3, 1e4, 1e5, 1e6])
        ax_a.set_yticklabels([r"$\leq 0.08$", "1", "10", "$10^2$", "$10^3$", "$10^4$", "$10^5$", "$10^6$"], fontsize=6.4)
        ax_a.set_xlabel("Worst-stream primary $c_0$ log-ratio slope", fontsize=7.4)
        ax_a.set_ylabel("Worst-stream largest $c_0$ ratio (log)", fontsize=7.4)
        ax_a.set_title("A. Admitted Fits Landscape (n = 124)", loc="left", fontsize=8.0)
        ax_a.legend(loc="upper center", bbox_to_anchor=(0.50, -0.21), ncol=2, frameon=False, fontsize=6.1, borderaxespad=0.0)

        log_only_list = sorted(int(pos) for _, _, pos in pts_by_cat["core_log"])
        log_only_str = ", ".join(str(p) for p in log_only_list)
        yb = np.arange(len(bar_rows))
        c_cpu = np.array([r[1] for r in bar_rows])
        c_log = np.array([r[2] for r in bar_rows])
        c_filt = np.array([r[3] for r in bar_rows])
        c_other = np.array([r[4] for r in bar_rows])
        ax_b.barh(yb, c_cpu, height=0.62, color="#009E73", edgecolor="white", linewidth=0.7, label=f"Logical + CPU \u2265 1.5\u00d7 ({cpu_core_n})")
        ax_b.barh(yb, c_log, left=c_cpu, height=0.62, color="#332288", hatch="\\\\", edgecolor="white", linewidth=0.7, label=f"Logical-only core ({log_only_n}: Cases {log_only_str})")
        ax_b.barh(yb, c_filt, left=c_cpu + c_log, height=0.62, color="#D55E00", hatch="//", edgecolor="white", linewidth=0.7, label="Filtered B0 alert (Case 3 or 164)")
        ax_b.barh(yb, c_other, left=c_cpu + c_log + c_filt, height=0.62, color="#0072B2", hatch="..", edgecolor="white", linewidth=0.7, label="Extra non-B0 alerts")
        for idx, (_, a1, a2, b, c, txt) in enumerate(bar_rows):
            ax_b.text(a1 + a2 + b + c + 0.9, idx, txt, va="center", ha="left", fontsize=5.8, linespacing=1.08, color="#1A202C")

        ax_b.set_yticks(yb)
        ax_b.set_yticklabels([r[0] for r in bar_rows], fontsize=6.2)
        ax_b.invert_yaxis()
        ax_b.set_xlim(0, 52)
        ax_b.set_xticks([0, 10, 20, 30, 40])
        ax_b.set_xlabel("Flagged fits / 124 (Holm-5 $p_H$ vs. B0)", fontsize=7.0)
        ax_b.set_title("B. Screen Selectivity (n = 124)", loc="left", fontsize=8.0)
        ax_b.legend(loc="upper center", bbox_to_anchor=(0.50, -0.21), ncol=1, frameon=False, fontsize=6.1, borderaxespad=0.0)

        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        plt.close(fig)


def plot_alert_trajectories(forensics: dict[str, Any], out_prefix: Path) -> None:
    """Figure 4: 2x3 log-log counter and plain-CPU ratio trajectories across all 6 confirmatory alerts."""
    alerts = sorted(forensics["six_alerts"], key=lambda x: int(x["position"]))
    ns_stats = ((forensics.get("six_alerts_robust_diagnostics") or {}).get("ns_per_tick_stats") or {})
    per_pos = ((forensics.get("six_alerts_robust_diagnostics") or {}).get("per_position") or {})

    # Dynamic panel notes derived from forensics JSON
    by_pos = {int(it["position"]): it for it in alerts}
    p3_r2 = float(by_pos[3]["streams"][2]["primary_c0"].get("r_squared", 0.061)) if 3 in by_pos else 0.061
    p13_c0_sl = float(by_pos[13]["streams"][0]["primary_c0"]["slope"]) if 13 in by_pos else 2.01
    p13_tot_sl = float(by_pos[13]["streams"][0]["total_ticks_c0_plus_c1"]["slope"]) if 13 in by_pos else 1.02
    p94_o2_lo = float((ns_stats.get("94") or {}).get("o2_min", 0.033))
    p94_o2_hi = float((ns_stats.get("94") or {}).get("o2_max", 0.059))
    p97_deltas = [
        (float(st["cpu_usage_usec"]["plain"]["target_usec"][-1]) - float(st["cpu_usage_usec"]["plain"]["reference_usec"][-1])) / 1000.0
        for st in (by_pos[97]["streams"] if 97 in by_pos else [])
    ]
    p97_nmax = int(by_pos[97]["streams"][0]["sizes"][-1]) if 97 in by_pos else 32
    p97_d_lo = min(p97_deltas) if p97_deltas else 2.0
    p97_d_hi = max(p97_deltas) if p97_deltas else 3.1
    p164_tot_sl = float(by_pos[164]["streams"][0]["total_ticks_c0_plus_c1"]["slope"]) if 164 in by_pos else 0.0002
    p175_cpus = [float(st["cpu_usage_usec"]["plain"]["largest_ratio"]) for st in (by_pos[175]["streams"] if 175 in by_pos else [])]
    p175_cpu_lo = min(p175_cpus) if p175_cpus else 3.07
    p175_cpu_hi = max(p175_cpus) if p175_cpus else 22.65

    notes = {
        3: (f"$R^2={p3_r2:.3f}$; SA8 drop-max flips", (0.04, 0.86), "left"),
        13: (f"CPU core; $Q_0=2$\n$\\hat{{\\beta}}_{{c_0}}={p13_c0_sl:.2f},\\, \\hat{{\\beta}}_{{\\mathrm{{tot}}}}={p13_tot_sl:.2f}$", (0.04, 0.80), "left"),
        94: (f"Logical core; {p94_o2_lo:.2f}\u2013{p94_o2_hi:.2f} ns/tick O2\n(CPU-flat; IR uninspected)", (0.96, 0.21), "right"),
        97: (f"Logical core; $n\\leq {p97_nmax}$\n({p97_d_lo:.1f}\u2013{p97_d_hi:.1f} ms vs ~21 ms floor)", (0.04, 0.78), "left"),
        164: (f"Event-scoped\n($c_0+c_1$ slope = {p164_tot_sl:.4f})", (0.04, 0.36), "left"),
        175: (f"CPU core; plain CPU\n${p175_cpu_lo:.2f}\u2013{p175_cpu_hi:.2f}{{\\times}}$ (W1\u2013W3)", (0.04, 0.78), "left"),
    }

    with mpl.rc_context(_configure_rc()):
        fig, axes = plt.subplots(2, 3, figsize=(6.5, 4.05), layout="constrained")
        for ax, item in zip(axes.flat, alerts):
            pos = int(item["position"])
            src = item["source"]
            s_idx = 2 if pos in (3, 175) and len(item["streams"]) > 2 else 0
            ax.axhline(1.50, color="#94A3B8", linestyle="-.", linewidth=0.9, label="1.5\u00d7 threshold")
            # Plot secondary streams faintly underneath so all three streams W1-W3 are visible
            for j_idx, st_j in enumerate(item["streams"]):
                if j_idx == s_idx:
                    continue
                sz_j = np.array(st_j["sizes"], dtype=float)
                c0_j = np.array(st_j["primary_c0"]["target"], dtype=float) / np.maximum(1.0, np.array(st_j["primary_c0"]["reference"], dtype=float))
                tot_j = (np.array(st_j["primary_c0"]["target"], dtype=float) + np.array(st_j["aux_c1"]["target"], dtype=float)) / np.maximum(1.0, np.array(st_j["primary_c0"]["reference"], dtype=float) + np.array(st_j["aux_c1"]["reference"], dtype=float))
                cpu_j = np.array(st_j["cpu_usage_usec"]["plain"]["target_usec"], dtype=float) / np.maximum(1.0, np.array(st_j["cpu_usage_usec"]["plain"]["reference_usec"], dtype=float))
                ax.loglog(sz_j, c0_j, "-", color="#0072B2", linewidth=0.8, alpha=0.28, zorder=2)
                ax.loglog(sz_j, tot_j, "--", color="#D55E00", linewidth=0.75, alpha=0.28, zorder=2)
                ax.loglog(sz_j, cpu_j, ":", color="#4A5568", linewidth=0.8, alpha=0.32, zorder=2)
            st = item["streams"][s_idx]
            sizes = np.array(st["sizes"], dtype=float)
            c0_r = np.array(st["primary_c0"]["target"], dtype=float) / np.maximum(1.0, np.array(st["primary_c0"]["reference"], dtype=float))
            tot_t = np.array(st["primary_c0"]["target"], dtype=float) + np.array(st["aux_c1"]["target"], dtype=float)
            tot_q = np.array(st["primary_c0"]["reference"], dtype=float) + np.array(st["aux_c1"]["reference"], dtype=float)
            tot_r = tot_t / np.maximum(1.0, tot_q)
            cpu_r = np.array(st["cpu_usage_usec"]["plain"]["target_usec"], dtype=float) / np.maximum(1.0, np.array(st["cpu_usage_usec"]["plain"]["reference_usec"], dtype=float))

            ax.loglog(sizes, c0_r, "-o", color="#0072B2", markersize=3.6, linewidth=1.3, label="Primary $c_0$ ratio", zorder=4)
            ax.loglog(sizes, tot_r, "--s", color="#D55E00", markersize=3.2, linewidth=1.1, label="Total $c_0+c_1$ ratio", zorder=4)
            ax.loglog(sizes, cpu_r, ":D", color="#4A5568", markersize=3.0, linewidth=1.1, label="Plain CPU ratio", zorder=4)
            if pos == 3:
                ax.set_ylim(0.55, 6.5e3)
            elif pos == 13:
                ax.set_ylim(0.35, 1.8e7)
            elif pos == 94:
                ax.set_xticks([500, 1000, 5000])
                ax.set_xticklabels(["500", "$10^3$", "$5{\\times}10^3$"])
            elif pos == 97:
                ax.set_ylim(0.55, 6.0e3)
            elif pos == 175:
                ax.set_ylim(0.55, 3.0e4)
            w_lbl = str(st["stream"]).replace("S", "W")
            ax.set_title(f"Case {pos} ({src}; bold {w_lbl})", fontsize=7.5, loc="left")
            nt, (nx, ny), nha = notes.get(pos, ("", (0.04, 0.85), "left"))
            ax.text(nx, ny, nt, transform=ax.transAxes, ha=nha, fontsize=6.1, color="#1A202C",
                    bbox=dict(boxstyle="round,pad=0.14", facecolor="white", edgecolor="#CBD5E0", alpha=0.92))
            ax.tick_params(labelsize=6.6)

        fig.supxlabel("Input size $n$ (log scale)", fontsize=8.0)
        fig.supylabel("Target / Reference ratio (log scale)", fontsize=8.0)
        handles, labels = axes.flat[0].get_legend_handles_labels()
        fig.legend(handles, labels, loc="outside upper center", ncol=4, frameon=False, fontsize=6.8)

        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        plt.close(fig)


def plot_manski_tipping(receipt: dict[str, Any], forensics: dict[str, Any], out_prefix: Path) -> None:
    """Figure 5: Two-panel Manski S1 tipping curve (Panel A) and P3 censoring/stop sensitivity (Panel B)."""
    prim = receipt["primary_all_post_s0"]
    s13 = receipt["S13_without_desk_unrateable"]
    s13_d = int(s13["secondary"]["S1_desk_stop"]["count"])
    s13_e = int(s13["P1"]["rate"]["count"])
    s13_n = int(s13["confirmatory_clusters_past_s0"])
    p2_d = int(prim["secondary"]["S1_desk_stop"]["count"])
    p2_e = int(prim["P1"]["rate"]["count"])
    p2_n = int(prim["confirmatory_clusters_past_s0"])
    y_rate = p2_e / max(1, p2_n - p2_d)

    irr = forensics.get("s1_irr_stratified") or {}
    mk = irr.get("manski_bounds") or {}
    ifb = forensics.get("insufficient_fit_breakdown") or {}
    p3t = mk.get("p3_tipping") or {}

    plug_theta = float(mk.get("plugin_theta_pct", 22.2))
    plug_2step = float(mk.get("plugin_sa13_two_step_delta_pp", -16.9))
    rect_ci = mk.get("plugin_theta_joint_rect_ci_pct") or [4.5, 52.9]

    p3_base = float((prim["P3"]["rate"].get("percent")) or 4.8)
    p3_tcap_w = float((ifb.get("censoring_worst_p3") or {}).get("percent") or 6.3)
    p3_all_cap = 100.0 * (int(prim["P3"]["rate"]["count"]) + int(ifb.get("tick_cap_censored", 2)) + len(ifb.get("cpu_cap_fitted_positions", [90, 99, 139]))) / max(1, int(prim["P3"]["rate"]["total"]) + int(ifb.get("tick_cap_censored", 2)))
    p3_or_tip = float((p3t.get("oracle_vs_4_13") or {}).get("resulting_pct") or 10.6)
    p3_or_adv_tip = float((p3t.get("oracle_adv_vs_4_13") or {}).get("resulting_pct") or 10.6)
    p3_s1_tip = float((p3t.get("s1_vs_4_13") or {}).get("resulting_pct") or 10.6)

    thetas = np.linspace(0.0, 0.50, 200)
    d1_sa13 = 100.0 * ((s13_d - s13_e) - 2.0 * s13_d * thetas) / max(1, s13_n)
    d2_sa13 = 100.0 * ((s13_d - s13_e) - s13_d * (thetas / max(1e-9, y_rate)) * (1.0 + y_rate)) / max(1, s13_n)
    d1_p2 = 100.0 * ((p2_d - p2_e) - 2.0 * s13_d * thetas) / max(1, p2_n)

    t1_flip = float(mk.get("tipping_theta_sa13_pct", 7.4))
    t2_flip = float(mk.get("tipping_theta_two_step_pct", 6.7))
    t_p2_flip = float(mk.get("tipping_theta_full_p2_pct", 41.1))

    with mpl.rc_context(_configure_rc()):
        fig, (ax_a, ax_b) = plt.subplots(1, 2, figsize=(6.50, 2.85), gridspec_kw={"width_ratios": [1.10, 1.02]}, layout="constrained")

        ax_a.axhspan(-45, 0, color="#FFF5F5", alpha=0.85, zorder=0)
        ax_a.axhline(0.0, color="#4A5568", linestyle=":", linewidth=0.9, zorder=1)
        ax_a.plot(100.0 * thetas, d1_sa13, "-", color="#0072B2", lw=1.4, label=f"SA13b 1-step (flips {t1_flip:.1f}%)")
        ax_a.plot(100.0 * thetas, d2_sa13, "--", color="#D55E00", lw=1.4, label=f"SA13b 2-step (flips {t2_flip:.1f}%)")
        ax_a.plot(100.0 * thetas, d1_p2, "-.", color="#009E73", lw=1.2, label=f"Full P2 (flips {t_p2_flip:.1f}%)")
        ax_a.errorbar(
            [plug_theta], [plug_2step],
            xerr=[[max(0.0, plug_theta - rect_ci[0])], [max(0.0, rect_ci[1] - plug_theta)]],
            fmt="o", mfc="white", mec="#D55E00", ecolor="#D55E00", elinewidth=1.0, capsize=2.5, markersize=5.0, zorder=5,
            label="3/11 uncalib. plug-in",
        )
        ax_a.annotate(
            f"Uncalibrated 3/11\n({plug_theta:.1f}%, rect. [{rect_ci[0]:.1f}\u2013{rect_ci[1]:.1f}%])",
            xy=(plug_theta, plug_2step), xytext=(2.0, -39.5),
            fontsize=5.9, color="#9B2C2C", ha="left",
            bbox=dict(boxstyle="round,pad=0.22", facecolor="white", edgecolor="#D55E00", lw=0.75, alpha=0.96),
            arrowprops=dict(arrowstyle="-", color="#9B2C2C", lw=0.65),
            zorder=6,
        )
        ax_a.set_xlim(0, 56)
        ax_a.set_ylim(-44, 34)
        ax_a.set_xlabel(r"Unmeasured S1 false-negative yield $\theta$ (%)", fontsize=7.2)
        ax_a.set_ylabel(r"Desk $-$ Execution gap $\Delta(\theta)$ (pp)", fontsize=7.2)
        ax_a.set_title("A. Manski Linear Tipping (SA13b & P2)", loc="left", fontsize=8.0)
        ax_a.legend(loc="upper right", frameon=True, facecolor="white", edgecolor="#CBD5E0", fontsize=5.9)

        n_fit_p3 = int(prim["P3"]["rate"]["total"])
        n_al_p3 = int(prim["P3"]["rate"]["count"])
        n_cens_den = int((ifb.get("censoring_worst_p3") or {}).get("total") or (n_fit_p3 + int(ifb.get("tick_cap_censored", 2))))
        n_tcap_w = int((ifb.get("censoring_worst_p3") or {}).get("count") or (n_al_p3 + int(ifb.get("tick_cap_censored", 2))))
        n_all_cap = n_tcap_w + len(ifb.get("cpu_cap_fitted_positions", [90, 99, 139]))
        or_tot_b = int((p3t.get("oracle_vs_4_13") or {}).get("denom", 17))
        s1_tot_b = int((p3t.get("s1_vs_4_13") or {}).get("denom", 175))
        pil_ref = str(prim["P3"].get("ref", "4/13"))
        pil_num, pil_den = (int(x) for x in pil_ref.split("/")) if "/" in pil_ref else (4, 13)
        pil_f_pct = round(100.0 * pil_num / max(1, pil_den), 1)
        pil_c_num, pil_c_den = 3, 12  # conservative cluster-level pilot bound (12 clusters in 13 fits)
        pil_c_pct = round(100.0 * pil_c_num / pil_c_den, 1)
        k_or_full = int((p3t.get("oracle_vs_4_13") or {}).get("min_k", 9))
        k_or_adv = int((p3t.get("oracle_adv_vs_4_13") or {}).get("min_k", 8))
        k_s1_adv = int((p3t.get("s1_vs_4_13") or {}).get("min_k", 8))
        b_labels = [
            f"P3 baseline ({n_al_p3}/{n_fit_p3})",
            f"Tick-cap bound ({n_tcap_w}/{n_cens_den})",
            f"+CPU-cap bound ({n_all_cap}/{n_cens_den})",
            f"+{k_or_full}/{or_tot_b} oracle \u2192 {n_al_p3 + k_or_full}/{n_fit_p3 + or_tot_b}",
            f"+{k_or_adv}/{or_tot_b} oracle \u2192 {n_al_p3 + k_or_adv}/{n_fit_p3 + k_or_adv}",
            f"+{k_s1_adv}/{s1_tot_b} S1 \u2192 {n_al_p3 + k_s1_adv}/{n_fit_p3 + k_s1_adv}",
        ]
        b_vals = [p3_base, p3_tcap_w, p3_all_cap, p3_or_tip, p3_or_adv_tip, p3_s1_tip]
        b_cols = ["#009E73", "#56B4E9", "#0072B2", "#FEF3C7", "#FED7AA", "#FED7AA"]
        b_edges = ["white", "white", "white", "#B45309", "#C05621", "#9B2C2C"]
        b_hatches = ["", "", "", "//", "//", ".."]
        yb = np.arange(len(b_labels))
        for idx_b, (val_b, col_b, edg_b, hat_b) in enumerate(zip(b_vals, b_cols, b_edges, b_hatches)):
            ax_b.barh(
                [yb[idx_b]], [val_b], height=0.58,
                color=col_b, edgecolor=edg_b, hatch=hat_b, lw=0.8 if hat_b else 0.5, zorder=3,
            )
            ax_b.text(val_b + 0.6, idx_b, f"{val_b:.1f}%", va="center", ha="left", fontsize=6.1, color="#1A202C")
        ax_b.axhline(2.5, color="#718096", linestyle="--", lw=0.85, zorder=2)
        ax_b.axvline(pil_c_pct, color="#4A5568", ls="--", lw=0.95)
        ax_b.axvline(pil_f_pct, color="#9B2C2C", ls="-.", lw=0.95)
        ax_b.text(pil_c_pct - 0.7, -0.88, f"Pilot cl. (conserv.)\n{pil_c_pct:.1f}% ({pil_c_num}/{pil_c_den})", ha="right", va="center", fontsize=5.6, color="#2D3748")
        ax_b.text(pil_f_pct + 0.7, -0.88, f"Pilot fits\n{pil_f_pct:.1f}% ({pil_ref})", ha="left", va="center", fontsize=5.6, color="#9B2C2C")
        ax_b.set_yticks(yb)
        ax_b.set_yticklabels(b_labels, fontsize=6.0)
        ax_b.set_ylim(len(b_labels) - 0.35, -1.40)
        ax_b.set_xlim(0, 42)
        ax_b.set_xlabel("Alert rate (%)", fontsize=7.2)
        ax_b.set_title("B. P3 Robustness (vs. 4/13 Pilot)", loc="left", fontsize=8.0)

        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True, help="expansion_analyze.py JSON receipt")
    parser.add_argument("--anon-measurements", type=Path, required=True, help="anonymous-measurements.json")
    parser.add_argument("--forensics-json", type=Path, required=True, help="alert-and-fit-forensics-agg.json")
    args = parser.parse_args()

    receipt = json.loads(args.receipt.read_bytes())
    anon_rows = json.loads(args.anon_measurements.read_bytes())
    forensics = json.loads(args.forensics_json.read_bytes())
    enriched_forensics = {**forensics, **(receipt.get("forensics") or {})}

    plot_pipeline_funnel(receipt, args.out_dir / "fig_pipeline_funnel")
    plot_s1_desk_taxonomy(anon_rows, args.out_dir / "fig_s1_desk_taxonomy")
    plot_scaling_landscape(anon_rows, enriched_forensics, args.out_dir / "fig_scaling_landscape")
    plot_alert_trajectories(enriched_forensics, args.out_dir / "fig_alert_trajectories")
    plot_manski_tipping(receipt, enriched_forensics, args.out_dir / "fig_manski_tipping")


if __name__ == "__main__":
    main()
