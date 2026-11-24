"""Publication-ready Matplotlib figure generator for the EAPG paired benchmark
qualification study. Uses Okabe-Ito colorblind-safe palette + redundant hatching
and direct numeric labels, Type-42 TrueType PDF fonts, and exact receipt inputs.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np

# Okabe-Ito palette on white background (high contrast + redundant hatching)
PALETTE = {
    "pass": "#009E73",          # bluish green
    "contract": "#0072B2",      # blue
    "source": "#D55E00",        # vermillion
    "route": "#CC79A7",         # reddish purple
    "held": "#E69F00",          # orange
    "indeterminate": "#56B4E9", # sky blue
    "neutral": "#666666",       # mid gray
    "conf": "#0072B2",
    "quar": "#E69F00",
}

HATCHES = {
    "pass": "",
    "contract": "//",
    "source": "\\\\",
    "route": "xx",
    "held": "..",
    "indeterminate": "++",
}


def _configure_rc() -> dict[str, Any]:
    return {
        "font.family": "DejaVu Sans",
        "font.size": 8.5,
        "axes.titlesize": 9.5,
        "axes.titleweight": "bold",
        "axes.labelsize": 8.5,
        "xtick.labelsize": 8.0,
        "ytick.labelsize": 8.0,
        "legend.fontsize": 7.5,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
    }


def plot_s1_desk_taxonomy(out_prefix: Path) -> None:
    """Figure 1: Verified 96/96 S1 disposition flow & desk-stop reason taxonomy.

    Source receipt: s1-m2-inventory-agg.json
      SHA-256: 589c2e93f7f972deffa939255a94548856d769da52bba9885751aba761bbb577
      Manifest SHA-256: 5b432d827f324c073eb7ed14b4df4b5d18f5eb2a90c4d97d358405a800d27346
      Amendment 4 SHA-256: 0d070e99d12c7b872a2db023e056586921c5aadcef90abe376fcee5006328940
    """
    strata = [
        "Confirmatory\nContest (n=444)",
        "Confirmatory\nRepository (n=33)",
        "Quarantined\nContest (n=500)",
    ]
    counts = {
        "pass": np.array([183, 0, 204]),
        "contract": np.array([160, 0, 256]),
        "source": np.array([11, 0, 25]),
        "route": np.array([2, 0, 0]),
        "held": np.array([86, 33, 14]),
        "indeterminate": np.array([2, 0, 1]),
    }
    totals = np.array([444, 33, 500])
    assert np.all(sum(counts.values()) == totals), "Stratum sum mismatch"

    labels_a = [
        ("pass", "S1 pass"),
        ("contract", "Contract stop"),
        ("source", "Source stop"),
        ("route", "Route stop"),
        ("held", "Held (desk_unrateable)"),
        ("indeterminate", "Indeterminate (A4)"),
    ]

    reasons = [
        ("Insufficient workload ladder (contract)", 93, 174),
        ("Unbundled statement images (held)", 86, 14),
        ("No executable work delta (contract)", 35, 18),
        ("No independent repo spec (held)", 33, 0),
        ("No isolated restoration (contract)", 10, 22),
        ("Fixed contract (contract)", 10, 20),
        ("No common calibrated work (contract)", 9, 20),
        ("Source-derived UB (source)", 5, 10),
        ("ISA / AVX / arch locked (source)", 3, 9),
        ("Source-derived oracle failure (source)", 3, 6),
        ("No matching work delta (contract)", 3, 2),
        ("Indeterminate (A4 terminal)", 2, 1),
        ("Missing pinned dependency (route)", 2, 0),
    ]
    assert sum(c for _, c, _ in reasons) == 294, "Confirmatory stop pair sum mismatch"
    assert sum(q for _, _, q in reasons) == 296, "Quarantined stop pair sum mismatch"

    with mpl.rc_context(_configure_rc()):
        fig, (ax_a, ax_b) = plt.subplots(
            1, 2,
            figsize=(7.6, 3.8),
            gridspec_kw={"width_ratios": [1.0, 1.45]},
            layout="constrained",
        )

        # Panel A: 100% stacked horizontal bars by stratum
        y_a = np.arange(len(strata))
        left = np.zeros(len(strata), dtype=float)
        for key, lbl in labels_a:
            pct = 100.0 * counts[key] / totals
            ax_a.barh(
                y_a,
                pct,
                left=left,
                height=0.58,
                color=PALETTE[key],
                edgecolor="white",
                linewidth=0.8,
                hatch=HATCHES[key],
                label=lbl,
            )
            for idx, (p, c) in enumerate(zip(pct, counts[key])):
                if p >= 14.0:
                    ax_a.text(
                        left[idx] + p / 2.0,
                        y_a[idx],
                        f"{c}\n({p:.0f}%)",
                        ha="center",
                        va="center",
                        fontsize=6.5,
                        color="white" if key in ("pass", "contract", "source", "route") else "#111111",
                        fontweight="bold",
                        bbox=dict(
                            boxstyle="round,pad=0.08",
                            facecolor=PALETTE[key],
                            edgecolor="none",
                            alpha=0.9,
                        ) if HATCHES[key] else None,
                    )
            left += pct

        ax_a.set_yticks(y_a)
        ax_a.set_yticklabels(strata)
        ax_a.invert_yaxis()
        ax_a.set_xlim(0, 100)
        ax_a.set_xlabel("Share of S0-pass pairs (%)")
        ax_a.set_title("A. S1 Dispositions by Stratum (n = 977)", fontsize=9.0)
        ax_a.legend(loc="upper center", bbox_to_anchor=(0.45, -0.22), ncol=2, frameon=False)

        # Panel B: Paired horizontal bar chart of desk-stop reasons
        y_b = np.arange(len(reasons))
        h = 0.38
        conf_vals = np.array([c for _, c, _ in reasons])
        quar_vals = np.array([q for _, _, q in reasons])

        ax_b.barh(y_b - h / 2, conf_vals, height=h, color=PALETTE["conf"], label="Confirmatory (n=294 stops)")
        ax_b.barh(
            y_b + h / 2,
            quar_vals,
            height=h,
            color=PALETTE["quar"],
            hatch="//",
            edgecolor="white",
            linewidth=0.4,
            label="Quarantined (n=296 stops)",
        )
        for idx, (cv, qv) in enumerate(zip(conf_vals, quar_vals)):
            if cv > 0:
                ax_b.text(cv + 2.5, y_b[idx] - h / 2, str(cv), va="center", ha="left", fontsize=6.8, color="#004466")
            if qv > 0:
                ax_b.text(qv + 2.5, y_b[idx] + h / 2, str(qv), va="center", ha="left", fontsize=6.8, color="#8A5A00")

        ax_b.set_yticks(y_b)
        ax_b.set_yticklabels([r[0] for r in reasons], fontsize=7.2)
        ax_b.invert_yaxis()
        ax_b.set_xlim(0, 205)
        ax_b.set_xlabel("Stopped pairs (count)")
        ax_b.set_title("B. Desk-Stop Reasons (n = 590)", loc="center", fontsize=9.0)
        ax_b.legend(
            loc="center right",
            bbox_to_anchor=(0.99, 0.38),
            frameon=True,
            facecolor="white",
            framealpha=0.95,
            edgecolor="#CCCCCC",
        )

        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        fig.savefig(out_prefix.with_suffix(".png"), dpi=300)
        plt.close(fig)


def plot_outcomes_forest(receipt: dict[str, Any], out_prefix: Path) -> None:
    """Figure 2: Primary outcomes & sensitivity forest plot from verified analysis receipt."""
    prim = receipt["primary_all_post_s0"]
    s13 = receipt["S13_without_desk_unrateable"]
    rows = [
        ("P1 Execution yield\n(confirmatory reps; replay-only)", prim["P1"]["rate"], 9.5, "147-pair R2 (9.5%)"),
        ("S1 Desk stops\n(confirmatory reps; replay-only)", prim["secondary"]["S1_desk_stop"], 70.1, "147-pair R1 (70.1%)"),
        ("S13 Desk stops\n(excl. held unrateable)", s13["secondary"]["S1_desk_stop"], 70.1, None),
        ("S2 Alerts / selected\n(confirmatory reps; replay-only)", prim["secondary"]["S2_alerts_per_selected"], 2.7, "147-pair R4 (2.7%)"),
    ]
    if prim["P3"]["rate"]["total"] > 0:
        lbl = (
            "P3 Alerts / fitted\n(confirmatory; replay-only)"
            if prim["P3"]["gate_met"]
            else "P3 Alerts / fitted\n(descriptive; <30 gate; replay-only)"
        )
        rows.append((lbl, prim["P3"]["rate"], 30.8, "147-pair R3 (30.8%)"))

    with mpl.rc_context(_configure_rc()):
        fig, ax = plt.subplots(figsize=(7.2, 3.4), layout="constrained")
        y = np.arange(len(rows))
        ax.axvline(100.0, color="#CCCCCC", linestyle=":", linewidth=0.9, zorder=1)
        for idx, (label, stat, ref_val, ref_lbl) in enumerate(rows):
            pct = stat["percent"]
            lo, hi = stat["clopper_pearson_95pct_percent"]
            ax.errorbar(
                pct,
                idx,
                xerr=[[pct - lo], [hi - pct]],
                fmt="o",
                color=PALETTE["conf"],
                ecolor=PALETTE["conf"],
                elinewidth=1.4,
                capsize=3.5,
                markersize=5.5,
                label="Expanded study (95% Clopper-Pearson)" if idx == 0 else None,
            )
            ax.scatter(
                [ref_val],
                [idx],
                marker="D",
                s=34,
                color=PALETTE["source"],
                zorder=4,
                label="147-pair fixed development reference" if idx == 0 else None,
            )
            ax.text(
                103.0,
                idx,
                f"{stat['count']}/{stat['total']} = {pct:.1f}% [{lo:.1f}, {hi:.1f}]",
                va="center",
                ha="left",
                fontsize=7.3,
            )
        ax.set_yticks(y)
        ax.set_yticklabels([r[0] for r in rows])
        ax.invert_yaxis()
        ax.set_xticks([0, 20, 40, 60, 80, 100])
        ax.set_xlim(-3, 156)
        ax.set_xlabel("Percentage (%) with exact two-sided 95% Clopper-Pearson CI")
        ax.set_title("Confirmatory Qualification Rates vs. 147-Pair Reference", loc="left")
        ax.legend(
            loc="upper center",
            bbox_to_anchor=(0.40, -0.20),
            ncol=2,
            frameon=False,
        )
        out_prefix.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(out_prefix.with_suffix(".pdf"))
        fig.savefig(out_prefix.with_suffix(".png"), dpi=300)
        plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, help="Optional expansion_analyze.py JSON receipt for Figure 2")
    args = parser.parse_args()
    plot_s1_desk_taxonomy(args.out_dir / "fig_s1_desk_taxonomy")
    if args.receipt:
        receipt = json.loads(args.receipt.read_bytes())
        plot_outcomes_forest(receipt, args.out_dir / "fig_qualification_outcomes")


if __name__ == "__main__":
    main()
