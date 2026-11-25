# When Can a C++ Performance Pair Support a Growth Claim?

Empirical study and reproducibility artifact for:

> **When Can a C++ Performance Pair Support a Growth Claim? An Empirical Study of Benchmark Qualification**

This repository contains the compiled manuscript, LaTeX sources (`0` unguarded empirical literals; `100%` macro-guarded via `data/paper_claims.json`), publication figures, frozen intake/screening protocol and dated amendments (`1`–`5`), identifier-free ordinal-indexed per-point counter traces (`data/anonymous-measurements.json`) and aggregate/forensic receipts, deterministic offline statistical replay code, pinned isolated execution runner, and unit tests.

---

## Summary of Principal Findings (`N = 1,000` Frozen Public Pairs)

A frozen five-stage qualification pipeline (`S0`–`S5`) tracked `1,000` frozen public C++ slow–fast pairs (`956` Contest pairs across PIE/CodeNet; `44` Repository pairs from public `github-performance-fix` snapshots; `held_out_used: false`). After `23` `S0` intake stops (`12` duplicates, `11` unretrievable), `476` confirmatory primary clusters (`477` pairs) and `500` development-exposed quarantined Contest pairs (`54` clusters; `204` held unexecuted) remained:

| Contrast / Outcome | Estimate | 95% Interval / Summary | Test / Context |
| --- | --- | --- | --- |
| **P1 — Execution yield** (`>= 1` executed variant post-`S0`) | `149 / 476` (`31.3%`) | CP `[27.2%, 35.7%]` (vs. pilot `14/147 = 9.5%`) | Holm `p = 1.97 x 10^-39` (reflects pilot deferral removal) |
| **Sec. S13 — Rateable Contest execution & contrast** (excl. `118` held `desk_unrateable` clusters) | `149 / 358` (`41.6%`), `+7.3 pp` | Cluster bootstrap `[-2.8, +17.0]` pp | Nominal exact sign-flip `p = 0.165` (`48.9%` desk stops vs. `41.6%` executed) |
| **P2 — All-cluster desk-stop minus execution contrast** | `+30.3 pp` | Cluster bootstrap `[+22.1, +38.4]` pp | Holm `p = 6.78 x 10^-12` (driven by `118` held `desk_unrateable` clusters) |
| **P3 — All-stream primary-event alerts among fits** | `6 / 124` (`4.8%`) | CP `[1.8%, 10.2%]` (`>= 30` gate met `4x`; vs. pilot `4/13`) | Holm `p = 2.53 x 10^-12` (diagnoses pilot outcome-selection distortion) |
| **Total-tick (`c0 + c1`) dual screen (`B3`)** | `5 / 124` (`4.0%`) | CP `[1.3%, 9.2%]` (`5/6` alerts retained; `0` additional alerts) | Excludes event-scoped Position `164` (`0.00` total-tick slope) |
| **Post-hoc multi-check diagnostic filter** (`c0`, `c0 + c1`, `R^2 >= 0.94`, drop-max, `>= 80%` restoration) | `4 / 124` (`3.2%`) | CP `[0.9%, 8.1%]` (Positions `13`, `94`, `97`, `175`) | Descriptive post-hoc filter; also excludes Position `3` (`R^2_min = 0.061`, flips on drop-max) |
| **Sec. S2 — All-stream alerts among post-`S0` clusters** | `6 / 476` (`1.3%`) | CP `[0.5%, 2.7%]` | Overall intake-passing yield |
| **Sec. S4 — Execution oracle failures among executed reps** | `17 / 149` (`11.4%`) | CP `[6.8%, 17.6%]` | Upstream-accepted revisions failing independent oracle/UBSan |
| **Sec. S14 — Pre-`S3` fixture stops after `S1` pass** | `32 / 183` (`17.5%`) | Conditional execution yield `149 / 183` (`81.4%`) | Amendment 5 partition |
| **WP-P1 — Repository frame build decision** | `NO-GO (native build not triggered)` | `0 / 32` post-`S0` Repository clusters executed (`E = 27.2% > 15.5%`) | All `32` Repository clusters held `desk_unrateable` (no independent spec) |

### Forensics, Baseline Screens & Blind Author Check

- **Baseline screen selectivity (`n = 124` fits):** Ratio-only (`T/Q >= 1.50`, no slope floor) alerts on `32/124 (25.8%)`, admitting `26` non-alerts failing the all-stream slope floor (`12` flat `|slope| <= 0.05` constant-factor ratios, `6` positive sub-`0.50` slopes, `5` negative-slope precomputation cases whose ratio shrinks with `n`, and `3` stream-selective `S7` cases; `5.3x` over-alerting). Single-process `plain` CPU-time dual screening (`>= 10 ms`) yields `0/124 (0.0%)` because `~15–22 ms` sandbox startup overhead flattens small-`n` slopes, while largest-size CPU ratio `>= 1.50` flags `17/124 (13.7%)` (`3/6` primary alerts recovered—Positions `13`, `164`, `175`—plus `14` non-alerts failing the all-stream logical-slope screen).
- **Stream distinctness & drop-largest refit (`n = 124` fits):** `70/124 (56.5%)` have `3/3` distinct `(n, T(n), Q(n))` trajectories, `9/124 (7.3%)` have `2/3`, and `45/124 (36.3%)` are size-determined (`1/3`); drop-largest refit admits `6/6` alerts (`5` retained, `1` flipped) and `117/118 (99.2%)` non-alerts (`117` remained `no_alert`, `1` range-limited).
- **50-case blind `S1` author check & bidirectional tension** (`38` clusters, `0` unblinded): exact agreement `13/50 (26.0%)`, $\kappa = 0.163$ (`[0.046, 0.277]`); bucket agreement `24/50 (48.0%)`, $\kappa = 0.154$ (`[-0.031, 0.326]`). Among the `9` confirmatory `S1`-pass pairs in the blind sample (`1` author `pass`, `3` author `contract` stops, `5` author `source` stops), `7/8 (87.5%)` author-rejected pairs constructively cleared fixture authoring, optimization/sham invariance, and Gate 1 execution (`6` `no_alert`, `1` `insufficient_fit`, `1` `fixture_stop`) with `0/8` false growth alerts, while `3/26 (11.5%)` sampled workflow `contract` stops were rated `pass` by the blind author and remain unexecuted in `P1`/`P2`/`Sec. S13`.
- **Optimization & sham invariance:** `9,794` `-O0`/`-O2`/`-O3` agreements (`0` disagreements, `1,294` capped/missing); `7,349` target–sham agreements (`0` disagreements, `967` capped/missing); `6/6` all-stream alerts passed `>= 80%` causal restoration.

---

## Repository Layout

```text
.
├── manuscript/
│   ├── paired_mechanism.pdf               # Compiled camera-ready manuscript (0 warnings/overfulls/underfulls)
│   ├── paired_mechanism.tex               # Main LaTeX source (0 unguarded empirical literals)
│   ├── paired_mechanism.bib               # CrossRef / OpenReview / arXiv-verified 21-entry bibliography
│   ├── benchmark_slots.tex                # Receipt-generated LaTeX macros for 100% of reported empirical values
│   ├── grouped_statistics_macros.tex      # Fixed 147-pair / pilot specificity reference macros
│   ├── fig_s1_desk_taxonomy.pdf           # Figure 1: S1 desk-screening stop taxonomy
│   └── fig_qualification_outcomes.pdf     # Figure 2: Qualification rates vs 147-pair pilot anchors
├── protocol/
│   ├── BENCHMARK_EXPANSION_PROTOCOL.md    # Frozen master protocol (SHA-256 8a969245...)
│   ├── EXPANSION_INTAKE_RULE.md           # Frozen intake & overlap quarantine rule
│   ├── EXPANSION_INTAKE_TIMELINE.md       # Frozen intake milestone sequence
│   └── S1_PROTOCOL_AMENDMENT_{1..5}.md    # Dated S1/S3 amendments (Amendment 5 SHA-256 17de6626...)
├── data/
│   ├── anonymous-measurements.json        # Ordinal-indexed 1,000-pair per-point [c0, c1] counter & step traces (c2ba8209...)
│   ├── alert-and-fit-forensics-agg.json   # Ordinal-indexed 6-alert, 124-fit baseline screen & S1 window receipt (b8ea9b8c...)
│   ├── final-a5-stats-agg.json            # 1,000-pair Amendment 5 aggregate ledger (9eebab8d...)
│   ├── author-check-50-agg.json           # 50-case blind author-check aggregate receipt (4f84a8ef...)
│   ├── final_receipt.json                 # Full offline statistical replay receipt emitted by expansion_analyze.py
│   ├── paper_claims.json                  # Machine-checked claim ledger (evidence_class, instrument, SHA-256s)
│   └── freeze/                            # Frozen 1,000-pair manifest, hold list, statement inventory & author draw
├── analysis/
│   ├── expansion_analyze.py               # Stdlib-only offline analyzer, counter verifier & macro/claims emitter
│   └── generate_figures.py                # Matplotlib Okabe-Ito publication figure generator
├── development/                           # Pinned Gate 1 sandbox & Amendment 5 isolated execution runner (04f1a1b2...)
├── docker/                                # Gate 1 sandbox container definition (Ubuntu 26.04 + GCC 15.2.0 + Bubblewrap 0.11.1)
├── tests/                                 # Unit tests for statistical replay, per-point forensics, claims & literal guards
├── verify.py                              # Stdlib-only end-to-end checksum, leak, literal-guard & replay verifier
└── SHA256SUMS.txt                         # SHA-256 digests of all 29 verified artifacts and scripts
```

---

## Verification & Reproduction

### 1. Verify Checksums, Quarantine, Per-Point Counter Replay, Claims & Literal Guard (Stdlib-Only)

Requires Python `>= 3.11` with no third-party dependencies:

```sh
python -B verify.py
```

### 2. Run Full Unit Test Suite

```sh
python -m pip install pytest
python -B -m pytest -q
```

### 3. Rebuild Figures & Manuscript PDF (`0` Warnings / Overfulls / Underfulls)

```sh
python -B verify.py --figures --pdf
```

---

## Data Availability & Disclosure

- The frozen manifest (`data/freeze/manifest-expanded.json`) identifies public upstream versions by pins and hashes (`held_out_used: false`).
- `data/anonymous-measurements.json` (`c2ba8209...`) provides identifier-free ordinal-indexed per-point `[c0, c1]` counter traces across `target`, `reference`, `restored`, and `sham` at `-O0`/`-O2`/`-O3` (joinable to `manifest-expanded.json` via frozen `rank(row)` order). Original upstream C++ source payloads, private S1 prompts/responses/session logs, and individual author ballots remain non-public under licensing and rater-blinding boundaries, so public verification replays recorded counter traces rather than re-executing C++.
- **Use of AI:** Automated desk screening (`S1`, `2026-11-23`) judgments come from one Devin workflow with undisclosed backend routing (`replay-only` under Amendment 3) and are strictly separated from deterministic sandbox builds, independent output oracles, logical counters, and statistical checks.
