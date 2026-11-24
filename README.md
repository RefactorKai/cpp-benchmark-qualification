# When Can a C++ Performance Pair Support a Growth Claim?

Empirical study and reproducibility artifact for:

> **When Can a C++ Performance Pair Support a Growth Claim? An Empirical Study of Benchmark Qualification**

This repository contains the compiled camera-ready manuscript, LaTeX sources and publication figures, frozen intake/screening protocol and dated amendments (`1`–`5`), de-identified aggregate receipts (confirmatory execution, protocol deviations, and blind 50-case human check), deterministic offline statistical replay code, pinned isolated execution runner, and unit tests.

---

## Summary of Principal Findings (`N = 1,000` Frozen Public Pairs)

A frozen five-stage qualification pipeline (`S0`–`S5`) tracked `1,000` frozen public C++ slow–fast pairs (`956` Contest pairs across PIE/CodeNet; `44` Repository pairs from public `github-performance-fix` snapshots; `held_out_used: false`). After `23` `S0` intake stops (`12` duplicates, `11` unretrievable), `476` confirmatory primary clusters (`477` pairs) and `500` development-exposed quarantined Contest pairs (`54` clusters; `204` held unexecuted) remained:

| Contrast / Outcome | Estimate | 95% Interval / Summary | Test / Gate |
| --- | --- | --- | --- |
| **P1 — Execution yield** (`>= 1` executed variant post-`S0`) | `149 / 476` (`31.3%`) | CP `[27.2%, 35.7%]` (ref. `14/147 = 9.5%`) | Holm `p = 1.97 x 10^-39` |
| **P2 — Desk-stop minus execution contrast** | `+30.3 pp` | Cluster bootstrap `[+22.1, +38.4]` pp | Holm `p = 6.78 x 10^-12` |
| **Sec. S13 — `P2` excluding `118` held `desk_unrateable` clusters** (`358` rateable Contest clusters) | `+7.3 pp` (`149/358 = 41.6%`) | Cluster bootstrap `[-2.8, +17.0]` pp | Nominal exact sign-flip `p = 0.165` |
| **P3 — All-stream alerts among fitted representatives** | `6 / 124` (`4.8%`) | CP `[1.8%, 10.2%]` (`>= 30` fits met `4x`; ref. `4/13`) | Holm `p = 2.53 x 10^-12` |
| **Sec. S2 — All-stream alerts among post-`S0` clusters** | `6 / 476` (`1.3%`) | CP `[0.5%, 2.7%]` | Secondary descriptive |
| **Sec. S4 — Execution oracle failures among executed reps** | `17 / 149` (`11.4%`) | CP `[6.8%, 17.6%]` | Secondary descriptive |
| **Sec. S14 — Pre-`S3` fixture stops after `S1` pass** | `32 / 183` (`17.5%`) | Conditional execution yield `149 / 183` (`81.4%`) | Amendment 5 partition |
| **WP-P1 — Repository frame build decision** | `NO-GO (native build not triggered)` | `0 / 32` post-`S0` Repository clusters executed (`E = 27.2% > 15.5%`) | Pre-specified gate |

### Blind Author Check & Measurement Stability Checks

- **50-case blind `S1` author check** (`38` clusters, `unblinded_count = 0`, pre-unblinding SHA-256 `1d868127...`): exact 5-label agreement `13/50 (26.0%)`, $\kappa = 0.163$ (`[0.046, 0.277]`); 3-way bucket agreement `24/50 (48.0%)`, $\kappa = 0.154$ (`[-0.031, 0.326]`). Confusion (`primary x author`): `pass (22)` -> `3 pass, 12 contract, 7 source`; `contract (26)` -> `3 pass, 19 contract, 4 source`; `source (2)` -> `2 source`.
- **Alert-level independent restoration:** `6/6` all-stream alerts passed $\ge 80\%$ independent oracle restoration (`0` failures).
- **Compiler optimization & sham invariance:** `9,794` `-O0`/`-O2`/`-O3` agreements (`0` disagreements, `1,294` capped/missing); `7,349` target–sham agreements (`0` disagreements, `967` capped/missing).
- **Censoring & oracle sensitivity:** Reverting all `3` `cpu_cap` (`exit 137`) positions (`[90, 99, 139]`, `28` events across `3` positions) bounds unpatched `P1` at `146/476 (30.7%)` and `P3` at `6/121 (5.0%)`; conservatively assigning the `6` Wave 1 oracle-restored pairs yields `P1 = 143/476 (30.0%)`, `P2 = +31.5 pp`, `S4 = 11/143 (7.7%)`, `S14 = 38/183 (20.8%)`.

---

## Repository Layout

```text
.
├── manuscript/
│   ├── paired_mechanism.pdf            # Compiled 11-page camera-ready manuscript (0 warnings/overfulls)
│   ├── paired_mechanism.tex            # Main LaTeX source
│   ├── paired_mechanism.bib            # CrossRef / OpenReview-verified 7-entry bibliography
│   ├── benchmark_slots.tex             # Receipt-generated LaTeX macros for all reported counts and p-values
│   ├── grouped_statistics_macros.tex   # Fixed 147-pair / Part A specificity reference macros
│   ├── fig_s1_desk_taxonomy.pdf        # Figure 1: S1 desk-screening stop taxonomy (Confirmatory vs Quarantined)
│   └── fig_qualification_outcomes.pdf  # Figure 2: Qualification rates vs 147-pair fixed development reference
├── protocol/
│   ├── BENCHMARK_EXPANSION_PROTOCOL.md # Frozen master protocol (SHA-256 8a969245...)
│   ├── EXPANSION_INTAKE_RULE.md        # Frozen intake & overlap quarantine rule
│   ├── EXPANSION_INTAKE_TIMELINE.md    # Pre-registered intake milestone sequence
│   └── S1_PROTOCOL_AMENDMENT_{1..5}.md # Dated S1 amendments (Amendment 5 SHA-256 17de6626...)
├── data/
│   ├── final-a5-stats-agg.json         # De-identified 1,000-pair Amendment 5 aggregate ledger
│   ├── author-check-50-agg.json        # De-identified 50-case blind author-check aggregate receipt
│   ├── final_receipt.json              # Full offline statistical replay receipt emitted by expansion_analyze.py
│   └── freeze/
│       ├── manifest-expanded.json      # Frozen 1,000-pair upstream version manifest (held_out_used: false)
│       ├── s1_hold_list.json           # Pre-execution deterministic desk_unrateable hold list (133 pairs)
│       ├── s1_statement_inventory.json # Statement inventory for frozen corpus rules
│       └── s1_author_check_draw.json   # Stratified 50-pair blind draw indices
├── analysis/
│   ├── expansion_analyze.py            # Stdlib-only offline analyzer & benchmark_slots.tex generator
│   └── generate_figures.py             # Matplotlib Okabe-Ito publication figure generator
├── development/
│   ├── gate1_sandbox.py                # Bubblewrap + systemd-run --scope Gate 1 execution wrapper
│   └── paired_study/
│       ├── expansion_run.py            # Pinned Amendment 5 isolated execution runner (04f1a1b2...)
│       ├── expansion_fixtures.py       # Pre-S3 fixture packaging & validation
│       ├── predict.py                  # Blind growth-fit & ratio scoring engine
│       └── path_b_run.py               # Compiler flag / mode definitions
├── docker/                             # Gate 1 sandbox container build definition (Ubuntu 22.04 + g++ + bwrap)
├── tests/
│   ├── test_expansion_analyze.py       # Offline statistical, Holm, bootstrap, kappa & LaTeX macro tests
│   ├── test_expansion_run.py           # Execution runner, exit-137 cpu_cap & A5 partition tests
│   └── test_expansion_fixtures.py      # Fixture validation tests
├── verify.py                           # Stdlib-only end-to-end integrity, leak audit & receipt replay script
├── SHA256SUMS.txt                      # SHA-256 digests of all published artifacts and scripts
├── pyproject.toml                      # Project and pytest configuration (Python >= 3.11)
└── requirements-ast.txt                # Pinned tree-sitter dependencies
```

---

## Verification & Reproduction

### 1. Verify Checksums, Quarantine, and Statistical Replay (Stdlib-Only)

Requires Python `>= 3.11` with no third-party dependencies:

```sh
python -B verify.py
```

This checks all entries in `SHA256SUMS.txt`, asserts `held_out_used == false` in `data/freeze/manifest-expanded.json`, scans `data/*.json` and `manuscript/*.{tex,bib}` for any unredacted submission/problem identifiers, replays `analysis/expansion_analyze.py` on the aggregate receipts inside a temporary directory, asserts byte-identical normalized `manuscript/benchmark_slots.tex` and exact equality to `data/final_receipt.json`, and checks every `\Bench*` and `\Grouped*` LaTeX macro reference.

### 2. Run Full Unit Test Suite

```sh
python -m pip install pytest
python -B -m pytest -q
```

### 3. Optional Figure & Manuscript PDF Rebuild

- Regenerate Figures 1 and 2 (`matplotlib` and `numpy` required):
  ```sh
  python -B verify.py --figures
  ```
- Recompile `manuscript/paired_mechanism.pdf` cleanly (`pdflatex` and `bibtex` required, asserts zero warnings and zero overfull hboxes):
  ```sh
  python -B verify.py --pdf
  ```

### 4. Isolated C++ Execution Environment (Docker / Gate 1)

See [`docker/README.md`](docker/README.md) and [`docker/gate1.Dockerfile`](docker/gate1.Dockerfile) for the pinned Bubblewrap (`0.11.1`) + `g++` C++17 execution environment used by `development/paired_study/expansion_run.py`.

---

## Frozen Protocol & Amendment Digests

| Document | SHA-256 Prefix | Role |
| --- | --- | --- |
| `protocol/BENCHMARK_EXPANSION_PROTOCOL.md` | `8a969245` | Frozen confirmatory `S0`–`S5` & `P1`–`P3` statistical plan |
| `data/freeze/manifest-expanded.json` | `5b432d82` | `1,000`-pair pinned draw (`held_out_used: false`) |
| `data/freeze/s1_hold_list.json` | `6bc97dea` | Deterministic `133`-pair `desk_unrateable` hold list |
| `protocol/S1_PROTOCOL_AMENDMENT_4.md` | `0d070e99` | Pre-`P3`-gate `indeterminate` terminal disposition rule |
| `protocol/S1_PROTOCOL_AMENDMENT_5.md` | `17de6626` | Pre-`S3` `fixture_stop` vs. `not_executed` quota partition |
| `development/paired_study/expansion_run.py` | `04f1a1b2` | Pinned Amendment 5 runner (`exit 137` -> `cpu_cap`) |

---

## Data Availability & Disclosure

- The frozen manifest identifies public upstream versions by pins and hashes.
- In accordance with upstream licensing and referee/rater privacy boundaries, locally retained raw source payloads, private work archives, and individual rater ballots are excluded (`data/` provides aggregate de-identified receipts only).
- **Use of AI:** Automated desk screening (`S1`) judgments are explicitly isolated and disclosed as model judgments separately from deterministic sandbox builds, independent output oracles, logical operation counters, and statistical tests. Generative AI assisted in manuscript drafting and tooling assembly under human verification.
