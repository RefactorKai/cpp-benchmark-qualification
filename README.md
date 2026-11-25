# When Can a Standalone C++ Performance Pair Support a Growth Claim?

Companion artifact and reproducibility suite for:

> **When Can a Standalone C++ Performance Pair Support a Growth Claim? An Empirical Study of Benchmark Qualification**

This repository contains the compiled manuscript and LaTeX sources, receipt-bound claim provenance (`data/paper_claims.json`: `21` manifest-recomputed `re-executable` claims, `48` `protocol-constant` design parameters, and `replay-only` execution/triage claims), five publication figures, immutable pre-execution protocol archives (`protocol/`, with reader index in `protocol/README.md`), de-identified ordinal-indexed counter traces (`data/anonymous-measurements.json`, `c2ba8209...`), byte-frozen aggregate forensic, CPU, and inter-rater receipts (`b8ea9b8c...`, `9eebab8d...`, `4f84a8ef...`), stdlib-only offline statistical replay scripts, pinned Gate 1 sandbox runners, and unit tests.

---

## Summary of Principal Findings (`N = 1,000` Frozen Public Pairs)

A five-stage qualification pipeline (`S0`–`S5`) audited `1,000` frozen public C++ slow–fast pairs (`956` Contest pairs from PIE and CodeNet; `44` Repository commits from public `github-performance-fix` snapshots; `held_out_used: false`).

After `23` Stage `S0` intake stops (`12` Contest duplicates and `11` unretrievable Repository pairs), `977` `S0`-pass pairs remained: `500` development-exposed quarantined Contest pairs (`54` clusters; `296` `S1` stops and `204` `S1` passes kept unexecuted at closure) and `477` confirmatory pairs across `476` confirmatory clusters (`444` Contest singletons and `32` Repository clusters comprising `33` pairs). All `32` confirmatory Repository clusters stopped at Stage `S1` under `no_independent_repository_spec`, and the conditional Protocol §9 native-build branch was not triggered (`27.2% > 15.5%` with zero Repository route stops); dynamic execution, oracle, and scaling measurements therefore characterize standalone Contest kernels exclusively while preserving all `32` Repository clusters in the `476`-cluster `S0`/`S1` denominator.

| Contrast / Outcome | Estimate | 95% Interval / Summary | Calibration / Context |
| --- | --- | --- | --- |
| **P1 — Execution yield** (`>= 1` executed variant post-`S0`) | `149 / 476` (`31.3%`) | CP `[27.2%, 35.7%]` (Contest `149/444 = 33.6%`) | Post-hoc conservative Fisher Holm-3 `p = 5.45 x 10^-8` (`1-S` `1.97 x 10^-39`) vs. pilot `14/147` |
| **P2 — All-cluster desk-stop minus execution contrast** | `+30.3 pp` (`476` cl.) | Cluster bootstrap `[+22.1, +38.4]` pp | Holm-3 `p = 2.03 x 10^-11` (`81.9%` from `118` pre-execution holds) |
| **SA13a / SA13b — Rateable Contest execution & contrast** (excl. `118` holds) | `149 / 358` (`41.6%`), `+7.3 pp` | Cluster bootstrap `[-2.8, +17.0]` pp | Exact sign-flip `p = 0.165` (stays `0.082`–`0.203` across receipt-backed toggles; fragile to S1 FPs/FNs) |
| **P3 — All-stream primary-event alerts among fits** | `6 / 124` (`4.8%`) | CP `[1.8%, 10.2%]` (vs. pilot `4/13`; `tick_cap` `8/126`, `p = 0.056` vs. `3/12`) | Post-hoc conservative Fisher Holm-3 `p = 0.0076` (`1-S` `2.53 x 10^-12`); sensitive to S1 `no_alert` FPs |
| **Total-tick (`c0 + c1`) dual screen (`B3`)** | `5 / 124` (`4.0%`) | CP `[1.3%, 9.2%]` (`5/6` alerts retained; `0` new alerts) | Excludes event-scoped `Case 164` (`0.0002` total-tick slope) |
| **4-check logical-counter upper bound** (`B3`, `SA8` drop-max, Theil–Sen `>= 0.50`, `>= 80%` rest.) | `4 / 124` (`3.2%`) | CP `[0.9%, 8.1%]` (`Cases 13, 94, 97, and 175`) | Unverified upper bound (`0/124` AST-verified minimal restorations); `>= 2/124` (`Cases 13, 175`) lower bound on single-invocation container CPU `>= 1.50x` |
| **SA2 — All-stream alerts among post-`S0` clusters** | `6 / 476` (`1.3%`) | CP `[0.5%, 2.7%]` | Overall intake-passing yield (invariant to S1 pass-arm FPs) |
| **SA4 — Execution oracle / UBSan failures** | `17 / 149` (`11.4%`) | CP `[6.8%, 17.6%]` (post-run sensitivity `7.7%`–`11.6%`) | Lower bound under `-O2`-only UBSan without ASan (`16/149` upstream + `1` confounded `restored` at `Case 27`) |
| **SA14 — Pre-`S3` fixture stops after `S1` pass** | `32 / 183` (`17.5%`) | CP `[12.3%, 23.8%]`; conditional yield `149 / 183` (`81.4%`) | `0/154` runner `S2` stops (`29` pre-execution synthesis stops + `3` post-execution audit reclassifications) |

### Forensics, Comparator Screens & Stratified Blind Author Audit

- **Screen selectivity (`n = 124` fits):** Ratio-only (`B1`, `r_max >= 1.50`) flags `32/124 (25.8%)` (`Holm-5 p = 1.49 x 10^-7` vs. `B0`), admitting `26` false-growth positives (`12` flat constant-factor, `6` positive sub-`0.50` / `Theta(log n)`, `5` negative-slope precomputations, `3` stream-selective `SA7`). Single-invocation container `plain` CPU dual screening (`B4`, `>= 10 ms`) flags `0/124 (0.0%, Holm-5 p = 0.094)` due to `14`–`22 ms` Bubblewrap + `systemd-run` spawn overhead, while single-invocation CPU ratio (`B5 >= 1.50x`) flags `17/124 (13.7%, Holm-5 p = 0.051)` (`2/4` logical-core alerts; `Case 97` runs at `54.2–90.3 ns/tick` on `n <= 32` beneath the wrapper floor).
- **Stratified 50-pair blind `S1` author audit (`38` clusters, `0` unblinded):** Overall exact match `26.0%` (`kappa = 0.163`), 3-bucket `48.0%` (`kappa = 0.154`), binary `pass/stop` `56.0%` (`kappa = 0.032`). Stratifying exposes a two-fold quarantine familiarity confound (`60.0%` on `30` quarantined pairs vs. `30.0%` on `20` confirmatory singletons, where binary reliability drops to `kappa = -0.170`). Among `8` sampled author-rejected confirmatory LLM passes, `7/8 (87.5%)` executed in Gate 1 yet produced `0` growth alerts (`6` `no_alert` fits, `1` `insufficient_fit`, `1` `fixture_stop`), showing that harness executability does not imply S1 work-delta eligibility. Two-sided S1 error bounds: `SA13b` flips negative at unmeasured FN yield `theta > 7.4%` (`6.7%` two-step; exact Jeffreys `[6.8, 46.1]%`) and flips significantly positive (`+10.6 pp, p = 0.0397`) if just `6/149 (4.0%)` executed passes are S1 FPs; among sampled confirmatory fitted LLM passes, the blind author rejected `6/7 (85.7%)`, and removing `20/118 (16.9%)` `no_alert` FPs lifts `P3` above `p = 0.05` vs. conservative `3/12` (`p = 0.0503`; `57/118 = 48.3%` vs. `4/13`, `p = 0.0517`).
- **Cross-optimization scalar exit-counter parity & sham checks:** `9,794/11,088` `-O0`/`-O2`/`-O3` triples (`0` mismatches; `12/12` `-O0`-only capped triples agree on `O2==O3`) verify scalar exit-count parity (UB/value divergence checking, not unoptimized runtime work), alongside `7,349/8,316` `target==sham` pairs (`0` mismatches, conditioned on unverified `sham != target` non-identity) and `0/47` violations of symmetric non-regression `R_0 <= max(T_0, Q_0)`.

---

## Repository Layout

```text
.
├── manuscript/
│   ├── paired_mechanism.pdf               # Compiled manuscript
│   ├── paired_mechanism.tex               # Main LaTeX source
│   ├── paired_mechanism.bib               # Verified bibliography (44 entries)
│   ├── benchmark_slots.tex                # Receipt-generated LaTeX macros
│   ├── grouped_statistics_macros.tex      # Archived pilot specificity diagnostic macros (3 used)
│   ├── fig_pipeline_funnel.pdf            # Figure 1: Qualification pipeline, attrition funnel & 3-zone boundaries
│   ├── fig_s1_desk_taxonomy.pdf           # Figure 2: Stage S1 desk-triage dispositions & stop-reason taxonomy
│   ├── fig_scaling_landscape.pdf          # Figure 3: 124-fit scaling regimes & B0-B5 screen selectivity
│   ├── fig_alert_trajectories.pdf         # Figure 4: Log-log counter & plain-CPU ratio trajectories (W1-W3, all 6 alerts)
│   └── fig_manski_tipping.pdf             # Figure 5: Manski linear tipping bounds & P3 censoring/stop sensitivity
├── protocol/
│   ├── README.md                          # Archive index, terminology mapping & custody notes (unpinned)
│   ├── BENCHMARK_EXPANSION_PROTOCOL.md    # Frozen master protocol (8a969245...)
│   ├── EXPANSION_INTAKE_RULE.md           # Frozen intake, pinning & quarantine rule (5525479a...)
│   ├── EXPANSION_INTAKE_TIMELINE.md       # Frozen chronological intake record (3622d0d3...)
│   └── S1_PROTOCOL_AMENDMENT_{1..5}.md    # Frozen protocol amendments 1-5 (through 17de6626...)
├── data/
│   ├── anonymous-measurements.json        # De-identified ordinal-indexed per-point [c0, c1] traces (c2ba8209..., 0 CPU fields)
│   ├── alert-and-fit-forensics-agg.json   # Byte-frozen 6-alert CPU series & non-alert B4/B5 confusion counts (b8ea9b8c...)
│   ├── final-a5-stats-agg.json            # Byte-frozen 1,000-pair Amendment 5 aggregate receipt (9eebab8d...)
│   ├── author-check-50-agg.json           # Byte-frozen 50-pair blind author audit aggregate receipt (4f84a8ef...)
│   ├── final_receipt.json                 # Offline statistical replay receipt emitted by expansion_analyze.py
│   ├── paper_claims.json                  # Provenance-linked claim table (re-executable, protocol-constant, replay-only)
│   └── freeze/                            # Frozen S0 manifest (5b432d82...), hold list (6bc97dea...), inventory & draw
├── analysis/
│   ├── expansion_analyze.py               # Stdlib-only offline analyzer, Lentz betainc/Simpson quadrature & macro/claims emitter
│   └── generate_figures.py                # Matplotlib Okabe-Ito 5-figure generator
├── development/                           # Byte-frozen Gate 1 sandbox (7f9bf00a), runner (04f1a1b2), predict (e695e1dd), MODES stub (d1457d53)
├── docker/                                # Pinned Gate 1 & verification container (Ubuntu 26.04 + GCC 15.2.0 + Bubblewrap 0.11.1)
├── tests/                                 # Unit tests for statistical replay, forensics, claims, fixtures & literal guards
├── verify.py                              # Stdlib-only checksum, identifier-leak, claim-SHA, literal-guard & replay verifier
└── SHA256SUMS.txt                         # SHA-256 digests covering every tracked repository file
```

---

## Verification & Reproduction

### 1. Verify Checksums, Quarantine, Claim Provenance, Per-Point Counter Replay & Literal Guard (Stdlib-Only)

Requires Python `>= 3.11` with no third-party dependencies:

```sh
python -B verify.py
```

### 2. Run Full Unit Test Suite

```sh
python -m pip install pytest
python -B -m pytest -q
```

### 3. Regenerate All 5 Figures (With Raster Parity Check) and Recompile the Manuscript PDF

Requires `matplotlib`, `numpy`, `pdflatex`, `bibtex`, and optionally `pdftoppm` (see `pyproject.toml` and `docker/README.md`):

```sh
python -B verify.py --figures --pdf
```

### 4. Exporting a Double-Blind Archive (Stripping `.git/` Metadata)

For double-blind conference submission, export a clean archive without Git commit authorship metadata:

```sh
git archive --format=zip --prefix=cpp-benchmark-qualification/ -o cpp-benchmark-qualification-blind.zip HEAD
```

---

## Evidentiary Boundaries & Custody (3-Zone Verification Model)

1. **Zone 1 (`re-executable` & `protocol-constant`):** `21` S0 intake, deduplication, clustering, and exact singleton counts recompute directly from `data/freeze/manifest-expanded.json` (`5b432d82...`, `held_out_used: false`); `48` fixed study parameters are tagged `protocol-constant`.
2. **Zone 2 (`replay-only`):** Stage `S1` hold and rateability aggregates, single-workflow LLM desk screening (undisclosed backend routing), and the 50-pair blind author audit replay from byte-frozen aggregates (`data/final-a5-stats-agg.json`, `data/author-check-50-agg.json`); per-pair author ballots remain offline.
3. **Zone 3 (`replay-only` above traces):** Gate 1 execution (`bwrap` + GCC 15.2.0, 4 variants × 5 modes) ran offline using pinned `expansion_run.py` (`04f1a1b2...`), `gate1_sandbox.py` (`7f9bf00a...`), and `predict.py` (`e695e1dd...`; `path_b_run.py` `d1457d53...` is the standalone `MODES` extract of archived `281d793c...`). Third-party C++ payloads and AST diffs remain offline. `data/anonymous-measurements.json` (`c2ba8209...`, zero CPU fields) replays all 124 fits, `B0`–`B3`, censoring bounds, and restoration counts, while `data/alert-and-fit-forensics-agg.json` (`b8ea9b8c...`) supplies per-point CPU series for the 6 primary alerts plus aggregated `B4`/`B5` 2×2 confusion counts for non-alerts.
4. **Identifier Hygiene:** Zero raw upstream identifiers appear in manuscript prose, tables, figures, or trace files; public intake identifiers appear solely in the frozen pinning artifacts under `data/freeze/` used for Zone-1 clustering, hold pinning, and Table 3 corpus-parity replay, while all measurement, aggregate, and receipt JSON files under `data/` are de-identified (`0` identifier matches).
