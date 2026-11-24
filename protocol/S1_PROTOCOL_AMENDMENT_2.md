# Amendment 2 to the frozen benchmark expansion protocol: drop the S1 agreement analysis

Date: 2026-11-23. Approved by the owner on 2026-11-23; the commit date of this file is its effective date. Amends `BENCHMARK_EXPANSION_PROTOCOL.md` (SHA-256 `8a9692457cdba6d9b2860717b8bc254dae47dc48eebe7baacabb17a82007953e`) as already amended by `S1_PROTOCOL_AMENDMENT_1.md` (SHA-256 `7e2b8dfdf03e8f0dfce563583e02302acadacf220fec65a511db66f45a0f5968`, freeze commit `f3110bfed0b02bdbacfddb4b3f469a8047a0d5bd`), for the frozen manifest `manifest-expanded.json` (SHA-256 `5b432d827f324c073eb7ed14b4df4b5d18f5eb2a90c4d97d358405a800d27346`). Both earlier files stay committed beside this one, unchanged.

This amendment is committed before any production S1 label exists and before any S2 or S3 run (§11). Two feasibility pilots exist: batch-001 with a Gemini primary rater (10 records) and a Groq second rater (2 records), and a Devin Lite pilot (2 records). They are workflow tests only. None of their labels enters the study, and none was read in drafting this amendment. The author has seen no production label, rater output or execution result.

## What changes

1. **No second rater (removes Amendment 1 item 3).** Only the primary rater runs. No second model family labels any pair, including the fixed 100-pair draw.
2. **No agreement statistic (removes Amendment 1 item 4 and protocol S11).** Cohen's κ, raw percent agreement and their bootstrap interval are not computed. The secondary outcome list loses S11. The numbering of S12 and S13 stays the same.
3. **Amendment 1 item 5 lapses.** With no second rater there are no disagreements to report. The rule that no third model adjudicates and that no primary label is ever changed by another model still holds.
4. **Agreement draw kept as a record only.** `s1_agreement_draw.json` (SHA-256 `e15d89ed6808527a91a6dd9188162dad4a280baefe44653fe5a9f5c97b521ced`) stays committed and `s1_scope.py` still checks it. It selects no case for any rater and feeds no analysis.
5. **Runner evidence contract.** For a bundle run under this amendment, the S1 evidence is the packet hash plus the sealed primary-rater output hash. The runner must refuse a bundle that carries a second-rater or agreement-draw pin as S1 evidence. It must never be given a placeholder, duplicate or synthetic hash in their place. The checkpoint header records this amendment's SHA-256 and a design label distinct from `amendment_1`.

## What stays the same

- The frozen manifest, clusters, representative pairs, quarantine and S0 labels.
- The 844 desk-rateable pairs, the 133 `desk_unrateable` pairs, the hold list (SHA-256 `6bc97deac805d67528e1939481c75745f51cf7350c0d3ee757598eb55c5dad01`) and its reason codes. Held pairs are never sent to a rater and stay in every denominator past S0, as in Amendment 1.
- Amendment 1 items 1 and 2: one primary rater labels all 844 pairs, and its label is the S1 label in every analysis.
- The blind input packet, its manifest (SHA-256 `1f66f5b6b46456208ea3f8ab9e0a86d04ed9f4c6e52c48da1d1c3a89a5261d4d`) and the rater ZIP (SHA-256 `723a0bae85d045e9fe2a91c270f514c9ca6a4cd372543ab0c2ebdbc9ae6a7c3e`) remain private custody material under D5.
- The primary rater's raw output is saved and hash-sealed before any use, with model ID, version, date, decoding settings and full prompt.
- The closed label set of §2 with `desk_unrateable`†, the rubric, the S1-before-S2 order, the no-deferral rule and the stable-hash order into S2.
- All thresholds, primary outcomes P1–P3, tests, the Holm family {P1, P2, P3}, the sample-size gates, the go/no-go rule, S13 and the Repository-frame treatment of Amendment 1. The analysis runs once, with no interim look at P1–P3.

## Reason

The owner decided on 2026-11-23 to drop the secondary agreement analysis. The S1 budget is $0. A second model pass would need paid quota or the unpaid Gemini API, whose terms let the provider use prompts and responses to improve its products, allow human review, and ask users not to submit confidential information. That conflicts with packet custody under D5. κ was secondary and outside the Holm family, so no primary outcome, threshold or test depends on it. The change is procedural.

## Deviations from the frozen protocol and owner rules

1. §2 line 54 and S11: no inter-model agreement is measured on any S1 label. Amendment 1 had already reduced this to a 100-pair sample.
2. §11: a change needs "disjoint evidence". There is none for this decision. The decision and its reason are recorded here instead.
3. Owner rule D4 and the repository skill `eapg-blind-validation` (two blind raters on different model families plus a third-model adjudicator): S1 now departs from it entirely, by owner decision on 2026-11-23.

## Effect on claims

- The S1 labels are single-model labels with no inter-model agreement check. P1 and P2 depend on them. The paper says so wherever it reports them. It reports no κ, agreement figure or "model-based validation" for the expansion S1 labels.
- §12 replaces Amendment 1's line "S1 labels come from one model; inter-model agreement was measured on a fixed 100-pair sample only" with: "S1 labels come from one model. No second model or human checked them."
- Agreement results for the 147-pair development panels come from their own receipts and are unaffected.
