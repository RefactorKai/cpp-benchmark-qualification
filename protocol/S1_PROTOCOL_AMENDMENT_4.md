# Amendment 4 to the frozen benchmark expansion protocol: `indeterminate` S1 label

Date: 2026-11-23. Approved by the owner on 2026-11-23; the commit date of this file is its effective date. Amends `BENCHMARK_EXPANSION_PROTOCOL.md` (SHA-256 `8a9692457cdba6d9b2860717b8bc254dae47dc48eebe7baacabb17a82007953e`) as already amended by `S1_PROTOCOL_AMENDMENT_1.md` (SHA-256 `7e2b8dfdf03e8f0dfce563583e02302acadacf220fec65a511db66f45a0f5968`), `S1_PROTOCOL_AMENDMENT_2.md` (SHA-256 `e35995283527e9ea4ae791e2b70ffe310ffe559367e61aa19207e63538f198d3`) and `S1_PROTOCOL_AMENDMENT_3.md` (SHA-256 `70e61917fb2401ad808408da8ae0f5b6483bf910048d0afa5674ba37569b330d`), for the frozen manifest `manifest-expanded.json` (SHA-256 `5b432d827f324c073eb7ed14b4df4b5d18f5eb2a90c4d97d358405a800d27346`). The earlier files stay committed beside this one, unchanged.

This amendment is committed after production S1 labeling under Amendment 3 has started. At that time 70 of the 96 packet batches were sealed, and the primary rater had returned `indeterminate` for one pair. No S2 or S3 run has taken place.

## What changes

1. **New terminal S1 label `indeterminate`†.** The closed label set of §2 gains `indeterminate`†, a terminal S1 outcome that the primary rater gives when it cannot decide the desk criteria for a pair. It has no bucket and no reason code.
2. **How `indeterminate` is counted.** It is counted the same way as `desk_unrateable` in Amendment 1. It is a terminal S1 outcome, not an exclusion (§7 "never excluded"). It stays in every denominator past S0. In P1 it counts as not reaching execution. In P2 it counts as a desk stop. A pair labelled `indeterminate` does not go to S2.
3. **Sealed labels stand.** An `indeterminate` label in a sealed batch is the S1 label for that pair. It is not re-rated, and the batch is not run again (Amendment 3 item 2).
4. **Runner evidence contract.** A bundle run under this amendment follows Amendment 3 item 4 unchanged, except that the runner and the private verifier accept `indeterminate`, with no bucket and no reason, as a desk entry.

## What stays the same

Everything else in the frozen protocol and Amendments 1–3, including the frozen manifest, the 844 desk-rateable pairs labelled across 96 packet batches, the 133 `desk_unrateable` pairs and the hold list, the primary rater, the batch log and private custody of Amendment 3, the blind author check, the rubric, the other labels of the closed set, all thresholds, primary outcomes P1–P3, tests, the Holm family {P1, P2, P3}, the sample-size gates, the go/no-go rule, S13 and the Repository-frame treatment. The production authorizations already recorded in the run log are unchanged.

## Reason

The frozen packet response schema lets the rater return `indeterminate`, but the closed label set of §2 had no such label and gave no rule for counting it. The owner decided on 2026-11-23 to keep the sealed `indeterminate` label and to count it as a terminal desk stop, the same way as `desk_unrateable`.

## Deviations from the frozen protocol

1. §2 line 43: the closed label set gains `indeterminate`†.
2. §11: this change is made after production S1 labels exist. It changes no existing label and no analysis rule other than adding this label's counting, and it was decided before any S2 or S3 result exists.
