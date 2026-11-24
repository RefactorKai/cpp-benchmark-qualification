# Amendment 5: Confirmatory S3--S5 Scope and `fixture_stop`

Date: 2026-11-23 (prior to any confirmatory S3 execution, §11). Amends `BENCHMARK_EXPANSION_PROTOCOL.md` (`8a9692457cdba6d9b2860717b8bc254dae47dc48eebe7baacabb17a82007953e`) and Amendments 1--4 (`7e2b8dfdf03e8f0dfce563583e02302acadacf220fec65a511db66f45a0f5968`, `e35995283527e9ea4ae791e2b70ffe310ffe559367e61aa19207e63538f198d3`, `70e61917fb2401ad808408da8ae0f5b6483bf910048d0afa5674ba37569b330d`, `0d070e99d12c7b872a2db023e056586921c5aadcef90abe376fcee5006328940`) for `manifest-expanded.json` (`5b432d827f324c073eb7ed14b4df4b5d18f5eb2a90c4d97d358405a800d27346`), `s1_hold_list.json` (`6bc97deac805d67528e1939481c75745f51cf7350c0d3ee757598eb55c5dad01`), and `primary_sealed.json` (`270e78aa514be5841e3b6220996dbb26a5cac90a7900f3c075e6faeb836af6eb`).

## Disjoint development evidence (§11)
- S2 sweep (`s2-confirmatory-183-sweep.json`, `163133eb8ef0be09aad2336f190411a905511e38e733a6bf83d3b0540134ae99`): 183/183 confirmatory S1 passes succeeded preprocessing (`GCC 15.2.0`).
- Quarantined diagnostic (`m2-quarantined-diag-5.tar`, `06de25a1b6f1d70a5664b3f3ad570643b9619e57ae356e59c4ae001143e0e3a4`): 2/5 executed (`1 alert`, `1 no_alert`); 3/5 stopped during fixture authoring (`insufficient_workload_ladder`, `source_derived_undefined_behavior` via UBSan, `no_common_calibrated_work`).

## Changes
1. **`fixture_stop`†:** Sealed S1 labels stand unchanged. An S1 pass failing constructive fixture verification before S3 gets terminal `fixture_stop` with `{bucket, reason}` (from `DESK_STOPS` + `original_compile_failure` under `route`) and a SHA-256-pinned proof (SPEC bound, Gate 1 stderr, or code rationale). It stays in post-S0 denominators, counts as not executed in P1/S9, keeps `desk_stop=0, executed=0` in P2, stays outside P3, and is reported as **S14** (`fixture_stop / S1_pass`).
2. **Confirmatory-only quota-gated execution:** Quarantined S12 passes (204) record `not_executed`. Confirmatory S1 passes (183) run in frozen `rank(row)` order across waves stopping cleanly at `<= 75%` weekly quota (80% hard cap); any unattempted tail records `not_executed` (zero outcome selection). If truncated (`K < 183`), report both frozen bounds and contiguous-prefix conditional yield.
3. **Runner contract:** Under `AMENDMENT_5_SHA`, `fixtures`, `fixture_stops`, and `not_executed` form an exact disjoint partition of `passes`.
