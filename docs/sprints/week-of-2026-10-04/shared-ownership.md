# Shared execution and proof ownership

Period: 2026-10-04 through 2026-10-10 (Sunday–Saturday).

[Week index](README.md)

## Objective

Consolidate shared arithmetic, HashLife and Isabelle ownership without changing
sequence semantics, scheduler identity, execution budgets or release assertions.

## Changes

The registration reader follows ROOTS, rebases session paths to one proof root,
and checks dependencies across registrations. Every ROOT remains subject to the
shared execution policy. Negative tests cover hidden roots, duplicates, cycles,
missing registrations, symlink escapes and nested policy overrides.

Shared Python algebra is extracted from family owners while recurrence-specific
adapters move in the opposite direction. Proof sessions are grouped beneath shared,
family and integration roots; theorem assumptions and session boundaries remain.

The proof inventory includes a Git-referenced ownership history, checks its live
destinations and declaration names, and labels audit-only sessions. Native Isabelle
validation exposed the need to quote nested session paths; the parser now rejects
the unquoted form. Multiline `sessions` dependencies and inline theory declarations
are retained rather than silently omitted.

The assertion-preserving test moves are:

| Previous owner | Current owner | Coverage disposition |
| --- | --- | --- |
| `tests/hashlife/execution/test_collatz_root_skip.py` | `tests/sequences/collatz/test_collatz_root_skip.py` | Same family root-skip assertions |
| `tests/hashlife/execution/test_collatz_root_completion.py` | `tests/sequences/collatz/test_collatz_root_completion.py` | Same authenticated completion assertions |
| `tests/hashlife/observation/test_diamond_cycles.py` | `tests/sequences/collatz/test_diamond_cycles.py` | Same Collatz cycle assertions |
| Finite cycle certificate test in shared `test_diamond_geometry_payloads.py` | `tests/sequences/collatz/test_diamond_cycles.py` | Same source, complete-phase and representation-boundary assertions, with explicit Collatz scheduler hooks |
| Last six tests in `test_semantic_comma_future.py` | `tests/repository/test_semantic_comma_occurrence_cache.py` | Same publication, memo-authority and selected-list assertions; split to preserve the source line limit |
| Pure clock tests in `tests/sequences/collatz/test_inverse_three_clock.py` | `tests/arithmetic/fields/test_inverse_three_clock.py` | Same bijection, phase/lift and single-root evaluation assertions; family source/tangent tests remain in Collatz |
| Prime tests in shared `test_source_bound_images.py` | `tests/sequences/prime/test_source_payload_audit.py` | Arena and image tampering remain rejected at their combined audit boundary; only the explicitly measured audit-member visit counter may change, with all execution counters and storage unchanged |
| `tests/hashlife/execution/test_tile_causal_pair_transfer.py` | `tests/sequences/reverse_add/test_tile_pair_transfer.py` | Same finite transfer, terminal, side, width and radix-2/3/10 cases; fixture supplies the production family strategy |
| Reverse public warm-projection test in shared `test_source_bound_images.py` | `tests/sequences/reverse_add/test_projection_authority.py` | Same rejection before a cache hit when the source binding changes |

The canonical P0 file selection is unchanged by these moves. The Schur/Native19 dependency assertions
now require `Shared_Carry_Dynamics` instead of `Reverse_Residuals`; their exclusions
of fuel, future-certificate and concrete-table dependencies remain intact.

The Python owner changes preserve recurrence-specific contracts:

| Previous implementation owner | Canonical implementation owner |
| --- | --- |
| `hashlife.tiles.tile_context.TemporalCocycle` | `hashlife.tiles.temporal_cocycle`, with the existing re-export |
| Collatz physical support grammar | Generic ordered Boolean grammar in `hashlife.tiles.ordered_boolean_support`; parity projections remain in `sequences.collatz.physical_support` |
| `resources.prime_number_theory` | Pure arithmetic in `arithmetic.number_theory`, with the public prime re-export |
| Generic arithmetic congruence/idempotent output modules | Prime congruence in `sequences.prime`; special-number output in `sequences.power_numbers` |
| Reverse extent implementation in `arithmetic.fields.symbolic_extent` | `sequences.reverse_add.extent`, implementing the shared extent protocol |
| Collatz root/cycle execution helpers in HashLife | `sequences.collatz`, supplied through the scheduler's typed family hooks |
| Collatz inverse-three clock used by Mahler | Pure unit-clock arithmetic in `arithmetic.fields.inverse_three_clock`; Collatz keeps its public re-export and source-cylinder projection |

Family adapters now supply scheduler hooks explicitly, including offline C4
construction and verification. The public compatibility hook remains available;
the production runtime hook does not load the proof-only physical kernel. Shared
payload auditing validates exact registered objects and ledger-issued snapshots.
It rejects stale snapshots, foreign roots, numeric key aliases and invalid child
dependencies without treating a whole container as an opaque approved payload.
Warm-parent, reset, cancellation and tampering assertions remain enabled.

The independent proof review compared 145 mapped declarations and found no changed
reviewed theorem statements or assumptions. Five carrier/locale declarations needed
manual review beyond the parser, and three identity aliases use equivalent forms.
The Comma-specific `selected_list_conversion.ML`, `proof_profile.ML` and
`Proof_Dependency_Audit.ML` belong to `families/comma/comma_entry_arithmetic`;
their 21 consumer sessions retain their names and logical dependencies. No ML
implementation remains under the extracted shared carry owner. Request-local refs
are distinguished from shared mutable caches; uncertain references remain review
findings rather than grounds for automatic deletion.

Two baseline acceptance-environment defects were identified: a probe fixture
assumed development evidence mode, and a documentation link assumed ignored local
results were present in a clean worktree. Coverage now checks both evidence modes;
the historical evidence location is described without requiring generated files.

## Established results

The unchanged baseline unit selection completed in 290.73 seconds: 8,974 passed,
16 failed and 2,078 deselected. Thirteen failures concern the reverse completed-child
constructor, one concerns special-number recovery, and two concern the acceptance
environment described above. There were no Collatz failures.

The first focused registration and runner selection passed 26 tests in 3.91 seconds.
The later registration, ownership-path and source-admission repair selection passed
170 tests in 24.95 seconds (`20261006T074343Z-98a4bb64b5f04a2da69fcdc2697265cd`).
This validates discovery and enforcement, not the full ownership migration.

The first dependency-aware native build passed. Rebuilt sessions were
`Shared_S_Arithmetic` (reported 60 seconds), `Shared_Carry_Dynamics` (5 seconds),
`Reverse_Residuals` (16 seconds) and `Collatz_Cylinder_Refinement` (8 seconds).
The second build passed Comma's extracted Schur/Native19 arithmetic, factored ports,
and Antihydra–Mahler integration. It identified an existing missing Antihydra theory
import in `Dyadic_Parity_Inverse_Arithmetic`; the corrected dependency-aware
`Balanced_Dyadic_Integration` build passed. These results do not certify the
separate global Comma cutover.

The original commit's five-trial 16–1024 comparison, using both output bases and
cold/warm/bypassed modes, completed for Antihydra in 16.68 seconds. The reverse
command reached the 60-second limit. The Collatz command's default point position
2 becomes out of range after cycle entry and raised `IndexError`; this is an
invalid probe configuration, not evidence of incorrect Collatz output. A valid
point position must be used identically for both sides of the migration comparison.
The corrected baseline Collatz comparison at point position 0 completed in 17.70
seconds with the same horizons, trials, bases and cache modes.

The final whole-tree typing, pinned Ruff, formatting, source policy, documentation,
proof inventory and installed-wheel checks passed in development run
`20261006T080727Z-38497c6ada784d49b74d2c22013a464a`.
The inventory has 138 sessions and 328 theories. The slowest quality command was
source policy at 36.09 seconds; installed-wheel validation took 34.23 seconds.

Two additional validation-marked reverse assertions request the absent
`reverse_morphism_directional_leaf_consumers` counter. Both failures reproduce on
the untouched baseline commit, with exact output assertions passing first. Their
assertions remain unchanged; they are not attributed to this relocation.

The aggregate native build passed the relocated Antihydra/Mahler safety sessions
and many Comma dependencies. `Comma_Semantic_Future` and `Temporal_Clock_Jumps`
reached their 60-second timeout. `Comma_Semantic_B1` reported completion at 62
seconds, which exceeds the policy even though Isabelle marked it successful.
The runner now separately rejects completed sessions whose reported duration
exceeds 60 seconds. The aggregate run was interrupted after Isabelle's
`process_manager` raised `NoSuchFileException` while removing a temporary
`poly-stats` file and stopped making progress. This run is incomplete, not an
aggregate pass; no timeout was increased.

The first full migration unit run completed in 282.24 seconds: 8,941 passed,
112 failed and 2,079 deselected. Missing explicit family hooks and stale ownership
fixtures account for most migration failures. These are repair evidence, not a
passing release result. The baseline construction assertions remain unchanged.

After repair, the complete unit selection finished in **291.36 seconds**:
**9,052 passed, 14 failed, 2,079 deselected**. Guarded invocation time was 294.09
seconds, peak aggregate memory was 429,540,240 bytes, and descendant cleanup was
confirmed. Comparing failure node IDs against the clean baseline finds **no new
failures**. The two environment defects are fixed; the thirteen reverse constructor
and one special-number recovery failures remain. There are no Collatz failures.
Collection and per-phase timing records, exact selection and slowest tests are
retained in `20261006T080905Z-5b970860f3f447a59507bd16b7aee76e`.

The unchanged P0 selection completed in 10.45 seconds: **41 passed, 19 failed**.
The failures are one Antihydra installed nonhalting-certificate gate, ten reverse
generic-range cases and eight special-number recovery/CLI cases. No Collatz P0
case failed. These assertions remain genuine release holds; unlike the unit
failures, this task did not independently rerun all P0 cases on the baseline.
Evidence: `20261006T081428Z-c43071e4dd5a4d02992317f908e73e46`.

The final dependency-aware native run actually rebuilt 19 sessions: 17 completed
in 5–37 seconds, including `Comma_Semantic_B1` (37),
`Comma_Decade_Occurrence_Lift` (31), `Comma_Source_Entry` (12) and the relocated
ML dependency audit smoke session (6). `Comma_Semantic_Future` and
`Comma_Native_Summary` timed out at 60 seconds, leaving
`Comma_Semantic_B1_Instance` and `Comma_Native_Summary_Occurrence` unfinished.
The process tree peaked at 2,157,306,472 bytes. This is a partial proof result,
not aggregate acceptance. Unreported sessions in the failed build are not counted
as successful cold builds or inferred heap reuse. Evidence:
`20261006T081544Z-ed500426c12948788f589fe293b4cae8`.

The unchanged five-trial 16–1024 comparisons completed for Collatz and Antihydra.
Both retain output bases 2 and 10 and cold/warm/bypassed routes. Collatz uses point
position 0 on both revisions; Antihydra uses position 2 on both. The following
medians are milliseconds, baseline → migrated:

| Family / demand | Cold | Warm | Bypassed |
| --- | --- | --- | --- |
| Collatz CLI | 210.595 → 225.656 | 2.058 → 2.148 | 2.150 → 2.124 |
| Collatz point | 1.622 → 1.867 | 0.046 → 0.048 | 1.177 → 1.210 |
| Antihydra CLI | 198.107 → 142.080 | 2.316 → 2.397 | 2.476 → 2.436 |
| Antihydra point | 1.841 → 2.127 | 0.049 → 0.055 | 1.412 → 1.470 |

Cold CLI includes interpreter startup; point measurements include `project_nth`.
These are route/output comparisons with no latency threshold, not evidence of a
new asymptotic bound or a general speedup. Exact outputs agreed. Collatz command
time was 17.70 → 19.48 seconds; Antihydra was 16.68 → 13.20 seconds. The unchanged
reverse seed-196/position-2 comparison timed out at 60 seconds on both revisions;
its partial samples are not compared as a completed workload. The final reverse
guard confirmed descendant cleanup. The original workloads and assertions remain.

Final comparison evidence: `20261006T075252Z-ebb973132cc14ef4b6dba7e2524b5fd5`
(Collatz) and `20261006T082330Z-59b226e3f7114fd48e3899517e6b2dd1`
(Antihydra and reverse). An intermediate Antihydra position-0 comparison is
supplementary only. An intermediate reverse run made during an API repair is
excluded from final evidence.

The current gate table is:

| Gate | Result | Scope |
| --- | --- | --- |
| Ownership and dependency enforcement | Pass | Python direction checks; ROOTS, theory and ML registration; ownership map and negative tests |
| Quality and installed wheel | Pass | Strict typing, pinned lint/format, source policy, docs, proof inventory and packaging |
| Full unit selection | Migration regression check passes; release remains red | 9,052 pass; 14 unchanged baseline failures; 291.36 seconds |
| P0 selection | Red | 41 pass; 19 explicit construction/certificate/recovery holds; no Collatz failures |
| Native executable proofs | Partial | Extracted shared/family sessions passed; final Comma run has two 60-second timeouts and two blocked dependents |
| Performance comparison | Partial | Collatz/Antihydra complete; reverse exceeds 60 seconds on both revisions |
| Clean-commit acceptance | Pending | Changes are uncommitted; these are development runs, not reusable release evidence |

## Rejected approaches

No additional scheduler, source-fingerprint protocol, timeout override, artificial
session splitting, proof-assumption weakening or success-on-refusal assertion is
introduced. Generic files may not hide family dependencies with lazy imports.
Lexically unused theorems and similar proof scripts are not automatically deleted.

## Validation provenance

Baseline: commit `d6fc72685aab9ed5c63701d46fcff7b2fbfa967d`, isolated acceptance
worktree, run `20261006T045238Z-e674e4f89bdb4ef2ab3f82a2e0659e56`.
Focused development run: `20261006T045806Z-bedc87a54ebe488598efba6471b079ac`.
Native development builds: `20261006T052708Z-4e991fdd036347678bc904f4b31db3fa`
and `20261006T053530Z-6f4102a8ec844deaaaa447bab36ac72e`.
Dyadic repair: `20261006T054508Z-d6f9d06550dd47aa8c35fa8313f45a8c`.
Original-commit comparison: `20261006T054708Z-6007a671de1f4a159d65a4046c478020`.
Incomplete aggregate proof run: `20261006T055006Z-9edc50ff34b14350b9b0b76572b6a0ee`.
Corrected baseline Collatz comparison: `20261006T062421Z-995c6a31ac1d48ca816b070e3bde7056`.
Baseline reverse counter reproduction: `20261006T071319Z-e148e9046ce44cda9ebc319bf70437b9`.
Python uses 60 seconds per test/standalone command and 300 seconds per selection,
4 GiB aggregate, serial execution. Isabelle uses 60 seconds per session, four
prover threads, one building session and 6 GiB aggregate. Dirty development results
do not certify a reviewed commit.

## Remaining work

Ownership extraction, registration migration, dependency enforcement and the
observed Python migration regressions are resolved. All edits remain uncommitted;
development evidence cannot certify a reviewed Git revision. After review and a
normal commit, the guarded acceptance mode must run in its isolated clean worktree.
The existing reverse, special-number and Comma mathematical/production gates remain
open; the native Comma timeouts also prevent complete proof acceptance.
