# Typed CLI contracts and source-derived checks

Period: 2026-10-11 through 2026-10-17 (Sunday–Saturday).

[Week index](README.md)

## Objective

Consolidate canonical CLI declarations, typed execution requests and current-source
repository checks while preserving sequence semantics, budgets and schema 8.

## Changes

The capability registry owns canonical families and lazy adapters. Frozen query
records replace the string-family `project_nth` interface; `project`, `nth` and
`project_digit` consume those records. Event and certificate requests are distinct
variants. Repository callers and installed-wheel cases use canonical commands.
CLI aliases and unused Namespace observation dispatchers have been removed.

Observation adapters publish explicit index metadata. Common result/error envelopes
and one iterative serializer preserve exact integers, null measurements and existing
family statuses. Serialization copies cached packets and rejects non-finite JSON
measurements. Optional observers remain demand-driven.

Git supplies tracked and nonignored untracked authored files. One invocation-local
inventory feeds current AST, ROOT/ROOTS and Isabelle ownership checks. The maintained
relocation-history JSON, its validator/tests, passive Python/Isabelle counterpart map,
and legacy-file/function inventories have been deleted. Current import-direction,
duplicate-body, recursion, proof-oracle and lifecycle checks remain.

The boundary audit retains foreign/stale handle and resource checks. It removes the
second validation of the identical admitted source in SourceGeometry and the repeated
mirror digit-budget check. Private Collatz partitioning trusts the horizon admitted by
its public callers, while retaining issued-object and memo-lifecycle checks.
Repeated 2rev10 queries use the existing bounded owner cache
with source, budget and disposal validation.

## Established results

The migrated CLI/API has no new failures against the dirty-tree baseline. Canonical
family parsing, compact indices, lazy observers, certificate dispatch, exact output,
foreign/stale handle rejection and cache reuse remain covered. An injected family
specification exercises help and typed request construction without another central
family branch.

The complete unit run finished with **9,472 passed, 14 failed and 2,106 validation
cases deselected** in 285.82 seconds. The guard measured 287.83 seconds and
430,293,904 peak bytes; instrumentation and cleanup completed. All 14 failures match
the baseline: 13 reverse-construction/routing failures and one special-number admission
failure. There are no Collatz failures. No mathematical release obligation is closed.

| Gate | Result |
| --- | --- |
| Strict mypy, pinned Ruff, formatting | Pass |
| Source policy and documentation | Pass |
| Current Isabelle registration/proof inventory | Pass; not a kernel build claim |
| Clean installed-wheel CLI checks | Pass |
| Full Python suite budget | Pass: 287.83 s / 300 s, below 4 GiB |
| Full Python correctness | Held by the same 14 baseline failures |

Comparable development measurements (single validation runs; parser comparison uses
five alternating fresh-process trials per wheel):

| Measurement | Before | After |
| --- | ---: | ---: |
| Unit collection | 7.797 s | 8.932 s |
| Unit tests and reporting | 279.72 s | 285.82 s |
| Outer unit guard | 281.85 s | 287.83 s |
| Repository policy | 28.634 s | 29.060 s |
| Proof inventory | 29.237 s | 28.170 s |
| Parser median, after imports | 7.30 ms | 7.36 ms |
| Parser import median | 25.22 ms | 37.14 ms |
| Parser fresh-process median | 57.65 ms | 69.35 ms |

Parser timing selects `collatz --seed 27 --nth 0` without executing arithmetic.
The typed declarations add import cost; these measurements do not establish a speedup.

## Rejected approaches

No compatibility dispatcher replaces the retired string API. No migration-history
database replaces the deleted inventories. Existing failing reverse-constructor and
special-number assertions are retained. Typed annotations do not authenticate handles.

Repository-layout assertions were retired where they only named previous files or
functions. Their current contracts are enforced by parsed import direction and duplicate
checks; the executable reverse trace-tower equality and installed-package contract remain.
Unknown commands use ordinary parser errors instead of historical migration hints.

One intermediate full run completed all tests in 298.27 seconds but exceeded the
300-second outer deadline during shutdown. Its guard outcome remains a failure.
Profiling found an extra cold comma certificate verification in the new all-family
API fixture. The `nth(CommaTermQuery(1)) == 20` assertion now shares the existing
comma prefix-admission test's verified state instead of repeating that preparation.
The exact-output assertion remains; no workload or timeout was reduced. The final
rerun above includes this consolidation.

## Validation provenance

Development validation uses the dirty worktree based on Git commit
`2e81a8aa75d94827fb34f7783871e712436bcfa5`; it is not clean-commit acceptance evidence.
The baseline full unit run was 9,473 passed, 14 failed and 2,106 validation cases
deselected in 279.72 seconds (guard 281.85 seconds; peak 424,919,928 bytes), from
`results/runs/20261013T070934Z-b1872b3603d44bdbb2b004e4091593ad`.

Quality and installed-wheel evidence:
`results/runs/20261013T084348Z-8071aa6271604f85906a4e77af3eb314`.
Final full-unit evidence:
`results/runs/20261013T083657Z-a27f6a8dc80b4ef2ba8797edc82eb79d`.
Guarded parser comparison of the saved baseline and candidate wheels:
`results/runs/20261013T084227Z-75b80d490478493cbf7af11e7d7aea58`.
Its candidate wheel comes from the preceding quality run
`results/runs/20261013T082833Z-859b81bd705d40b38980bf9b8d91d695`;
the parser sources are unchanged between those two quality runs.

Python validation retains 60 seconds per test, 300 seconds per suite and 4 GiB;
Isabelle policy remains 300 seconds per session, 6 GiB and four prover threads.
No theorem sources or assumptions were intentionally changed by this migration.

## Remaining work

The existing reverse-construction, special-number and comma forest/fuel release holds
remain outside this refactor. Development runs on this preserved dirty checkout do not
certify a clean Git commit. Existing proof-source edits from other work were preserved;
the registration inventory result does not claim that those proofs build.
