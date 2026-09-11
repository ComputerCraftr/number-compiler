# Two-sided tile execution checkpoint

Status: incomplete implementation, 2026-09-05. This checkpoint does not finish
arbitrary-depth absorption, production family cutover, or the five-minute gate.

Frozen source: `994fa53f9182f80898ba7af893ebf60d8a2686c717e59789e62c64e1fff1facd`.
The previous checkpoint remains in `HASHLIFE_BOUNDARY_QUOTIENT_CHECKPOINT.md`;
its historical measurements are preserved.

## Executable changes

- `BoundPorts` binds one finite assignment, normalized wiring and exact spatial
  operands. `FusedBoundaryContract` keeps producer and consumer contracts
  distinct on explicit execution requests and completed results. Signatures
  derive from wiring rather than a second independent field.
- Foreign producer signatures, invalid producer domains and foreign boundary
  operands reject before changing the complete ledger snapshot, including
  validation-work counters. Successful validation work remains counted.
- Existing public record imports and positional constructors remain valid.
  Frozen records moved to `tile_result_records`; the result owner remains one
  arena, with no new execution memo or semantic carrier.
- `BoundaryTileView.source_offset` selects a clipped interval of its backing
  canonical tile. It is separate from the signed translated `relative_origin`.
  Offset plus extent is checked against the live tile width, including empty
  slices and forged numeric aliases.
- Primitive boundary execution scans maximal covered canonical interfaces in
  the proper direction. It consumes each exact exterior into the primitive
  finite port and never copies a prefix tape. Oriented source views use the
  existing canonical mirror operation.
- Explicit primitive-pair point/width requests preserve distinct noninitial
  producer and consumer ports. Cached-midpoint consumption uses the consumer's
  supplied contract, rather than resetting it to the initial state.
- Full explicit pair completion returns both outgoing contracts and composed
  cocycles. Spatial joins verify forward and backward midpoint consistency
  independently before parent publication.
- Primitive point/width and clipped activity paths propagate exact boundary
  operands. The two previous clipped-activity loops are now one iterative
  dependency loop.
- Reverse indexes, result leases, failed-publication rollback, retirement and
  independent inventories include both contracts' input/output boundary tiles.
  Query reporting counts boundary transfer work, peaks and operand geometry
  separately and remains read-only.

`tests/test_tile_two_sided_execution.py` checks noninitial contracts, cold fused
versus completed output, cached-midpoint behavior, both clipped scan directions,
source mirroring, executed exact operands, and injected midpoint inconsistency.
The ten tests in `tests/test_powered_output_absorption.py` are unchanged:
SHA-256 `e26bd38d306b0a3165beceb9374250f1a7168d010f0f66f4a72f54c19817745a`.

## Remaining first gate

The production fuser still accepts only a primitive pair. The P4/P8 experiment
reproduced `(2,0,0,4)` and `(2,4,0,2)` for base-3 input `(0,0,0,1)`, but used nested
residual objects whose hashing traversed the continuation structure. That
experiment was removed. It is not production support or acceptance evidence.

A P2 boundary retains both a producer anchor and dependence on the opposite
producer state. `BoundPorts` currently represents finite primitive assignments;
adding an exact source slice does not by itself make that missing dependence
executable. Existing higher semantic construction and midpoint equations are
available, but an integration must reduce and publish the complete behavior
without reintroducing a continuation interpreter, growing finite port domains,
or treating syntax-canonical higher IDs as extensional equivalence classes.
This is unfinished integration, not evidence that a new successor theorem is
required or that the current closure/reuse gates have passed.

Other incomplete paths:

- Legacy implicit composite requests retain their old key/result convention;
  only explicit current-edge fusion results carry both outgoing contracts.
  Normalizing legacy and explicit defaults must preserve noninitial and
  heterogeneous semantics and must happen before the first lookup.
- Arbitrary-depth noninitial/composite contexts remain unadmitted by the pair
  fuser. No depth guard was removed to conceal missing semantics.
- Public deep reverse and Collatz still use their prior runtime. No old
  executor was deleted without a working replacement and poison coverage.
- Exact tile mirroring is available; complete request/result symmetry
  normalization and higher future-behavior quotienting are not integrated.
- Demand-driven public radix and compatibility cutover remain unfinished.

## Validation

The serial unfiltered run and checks are recorded under
`results/hashlife_two_sided_checkpoint_994fa53f9182.*`.
The frozen serial run has **4,348 passed, 10 failed, 0 skipped in 380.09 s**
(380.94 s wall). The source fingerprint before and after is identical. The ten
failures are the unchanged powered-output absorption gates. All new execution,
contract and accounting tests pass.

Ruff passes; strict mypy passes over 608 source files. The full run includes
passing recursive source-size, recursion, package/export, proof-boundary and
resource-store checks. The serial five-minute gate fails. The time difference
from the previous 386.08-second checkpoint does not establish an improvement
in the unchanged public deep-query algorithm.
No test fixture, budget, tracing option or watchdog was weakened.

The intermediate `ecc6baa1a5bc` run (4,344 passed, ten failed, 377.65 s) is
preserved. The final tree adds the validation-order repair and four regressions;
its separate frozen run is the current evidence.

## Final cold observations

Source-matched evidence: `results/field_two_sided_994fa53f9182.json` and
`results/radix_two_sided_994fa53f9182.json`. Response and microblock acceleration
are disabled in the field probes.

| N | Reverse 196 cold seconds | Collatz 27 cold seconds |
|---|---:|---:|
| 16 | 0.2084 | 0.1527 |
| 32 | 0.2603 | 0.1515 |
| 64 | 0.4411 | 0.1794 |
| 128 | 1.1418 | 0.2747 |
| 256 | 3.4352 | 0.4401 |
| 512 | 12.5933 | 0.7742 |
| 1024 | 35-second watchdog timeout | 1.4748 |

Both public families still report zero canonical production tile nodes and zero
absorbed temporal span. At reverse N=512 the counts remain exactly 164,720
higher-continuation requests, 2,504,109 internal work units, 1,237,159 ledger
entries and 332,255 ledger nodes. This is not a production performance cutover.
Reverse and Collatz probe status is RED; the missing N=1024 reverse sample is
reported separately from the observed prefix-envelope violations.

The fixed five-process radix gate passes: cold median 0.000178917 s, repeat median 0.000094167 s. This is the existing narrow original-source radix regression,
not evidence of demanded powered-radix migration.
