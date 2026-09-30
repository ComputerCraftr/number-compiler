# Metrics reference

## Metrics schema 8

CLI
`--info metrics` emits a compact `execution_metrics` object with
`schema_version: 8`. The detailed Python ledger report remains available to
probes; its `metrics_schema_version` is also 8.

- `action`, `application` and `projection` keep separate reuse populations.
  Action counts describe the current admitted action arena; they do not certify
  a saturated extensional macrocell or count its semantic equivalence classes.
- `construction` reports scheduler operations; finite source discovery is
  reported separately under `family_work`.
- `family_work.finite_block_*` separates finite-cylinder lookups, hits, misses,
  publications, evictions and cold arithmetic (atoms and transitions) from
  action interning and the outer balanced-effect memo. These are read-only
  counters shared by Collatz and Antihydra; Mahler consumes the latter's support.
  Repeated finite-cylinder hits do not certify a temporal pumping theorem.
- `demand` and `stream` distinguish query counts, spatial visits and emitted
  symbols. A stream visit is not a temporal jump.
- `observations` exposes measured observer work; `resources` reports entries,
  nodes, peaks and accounting status.
- `null` means the exact counter is unavailable. Only an instrumented zero is
  emitted as `0`. Antihydra snapshot capture leaves `audit_complete=false`;
  unknown inventory comparisons remain `null`. No bootstrap bound or constructor success is inferred from
  missing counters, cache hits or a zero primitive count.

The detailed `power_metrics()` APIs retain per-owner inventory and raw work counters for explicit audit tooling.


Comma metrics distinguish `cycle_rule_evaluations` (closed-form arithmetic)
from represented literal transitions, and boundary-template publications from
source-bound applications. `evaluated_transitions` counts actual scalar step
evaluations, including failed attempts; a powered application or relative cache
hit never increments it by its represented duration. `seam_predicate_check_bound` is a conservative count
of candidate checks, not an observed branch count. Streaming reports emitted
digits and peak logical workspace slots/integer bits; those bits are not a
Python heap-byte measurement. Reading metrics never constructs a macro or
verifies a certificate.

For A367620, `--no-value --info certificate` reports evidence availability
without checking the current forest. `runtime_verified` describes admission
already performed by that query; a metadata-only request reports false. Value
admission remains mandatory and separate until the boundary-quotient cutover
passes its proof and consumer gates.
Digit-stream admission runs at first consumption. Resetting the shared cache
during consumption invalidates that stream before its next digit is emitted.
