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

The `macrocells` rows, when instrumented, distinguish semantic interning from
source-qualified occurrence reuse. Each instrumented lane reports lookups, misses and publications.
`exact_hits` and `transported_hits` are disjoint retrieval outcomes;
`local_hits` and `process_hits` describe the separate storage-location axis.
`applied_hits` counts only admitted records actually consumed by execution, and
`applied_parent_hits` identifies applications that bypass child construction.
`rejected_fit` records a retrieved occurrence whose physical weight does not fit
the requested remainder. `admission_rejections` records present entries rejected
before an admitted retrieval; it is neither a hit nor a miss. Instrumented
lookups partition into hits, misses and admission rejections. Older producers without these distinctions expose
`unclassified_hits`; reporting does not relabel them as exact hits. A semantic
hit does not imply that construction was skipped. `max_level` uses absolute
depth in the row's explicit `index_unit`: D8 is level 3. Collatz macrocells
count normalized symbols, whereas the public nth index counts physical ticks.
Primitive discovery, merges, spatial
leaf visits and operand-bit work retain their own units. Missing instrumentation
remains `null`; a family without this owner has no macrocell row.

Additional macrocell measurements distinguish consumed `applied_parent_hits`
from key construction (`key_operand_bits`), `cold_child_discoveries`, and
`coefficient_compositions`. `occurrence_frontier_joins` counts joins of already
observed adjacent block metadata; it is not a count of skipped transitions.
`capacity_bypasses` records optional cache admission failures, once per refused
publication or lease. For Mahler it sums the measured source-action and outer
observer lanes; each lane retains its own `bypasses` counter. Output-region
visits, emitted digits and failed work remain nullable until their owners measure
them. Reading these columns does not run a constructor or a storage audit.

Shared reuse is process-local: separate CLI processes start cold. Same-process
API requests may reuse compatible admitted germs; `shared_cache=False` bypasses
that reuse and `clear_shared_cache()` invalidates it. Full-output rendering and
cold discovery remain separately charged. `process_cache` reports aggregate
process retention and reuse, explicitly labeled `process_aggregate_not_query_work`;
reading it never creates the cache or a lease. Descriptor-era `shared_cache_*`
fields describe the prime query snapshot, not these later macrocell operations.

The detailed `power_metrics()` APIs retain per-owner inventory and raw work counters for explicit audit tooling.
The legacy `bimachine_composition_certified` field checks the live registered
generic application and its ownership/lease binding. It is not an Isabelle
completion declaration or a certificate for a different family executor.


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

The macrocell `cache_scope` distinguishes `source_cylinder` application reuse
from Mahler's `complete_associated_observer` memo. The latter reuses exact
consumer coefficients for an already admitted image; it is not an all-level
temporal constructor or a claim of skipped source discovery.
When an admitted Mahler source occurrence supplies both its arithmetic summary
and associated action, the scope is `source_occurrence_associated_action`.
Its reuse lane reports source-action lookups and hits separately from the outer
observer memo; observer hits never count as skipped child discovery.

## Removed architectural declarations

The detailed runtime fields `bounded_temporal_runtime_cutover_complete` and
`bounded_temporal_runtime_cutover_blocker` have been removed without aliases.
They were architectural/proof declarations, not measured execution. Consumers
should check exact output, admitted image ownership, demanded-consumer work,
resource accounting and forbidden reconstruction directly. Checked refinement
status belongs to the source-fingerprinted proof inventory and build evidence.
A missing refinement theorem does not retroactively make a successful runtime
comparison a construction failure.

Mahler's `source_action` and `outer_observer` lanes are both reported when
present. The first measures admitted complete source actions; the second
measures exact whole-observation memo retrieval. Their hits are not added.
No number of semantic interning hits or temporal depth is converted into
occurrence applications or estimated work saved.
