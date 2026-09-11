# Early canonical lookup and metrics schema 3

The v4 implementation still had two distinct problems. Legacy spatial counters counted exact-source occurrences while omitting retained range bindings, and the legacy total added node counts to container slots that already included node-array entries. The broad temporal total also omitted application programs. Separately, a known interval composition could evaluate its component functions before its output interner found a duplicate.

## Reporting contract

Schema 3 reports the actual retained inventory in separate units:

| Field | Meaning |
|---|---|
| `cache_slots` | Slots in registered containers, including node arrays and memo/interner maps. |
| `source_payload_nodes` | Original-source records and source geometry nodes. |
| `temporal_program_nodes` | Compiler and application program nodes. |
| `canonical_transfer_nodes` | Interned finite transfer nodes and complete interval effects. |
| `spatial_occurrence_bindings` | Range, view, and result bindings, including bindings that reference existing nodes. |
| `spatial_binding_nodes` | Allocated records belonging to those bindings. |
| `finite_port_state_nodes` | Explicit finite-interface state records. |
| `exact_endpoint_nodes` | Explicitly lowered endpoint records. |
| `other_retained_nodes` | Independently counted records with other inventory roles. |

The node categories reconcile with `resource_observed_nodes`. They are not added to `cache_slots`. These are logical storage counts, not byte-accurate Python memory measurements.

Legacy fields now follow this contract. `total_hashlife_retained_entries` equals `cache_slots`. `temporal_description_nodes` includes compiler and application programs. `spatial_occurrence_description_nodes` includes allocated spatial bindings and canonical transfer nodes. Exact tile counters continue to count exact tiles; they are not totals for all spatial storage. `seed_application_temporal_state_nodes` is zero because the symbolic path has no separate exact temporal-state records; observed carry-effect classes are reported as spatial classes.

`transfer_summary_nodes` is now an alias for canonical transfer nodes. Its old value mixed range bindings with canonical functions. A comparison with the old v4 field must therefore use **new spatial binding nodes plus new canonical transfer nodes**. Reclassification alone is not a memory optimization.

Some compatibility fields have a narrower historical meaning and are **retired for the lazy execution path**, rather than aliases for its resources:

| Retired fields, including forwarded `hashlife_` prefixes | Current measurement |
|---|---|
| `finite_action_unique`, `finite_action_retained_entries`, `finite_action_*_hits` | The old finite tile/bimachine action arena. Use `canonical_transfer_nodes`, `spatial_interval_action_classes`, and the inventory for current finite actions. |
| `boundary_cache_entries`, `boundary_cache_hits`, `boundary_requests` | The old exact-boundary cache. Use `spatial_occurrence_bindings`, `summary_cache_hits`, and the family-specific lookup counters. |
| `section_*`, `leaf_word_*`, `high_level_tile_*`, `spacetime_*` | The removed exact tile/slab execution routes. Their zeros do not describe current program or transfer-summary work. |

The old `bounded_application_temporal_state_classes` label still forwards local carry classes: observed interval effects for reverse/add, or the three carry states for Collatz. It does not identify a temporal quotient. Use `spatial_interval_action_classes` for the reverse interval population. Likewise, `bounded_application_temporal_action_classes` describes syntax/program nodes; use `application_program_nodes`. These names are retained for compatibility, with this explicit scope. Neither the retired zero counters nor a bounded spatial class count is evidence of logarithmic execution.

## Lookup before evaluation

`CarryIntervalCompositionKey` contains validated scoped input IDs and the port. The interval arena checks that key before invoking either component composition or output interning. Aliased input histories therefore reuse the same composition entry without recomputing its effect. The three one-symbol carry functions induce seven complete spatial interval classes; an exhaustive test evaluates each of their 49 input pairs once and verifies that replay performs no new composition evaluation.

Reverse range lookup canonicalizes even-width interval coordinates modulo reflection before evaluating coefficients. Reflection swaps the complete effect's forward and backward functions and preserves its capped reset observation. Only one binding is retained for a mirrored pair of aligned intervals. Odd-width reflection does not preserve the disjoint two-cell grid, so those intervals keep their original alignment. Warm interval scans also check retained IDs before requesting coefficients.

Reflection and finite literals have their own scoped-ID lookups before constructing an effect descriptor. Self-symmetric reflection is an identity shortcut and is counted separately from a memo hit. The counters satisfy `literal requests = hits + evaluations` and `reflection requests = cache hits + identity hits + evaluations`; output-interner hits cannot inflate those early-hit counters.

Collatz `mul3_summary()` now checks the scoped program ID and extent before streaming the program. Its evictable memo retains a complete three-carry transfer summary: exit carries and first/last nonzero coordinates. It retains no emitted bits, tail integer, or affine offset. Extending a request from eight to nine events reuses eight existing summaries and evaluates one new summary. This adds bounded summary records to cold retention in exchange for avoiding repeated scans.

The work counters distinguish lookup requests, early hits, evaluations, and output-interner hits. Foreign handles are validated before warm lookup. Eviction releases memo slots while preserving live canonical IDs. Tests poison coefficient evaluation, component composition, output interning, or the Collatz stream to verify that known early hits bypass the corresponding work.

## Limits

Canonical input identity is available before evaluation when it follows from existing program IDs, complete transfer IDs, or a proved coordinate symmetry. The first evaluation of an unknown nonlinear effect still requires discovery. Seven spatial effect classes do not prove that different output-complete temporal programs have identical successors.

Cold reverse branch discovery and application-program retention remain linear in the requested generation. Spatial occurrence bindings still grow across generations, even after reflection reduces their number. No logarithmic cold-execution claim is enabled.

## Validation and measurements

The final validation record (local artifact: `../../../results/early_canonical_validation_v5.json`) reports:

- `ruff check .`: passed.
- `mypy --strict src`: passed for 167 source files.
- Full pytest: **1,243 passed**, zero failures, errors, or skips, in 725.065 seconds.
- Repository policy: **26 passing checks**, including no Python recursion and the 1,000-line source-file limit.
- Adversarial gate (local artifact: `../../../results/followup_representation_audit_v5.json`): **310 passing tests across 25 groups**, each group run in a fresh pytest process after the final production changes. No prior-revision results were reused.
- All ten fresh-process cold rows passed their scalar oracle, ownership, bounded-payload, and counter-reconciliation checks. Construction, cold, and warm observations reconcile independently.

The early-lookup regressions include poisoned evaluation paths, all 49 pairs of complete reverse interval classes, mirrored-coordinate reuse, Collatz summary reuse, foreign handles, and eviction. The v4 artifacts remain historical evidence under metrics schema 2.

## Cold measurements

The v5 matrix (local artifact: `../../../results/lazy_resource_audit_v5.json`) uses a fresh process per row and an independent scalar oracle. All ten rows are exact, have reconciled ownership and node inventories, and report zero forbidden future payloads and zero explicit endpoint lowerings. These runs overlap other validation work; their wall times are not a controlled performance comparison.

| Family | N | Program nodes | Spatial bindings | Canonical transfer nodes | Cache slots | Total nodes | Branch observations | Bounded arithmetic operations | Cold seconds |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| reverse | 16 | 71 | 35 | 10 | 214 | 128 | 15 | 9,691 | 0.013 |
| reverse | 32 | 137 | 106 | 10 | 403 | 267 | 31 | 70,796 | 0.102 |
| reverse | 64 | 267 | 381 | 10 | 908 | 674 | 63 | 239,604 | 0.376 |
| reverse | 128 | 525 | 1,455 | 10 | 2,436 | 2,008 | 127 | 857,278 | 1.633 |
| reverse | 256 | 1,039 | 5,456 | 10 | 7,339 | 6,525 | 255 | 7,592,429 | 24.668 |
| collatz | 16 | 22 | 10 | 0 | 70 | 48 | 7 | 414 | 0.001 |
| collatz | 32 | 37 | 17 | 0 | 109 | 72 | 14 | 1,814 | 0.003 |
| collatz | 64 | 65 | 30 | 0 | 180 | 115 | 27 | 9,095 | 0.011 |
| collatz | 128 | 99 | 45 | 0 | 265 | 166 | 42 | 29,512 | 0.062 |
| collatz | 256 | 99 | 45 | 0 | 267 | 168 | 42 | 29,470 | 0.037 |

For reverse N=256, retained nodes fall from **8,378 to 6,525**, and slots from **9,178 to 7,339**. Comparing equivalent categories, the old mixed transfer count of **7,319** becomes **5,456 spatial binding records plus 10 canonical transfer nodes**, or **5,466** combined. The seven complete interval effects and three Boolean decision nodes account for the ten canonical nodes.

The reverse run makes **10,912 joint interval-composition requests: 10,903 early hits and 9 evaluations**. Across all composition kinds, evaluations fall from **14,772 to 36**. Reflection contributes **729,586** range-lookup hits. Bounded arithmetic operations fall from **10,621,780 to 7,592,429**.

Literal lookup has **16,368 requests: 16,365 early hits and 3 evaluations**. Reflection has **729,586 requests: 276,502 cache hits, 453,082 identity shortcuts, and 2 evaluations**. Output interning reports **7 hits and 7 misses**, separately from these pre-evaluation lookups. The first implementation of this change still had 292,874 interner hits; those repeated descriptor constructions have now been removed.

Measured reverse N=256 wall time changes from **15.349 to 24.668 seconds** in these concurrent validation runs. No wall-time speedup is claimed; reduced evaluation and retention counts must not be substituted for that claim.

Collatz N=256 retains **42 additional bounded summaries**, increasing nodes from **126 to 168** and slots from **225 to 267**. A single cold request has 42 summary evaluations and no mul3-summary hits; its arithmetic work is unchanged. Reuse is demonstrated by the separate repeated-view and extended-event regressions. Collatz summaries here are program-bound records, not an extensional interner, so `canonical_transfer_nodes` correctly reports zero.
