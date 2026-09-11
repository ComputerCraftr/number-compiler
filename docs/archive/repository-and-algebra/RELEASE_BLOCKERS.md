# Current release blockers

## Checkpoint status (2026-09-03)

The sequential reverse/add, physical-Collatz, and recursive radix replay blockers are closed for the bounded checkpoint route. The checkpoint uses verified T^2/C^4 bisimulation-machine rungs, capped exact final microblocks, and zero retained future tapes/provider histories. See [LINEAR_BISIMULATION_CHECKPOINT.md](LINEAR_BISIMULATION_CHECKPOINT.md).

The remaining HashLife performance blocker is higher-rung bisimulation closure: low-power machine applications are linear in temporal distance, but their repeated spatial scans are not the final logarithmic parent-macrocell behavior. Higher powers must be composed and minimized extensionally using the mod-32/H=20 reverse interface and bounded 3-adic/affine Collatz interface, with fail-closed fallback to the largest verified rung.

The bounded family **cutover is complete for the linear bisimulation checkpoint**.
Certified decimal reverse/add and physical Collatz no longer route through sequential
generation/event adapters, and the frozen N=256 execution/retention gate passes. The
remaining HashLife blocker is specifically higher-rung bisimulation closure: repeated
T^2/C^4 applications still scan the bounded working word and therefore do not yet
provide the final logarithmic parent-macrocell execution.

Current architecture, validation checkpoints, and measured limitations are in
[the diamond implementation status](../hashlife/DIAMOND_IMPLEMENTATION_STATUS.md).
Schema 5 separates execution work, canonical programs/functions, source/image
nodes, memo entries, bounded microblock payloads/workspace, and explicit endpoint lowering. Small compiler
DAGs or small carry-class counts do not establish logarithmic execution.

The report below is preserved as historical evidence. Its descriptions of the
then-current H=20 carry-cut carrier, production routes, and counters are
superseded; they must not be used as current release assertions.

## Historical v0.59.9 bounded-temporal report

## Cached recursive HashLife/quadtree execution — BOUNDED TEMPORAL CUTOVER CLOSED; REVERSE SPATIAL-ACTION SCALING OPEN

The original release blocker mixed three separate problems: unstable/late cache identity, raw temporal history retained as state, and genuinely growing exact spatial work. The first two are now removed from the production reverse/add and Collatz nth-term paths. The third remains explicit for reverse/add.

### Closed correctness / identity / ownership debt

1. Persistent dyadic caches retain canonical tile objects; construction-order `node_id` is diagnostic only in core semantic/work traversals.
2. Raw `SpacetimeBoundary` temporal state is deleted.
3. `_RecursiveResidualAction` no longer carries scalar `length`, `depth`, or `anchor_before`; production reverse/add/Collatz bypass it entirely.
4. Source-index duplicate composed-action ownership is zero.
5. Late partition alias/cache-compaction repair is deleted; canonical IDs are final before parent retention.
6. Compiler/query metrics and process-global/per-index tile metrics are separated.
7. Retained memo accounting includes the declared leaf/algebra/bounded-backend categories.
8. Adversarial duplicate diagnostic node IDs cannot change directed tile-action results.
9. Reverse/add production temporal state is the fixed H=20 carry-cut quotient.
10. Collatz production temporal state is bounded residue/local phase plus symbolic affine/event transport; exact normalized tail is spatial payload only.

### Hard production invariants

```text
bounded_temporal_runtime_cutover_complete             == true
unquotiented_recursive_application_description_nodes  == 0
raw_temporal_scalar_length_fields                     == 0
raw_temporal_span_fields                              == 0
raw_spatial_occurrence_scalar_extent_fields           == 0
recursive_boundary_wrapper_nodes                      == 0
spacetime_macro_cache_entries                         == 0   # retired generic production path
recursive_value_cache_entries                         == 0   # retired generic production path
source_index_advance_entries                          == 0
canonical_tile_node_id_collisions                     == 0
canonical_tile_invalid_intern_entries                 == 0
operator_node_id_collisions                           == 0
semantic_effect_duplicate_owners                      == 0
```

### Current N=256 production metrics

| metric | reverse/add 196 | Collatz 27 |
|---|---:|---:|
| seed payload tiles | 3 | 5 |
| compiled `F^N` description | 45 | 181 |
| bounded temporal state/action classes | 2 / 2 | 3 / 3 |
| generic recursive application nodes | 0 | 0 |
| exact spatial occurrences | 236 | 41 |
| symbolic spatial action nodes | 10,567 | 122 |
| binary jump entries | 464 | 161 |
| primitive quotient/forcing evaluations | 255 | 42 |
| residual physical steps | 0 | 1 |
| app spatial tile nodes | 9,626 | 40 |
| accounted retained entries | 18,557 | 783 |
| generic macro misses / entries | 0 / 0 | 0 / 0 |

The old 94,259 reverse/add / 49,027 Collatz macro-miss numbers were valid measurements of the **pre-cutover generic carrier**, but they are not current production statistics and are superseded by the bounded-application counters above.

### N=16..256 scaling gate

Reverse/add compiled `F^N` stays compact (`21, 27, 33, 39, 45`), and the seed temporal quotient saturates at 2 state / 2 action classes. However the exact spatial forcing backend still performs `15, 31, 63, 127, 255` primitive evaluations; the N=256 tail exponent is **1.006**. Spatial forcing/action composition is therefore still a release blocker.

Collatz seed 27 compiled `F^N` is `169, 172, 175, 178, 181`, bounded temporal classes reach 3 / 3, and primitive work is `8, 17, 32, 43, 42` with tail exponent **-0.034**. This representative seed passes the tail sublinear gate, but arbitrary-source logarithmic closure remains unproved.

### Remaining HashLife blocker

**Reverse/add spatial forcing action composition — OPEN.** The temporal H=20 memory quotient is no longer growing; the remaining O(N)-like work comes from applying exact forcing occurrences one generation at a time. Closure requires a recursively composable cut-to-cut spatial action so `primitive_forcing_steps` and symbolic spatial action growth bend below linear while exact digit projection remains unchanged.

Do not "fix" this by reintroducing raw prefix/tail history, scalar lengths, post-hoc aliases, or by relabeling spatial occurrences as temporal states.

Machine-readable evidence:

- `results/hashlife_state_action_growth_reverse_196.json`
- `results/hashlife_state_action_growth_collatz_27.json`
- `results/hashlife_cache_audit_reverse_196_n256.json`
- `results/hashlife_cache_audit_collatz_27_n256.json`
- `results/reverse_temporal_power_metrics.json`
- `results/collatz_temporal_power_metrics.json`

## Exact nth-prime

**OPEN.** Recursive fixed-wheel rank/select no longer expands ancestor wheel
carriers, but exact nth-prime selection still requires collapsing the growing
factor-stage axis.

## Fermat/Mersenne projection

**OPEN.** Symbolic source/extents are compact. Candidate-derived support-defect
projection remains unresolved for theorem-sensitive primality projection.
