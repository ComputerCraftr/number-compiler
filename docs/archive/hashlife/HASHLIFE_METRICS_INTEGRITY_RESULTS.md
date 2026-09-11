# HashLife metrics and identity integrity audit

## Correct production meaning

The production reverse/add and Collatz point paths no longer use the generic composed spacetime macro/residual cache. Therefore a production value of

```text
spacetime_macro_cache_hits = 0
spacetime_macro_cache_misses = 0
spacetime_macro_cache_entries = 0
recursive_value_cache_entries = 0
```

means **the bounded family-specific application backend bypassed that retired path**; it does not mean "HashLife got no hits." Reuse is now reported by the bounded-application quotient/action counters and the canonical dyadic arenas that they own.

The historical 94,259 reverse/add and 49,027 Collatz generic macro misses are pre-cutover measurements and must not be compared with current production counters.

## Corrected N=256 cold query

| metric | reverse/add 196 | Collatz 27 |
|---|---:|---:|
| bounded application enabled | 1 | 1 |
| bounded temporal state classes | 2 | 3 |
| bounded temporal action classes | 2 | 3 |
| exact spatial occurrences | 236 | 41 |
| symbolic spatial action nodes | 10,567 | 122 |
| binary jump entries | 464 | 161 |
| primitive quotient/forcing evaluations | 255 | 42 |
| residual physical steps | 0 | 1 |
| bounded semantic/memo subtotal | 18,557 | 525 |
| total accounted retained entries | 18,557 | 783 |
| reachable canonical tile nodes | 9,645 | 63 |
| query tile allocations | 32,218 | 131 |
| generic macro entries | 0 | 0 |
| generic recursive-value entries | 0 | 0 |
| source-index duplicate action entries | 0 | 0 |
| unquotiented recursive application nodes | 0 | 0 |
| raw temporal scalar/span fields | 0 / 0 | 0 / 0 |

`bounded_application_retained_entries` is an explicitly defined semantic/memo subtotal for the bounded backend, not a claim to count every Python object allocation. `retained_cache_entries` is the sum of the accounted persistent memo categories exposed by the public runtime metrics.

## Node identity

Construction-order `node_id` is now diagnostic only in the HashLife core. Parent interning, mirror/uniform analysis, directed tile action traversal, finite action traversal, and operator ownership use canonical objects/semantic keys instead.

The adversarial integrity test deliberately gives two different sibling tiles the same diagnostic `node_id`; directed action projection still distinguishes them and returns the correct result. The release audit also requires these diagnostics to stay zero:

```text
canonical_tile_node_id_collisions
canonical_tile_invalid_intern_entries
canonical_tile_mirror_involution_violations
operator_node_id_collisions
semantic_effect_duplicate_owners
```

## Eagerness and phase accounting

Compiler-created and query-created activity are separate. Collatz may build its bounded exact quotient/symbolic tables during compilation; query counters start from a compiler baseline. Reverse/add production carries no generic macro prewarm into the point query.

The identical-warm-query regression requires:

- query request count increases;
- quotient build count does not increase;
- primitive step count does not increase;
- exact spatial occurrence count does not increase;
- symbolic action-node count does not increase;
- canonical tile allocations do not increase;
- generic macro/residual counters remain zero.

That regression passes for both families.

## Integrity status

The current focused quotient/HashLife/forcing/cache/policy regression set is **135/135 passing**. See `tests/test_spacetime_cache_integrity.py` for the adversarial ID and warm-query invariants.
