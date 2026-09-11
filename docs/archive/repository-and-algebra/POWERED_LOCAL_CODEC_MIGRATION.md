# Powered local codec migration map

The old implementation contains a useful bounded spatial codec alongside
occurrence-specific execution machinery that cannot cross the production
representation boundary. The production seam is
`runtime.powered_local_codec.PoweredLocalCodec`.

## Algorithms to port

| Existing location | Reusable algorithm | New destination |
|---|---|---|
| `shared_powering.FiniteKernel` | Freeze and exhaustively validate a finite transition table; bind identity to its complete semantics | Family kernel admission or a ledger-owned local-interface arena |
| `shared_powering.OrientedFiniteActionArena._compose_mapping` | Compose finite maps as `after[before[state]]` | `PoweredLocalCodec.compose_spatial` implementation |
| `shared_powering.OrientedFiniteActionArena._canonicalize_pair` | Canonicalize forward/reverse maps under certified mirror and conjugacy before assigning an ID | Local-interface publication before the parent-cache probe |
| `shared_powering.OrientedFiniteActionArena.compose` | Forward composition `right ∘ left` and reverse composition `left.reverse ∘ right.reverse` | Spatial interface composition |
| `finite_tile_action._SideArena.action_ref` | Iterative postorder construction and canonical child-action composition | Source-leaf compiler and iterative field-transfer scheduler |
| `_block_spacetime_runtime._advance_second_over_first_output` | Probe the parent diamond first and substitute the second action through the first output without a midpoint tile | Temporal local-effect composition |
| `_block_spacetime_runtime._advance_effect_tile_macro` | Route work to the canonical child action owner and use an explicit iterative task stack | Shared field-transfer scheduling |

These algorithms operate on bounded functions or canonical recursive children.
The new codec returns `PoweredLocalEffect(interface, output)`. Complete field
summaries supply activity, first/last active coordinates, extent, halos, growth,
termination, normalization, and frame behavior separately.

## State and caches to leave behind

| Existing location | Forbidden payload or behavior | Reason |
|---|---|---|
| `finite_tile_action._tile_actions` | `DyadicTile -> action` cache in the semantic arena | Couples the quotient to exact source occurrence identity; source bindings belong in the field-transfer layer |
| `_block_spacetime_runtime._RecursiveBoundaryState` and `_RecursiveResidualAction` | Linked exact residual forests and child boundary occurrences | Retains the scanned source history and creates occurrence-specific temporal keys |
| `_macro_tile_advance_cache` | Keys containing exact boundary state and `DyadicTile` | A concrete incoming state belongs to observation, not the parametric parent identity |
| `_macro_tile_output_cache` | State-bound outputs for exact source tiles | Publishes observation results instead of one complete bounded parent action |
| `_advance_uniform_macro` | State-discovery loop over a represented run | Performs eager scan work before canonical parent reuse |
| `BinaryLiftEngine` | Lazy jumps keyed by exact state | A cold unique orbit evaluates a linear successor chain |
| `FiniteQuotientLiftEngine` | Whole finite-domain transition tables | Permitted only when a separate complete finite closure proof exists; it is not the default field carrier |
| T2/C4 finite machine tables | 757/179 and 50/90 proof-state domains | Proof metadata only; these sorts cannot enter runtime handles or cache keys |

## Integration sequence

1. Compile each family leaf law to one `PoweredLocalEffect` using immutable
   source symbols only at level zero.
2. Compose spatial children through bounded oriented transfer functions and the
   coordinate output morphism. Canonicalize certified automorphisms before
   interning.
3. Compose temporal actions by symbolic substitution in apply-before-then-after
   order, without loading the generic continuation codec or emitting a midpoint.
4. Combine the local effect with the family's independently canonical summary
   channels and publish the complete field transfer atomically.
5. Bind that transfer to immutable source geometry only in the request/binding
   cache. Bind concrete port values only while observing a point or width.
6. Keep exact future blocks confined to explicit endpoint lowering and the
   capped microblock facility.

The first family bridge is complete only when powers above the primitive proof
kernel succeed with the generic semantic codec, old spacetime runtime, proof
tables, whole-word executor, and generation loops poisoned.
