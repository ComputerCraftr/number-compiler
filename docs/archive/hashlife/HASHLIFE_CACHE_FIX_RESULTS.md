> **Historical pre-bounded-cutover report.** The generic macro/residual counts below document earlier bugs and optimizations. Current production reverse/add/Collatz bypass that carrier; use `HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md` and `HASHLIFE_METRICS_INTEGRITY_RESULTS.md` for current metrics.

# HashLife cache/canonicalization repair results — v0.59.9

> **Metrics-integrity correction:** the macro hit/miss figures in this historical
> pass remain valid, but its `retained_cache_entries` figures were an incomplete
> subtotal: they omitted leaf caches and persistent partition/symbolic algebra
> memos, and its tile-arena gauge was process-global rather than per-term. Use
> `HASHLIFE_METRICS_INTEGRITY_RESULTS.md` for current retained/cache/tile counts.

This pass is limited to the recursive quadtree/block runtime used by powered
reverse/add and physical Collatz. It removes the concrete late-hit,
noncanonical-ID, duplicate-state-space, cache-accounting, and avoidable
finite-carrier cutover defects. The remaining cold first-use scaling gate is
reported rather than hidden.

## Defects removed

- weak dyadic node lifetime combined with persistent integer-ID cache keys;
- noncanonical/recreated mirrored tile identity;
- duplicate source-index and composed-effect tile-action memos;
- a raw `SpacetimeBoundary` wrapper used as a second higher temporal carrier;
- functional/partition carrier overlap;
- higher-carrier selection controlled by `exponent <= 8` / `max_states=4096`;
- recursive state IDs depending on bulk-vs-leaf traversal segmentation;
- post-hoc partition behavioral aliases that changed child identity after parent
  recursive actions had retained the old child object;
- the now-unused cross-effect cache-compaction transaction that existed only to
  repair those late aliases;
- compiler/determinizer scalar probes retained as runtime cache entries;
- parent symbolic rows rebuilt through scalar Cartesian probing;
- repeated reconstruction of an immutable nested temporal effect key on every
  macro-cache lookup;
- Collatz T^8 falling into recursive history even though its T^4 child owns a
  complete exact 50/90-state boundary partition domain.

## Production state ownership now

Higher composed effects use one exact carrier at a time. A complete partition
carrier may be lifted one structural level only when the child proves that its
domain came from a complete extensional carrier. Physical Collatz consumes that
capability at T^8 and cuts over to recursive HashLife at T^16. Reverse/add does
not satisfy that small-domain condition and cuts over at T^8.

```text
_RecursiveBoundaryState
    = (canonical first-child anchor, canonical residual action root)

_RecursiveResidualAction
    = hash-consed dyadic action forest node
```

Incoming tiles are aligned to the residual scan origin before folding, so a
bulk dyadic tile and its recursively visited leaves converge to the same state
identity. Partition states have immutable/final IDs before a recursive parent can
retain them. Raw boundary-wrapper execution is absent from the production block
runtime.

## Final cold-cache measurements

| family | N | retained | macro | recursive values | scalar emit | recursive actions | macro hit rate | first recursive |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| reverse/add 196 | 64 | 16,663 | 6,688 | 2,013 | 1,346 | 1,637 | 56.2% | T^8 |
| reverse/add 196 | 256 | 170,688 | 94,259 | 32,633 | 20,312 | 22,261 | 58.6% | T^8 |
| Collatz 27 | 64 | **5,489** | **2,953** | **1,094** | **880** | **870** | 61.3% | **T^16** |
| Collatz 27 | 256 | **82,126** | **49,027** | **20,802** | **11,530** | **13,106** | **63.8%** | **T^16** |

At Collatz N=256, compared with the previous recursive-finished tree, macro
misses fall 85,273 -> 49,027 (-42.5%) and tile-output misses fall 47,392 ->
26,605 (-43.9%). The old retained-cache percentage used incomplete accounting
and is superseded by `HASHLIFE_METRICS_INTEGRITY_RESULTS.md`. See
`HASHLIFE_ACTION_FIX_RESULTS.md` for the action-layer before/after table.

All representative probes report:

```text
source_index_advance_entries             0
raw_spacetime_boundary_cache_entries     0
retained_cache_accounting_delta          0
scalar_emit_compiler_probes              0
sparse_carrier_layers_left/right         0/0
```

The Collatz symbolic-output row cache at N=256 records 1,831 hits / 184 misses;
those rows are compiled compositionally and do not populate the scalar runtime
memo.

## Verification

HashLife/reverse/Collatz targeted release suite after the action-layer follow-up:

```text
62 passed
```

The whole repository test suite is broader than this subsystem and is not
reported as a completed pass in this artifact.

## Audit commands

```sh
PYTHONPATH=src python bench/hashlife_cache_audit.py reverse 196 256 --position 0
PYTHONPATH=src python bench/hashlife_cache_audit.py collatz 27 256 --position 0
```
