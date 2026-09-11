> **Historical pre-bounded-cutover report.** The generic macro/residual counts below document earlier bugs and optimizations. Current production reverse/add/Collatz bypass that carrier; use `HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md` and `HASHLIFE_METRICS_INTEGRITY_RESULTS.md` for current metrics.

# HashLife semantic-action follow-up — v0.59.9

This report records the semantic-action changes made after
`number_compiler_v0.59.9_hashlife_recursive_finished.zip`. The subsequent
metrics-integrity audit found additional reporting/accounting defects; therefore
**macro request/miss comparisons below remain valid, while the old total
retained-cache figures are superseded by `HASHLIFE_METRICS_INTEGRITY_RESULTS.md`.**

## Changes

1. `ComposedBlockEffect.canonical_key` is constructed once with the immutable
   temporal DAG node instead of recursively rebuilding the nested effect key on
   every macro lookup.
2. A complete partition carrier may advertise one structural higher lift only
   when its domain came from a complete extensional child. Physical Collatz T^4
   closes on exact 50/90 opposite-boundary domains, so T^8 stays an exact
   partition/bimachine carrier and T^16 is the first recursive HashLife layer.
3. The lifted partition compiler consumes child-owned symbolic output selector
   rows and does not re-probe composed children through scalar runtime `emit`.
4. Reverse/add is not forced through the Collatz lift. Its T^4 reached state
   space is much larger; its remaining T^8+ work needs a stronger exact symbolic
   transduction/action representation rather than an ID alias table.

## N=256 action-layer comparison that remains valid

| metric | reverse/add before | reverse/add after | Collatz before | Collatz after |
|---|---:|---:|---:|---:|
| macro hits | 133,335 | 133,335 | 145,839 | 86,308 |
| macro misses / entries | 94,259 | 94,259 | 85,273 | **49,027** |
| macro hit rate | 58.58% | 58.58% | 63.10% | **63.77%** |
| tile-advance misses | 53,395 | 53,395 | 37,881 | **22,422** |
| tile-output misses | 40,864 | 40,864 | 47,392 | **26,605** |
| recursive-action intern misses | 22,237 | 22,237 | 22,488 | **13,096** |
| recursive-value misses | 32,633 | 32,633 | 34,357 | **20,802** |
| first recursive exponent | T^8 | T^8 | T^8 | **T^16** |
| scalar compiler probes | 0 | 0 | 0 | **0** |
| raw boundary entries | 0 | 0 | 0 | **0** |
| source-index duplicate entries | 0 | 0 | 0 | **0** |

For Collatz, total macro requests fall from 231,112 to 135,335 (-41.4%); macro
misses fall 42.5%, tile-advance misses 40.8%, tile-output misses 43.9%, and
recursive-action misses 41.8%. The lower absolute hit count is expected because
an entire family of premature T^8 recursive requests no longer exists.

The prior report also compared `retained_cache_entries` as though it were a
complete retained-memory count. That counter omitted leaf caches and persistent
partition/symbolic algebra memo tables. The current corrected N=256 totals are:

```text
reverse/add 196: 170,688 retained effect memo entries
Collatz 27:        82,126 retained effect memo entries
```

Those corrected totals are **not** used to claim the earlier percentage memory
reduction because the pre-action tree was not measured with the corrected
schema. The macro-work reduction remains independently established.

## Compiler/query split after the metrics repair

At N=256:

```text
reverse/add 196:
  compiler retained memo entries      0
  query-created retained memos   170,688
  compiler semantic nodes             52
  query-created semantic nodes    49,597

Collatz 27:
  compiler retained memo entries       258
  query-created retained memos       81,868
  compiler semantic nodes              182
  query-created semantic nodes      26,343
```

Collatz's 258 compiler memos are exact algebraic preparation for the retained
partition/bimachine layer. The scalar compiler probe counter remains zero.

## Corrected current scaling

| family | N | retained effect memos | macro entries | query semantic nodes | reachable canonical tiles | macro hit rate |
|---|---:|---:|---:|---:|---:|---:|
| reverse/add 196 | 16 | 3,608 | 540 | 474 | 76 | 47.8% |
| reverse/add 196 | 32 | 6,351 | 1,869 | 1,209 | 201 | 53.1% |
| reverse/add 196 | 64 | 16,663 | 6,688 | 3,847 | 584 | 56.2% |
| reverse/add 196 | 128 | 51,486 | 24,960 | 13,588 | 1,736 | 57.6% |
| reverse/add 196 | 256 | 170,688 | 94,259 | 49,597 | 5,435 | 58.6% |
| Collatz 27 | 16 | 561 | 85 | 55 | 25 | 34.1% |
| Collatz 27 | 32 | 1,479 | 593 | 380 | 35 | 55.1% |
| Collatz 27 | 64 | 5,489 | 2,953 | 1,808 | 94 | 61.3% |
| Collatz 27 | 128 | 22,746 | 12,931 | 7,709 | 202 | 63.4% |
| Collatz 27 | 256 | 82,126 | 49,027 | 26,343 | 237 | 63.8% |

The global logarithmic first-use release gate remains open. The corrected metrics
show that the remaining cold growth is not an artifact of process-global tile
counters, node-ID collisions, failed memo insertion, or compiler/query mixing.

## Verification

The current focused block/reverse/Collatz/causal-spacetime/HashLife/cache-integrity
suite passes:

```text
62 passed
```

See `HASHLIFE_METRICS_INTEGRITY_RESULTS.md` for the metric bugs, warm-repeat
checks, identity invariants, and current machine-readable audit files.
