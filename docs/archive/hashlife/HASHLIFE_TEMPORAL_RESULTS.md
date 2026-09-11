> **Historical pre-bounded-cutover report.** The generic macro/residual counts below document earlier bugs and optimizations. Current production reverse/add/Collatz bypass that carrier; use `HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md` and `HASHLIFE_METRICS_INTEGRITY_RESULTS.md` for current metrics.

# v0.59.9 temporal HashLife results

> **Metrics-integrity correction:** the macro request/hit/miss figures below remain
> valid. The historical retained-cache percentage used the old budgeted-only
> subtotal and is superseded by `HASHLIFE_METRICS_INTEGRITY_RESULTS.md`. Current
> N=256 retained effect memos are 170,688 for reverse/add and 82,126 for Collatz.

The temporal operator DAG and spatial dyadic tree meet at one canonical cache
boundary. A composed effect owns its tile action; the source index does not learn
a second copy. Immutable temporal effect keys are precomputed once per DAG node.

For a demanded tile the runtime caches:

```text
(effect, side, canonical boundary state, canonical DyadicTile)
    -> canonical boundary state

(side, canonical DyadicTile, left/right causal interfaces)
    -> (updated interfaces, canonical future DyadicTile)
```

Low finite layers keep their algebraic action structure as long as it is exact
and complete. In physical Collatz, the complete T^4 partition domain is only
50/90 opposite-boundary states, so T^8 remains an exact partition/bimachine
carrier. The capability is consumed once; T^16+ uses the recursive quadtree.
Reverse/add's T^4 reached universe is much larger, so reverse/add enters the
recursive carrier at T^8 rather than eagerly determinizing it.

Measured cold position-0 probes:

```text
reverse/add 196, N=256:
  macro hits                         133,335
  macro misses / entries             94,259
  recursive-value entries            32,633
  recursive action nodes             22,261
  macro hit rate                       58.6%
  first recursive layer                  T^8
  raw boundary cache entries               0
  source-index composed entries            0
  accounting delta                         0

Collatz 27, N=256:
  macro hits                          86,308
  macro misses / entries             49,027
  recursive-value entries            20,802
  recursive action nodes             13,106
  macro hit rate                       63.8%
  first recursive layer                 T^16
  symbolic row hits / misses       1,831 / 184
  scalar compiler probes                   0
  raw boundary cache entries               0
  source-index composed entries            0
  accounting delta                         0
```

Relative to the previous recursive-finished Collatz tree, total macro requests
fall 41.4% and macro misses fall 42.5%. The earlier retained-cache percentage is
not repeated under the corrected schema because the pre-action tree was not
measured with complete leaf/algebraic memo accounting. The absolute hit count
falls too because the eliminated T^8 recursive layer no longer makes those
requests; hit percentage alone would hide the improvement.

This materially improves Collatz and removes another late-work layer. It does
**not** close the global asymptotic gate. Reverse/add's exact cache counts are
unchanged by the finite-carrier lift, which is evidence that its remaining T^8+
contexts need a stronger exact symbolic transduction/action quotient rather than
another structural ID canonicalizer.
