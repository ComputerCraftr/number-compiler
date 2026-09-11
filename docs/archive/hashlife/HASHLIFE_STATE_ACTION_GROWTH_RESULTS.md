# HashLife bounded temporal application growth audit

## What is measured

Production now separates four different objects instead of treating every generated digit/tile occurrence as temporal state:

1. **literal seed root** — the canonical dyadic payload for `196` or `27`;
2. **compiled jump function** — the source-independent binary-powered `F^N` description;
3. **bounded temporal application state/action** — the family-specific quotient used when `F^N` is applied to the seed;
4. **exact spatial payload/action work** — dyadic pair/tail geometry needed only for exact projection.

For any count `M(N)` on the doubling schedule the probe reports

```text
alpha(N) = log2(M(N) / M(N/2))
```

`alpha < 1` is sublinear in generation count. Temporal closure is judged from bounded temporal state/action growth; exact spatial work is reported separately and is not allowed to masquerade as temporal state.

## Production cutover invariants

Both reverse/add and Collatz satisfy all of these in the N=16..256 probes:

```text
bounded_temporal_runtime_cutover_complete             true
unquotiented_recursive_application_description_nodes  0
raw_temporal_scalar_length_fields                     0
raw_temporal_span_fields                              0
raw_spatial_occurrence_scalar_extent_fields           0
recursive_boundary_wrapper_nodes                      0
eager_spatial_observer_fields                         0
spatial_occurrence_accounting_delta                   0
```

The retired `SpacetimeBoundary` temporal carrier is deleted. `_RecursiveResidualAction` remains generic infrastructure for other effects but is not allocated by production reverse/add or Collatz point queries.

## Reverse/add seed 196

Decimal reverse/add uses the fixed carry-cut horizon

```text
H = 4 * bit_length(18) = 20
cell payload = 20 carry bits + 20 active bits
bounded temporal classes at N=256 = 2 state / 2 action
```

No temporal identity contains the whole prefix, pair length, row-width vector, `anchor_before`, or a scalar residual extent. Exact growing digits remain dyadic spatial payload.

| N | exact digits | seed tiles | compiled `F^N` | bounded state/action | exact spatial occurrences | symbolic spatial actions | jump entries | primitive forcing evals | app spatial tiles | primitive alpha |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 9 | 3 | 21 | 1 / 1 | 0 | 126 | 0 | 15 | 54 | — |
| 32 | 16 | 3 | 27 | 2 / 2 | 12 | 346 | 19 | 31 | 227 | 1.047 |
| 64 | 31 | 3 | 33 | 2 / 2 | 44 | 1131 | 82 | 63 | 852 | 1.023 |
| 128 | 58 | 3 | 39 | 2 / 2 | 108 | 3439 | 209 | 127 | 2767 | 1.011 |
| 256 | 113 | 3 | 45 | 2 / 2 | 236 | 10567 | 464 | 255 | 9626 | 1.006 |

At N=256 the **temporal application description is only 4 bounded nodes** and its tail local exponent is `0.000`. The compiled function tail exponent is `0.206`.

The remaining reverse/add blocker is no longer temporal-history retention. It is the cold exact **spatial forcing action**: primitive forcing evaluations are `255` at N=256 with tail exponent `1.006`, and symbolic spatial action nodes grow to `10,567`. The next optimization must compose that cut-to-cut spatial forcing action recursively instead of walking one exact forcing occurrence per generation.

## Physical Collatz seed 27

The production Collatz application uses a bounded 3-adic/residue/local phase plus symbolic event transport. Exact normalized tail tiles are spatial payload, not temporal identity. The descriptor tracks symbolic multiplier/shift information instead of materializing a giant multiplier integer.

At N=256 the bounded temporal application has **3 state / 3 action classes**.

| N | exact bits | seed tiles | compiled `F^N` | bounded state/action | exact spatial occurrences | symbolic spatial actions | jump entries | primitive evals | app spatial tiles | primitive alpha |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 7 | 5 | 169 | 2 / 2 | 9 | 18 | 16 | 8 | 11 | — |
| 32 | 10 | 5 | 172 | 2 / 2 | 17 | 32 | 42 | 17 | 19 | 1.087 |
| 64 | 11 | 5 | 175 | 2 / 2 | 33 | 59 | 95 | 32 | 38 | 0.913 |
| 128 | 2 | 5 | 178 | 3 / 3 | 41 | 107 | 154 | 43 | 40 | 0.426 |
| 256 | 3 | 5 | 181 | 3 / 3 | 41 | 122 | 161 | 42 | 40 | -0.034 |

For seed 27 the cold quotient visibly saturates on the tail: primitive evaluations are `43 -> 42` from N=128 to 256, with local exponent `-0.034`; exact spatial occurrence tail exponent is `0.139`. This is a representative-seed result, **not** a proof of arbitrary-source logarithmic Collatz projection.

## Release interpretation

The previous 49,597 reverse/add and 26,343 Collatz "seed-specific temporal nodes" were measurements of the retired generic residual occurrence carrier. They are intentionally **zero** on the new production path and must stay zero.

The correct release gate is now:

- bounded temporal state/action class counts must stay generation-independent;
- raw temporal length/span fields must stay zero;
- generic recursive application allocations must stay zero;
- exact spatial action work is measured separately with its own local exponent;
- reverse/add remains open until its cold spatial forcing/action work bends below linear;
- Collatz seed 27 passes the representative tail gate, while arbitrary-source closure remains open.

## Machine-readable artifacts

- `results/hashlife_state_action_growth_reverse_196.json`
- `results/hashlife_state_action_growth_collatz_27.json`
- `results/hashlife_cache_audit_reverse_196_n256.json`
- `results/hashlife_cache_audit_collatz_27_n256.json`
- `results/reverse_temporal_power_metrics.json`
- `results/collatz_temporal_power_metrics.json`
