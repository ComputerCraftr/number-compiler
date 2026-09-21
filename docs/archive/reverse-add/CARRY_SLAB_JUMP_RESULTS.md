# Native carry-slab morphism / strict jump results — v0.12.0

## What changed

The fixed-height theorem is now the primary powered algebra rather than an expanded
Boolean implementation of it.  Production `Gamma` uses only four semantic spatial
node kinds around its 40 slab inputs:

```text
SLAB_PAIR_CORE   -- exact H-row pair reconstruction
SLAB_PAIR_BIT    -- five projections sharing that one core
CARRY_SCAN       -- exact LT/EQ/GT prefix-carry monoid
ACTIVE_NEXT      -- exact prefix-domain growth
```

`SLAB_PAIR_CORE` is not an unverified opaque temporal token.  The repository keeps
an independent fully factored implementation which expands the same fixed-H theorem
as

```text
carry-event set maps
 -> endpoint-width r/q
 -> prime-power binomial transport modulo 2^w
 -> fixed-H modular sum
```

and randomized multibase tests require the native and factored results to agree.
The factored proof path currently has **265 nodes / 16,198 charged bits**
and visibly contains `CARRY_EVENT`, `INTERVAL_TRANSPORT`, and `MODSUM`.

The exact boundary/innovation coordinate `B_i=C_i xor C_(i+1)` was also implemented.
After charging prefix integration it is larger than the direct carry coordinate at
N=256 (688,945 vs 182,340 bits),
so it is cost-rejected rather than retained as duplicate state.

## Reduction versus v0.11

At fixed capacity 80 and `Gamma^256`:

```text
v0.11 expanded slab       299,297 nodes   18,088,620 bits
v0.12 native morphisms      2,095 nodes      182,340 bits
node reduction             99.30% (142.9x)
bit reduction              98.99% (99.2x)
```

The bounded Boolean residual minimizer now reaches a structural fixed point on the
primitive: no AND/OR/XOR decision cones survive in powered slab roots, so later
squares do not repeatedly rescan a quotient that has nothing left to merge.

## Exact guarded 196 jumps

| strict jump | advance | target width | powered nodes | closed bit evaluations | jump seconds |
|---|---:|---:|---:|---:|---:|
| 32 -> 65 | 33 | 32 | 311 | 5,162 | 1.717 |
| 64 -> 128 | 64 | 58 | 559 | 18,218 | 5.921 |

Both roots materialize outside the powered guard to the independent decimal oracle
exactly.  Forbidden-operation maps are empty.

## Source-independent powered scaling

| N | nodes | references | description bits | depth |
|---:|---:|---:|---:|---:|
| 1 | 55 | 99 | 1,206 | 6 |
| 2 | 63 | 151 | 1,602 | 9 |
| 4 | 79 | 255 | 2,649 | 15 |
| 8 | 111 | 463 | 4,441 | 27 |
| 16 | 175 | 879 | 8,904 | 51 |
| 32 | 303 | 1,711 | 18,615 | 99 |
| 64 | 559 | 3,375 | 39,654 | 195 |
| 128 | 1,071 | 6,703 | 85,013 | 387 |
| 256 | 2,095 | 13,359 | 182,340 | 771 |
| 512 | 4,143 | 26,671 | 390,259 | 1,539 |
| 1024 | 8,239 | 53,295 | 832,674 | 3,075 |

Larger-power log-log fits are approximately:

```text
nodes             ~ N^0.933
description bits  ~ N^1.094
```

The remaining growth is therefore no longer expanded set arithmetic or duplicated
carry/event coordinates.  It is transparently the nonlinear temporal chain itself:
roughly one fixed `SLAB_PAIR_CORE + CARRY_SCAN` generation survives per represented
step.  This is a much smaller exact jump representation, but it is still not a
bit-length-polynomial full-state theorem.

## Honest release boundary

`CarrySlabJumpBackend` remains executable and exact, but `full_state_exact` remains
**false**.  The remaining theorem is an exact finite/polylog behavioral quotient of
the repeated nonlinear slab morphism.  A `Power(Gamma,N)` placeholder, sampled
residual collision, finite orbit table, or hidden successor replay is not accepted.
