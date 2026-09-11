> **v0.53.8 note:** the historical fixed-height carry-slab backend described below has been removed. Current 196 spatial carry/digit projection uses the exact finite threshold-defect state and shared logarithmic prefix monoid in `reverse_domain.py` / `prefix_monoid.py`. Historical measurements are retained only as research evidence.

# Generalized reverse-add power results

## What is now closed

The release now contains two arbitrary-power constructions with distinct contracts.

1. `compile_native_power(arena, source, N, spec)` algebraically substitutes every
   finite temporal layer into **one final FormulaRoot**.  No intermediate FormulaRoot,
   `successor()`, T² root, or T⁴ root is constructed.  It is the generalized exact
   equation-elimination oracle.  Because it still resolves one closed growth event per
   temporal layer, its compile work is linear in `N` and it is intentionally rejected by
   `powered_jump_scope`.
2. `power_block_effect(base=b, exponent=N)` compiles the exact **source-independent local
   T^N operator** by binary composition.  It constructs no source word and replays no
   elementary generation.  For `N=10^18` (60 bits) it has
   **82 operator nodes**, **81 compositions**,
   and syntax depth **60**.

The second object is the generalized powered operator that was missing from the canonical
FormulaRoot tree.  Applying it once to a finite padded pair field is exact and creates zero
intermediate pair words.

## Exactness

- randomized multibase powered-block comparisons: **1350 exact cases**;
- bases 2..16, exponents 0..8, randomized symmetric pair fields;
- existing native T²/T⁴ differential tests remain green;
- full repository test suite is run separately by the release gate.

## Formula elimination scaling on decimal 196

| N | output width | FormulaRoot nodes | depth | description bits | closed growth-bit evaluations |
|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 21 | 11 | 500 | 9 |
| 2 | 4 | 66 | 24 | 2064 | 34 |
| 4 | 5 | 128 | 47 | 4597 | 155 |
| 8 | 7 | 272 | 105 | 10653 | 567 |
| 16 | 9 | 519 | 224 | 22464 | 1727 |
| 32 | 16 | 1147 | 501 | 53443 | 5436 |
| 64 | 31 | 2586 | 1151 | 130492 | 17379 |
| 128 | 58 | 5695 | 2631 | 314358 | 72304 |
| 256 | 113 | 12531 | 5948 | 759479 | 283587 |

At N=256 the fully substituted closed formula has 12531 reachable nodes and
759479 description bits.  This is exact elimination, but not a
polylogarithmic temporal compiler.

## Binary operator syntax versus bounded production application

The source-independent powered operator remains a compact binary DAG, but production reverse/add and Collatz no longer apply it through the generic recursive occurrence carrier. They use family-specific bounded temporal backends.

For reverse/add 196, the fixed H=20 carry-cut state reaches 2 state / 2 action classes by N=256 and allocates zero generic recursive application nodes. Exact pair/tail geometry is spatial payload. The remaining cold cost is the exact spatial forcing action: 255 primitive forcing evaluations and 10,567 symbolic spatial action nodes at N=256.

For Collatz 27, the bounded residue/local-phase + symbolic event quotient reaches 3 / 3 classes, 42 primitive evaluations, and 122 symbolic spatial action nodes at N=256; the final doubling is sublinear. Arbitrary-source logarithmic closure remains unproved.

The old 94,259 / 49,027 generic macro-entry measurements are pre-cutover historical results. Current production generic macro/residual counters are zero by construction; see `HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md` and `HASHLIFE_METRICS_INTEGRITY_RESULTS.md`.

## Restored fixed-height carry/event theorem

The nonlinear forcing is again exposed as a derived compiler IR, not semantic state.  In decimal,
`H=20` previous forward binary carry fields reconstruct the exact endpoint pair; the signed event
field is a pure function of that one forward carry field, and `len(E_t)=len(S_(t+1))`, so event
widths recover the later growth/length sequence.  The release therefore treats the remaining
nonlinear theorem target as **20 binary carry position-set fields × spatial coordinate**, not an
unbounded temporal tower of T^8/T^16 program syntax.  See `CARRY_EVENT_FORMULA_RESULTS.md`.

## Full J status

An exact source-specialized `J_a : FormulaRoot_n -> FormulaRoot_(2n+a)` **research backend is installed** for decimal 196 through the fixed-height carry slab. v0.12 replaces the expanded slab arithmetic by native fixed-H spatial morphisms and reuses the powered morphism's final pair directly; guarded 32->65 and 64->128 jumps are exact and non-replaying.

Historical slab powers did not close temporally and are no longer a live backend. The current open question is whether the finite threshold-defect/domain morphism itself admits a successor-closed polylogarithmic temporal quotient; v0.53.8 changes only the spatial prefix engine.
