# v0.53.4 early algebraic cache cleanup

## Scope

v0.53.4 moves memoization ahead of nonsemantic coordinate actions.  The fix is deliberately narrower than an asymptotic theorem claim: canonical algebraic state is now interned before absolute BSGS translations/scales and before Collatz root-matching frame depth is converted into an emitted valuation.

The old late caches remain only as carrier/lowering caches.  They no longer define semantic identity.

## BSGS progression products

A concrete progression block is

`P(a,s,n;X) = product_(0<=j<n) (X-(a+j*s))`.

`ProgressionProductMorphism.canonical_key` still identifies the exact absolute block for coefficient lowering, but the new upstream `algebraic_shape` removes coordinate actions first:

- translation `a` is always action state;
- when `gcd(s,N)=1`, scale `s` is action state too;
- the retained unit-step algebraic shape is therefore only `(N,n)`;
- a nonunit `s` stays in the shape because scaling by it is not invertible in `Z/NZ`.

`ProgressionProductArena.canonicalize()` is called before balanced splitting or coefficient lowering.  Split widths are obtained from the canonical shape, not reconstructed from each translated instance.

Measured fixed-window controls:

| control | raw absolute progression states | canonical algebraic shapes | compression | shape-cache hits | shape-cache misses |
|---|---:|---:|---:|---:|---:|
| F5 / 511 slots | 88 | 9 | 9.78x | 273 | 9 |
| M29 / 399 slots | 76 | 9 | 8.44x | 234 | 9 |

This closes the *late structural cache* bug.  It does **not** make the first support evaluation polylogarithmic.  Exact composite-ring coefficient/remainder lowering still uses the existing absolute product tree because the attempted division-free Taylor transport was measured to cost more ring work on the release controls.  The release therefore retains 5,440 charged ring operations for F5 and 4,749 for M29 rather than hiding a regression behind a smaller descriptor.

## Collatz rational-root transitions

`CollatzGermTransitionCache` now sits between `CollatzAffineSuffixGerm` and valuation/event emission.

For a pulled-back rational root `-c/3^h`, `RationalPadicRootGerm.normalize_matching_prefix_word()` removes the maximal radix-4 prefix that agrees with the root.  The removed quarter count is a gauge action contributing only `2*q` valuation bits.  Cache identity is formed from the normalized rational root plus residual canonical suffix; logical time and the removed matching depth are not in the transition key.

On a cache miss, the first actual mismatch is computed once and stored as a canonical angular-boundary transition.  On a hit, the caller-specific valuation offset is restored after lookup.  Thus reuse occurs before a new valuation or `CollatzEventNode` is created.

Control with the same residual tail digit 3 but two radically different sentinel depths:

- `q=100`: two transition misses, total shift 205;
- `q=1,000,000`: **two transition hits, zero new misses**, total shift 2,000,005;
- both normalize to the same two-step target `1`;
- affine cocycle materializations remain zero.

The ordinary `collatz_affine_suffix_valuations_*` projection and direct root-germ -> event-DAG projection both use the same upstream transition cache.

## Honest frontier

This release fixes cache identity, not the still-open behavioral quotients.

- BSGS: canonical algebraic structure is `O(log b)` width shapes on the balanced controls, but exact unseen coefficient/support specialization is still charged separately and remains non-polylogarithmic.
- Collatz: equivalent root/frame states now converge before valuation emission, but genuinely distinct future normalized frame states can still grow with event count.  No claim is made that arbitrary Collatz event generation is logarithmic.
- Production Fermat/Mersenne theorem resolution retains the exact lazy-constraint + Pepin/Lucas--Lehmer ceiling.

Reproduce with `PYTHONPATH=src:. python bench/early_algebraic_cache_probe.py`; metrics are written to `results/early_algebraic_cache_metrics.json`.
