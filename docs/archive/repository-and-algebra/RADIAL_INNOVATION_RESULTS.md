# Radial-mode / normalized-innovation quotient results — v0.46.0

## Reverse-add radial theorem

For a block with `q` no-growth and `r` growth steps the homogeneous pair-field action is `2^q(1+z)^r`; at `z=1` the common physical scale is exactly `2^(q+r)`. In `Phi_(2m)=z^m+1`, the coefficient-content valuation is `q+floor(r/m)`, so the large radial mode is represented only by that valuation and the remaining unit polynomial is binary-powered at reduced precision.

| m | q | r | radial exp | v2 | r mod m | annihilated | exact multiplier reconstruction |
|---:|---:|---:|---:|---:|---:|---|---|
| 1 | 0 | 1 | 1 | 0 | 0 | True | True |
| 1 | 3 | 2 | 5 | 3 | 0 | True | True |
| 1 | 4 | 4 | 8 | 4 | 0 | True | True |
| 1 | 8 | 7 | 15 | 8 | 0 | True | True |
| 1 | 12 | 16 | 28 | 12 | 0 | True | True |
| 2 | 0 | 1 | 1 | 0 | 1 | False | True |
| 2 | 3 | 2 | 5 | 4 | 0 | False | True |
| 2 | 4 | 4 | 8 | 6 | 0 | True | True |
| 2 | 8 | 7 | 15 | 11 | 1 | True | True |
| 2 | 12 | 16 | 28 | 20 | 0 | True | True |
| 4 | 0 | 1 | 1 | 0 | 1 | False | True |
| 4 | 3 | 2 | 5 | 3 | 2 | False | True |
| 4 | 4 | 4 | 8 | 5 | 0 | True | True |
| 4 | 8 | 7 | 15 | 9 | 3 | True | True |
| 4 | 12 | 16 | 28 | 16 | 0 | True | True |
| 8 | 0 | 1 | 1 | 0 | 1 | False | True |
| 8 | 3 | 2 | 5 | 3 | 2 | False | True |
| 8 | 4 | 4 | 8 | 4 | 4 | False | True |
| 8 | 8 | 7 | 15 | 8 | 7 | True | True |
| 8 | 12 | 16 | 28 | 14 | 0 | True | True |

## Reverse-add live innovation after radial annihilation

The audit discards the old pair separately in each cyclotomic factor as soon as its multiplier is provably zero. Only the transported forcing innovation remains.

| domain | modes | usable | innovation classes | distinct pairs | growth conflicts | action conflicts | max live | near reconstruction |
|---|---|---:|---:|---:|---:|---:|---:|---|
| train | 2,4,8 | 1,641 | 124 | 124 | 0 | 0 | 8 | True |
| holdout | 2,4,8 | 1,266 | 937 | 953 | 8 | 17 | 9 | True |
| high | 2,4,8 | 646 | 447 | 450 | 1 | 3 | 9 | True |
| train | 2,4,8,16 | 1,625 | 122 | 122 | 0 | 0 | 10 | True |
| holdout | 2,4,8,16 | 1,259 | 946 | 946 | 0 | 0 | 11 | True |
| high | 2,4,8,16 | 643 | 447 | 447 | 0 | 0 | 11 | True |

Low modes expose real finite source-annihilation but retain next-action conflicts. Adding enough modes to close the bounded action approaches one state per distinct pair on holdouts, so the closure path is rejected as source reconstruction. The radial theorem itself remains canonical and useful for proving source death.

## Reverse-add reversal-fixed symmetry frame

The width-growth action is quotiented as a two-sector reflection frame. Even-width palindromes first lose their exact `(1+z)` symmetry factor and are then centered; odd-width palindromes are centered directly.  The low `Phi_2/Phi_4/Phi_8` views are now one `FixedRealCyclotomicGerm` in `x=z+2+z^-1`: for `F=R8+P8*Q`, `P8=x^2-4x+2`, it retains `R8`, `Q(0)`, and `(Q(2)-Q(0))/2`.  Every component is taken at one common source-annihilation horizon.  In this frame no-growth acts by `2`, odd-to-even growth by `1`, and even-to-odd growth by `x`.

| domain | modes | usable | fixed-frame classes | distinct pairs | growth conflicts | action conflicts | max live | near reconstruction |
|---|---|---:|---:|---:|---:|---:|---:|---|
| train | 2,4,8 | 1,681 | 124 | 124 | 0 | 0 | 8 | True |
| holdout | 2,4,8 | 1,266 | 945 | 953 | 6 | 13 | 9 | True |
| high | 2,4,8 | 646 | 448 | 450 | 1 | 2 | 9 | True |
| train | 2,4,8,16 | 1,625 | 122 | 122 | 0 | 0 | 10 | True |
| holdout | 2,4,8,16 | 1,259 | 946 | 946 | 0 | 0 | 11 | True |
| high | 2,4,8,16 | 643 | 447 | 447 | 0 | 0 | 11 | True |

The shared-horizon germ also fixes a real audit bug: factor-local source death can occur at different suffix lengths (the regression witness is `2,6,7`), so the old concatenation did not necessarily describe one forcing polynomial.  The corrected low germ still leaves action conflicts and is already near reconstruction.  Its exact invisible difference ideal is `P8*(2^(w-1),2^(w-2)*x,x*(x-2))`; adding `Phi_16` again reaches one class per pair.  The remaining 196 problem is therefore a proper **behavioral quotient of that hidden `P8` layer**, not another cyclotomic coordinate.

## Collatz 3-adic radial innovation

An accelerated valuation slab is exactly `(3^H*x+C)/2^K`. Modulo `3^a`, the source multiplier has valuation `H`; after `a` odd steps it is zero and the current residue is exactly the innovation term. No digit or multiplication carry field is used.

| domain | precision a | usable | innovation classes | distinct current states | next-v2 conflicts | source dead | projection exact | near reconstruction |
|---|---:|---:|---:|---:|---:|---|---|---|
| small | 4 | 44,544 | 54 | 2,149 | 19,378 | True | True | False |
| small | 8 | 33,133 | 995 | 1,371 | 1,284 | True | True | False |
| small | 12 | 22,911 | 933 | 933 | 0 | True | True | True |
| small | 16 | 14,056 | 640 | 640 | 0 | True | True | True |
| holdout | 12 | 31,624 | 8,405 | 8,766 | 431 | True | True | True |
| holdout | 16 | 20,208 | 4,982 | 4,982 | 0 | True | True | True |
| high | 16 | 22,079 | 5,134 | 5,135 | 1 | True | True | True |

The 3-adic radial split is an exact finite-memory theorem for local projections, but increasing precision eliminates next-valuation conflicts only by approaching the current odd state itself. It is therefore retained as a theorem/projection channel, not promoted as the Collatz orbit state.
## Collatz radix-4 fixed-point frame

The low radix-4 `1` run is a removable 2-adic fixed-point frame around `-1/3`.  If `n=(4^q-1)/3+4^q m`, then `3n+1=4^q(3m+1)`.  The unbounded frame depth `q` contributes only `2q` to the current valuation and disappears from the accelerated successor; after stripping it, only the local sector `t=k mod 2` remains.

The following branch is itself a first-hole boundary query: `k_next=v2(9m+4)` for `t=0`, and `k_next=v2(9m+5)-1` for `t=1`.  v0.46 removes the literal periodic implementation.  `RationalPadicRootGerm` represents a general root `-c/3^h` and skips constant radix-4 runs from `v2(3c-3^h*d)` plus one exact shift.  At the first mismatch `PadicAngularBoundaryGerm` rewrites the normalized discrepancy as an affine map of the unconsumed higher suffix, and `CollatzAffineSuffixGerm` pulls subsequent roots back through that affine map.  No intermediate Collatz digit word or root period of length `3^(h-1)` is materialized.

| domain | precision | usable | distinct current | raw future classes | raw conflicts | framed classes | framed conflicts | projection exact | near reconstruction | exact finite-precision collision |
|---|---:|---:|---:|---:|---:|---:|---:|---|---|---|
| small | 8 | 30,445 | 1,359 | 985 | 1,157 | 1,102 | 450 | True | False | True |
| small | 12 | 20,566 | 915 | 915 | 0 | 851 | 0 | True | False | True |
| holdout | 12 | 28,697 | 8,329 | 8,008 | 297 | 7,619 | 84 | True | False | True |
| holdout | 16 | 17,512 | 4,547 | 4,547 | 0 | 4,204 | 0 | True | False | True |
| high | 16 | 19,180 | 4,629 | 4,628 | 1 | 4,329 | 0 | True | False | True |

The reduction is real: at precision 16 the holdout shrinks from 4,547 raw classes to 4,204 framed classes and the high guard from 4,628 to 4,329 while sampled future-valuation conflicts are zero and the 95% reconstruction guard stays false.  This bounded closure is not promoted globally.  For every finite precision `a`, tails `m1=3` and `m2=3+4*3^a` have the same framed residue modulo `3^a` and the same sector `t=1`, but their next valuations are exactly `4` and `1`.

The finite-precision 3-adic frame is still not globally closed, but its formerly missing local 2-adic boundary operation is now explicit and exact.  The remaining Collatz theorem is **temporal binary composition of the branching affine/root germs**.  More 3-adic precision, the discarded frame depth, a literal periodic root table, or a stored valuation itinerary are explicitly rejected as substitutes.

## Collatz rational-root/angular-germ differential audit

- odd sources: **2,500**
- accelerated projections per source: **8**
- exact against integer Collatz: **True**
- direct rational-root denominators checked through: **3^8**
- one-million-radix-4-digit frame first valuation: **2,000,001**
- second valuation: **4**
- final unconsumed suffix length: **0**
- literal `PeriodicSentinelBoundarySummary` production definitions: **0**
