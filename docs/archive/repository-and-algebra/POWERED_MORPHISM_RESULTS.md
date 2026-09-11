# Powered morphism / factored automaton results

## Prime factored-congruence decision automaton

This decision DAG is compiled directly from packed congruence states; no prime bitmap is materialized on this path.

| 4096-candidate coordinate | description bits | congruence transitions | nodes |
|---|---:|---:|---:|
| binary `(2,)` | 8983 | 638820 | 475 |
| base-4 `(4,)` | 8034 | 425880 | 246 |
| alternating `(4,2,8)` | 6235 | 446160 | 159 |

Base 4 retains 89.44% of the binary decision-description bits and 66.67% of its scalar residue-transition work.  `(4,2,8)` reduces retained description further but is not uniformly best in transition work or padding, so it remains an alternate exact coordinate rather than the default.

A random-access +2 candidate jump of `2^20` uses 21 semantic affine compositions after the start residue state has been compiled.

## Residual-divisor set quotient

The whole prime block is also compiled by propagating divisor progressions/points through radix partitions before candidate leaves.  This is the retained production block projector; packed-residue and hyperbolic paths remain independent differentials/random-access machinery.

| candidates | radix | interfaces | lane transforms | nodes | description bits |
|---:|---|---:|---:|---:|---:|
| 64 | base4 | 13 | 214 | 9 | 111 |
| 256 | base4 | 37 | 758 | 26 | 494 |
| 1024 | base4 | 110 | 2658 | 81 | 2275 |
| 4096 | base4 | 368 | 8430 | 244 | 7968 |

At 4096 candidates the base-4 residual-set quotient executes 8430 arithmetic lane/point checks and reuses 7526 exact cached transforms, plus 17054 bounded-word generator gcds, versus 425880 scalar packed-residue transitions on the direct factored decision path.

## Collatz radix and inverse-coordinate representations

| seed 27 radix | max formula nodes |
|---:|---:|
| 2 | 9897 |
| 3 | 3158 |
| 6 | 2571 |
| 12 | 4325 |
| 18 | 6073 |

Radix 6 makes both `3*n+1` and `/2` radius-1 digit maps: no carry-prefix/remainder-prefix scan survives in either branch.

| inverse width | ROBDD nodes | streaming state bits | streaming symbol steps |
|---:|---:|---:|---:|
| 24 | 62874 | 48 | 24 |
| 28 | 250474 | 56 | 28 |
| 32 | 971238 | 64 | 32 |

The previous `O(sqrt(k) 2^(k/2))` result is a bound for the shared **decision diagram**, not for arbitrary arithmetic circuits.  The exact inverse map also has a uniform streaming arithmetic transducer with `2k` retained state bits and `k` independent input-symbol steps.  This removes the subexponential representation bound, but not the linear information cost of reading an arbitrary parity word.

## Reverse-add extensional action key

Decimal 196: 0 pre-scan nonlinear-action reuses in 512 transitions.
Octal 196: 191 pre-scan reuses; only 0 historical carry-prefix evaluations remain, while complete source interfaces stay unique.

The exact source key is the live suffix alone; the primary/cyclotomic jet is a derived theorem interface.  The nonlinear action is keyed by the universal `<,=,>` threshold word; the old scan IR was removed in v0.53.8.  Decimal 196 still has no reuse, while radix 8 has substantial exact reuse.

## Powered theorem/residue projections

A primary-jet digit run of length `2^20` is constructed with 22 compositions.
Fermat/Mersenne sparse binary words and their cross-radix cyclotomic reinterpretations use the same powered word/jet/factored-residue morphisms.  Primality tests remain separately charged.

Among the 503 primes in the 4096-candidate block near 10^7, **0** binary digit polynomials had a cyclotomic factor of order <=48.  In contrast, Mersenne/Fermat prime bit strings are pure cyclotomic words.  Thus literal bit reinterpretation exposes special-family structure but does not create a generic prime classifier in this sample.
