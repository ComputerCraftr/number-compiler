# Quotient-pattern research — v0.19.0

This pass asks whether exact behavior can be quotiented **before** projection/composition rather than becoming small only after the expensive work has already been performed.

## 1. Prime block: residual-divisor set morphism + lane-action quotient

The retained prime block projector propagates canonical divisor progressions and singleton hit points through radix partitions.  A second quotient now hash-conses each individual `(period, local phase, interval size, radix)` transform before child interfaces are constructed, so the same lane action is not recomputed merely because it occurs inside a different residual interface.

| candidates | residual interfaces | arithmetic transform checks | transform cache hits | decision nodes | description bits | charged projection work |
|---:|---:|---:|---:|---:|---:|---:|
| 64 | 13 | 214 | 51 | 9 | 111 | 18865 |
| 256 | 37 | 758 | 310 | 26 | 494 | 19764 |
| 1024 | 110 | 2658 | 1550 | 81 | 2275 | 23196 |
| 4096 | 368 | 8430 | 7526 | 244 | 7968 | 36055 |

At 4,096 candidates the exact result remains `503` primes with first index `13`, but only **8,430** radix membership calculations are executed.  **7,526** exact single-lane/point transforms are reused before interface construction.  Charged projection work is **36,055**, including cache-hit lookup work and the self-modifying factor-basis construction.

Finite log-log fits over 64..4,096 are diagnostics, not asymptotic theorems.  For base 4, executed arithmetic transform checks fit about `L^0.885`, while charged radix-partition work including exact cache-hit lookups and primary-jet composition fits about `L^0.970`.  The retained decision description still fits about `L^1.035`.  Thus the action cache removes repeated arithmetic and makes the measured transform count sublinear-looking, but v0.19 does **not** claim a universal sublinear/polylog prime projector.

## 2. Reverse-add: pre-scan carry automaton quotient

The raw pair field is mapped to the exact threshold word `< b-1`, `= b-1`, `> b-1`.  These are precisely the carry functions `CONST0`, `ID`, `CONST1`; v0.53.8 composes them directly in the shared prefix monoid. Historical scan measurements below predate that replacement.

For seed 196 over 512 transitions, radix 8 reuses **191** nonlinear actions and evaluates only **0** scans.  Decimal still has **0** reuse, so the decimal full-J frontier remains open.

## 3. Shared `(z+1)` primary jet

A theorem/digit run of length `2^20` is represented with **22 binary compositions**.  The primary jet is a derived theorem interface shared by reverse-add, Collatz, prime summaries, Fermat and Mersenne; it is not a second semantic sequence state.

## 4. Collatz inverse coordinate

The exact inverse parity coordinate has a uniform streaming arithmetic transducer.  It consumes one parity symbol per position and retains `2k` state bits; the earlier `O(sqrt(k) 2^(k/2))` result is an ROBDD bound, not a lower bound on arithmetic projection.

| width k | retained state bits | program description bits | symbol steps |
|---:|---:|---:|---:|
| 24 | 48 | 32 | 24 |
| 28 | 56 | 36 | 28 |
| 32 | 64 | 41 | 32 |
| 64 | 128 | 74 | 64 |
| 128 | 256 | 139 | 128 |

## Release conclusion

The reusable pattern is now `canonical source/set interface -> derived nilpotent/congruence theorem interface -> extensional action key before projection -> hash-cons/binary composition -> separately charged terminal projection`.  It materially reduces prime projection work and radix-8 reverse-add scan work, but the old slab backend is now deleted; temporal closure remains open for the finite defect-domain morphism itself.
