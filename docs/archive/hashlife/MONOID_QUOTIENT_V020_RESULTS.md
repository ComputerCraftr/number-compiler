# Cross-family monoid / quotient search — v0.20.0

This pass charges construction and projection separately. A representation is retained only when it is an exact semantic quotient or when a static pre-execution optimizer selects it without compiling losing alternatives.

## Prime residual-set radix schedule

| candidates | v0.19 work | v0.20 period | v0.20 work | ratio | retained bits |
|---:|---:|---|---:|---:|---:|
| 64 | 18865 | `(4,)` | 18865 | 1.000 | 111 |
| 256 | 19764 | `(4,)` | 19764 | 1.000 | 494 |
| 1024 | 23196 | `(4, 8)` | 23004 | 0.992 | 2055 |
| 4096 | 36055 | `(4, 8)` | 34603 | 0.960 | 9982 |

The schedule is static: radix 4 below 1024 candidates and `(4,8)` at/above 1024. No rejected schedule is executed at runtime.

## Reverse-add carry automaton

The exact action key is now the carry-reset behavior. The compiler stores whichever exact encoding is cheaper: the palindromic half-threshold mask or the reset-change itinerary.

| seed/base | unique actions | reuses | half-threshold avg bits | reset avg bits | selected avg bits |
|---|---:|---:|---:|---:|---:|
| 196/8 | 321 | 191 | 86.0 | 38.7 | 38.2 |
| 196/10 | 512 | 0 | 134.5 | 443.6 | 134.4 |
| 195/4 | 427 | 85 | 108.9 | 41.1 | 40.7 |

## Collatz operation-adapted radix

| radix | max formula nodes | max description bits |
|---:|---:|---:|
| 2 | 9897 | 389133 |
| 3 | 3158 | 77958 |
| 6 | 2571 | 81105 |
| 12 | 4325 | 188927 |
| 18 | 6073 | 308923 |
| 24 | 7611 | 418223 |
| 30 | 9174 | 569816 |
| 36 | 10936 | 732864 |

Radix 6 remains the strongest tested single coordinate because multiplication by 3 and division by 2 are both local. Switching whole-number coordinates per branch was not retained because conversion is a separate linear digit projection.

## Fermat/Mersenne digit-field carry quotient

Every cyclic/negacyclic coefficient block normalizes through one scalar fixed/anti-fixed boundary carry; no carry vector is retained. The square compiler uses schoolbook on small/sparse fields and Karatsuba only after the charged crossover.

| dense width | selected | charged ops | schoolbook charged ops |
|---:|---|---:|---:|
| 64 | schoolbook | 8065 | 8065 |
| 128 | schoolbook | 32513 | 32513 |
| 256 | schoolbook | 130561 | 130561 |
| 512 | karatsuba | 144397 | 523265 |
| 1024 | karatsuba | 439330 | 2095105 |

Supplied factor witnesses are even smaller: Fermat factor testing takes `n` modular squarings in the exponent-doubling coordinate, while Mersenne factor testing takes `O(log p)` binary modular compositions. Factor *search* remains separately unsolved/charged.

## Prime bit reinterpretation

Reinterpreting binary prime words into other radices exposes cyclotomic classes but does not classify the block: many classes remain mixed prime/composite. Mixed-radix residual languages do reduce finite automaton state, which is why the production projector uses a radix schedule on the factored congruence/set state rather than on raw prime bits.

## Shared radial / sensitivity theorem stack

The old reverse-add and Collatz valuation-only aliases are gone. Reverse-add now exposes the strictly richer exact radial split `2^q(1+z)^r = 2^v * unit`; Collatz exposes the exact p-adic affine map and its `PadicRadialQuotient`. The generic tropical `v -> min(W,a*v+b)` monoid remains only where valuation is the whole theorem channel (Fermat/Mersenne and prime controls). None of these derived views replaces exact sequence state.

## Bound conclusion

The new work reduces retained carry state and some projection constants/sublinear-looking finite-window work, and it gives logarithmic factor-witness/exponent morphisms for the special families. It does **not** prove logarithmic total primality projection, the Collatz conjecture, or a polylog decimal-196 full-J quotient. Those release blockers remain explicit.
