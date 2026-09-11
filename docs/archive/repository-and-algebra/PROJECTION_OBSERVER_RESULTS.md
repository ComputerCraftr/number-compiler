# Projection observer quotient results

Two states merge only after exact Moore/Myhill--Nerode refinement of the projection process.
Short bounded traces are reported separately and never authorize a production merge.

## Reverse-and-add

The per-digit carry/growth observer is already the 3-element transformation monoid `CONST0 / ID / CONST1` on two carry states.
The universal no-four-consecutive-growth theorem reduces the future growth language, but not to a finite temporal quotient:

| horizon | admissible growth words | information bits | bits/step |
|---:|---:|---:|---:|
| 4 | 15 | 4 | 1.0000 |
| 8 | 208 | 8 | 1.0000 |
| 16 | 39,648 | 16 | 1.0000 |
| 32 | 1,439,975,216 | 31 | 0.9688 |
| 64 | 1,899,425,365,020,742,591 | 61 | 0.9531 |

The asymptotic information rate therefore remains linear in temporal horizon even though one *current* growth projection is constant-state.

## Collatz

The finite parity coordinate `Q_k` is bijective modulo `2^k`.  Exact future parity observers therefore have no nontrivial universal quotient:

| horizon k | exact future words | required bits |
|---:|---:|---:|
| 4 | 16 | 4 |
| 8 | 256 | 8 |
| 12 | 4,096 | 12 |
| 16 | 65,536 | 16 |

This is an information lower bound, not a weakness of the radix-4 sentinel implementation: the sentinel quotient makes each *next* valuation/phase projection cheap, but arbitrary future parity data still carries one independent bit per normalized step.

## Prime congruence observers

A single odd divisor lane has exactly `q` Moore classes under candidate translation by `+2`; the residue coordinate is already minimal.  Raw wheel products are also unminimized:

| observer | source states | minimal classes |
|---|---:|---:|
| `prime-lane-3` | 3 | 3 |
| `prime-lane-5` | 5 | 5 |
| `prime-lane-7` | 7 | 7 |
| `prime-lane-11` | 11 | 11 |
| `prime-lane-31` | 31 | 31 |
| `prime-wheel-3x5` | 15 | 15 |
| `prime-wheel-3x5x7` | 105 | 105 |
| `prime-wheel-3x5x7x11` | 1,155 | 1,155 |

Hence CRT/factored congruence is not optional bookkeeping: it is the compact representation of an otherwise product-sized exact observer.  The residual-divisor interval morphism remains the path that avoids expanding that universal wheel for block summaries.

## Fermat squaring observer

For prime Fermat moduli F0..F4, the full residue state collapses to `2^n+1` future `x==-1` classes:

| term | residues | observer classes | residue bits | observer bits | Pepin squarings |
|---|---:|---:|---:|---:|---:|
| F0 | 3 | 2 | 2 | 1 | 0 |
| F1 | 5 | 3 | 3 | 2 | 1 |
| F2 | 17 | 5 | 5 | 3 | 3 |
| F3 | 257 | 9 | 9 | 4 | 7 |
| F4 | 65,537 | 17 | 17 | 5 | 15 |

In a prime Fermat field this class is the 2-adic valuation of the multiplicative-group exponent (plus one never-hit sink).  The class itself is tiny; extracting it from an arbitrary residue without already knowing order/factor information remains the hard projection.

## Mersenne / Lucas--Lehmer observer

For prime Mersenne moduli the exact `x -> x^2-2`, `x==0` observer has exactly p classes.  Composite M11 collapses differently and the initial state falls into the never-zero sink:

| exponent | residues | observer classes | observer bits | initial class |
|---:|---:|---:|---:|---:|
| 3 | 7 | 3 | 2 | 2 |
| 5 | 31 | 5 | 3 | 2 |
| 7 | 127 | 7 | 3 | 2 |
| 11 | 2,047 | 3 | 2 | 1 |
| 13 | 8,191 | 13 | 4 | 2 |

The quadratic-unit conjugacy explains the prime case: the projection observer is an exponent-doubling depth class.  Again, observer state is logarithmic in modulus bitlength while extracting the class is not yet sublinear.

## Production short-circuit from digit evolution

The existing factored radix-word observer is now allowed to terminate special-number compilation before the longer modular recurrence when it proves a proper factor:

- F5: factor **641**, skips **31** Pepin squarings and the duplicate digit-square path.
- M11: factor **23**, skips **9** Lucas--Lehmer iterations.
- M23: factor **47**, skips **21** Lucas--Lehmer iterations.
- M31 has no bounded factor witness and therefore correctly falls through to Lucas--Lehmer.

The important boundary is now explicit: projection observers can be dramatically smaller than arithmetic states, but the compiler only gains asymptotically when the observer class can itself be synthesized from the digit/factor coordinate before running the long evolution.
