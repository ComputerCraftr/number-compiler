# Collatz raw-digit / sentinel quotient results

The decimal odd-step field `r_i = 3*d_i + [i=0]` is retained only as a redundant radix field;
normalised output digits and the ternary carry vector are derived on demand.  Decimal coefficients
therefore remain in `0..28`, but the compiler does not keep four parallel forms of the same integer.

## Sentinel theorem

For any radix `B == 1 (mod 3)`, `D=(B-1)/3` satisfies

```text
n = D*(1+B+...+B^(q-1)) + B^q*m
3*n+1 = B^q*(3*m+1).
```

Thus trailing sentinel digits can be deleted before multiplication.  For `B=4^k`, the residual
2-adic valuation is determined by the first non-sentinel digit alone.  Radix 4 is especially simple:
an odd LSD `3` means an increasing accelerated step (`v2=1`), while LSD `1` means `v2>=2` and
therefore a decreasing step except at the fixed point.

## Seed 27

| radix | sentinel | valuation digit checks | residual transform digits | bit-charged symbol volume | max live carry |
|---:|---:|---:|---:|---:|---:|
| 4 | 1 | 61 | 159 | 440 | 2 |
| 16 | 5 | 44 | 97 | 564 | 2 |
| 64 | 21 | 41 | 73 | 684 | 1 |
| 256 | 85 | 41 | 61 | 816 | 1 |

The symbol-count optimum shifts toward larger power-of-four radices, but once digit payload is charged
radix 4 is best among these four for seed 27 and for the aggregate release family.  The canonical compiler
therefore fixes the theorem coordinate at radix 4 rather than retaining a per-seed radix choice.

Aggregate charged symbol volumes across seeds 27/97/871/6171: `{'4': 3094, '16': 3824, '64': 4572, '256': 5320}`; selected radix: **4**.

## Carry monoid is synthesized, not retained

For radices 4, 10, 16, 64, and 256, deriving `floor((3*d+c)/B)` over the radix alphabet and closing
under composition yields the same **five** carry-transfer functions.  The compiler can regenerate this
constant monoid from the radix; it is not part of per-number semantic state.  In radix 4 the LSD itself
also synthesizes the accelerated phase: digit `3` means `v2=1`/growth, digit `1` starts the sentinel run
and therefore means `v2>=2`/nonincrease.

## RLE/SLP powering

A synthetic **2,000,001-digit** radix-16 word with one million sentinel `5`s on each side
is represented by **3 runs / 4 word nodes**.  Its first-hole
summary finds mismatch 1,000,000 and valuation 4,000,001
without expanding the run.  The sentinel query is therefore a genuine associative set/word morphism.

## Direct automaton powering is rejected

The exact radix-4 accelerated map minimizes to 10 subsequential states, but exact aligned composition
does not stay small:

| accelerated power | minimized states | description bits |
|---:|---:|---:|
| 1 | 10 | 317 |
| 2 | 70 | 3,189 |
| 3 | 448 | 25,156 |
| 4 | 2,761 | 196,105 |
| 5 | 16,747 | 1,434,376 |
| 6 | 100,906 | 9,748,624 |

So the one-step digit automaton is kept as a research differential, not as the powered production carrier.
The remaining Collatz powering problem is to quotient those residual transducer states by a stronger
domain/theorem interface rather than repeatedly composing the concrete automaton.

## Boolean formula embedding is rejected

| path | max FormulaArena nodes, seed 27 |
|---|---:|
| binary physical | 9897 |
| ternary physical | 3158 |
| senary physical | **2571** |
| radix-4 sentinel accelerated, naively re-embedded | 4804 |
| radix-16 sentinel accelerated, naively re-embedded | 8628 |

So the new quotient is kept as a native digit/run morphism.  Forcing it back through the older Boolean
formula representation loses the gain even though the arithmetic theorem is stronger.
