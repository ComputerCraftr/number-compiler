# Cross-family canonical sequence compiler results

The suite uses the production `CanonicalSequenceCompiler`; benchmark/test helpers are not imported by it.

## Reverse-and-add seed/base matrix

Compiled 54 exact 24-step orbits: seeds [1, 89, 195, 196, 197, 4994], bases [2, 3, 4, 5, 7, 8, 10, 12, 16].
Live carry suffix average range: 4.769..9.800 rows.
Live carry suffix maximum across the matrix: 11 rows.
Charged live/fixed-H carry-bit ratio range: 0.3891..0.6695.
Exact current-growth observer class range: 11..25 classes; maximum charged observer size 13 bits versus reset-signature 101 bits.

## Collatz raw-field theorem interface

Every Collatz compilation now carries one fixed radix-4 sentinel theorem summary as derived metadata.
It synthesizes accelerated valuation and growth/nonincrease phase from the digit word and charges only
first-hole checks plus residual target-digit work; source/raw/normalized/carry vectors are not retained.
The retained accelerated projection sees at most 5 distinct valuation-action states in this suite, with maximum charged state size 3 bits; the explicit valuation symbol itinerary is an on-demand view only.

| seed | odd symbols | valuation sum | digit checks | stripped digits | residual digits | scalar carry peak |
|---:|---:|---:|---:|---:|---:|---:|
| 97 | 43 | 75 | 65 | 23 | 167 | 2 |
| 27 | 41 | 70 | 61 | 21 | 159 | 2 |
| 7 | 5 | 11 | 8 | 4 | 7 | 1 |
| 3 | 2 | 5 | 3 | 2 | 1 | 1 |
| 1 | 0 | 0 | 0 | 0 | 0 | 0 |

## Special binary families

Fermat radix programs have at most three runs; Mersenne radix programs have one run.  Their retained radix descriptions therefore grow logarithmically in represented bit length.  The factored digit observer now short-circuits a long primality projection when it already proves a proper factor; otherwise Pepin/Lucas-Lehmer iteration counts remain separately charged.
After a prime projection succeeds in the bounded theorem range, the modular residue is replaced by the exact closed order-depth Moore state; failed/composite projections do not receive that prime-group state.

| family term | represented bits | radix runs | radix description bits | primality iterations |
|---|---:|---:|---:|---:|
| F_5 | 2**5+1 | 3 | 20 | — |
| F_8 | 2**8+1 | 3 | 21 | — |
| F_12 | 2**12+1 | 3 | 21 | — |
| M_31 | 31 | 1 | 7 | — |
| M_127 | 127 | 1 | 9 | — |
| M_8191 | 8191 | 1 | 15 | — |

## Prime block projection

The production block projector is now the residual-divisor set morphism.  The packed-hyperbolic and floor-quotient implementations are independent benchmark/differential paths rather than duplicate retained compiler state.

| candidates | residual interfaces | arithmetic transforms | cached transforms | radix work | packed cofactor points | quotient states | quotient updates |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 64 | 13 | 214 | 51 | 265 | 115 | 6323 | 980561 |
| 256 | 37 | 758 | 310 | 1068 | 473 | 6323 | 1225703 |
| 1024 | 66 | 3005 | 1055 | 4060 | 1893 | 6324 | 1470866 |
| 4096 | 192 | 9602 | 5078 | 14680 | 7562 | 6326 | 1716105 |

## Bound status

* Fermat/Mersenne **radix generation/projection** is sublinear in represented digit length because the exact binary words are canonical RLE programs.
* Fermat Pepin and Mersenne Lucas-Lehmer **primality projection** remains linear in represented bit length/iteration count in this implementation.
* Prime floor-quotient summary is sublinear in block length for fixed magnitude, but remains O(sqrt(n)) in magnitude.
* The retained prime residual-divisor projector reuses exact single-lane radix morphisms before interface construction.  Transform work is sublinear-looking in the measured block window, while retained decision description remains roughly linear; this is not a universal sublinear theorem.
* Reverse-add current growth no longer retains a linear growth itinerary: it is emitted from the logarithmic boundary valuation/sign observer already present in the canonical summary.  That observer is not successor-closed, so the full-J blocker remains the reduced-state successor, not current growth extraction.
* Collatz no longer retains the linear valuation-symbol itinerary beside the composed valuation slab.  A single `k=v2(3n+1)` is the exact accelerated action and cyclotomic shift phase, but `k_t` is not a closed orbit state.
* Fermat/Mersenne successful prime projections can discard the modular residue in favor of a logarithmic-size closed order-depth state; its one-time extraction is still charged and is not claimed asymptotically cheaper than the original recurrence.
