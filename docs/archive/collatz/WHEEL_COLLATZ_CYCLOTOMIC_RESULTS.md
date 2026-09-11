# Wheel-cyclotomic / self-branching Collatz results — v0.29.0

## Prime wheel as a cyclotomic field automaton

Each finite divisor cycle `j == phase (mod q)` is represented by a root-of-unity projection. Several squarefree periods are packed into one field `F_P` with `prod(q) | P-1`; one live state `a^j` advances by multiplication and projects to every constituent q-th root subgroup. No prime bitmap or Boolean output jet is part of this automaton.

| candidates | lanes | packed groups | packed state bits | cyclotomic groups | cyclotomic state bits | cyclotomic descriptor bits | charged packed | charged cyclotomic | selected |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 64 | 54 | 78 | 4,454 | 8 | 425 | 1,951 | 8,908 | 2,376 | cyclotomic |
| 256 | 150 | 78 | 4,454 | 25 | 1,394 | 6,690 | 8,908 | 8,084 | cyclotomic |
| 1,024 | 317 | 78 | 4,454 | 57 | 3,276 | 16,281 | 8,908 | 19,557 | packed |
| 4,096 | 446 | 78 | 4,466 | 84 | 4,850 | 24,455 | 8,932 | 29,305 | packed |

The field coordinate is therefore a real block-specific random-access alternative, not a replacement theorem for the residual-divisor block projector. The compiler selects it only when state+descriptor charge beats the packed carrier; larger blocks currently cross back to the packed representation.

## Collatz successor manufactures its own branch

All **4,096/4,096** physical successors are exact in the shared cyclotomic digit layer (2,048 even, 2,048 odd). Even is `z^-1`; odd is `(1+z)D+1` followed by canonical binary normalization. No parity/valuation itinerary is an input to the operator.

The normalized successor still does not descend to one small current cyclotomic component. Bounded closure audit:

| components | classes / 4096 | successor conflicts | next-closed | non-injective |
|---|---:|---:|---|---|
| Phi_4 mod 32 + parity | 84 | 1,888 | False | True |
| Phi_8 mod 32 + parity | 384 | 1,835 | False | True |
| Phi_16 mod 32 + parity | 1729 | 1,430 | False | True |
| Phi_5,Phi_7 mod 32 + parity | 4096 | 0 | True | False |

`Phi_5 + Phi_7` is conflict-free only because it is injective on this bounded source set; it is explicitly rejected as a state reduction. The useful architectural gain is that branch generation and cyclotomic transport are now one operator, so the remaining Collatz theorem is precisely a non-injective normalized quotient of that operator—not an unknown parity-word generator.
