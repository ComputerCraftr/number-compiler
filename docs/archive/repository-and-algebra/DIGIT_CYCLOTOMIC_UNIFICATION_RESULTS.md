# Unified source-digit cyclotomic algebra (v0.43.0 cleanup refresh)

The cyclotomic algebra now sits below projection/carry instrumentation. `CyclotomicDigitBlock`
is the one canonical implementation for source digits, output jets, and quotient blocks, so
actual digit/pair fields no longer have fragmented quotient arithmetic.

One canonical digit/cyclotomic block, legacy aliases absent: **True**.
Cross-family exactness audit: **True**.

## Normalization is the shared `base-z` morphism

For `A-D=(base-z)Q+boundary`, a component can reconstruct its carry residue whenever
`base-z` is a unit.  Equivalently the quotient divisor evaluated at `base` is invertible
in the coefficient modulus.  Over `mod 32`:

| radix | unit orders | singular orders |
|---:|---|---|
| 2 | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 | - |
| 3 | 3,5,6,7,9,10,11,12,13,14,15 | 1,2,4,8,16 |
| 4 | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 | - |
| 10 | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 | - |
| 16 | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 | - |

Every tested channel for the even radices 2/4/10/16 is a 2-adic unit.  Ternary is different:
its power-of-two cyclotomic orders are singular.  Thus binary Collatz makes the 2-adic
carry spectrum entirely derived from source/raw/normalized digit components, while ternary
can retain genuine normalization-kernel information in those channels.

## Exact cross-family adapter audit

| family | cases | components | exact | unit normalizations | carries recovered |
|---|---:|---:|---:|---:|---:|
| reverse-add | 64 | 512 | 512 | 512 | 512 |
| collatz | 205 | 1640 | 1640 | 1435 | 1435 |
| mersenne | 127 | 381 | 381 | 381 | 381 |
| fermat | 17 | 85 | 85 | 85 | 85 |

The adapters exercise actual reverse-add digit reflection/pairing, radix-polynomial Collatz
`3n+1`, Lucas-Lehmer cyclic square/add, and Pepin negacyclic squaring through the same block.

## Carry dependency on long real trajectories

| family | radix | steps | orders | components | unit | recovered |
|---|---:|---:|---:|---:|---:|---:|
| reverse-add | 10 | 256 | 16 | 4096 | 4096 | 4096 |
| collatz | 2 | 41 | 16 | 656 | 656 | 656 |
| collatz | 3 | 41 | 16 | 656 | 451 | 451 |

For reverse-add 196/base-10 and binary Collatz, all tested `mod 32` carry components are
algebraically reconstructed.  They must therefore not be retained as independent cyclotomic
observer state.  Ternary Collatz intentionally shows the singular exception.

## Deeper finite-field cyclotomic factors

A whole `Phi_m mod p` block now splits lazily into irreducible factors and reconstructs exactly
by polynomial CRT.  This exposes much smaller primary components:

| family | parameter | p | order | whole degree | factors | factor degree |
|---|---:|---:|---:|---:|---:|---:|
| mersenne | 7 | 2 | 7 | 6 | 2 | 3 |
| mersenne | 17 | 2 | 17 | 16 | 2 | 8 |
| mersenne | 23 | 2 | 23 | 22 | 2 | 11 |
| mersenne | 31 | 2 | 31 | 30 | 6 | 5 |
| fermat | 2 | 3 | 8 | 4 | 2 | 2 |
| fermat | 3 | 3 | 16 | 8 | 2 | 4 |
| fermat | 5 | 3 | 64 | 32 | 2 | 16 |
| fermat | 5 | 7 | 64 | 32 | 4 | 8 |

In particular `Phi_31 mod 2` is **6 degree-5 factors**, rather than one opaque degree-30 block.

## Normalization can couple primary factors back together

| family | parameter | p | selected factors | classes | conflicts | target separating |
|---|---:|---:|---|---:|---:|---:|
| mersenne | 7 | 2 | 0 | 8 | 108 | False |
| mersenne | 7 | 2 | 1 | 8 | 106 | False |
| mersenne | 7 | 2 | 0,1 | 64 | 0 | True |
| fermat | 3 | 3 | 0 | 64 | 192 | False |
| fermat | 3 | 3 | 1 | 64 | 192 | False |
| fermat | 3 | 3 | 0,1 | 257 | 0 | True |

M7 is the clean warning: each degree-3 factor has only 8 states but fails successor closure;
both factors together give the exact 64-class sign quotient.  F3 over `F_3` is harsher:
each degree-4 factor fails, while both together reconstruct all 257 integer states.  Finite
factorization is therefore a discovery/quotient tool, not automatic dynamical independence.

## Architectural consequence

The search order is now `source digits -> cyclotomic primary components -> raw operator ->
normalization morphism -> target/next closure`.  Carry factors are synthesized from this path
when invertible; separate carry-cyclotomic state is forbidden unless the normalization map is
singular and an exact observer theorem requires its kernel/cokernel information.
