# Terminal r-level Frobenius chunk quotient

The terminal lift language is now represented as one contiguous block rather than
one Kummer/Frobenius bit per level.  Locally, if `q=eps+m*k`, an `r`-level
chunk retains only `rho=k mod 2^r`; the folded coefficient of `X` is `+1`
exactly for `rho=0`.  No negacyclic polynomial is materialized.

## Factor-backed semantic audit

| family | parameter | q | span | reaches | rho | [X] | all pass |
|---|---:|---:|---:|---:|---:|---:|---:|
| fermat | 4 | 65537 | 2 | True | 0 | 1 | True |
| fermat | 5 | 641 | 9 | True | 5 | 0 | False |
| fermat | 5 | 6700417 | 9 | True | 123 | 0 | False |
| mersenne | 13 | 8191 | 3 | True | 0 | 1 | True |
| mersenne | 11 | 23 | 2 | False | None | None | False |
| mersenne | 11 | 89 | 2 | False | None | None | False |

Every row records `polynomial_terms_materialized=0` and `one_level_replays=0`.

## Composition audit

| family | parameter | q | split | combined rho | direct rho | exact |
|---|---:|---:|---|---:|---:|---:|
| fermat | 5 | 641 | 1+1 | None | 1 | True |
| fermat | 4 | 65537 | 1+1 | 0 | 0 | True |
| mersenne | 13 | 8191 | 1+2 | 0 | 0 | True |

## Final defect/gcd packet audit

| family | parameter | local defects | gcd | status |
|---|---:|---|---:|---|
| fermat | 4 | (0,) | 65537 | ALL_PASS |
| fermat | 5 | (-1, -1) | 1 | ALL_FAIL |
| mersenne | 13 | (0,) | 8191 | ALL_PASS |
| mersenne | 11 | (-1, -1) | 1 | ALL_FAIL |

After a folded-X defect is available, one `gcd(E,N)` is sufficient: full
modulus is ALL_PASS, one is ALL_FAIL, and a proper gcd is a natural SPLIT.
No scalar sign multiplication is used, so mixed local support cannot cancel.

## Production boundary

| family | parameter | span | required local v2 | status |
|---|---:|---:|---:|---|
| fermat | 4 | 2 | 8 | UNKNOWN |
| fermat | 5 | 9 | 16 | UNKNOWN |
| mersenne | 11 | 2 | 4 | UNKNOWN |
| mersenne | 13 | 3 | 5 | UNKNOWN |

Production now routes the terminal threshold through this chunk surface, but the
unfactored candidate-derived zero-class extractor is not proved.  Therefore all
nontrivial unresolved candidates remain `UNKNOWN` with zero polynomial terms, zero
one-level replays, zero raw Lucas squarings, and zero factor enumeration.

The remaining P0 is only the direct candidate computation of the folded `X`
coefficient / stride-zero class.  The local block quotient and its composition law
are closed.
