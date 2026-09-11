# Saturated two-power cyclotomic terminal audit

For the shortened terminal conductor `s=2^v`, classical cyclotomic-extension
existence is exactly the special-number all-local congruence.  Fermat has
`ord_s(N)=1`, hence every factor must be `1 mod s`; Mersenne has
`ord_s(N)=2`, hence every factor must be `+/-1 mod s`.  At the current
square-root/CRT decision thresholds those conditions are equivalent to primality.

| family | parameter | v | degree | local residues | extension exists |
|---|---:|---:|---:|---|---|
| fermat | 4 | 8 | 1 | `(1,)` | True |
| fermat | 5 | 16 | 1 | `(641, 15745)` | False |
| mersenne | 11 | 4 | 2 | `(7, 9)` | False |
| mersenne | 13 | 5 | 2 | `(31,)` | True |

## Constructor boundary

The low extension degree does not supply the missing candidate state.  In
the Fermat degree-one case the orbit polynomial is `X-zeta`, so its
coefficient is the primitive `2^v` root itself.  In the Mersenne degree-two
case it is `X^2-TX+1`, where `T=zeta+zeta^-1` is exactly the missing
norm-one Lucas trace.  Constructing these from the fixed special generators
and proving exact order consumes the classical sequential squaring chain:

| family | parameter | build | verify | total | classical |
|---|---:|---:|---:|---:|---:|
| fermat | 4 | 8 | 7 | 15 | 15 |
| fermat | 16 | 32768 | 32767 | 65535 | 65535 |
| mersenne | 13 | 8 | 4 | 12 | 12 |
| mersenne | 10007 | 5016 | 4990 | 10006 | 10006 |

Therefore saturated/cyclotomic-extension existence is an exact semantic
reformulation of the desired theorem, but not a new source extractor.  It
cannot be promoted to production without an independent compact constructor
for the primitive root (Fermat) or its trace (Mersenne).
