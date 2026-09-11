# Terminal section-constructor frontier

The binary section law and its temporal powering are closed.  This pass
checks whether low-degree cyclotomic orbit polynomials or the high-2-adic
AKS/Berrizbeitia tradeoff supply the missing candidate-derived source.

## Orbit-polynomial section

| family | degree | current coordinate | section equation | new constructor? |
|---|---:|---|---|---|
| fermat | 1 | `zeta_v (primitive 2^v root in Z/NZ)` | `zeta_(v+1)^2 = zeta_v` | False |
| mersenne | 2 | `T_v = zeta_v + zeta_v^-1` | `T_(v+1)^2 = T_v + 2` | False |

Thus conductor doubling in the degree-1 Fermat representation is exactly
square-root extraction in `Z/NZ`; in the degree-2 Mersenne trace
representation it is exactly the half-angle square-root `U^2=T+2`.
The orbit polynomial is therefore an exact re-expression of the existing
quadratic-etale selector, not a new source projection.

## Fermat high-2-adic AKS/Berrizbeitia endpoint tradeoff

Write `F_n-1=2^K`, `K=2^n`.  Two exact endpoints are:

| n | endpoint | u | power squarings | log2 polynomial degree | compact? |
|---:|---|---:|---:|---:|---|
| 4 | small-polynomial | 1 | 15 | 8 | False |
| 4 | tautological-power-condition | 12 | 0 | 30 | False |
| 16 | small-polynomial | 1 | 65535 | 32 | False |
| 16 | tautological-power-condition | 65520 | 0 | 131070 | False |

At `u=1` the polynomial side is only `K^2` degree, but the prerequisite
power condition is the full Pepin-length `K-1` chain.  Choosing base 2
and `u=K-n` makes the power condition the defining identity
`2^(2^n)=-1 mod F_n`, but raises the polynomial degree to `2^(2K-2)`.
Neither endpoint is a bit-length-of-horizon section quotient.

## Remaining theorem

The surviving operation is still exactly:

```text
unfactored sparse special candidate
    -> candidate-derived ZERO / ONE / natural SPLIT
       for one quadratic-etale section equation
    -> shared binary section morphism
```

No production selector is promoted by this research result.
