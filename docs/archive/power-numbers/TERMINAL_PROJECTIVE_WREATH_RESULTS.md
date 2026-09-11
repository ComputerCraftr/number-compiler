# Terminal projective-Cayley / Frobenius-wreath research

The nonlinear projective quotient is exact:

```text
t=(x-2)/(x+2)=A/B
(A:B) -> (4AB:(A+B)^2)
S=A+B, D=B-A -> (2S^2-D^2, D^2)
```

Thus `D` is a known dyadic square clock.  This representation is division-free and any target/nonunit packet can be exposed by gcds, but the simple projective target gcd does not by itself classify the composite controls.

## Exact local wreath section

For local stride `k`, Frobenius is the binary odometer:

```text
tau_(2a)   = (tau_a,tau_a)
tau_(2a+1) = (tau_a,tau_(a+1)) sigma
```

When the current lift passes (`k` even), the conditional section is exactly `k/2`, the stride at the doubled boundary.  Hence `Section(Frob_m)=Frob_(2m)` is proved locally without materializing the tree.

| family | parameter | q | start | span | root | next section | direct next | exact | all pass |
|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| fermat | 4 | 65537 | 2 | 2 | 0 | 512 | 512 | True | True |
| fermat | 5 | 641 | 2 | 9 | 1 | None | None | True | False |
| fermat | 5 | 6700417 | 2 | 9 | 1 | None | None | True | False |
| mersenne | 13 | 8191 | 1 | 3 | 0 | 1024 | 1024 | True | True |
| mersenne | 11 | 23 | 1 | 2 | None | None | None | True | False |
| mersenne | 11 | 89 | 1 | 2 | None | None | None | True | False |

## Boundary

The section *law* is closed; the candidate-derived section constructor is not.  The unfactored production candidate still does not supply the local odometer section, so no production selector is promoted.  The next theorem is now specifically to realize this conditional section in the sparse principal quotient with unit normalization / natural gcd emission.

## Shared binary piecewise cleanup

The control skeleton is now production-shared with Collatz.  The new
`number_compiler.binary_piecewise` module owns the one canonical decision
lattice

```text
ZERO | ONE | SPLIT(g) | UNKNOWN
```

and dispatches exactly one branch.  `CollatzPiecewiseMorphism` derives ZERO/ONE
from the current formula LSB.  `SpecialFrobeniusSectionMorphism` uses the same
handler with

```text
ZERO -> conditional section at the doubled boundary
ONE  -> terminal FAIL
SPLIT(g) -> terminal SPLIT
UNKNOWN -> fail closed
```

The Frobenius controller never accepts a supplied `k & 1`.  Its production
root-action probe remains `UNKNOWN` until the sparse candidate itself provides
the root permutation.
