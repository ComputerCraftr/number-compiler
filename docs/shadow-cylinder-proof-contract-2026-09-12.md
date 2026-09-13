# Shadow-cylinder proof target and withdrawn counterexamples

Release remains **BLOCKED (P0)**. The carry-only Collatz and mirror-only 196
examples were the wrong target for the requested powered construction. Their
new theories and regression file have been removed. Neither those examples nor
nonclosure of the supplied quadratic-root set disproves the common
source-sensitive shadow-cylinder morphism.

## The contract to prove

Keep the canonical cylinder action `A` separate from its admitted source
occurrence `O`. Carry geometry, skew/S-arithmetic evaluations, Hensel cylinders,
twisted sheets, tropical values and factors are demanded views of the action.
They must not become a Cartesian tuple used to reconstruct its source identity.
Source and target boundaries, width and admission remain part of the binding
contract wherever the action needs them.

For the concrete production constructor `compile`, normalizer `NF`, action
composition and observer pullback, the obligations are:

```
eval(O, pullback(compile(n), D)) = D(T^n(O))
eval(O, pullback(NF(A), D)) = eval(O, pullback(A, D))
pullback(B o A, D) = pullback(A, pullback(B, D))
```

The last equality is semantic equality on admitted bindings; it need not mean
syntactically identical expressions. Composition must preserve the intermediate
source/target admission and the demanded physical duration. In Collatz,
accelerated event count and physical tick count are different clocks.

These statements must use executable production definitions. Defining
`compile(n)` as the exact endpoint or assuming the first equality inside a
locale does not discharge the constructor obligation. A correct but expensive
constructor still has to pass the unchanged cold-work and retention gates.

An exact counterexample must identify an admitted binding and demand for which
one of these laws fails, or show two allegedly equivalent actions disagree
under the same admitted binding and demand. Different outputs on different
source occurrences are permitted. Equality of one derived carry map, mirror
sheet or primary jet is not equality of the common morphism.

## Audited production and proof boundaries

| Route | Present implementation | Missing acceptance evidence |
| --- | --- | --- |
| Physical Collatz | `PoweredCollatzTerm` compiles the binary effect into the source-bound `HashLifeBlockIndex` tile route | Normalized shadow-cylinder constructor and its refinement to physical output, including source-dependent event discovery and partial-block timing |
| Collatz observer CLI | `observe_collatz` discovers a finite accelerated prefix, then folds `CollatzEventArena` using demanded skew/S-arithmetic, Hensel or tropical views | Connection of these views to the same powered physical constructor without rediscovering its events sequentially |
| 196 | `ReverseAddPoweredTerm` powers the block effect; positive-generation mirror queries fold a completed target DAG | Source-sensitive publisher/pullback construction, carry and growth seam refinement, and cold construction bound |
| Fermat/Mersenne root observer | `observe_etale_root` accepts a supplied checked defect and observes one `ArithmeticTile` square/trace-square | Candidate/source-clock terminal construction and agreement with the CLI's decision/factor consumer |

`Skew_Cylinder_Observers.thy` proves the chronological skew law and
homomorphic observer composition. `Runtime_Cylinder_Refinement.thy` and
`Cylinder_Vector_Refinement.thy` prove further concrete observer algebra.
`Temporal_Clock_Jumps.thy` proves quotient powering under its successor
congruence premise. These are valid component theorems. No inspected theorem
instantiates the complete production constructor contract above for all four
families.

The missing object is a concrete canonical action/pullback implementation and
its refinement, not a record bundling the separately evaluated shadows. The
absence of a class literally named `ShadowCylinder` would not itself be a
failure: the audited failure is the absent constructor-to-CLI/proof connection.

## Validation disposition

After removing the misdirected development, `Etale_Primary_Carry` builds with
`quick_and_dirty=false` and the existing oracle-dependency checks. This restores
the component session; it neither proves nor refutes the full powered contract.
The prior failed/timed-out performance records remain failures. Conditional
proper-factor printing remains accepted and does not waive any constructor gate.

See the [P0 ledger](cylinder-p0-release-gates-2026-09-12.md) and the earlier
[constructor audit](constructor-quotient-proof-audit.md), which already explained
why carry readouts cannot replace the source-sensitive cylinder proof target.
