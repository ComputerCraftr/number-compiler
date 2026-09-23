# Decimal comma cylinders and A367620

- **Definition:** A367620 is the lexicographically earliest infinite path in the
  decimal comma-child graph, with OEIS index one at 20. A smallest-child rule
  alone does not define it. [OEIS definition](https://oeis.org/A367620)
- **Published mathematical result:** the comma-sequence paper identifies the
  infinite component rooted at 20 using finite-root coverage and computation of
  the other root trees. The outstanding repository gate is its executable
  formal refinement. [Primary paper](https://arxiv.org/html/2401.14346v2)
- **Implemented finite construction:** source-bound guarded phase-cycle actions
  use `TileScheduler`; near-boundary alternatives are enumerated exactly.
- **Runtime certificate:** the packaged finite-region forest excludes the 49
  other roots and the first fork's right child. Production streams and verifies
  every sector entry and outgoing alternative before admitting the prefix
  through index 412987860. Published branch bits are cross-checks, not selectors.
- **Checked theorem:** predecessor descent covers all positive integers by the
  classified 50 roots.
- **Open formal release obligation:** refine the executable certificate parser
  and checker, check the concrete instance in Isabelle and finish the
  infinite-path/prefix and scheduler cost chain. Runtime certificate admission
  does not claim that those proof gates are closed.

## Arithmetic and admission

Write `k=10m+d`. For each `e` from 1 through 9 there is a candidate
`k'=k+10d+e`; retain it exactly when its decimal leading digit is `e`.
Then

\[
d'=(d+e)\bmod10,\qquad m'=m+d+\lfloor(d+e)/10\rfloor.
\]

In a sector with constant leading digit `f`, the phase period is
`L=10/gcd(f,10)`. With `g=gcd(f,10)` and `r=d mod g`, its displacement is

\[
P=10\bigl(Lr+gL(L-1)/2\bigr)+Lf.
\]

**Conditional exact identity:** `t` complete cycles add `tP` and represent `tL`
transitions, provided every intermediate child remains inside the admitted
sector. The executable guard bounds all phase prefixes before the sector seam.
It clamps the admitted cycle count to zero near a boundary.
The implementation uses the shared `PrefixSafety(-P,-G)` action on headroom;
its `then`, `repeat` and first-failure operations transport the boundary guard.
The shared formal algebra is `prefix_safety_chronological` and
`repeated_prefix_minimum_closed` in
[Associated_Action_Pullback](../../devtools/proofs/isabelle/integration/Associated_Action_Pullback.thy).
This algebraic connection does not yet prove the Python constructor. Small values,
forks, missing children and power-of-ten crossings use literal child semantics.

The real decimal scale and term weight remain in occurrence/admission data.
An equal phase residue does not imply equal elapsed term count. Composition
retains chronological children for mixed actions; an admitted cycle power may
use its summed displacement directly. Endpoint demands reuse the resulting
image and do not reconstruct the orbit.

Implementation: [arithmetic](../../src/number_compiler/sequences/comma/arithmetic.py),
[source-image adapter](../../src/number_compiler/sequences/comma/power.py).
The finite owner intentionally does not assert OEIS membership.

## Certificates and proof scope

[Comma_Child_Cylinder](../../devtools/proofs/isabelle/comma/Comma_Child_Cylinder.thy)
models child, phase and interior-guard equations.
[Comma_Root_Forest](../../devtools/proofs/isabelle/comma/Comma_Root_Forest.thy)
states the root-exhaustion bridge: global finite-root coverage and finite
child-closed regions for all roots except 20 imply unbounded descendants of 20.
[Comma_Decimal_Parent](../../devtools/proofs/isabelle/comma/Comma_Decimal_Parent.thy)
checks the 50-root classification and establishes global root coverage by
predecessor descent. The concrete closed regions remain obligations; the
conditional finite-set argument is not checker refinement.

The development [forest checker](../../devtools/experiments/comma/forest_certificate.py)
uses exact integer sectors. Production imports no generator or fixture.
[Production admission](../../src/number_compiler/sequences/comma/certificates.py)
requires the independent streaming checker to exhaust the exact source forest.
It reports `runtime_verified=true` and `isabelle_instance_checked=false`.
A checksum authenticates the artifact; the complete child-closure checks
supply its finite-termination argument. Missing or forged records are rejected.

Beyond the first fork, a discarded branch needs a complete finite termination
certificate. Only the common prefix of all surviving candidate paths is
certified by this method. [Published branch-pruning method](https://oeis.org/A399179/a399179.txt)

**Research only:** `(p mod 924,f,s)` and the proposed 314-fork period are not
proved right-congruences. A surviving abstract SCC cannot establish a concrete
infinite path without a lifting theorem preserving every child alternative.

## First-fork index discrepancy

The published first-fork value is `19999999918`, with children `19999999999`
and `20000000000`. The paper/OEIS gives index **412987860**. Our guarded
constructors and a separate literal C enumerator, initialized explicitly at
`k=20,n=1`, reach it at **412987859**. This is a disagreement with the published
anchor, not a convention change. The preceding value is checked in the
arithmetic tests; no later branch is chosen by a fixture.
The first excluded child is `20000000000`; its complete finite forest forces
the other child, `19999999999`, at index 412987860. That agrees with the first
decision in [A399179](https://oeis.org/A399179). The other 29 published decisions
do not automatically extend the admitted production boundary.

Reproduction and frozen measurements belong in the
[weekly implementation record](../../results/current/2026-W39/README.md#a367620-integration).
Public acceptance, finite arithmetic, certificate soundness and performance
remain separate gates.
