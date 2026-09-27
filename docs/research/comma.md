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
- **Replacement proof target:** prove the executable boundary macro, its
  periodic lifting, the complete finite losing/winning classification, and the
  repeating source-20 path. The forest remains the current admission route until
  this replacement and its weighted scheduler consumers pass. Completing the
  forest parser proof is no longer the cutover objective.

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
[Comma_Root_Forest](../../devtools/proofs/isabelle/comma_legacy/Comma_Root_Forest.thy)
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
Successful admission records `runtime_verified=true` and
`isabelle_instance_checked=false`. Certificate information is a read-only
snapshot: requesting it alone performs no asset verification and reports
`runtime_verified=false`. Reporting available evidence does not authorize a
value request.
A checksum authenticates the artifact; the complete child-closure checks
supply its finite-termination argument. Missing or forged records are rejected.

Beyond the first fork, a discarded branch needs a complete finite termination
certificate. Only the common prefix of all surviving candidate paths is
certified by this method. [Published branch-pruning method](https://oeis.org/A399179/a399179.txt)

**Research only:** `(p mod 924,f,s)` and the proposed 314-fork period are not
proved right-congruences. A surviving abstract SCC cannot establish a concrete
infinite path without a lifting theorem preserving every child alternative.

## Boundary quotient and weighted returns

The replacement candidate uses `Q=(N/Z,a,p mod 924)`, where
`N(a,p)=a*10^p-1`, `Z(a,p)=a*10^p`, `2<=a<=9` and `p>=5`.
The concrete exponent remains part of the source occurrence.

- **Exact arithmetic construction:** a macro terminates at the next fork or
  landmine. Its weight is `(A*10^p+B)/D`; it excludes the next fork-choice tick.
  Both children remain in its output. Selecting an infinite child is a separate
  obligation, even when that child is the smaller one.
- **Executable lifting checks:** every affine sector and guard inequality must
  hold on the entire exponent ray. The period of `10^p mod P` alone is
  insufficient. The [development checker](../../devtools/experiments/comma/macro_lifting.py)
  checks these inequalities, fixed floor remainders, complete alternatives and
  the weighted index used for partial selection.
- **Weighted composition:** a return with exponent gain `delta` transports the
  next coefficient by `10^delta`. Repetition gives an exact geometric sum;
  capped evaluation can compare it with a requested term index without expanding
  the sum. Capped binary descent selects a complete repetition prefix and a
  residual literal offset, including negative affine offsets. This arithmetic
  law does not prove that a return is source-admitted.
- **Production local integration:** production and the boundary constructor use
  one tropical child classifier in the arithmetic owner for exponents at least
  two. The nine-candidate search remains only for small startup values. Tests
  retain an independent literal child enumerator.
- **Checked local theorems:** the
  [complete child classification](../../devtools/proofs/isabelle/comma/Comma_Child_Classification.thy)
  proves both candidate directions for every decimal sector at exponent at least
  two. The finite-period theory proves the 17 displacement catalog; the
  power-residue theory proves the 924-period modular law, and the affine-ray
  theory proves transport of sign guards. These
  statements establish local arithmetic, not the full macro checker.
- **Checked conditional constructor:** a successful HOL macro run from an
  admitted sector has an exact literal path with `weight=initial_weight+steps`,
  the correct terminal chart and the complete ordered child set. This is an
  induction over the executable constructor, not merely a composition law.
  [Exact weighted refinement](../../devtools/proofs/isabelle/comma_scalar/Comma_Weighted_Macro.thy)
- **Checked conditional selection:** the canonical weighted chart and binary
  prefix selector refine every partial literal prefix of a successful trace,
  using the cycle-count/remainder expression for Entry fragments.
  [Whole-macro selection](../../devtools/proofs/isabelle/comma_literal/Comma_Macro_Selection.thy)
- **Formal frontier:** discharge successful evaluation for every admitted
  boundary state. Only then instantiate the kernel-checked
  losing-rank/winning-cycle proof from that same constructor.
  The Python ray checker is an independent oracle, not a theorem premise. The
  [boundary theory](../../devtools/proofs/isabelle/comma/Comma_Boundary_Quotient.thy)
  develops the seam and modular ingredients; it does not certify the complete
  constructor or authorize removing production forest admission.

The canonical weighted chart emits an exact affine weight on every move;
finite control is its weight-erasing projection. An
`Entry(f,delta,x)` represents `f*10^(p+delta)+x`; a `Near(f,delta,H)` represents
`(f+1)*10^(p+delta)-H`. The entry reduction retains the exact remainder

\[
H=1+e+((10^{p+\delta}-x-1-e)\bmod P),\qquad e=[f<9].
\]

The exact starts are `N(a,p) ↦ Near(a−1,0,1)` and
`Z(a,p) ↦ Entry(a,0,0)`. Starting N directly at `Entry(a,0,a+89)`
omits one literal edge. The checked 92-position Entry trace is therefore a
suffix of the 93-position N-boundary trace.

The [chart owner](../../src/number_compiler/sequences/comma/boundary_chart.py)
drives both weighted construction and finite rank-data generation; the macro
builder consumes its emitted weights rather than deriving a second weight rule. Branch
control uses modular powers without constructing a representative decimal
endpoint. Weighted results retain the terminal chart, so exact landmine
headroom is available. Erasing weights must preserve the finite outcome;
this alone does not prove literal refinement, totality or infinite safety.

**Checked round weights.** The
[weighted-prefix theorem](../../devtools/proofs/isabelle/comma_round_weights/Comma_Round_Weights.thy)
separates chart operations from literal transitions. Given an admitted source,
exponent `p ≥ 5` and `r mod 924 = p mod 924`, its emitted weight is the length
of a literal comma path. A decimal crossing adds one transition; inspecting a
fork or landmine adds none. Constructor ranks count control rounds, not these
literal weights, and do not establish that a fork child survives forever.

**Chart-local headroom is not a transition count.** For a fixed-sector Near
run from headroom `h` to `t`, every internal edge decreases headroom. Its
signed displacement and minimum prefix displacement are both `t−h`; its
literal weight is the separate internal-edge count `n`. A prefix labelled
by `n` copies of `−1` only proves an operation-count bound.

That headroom effect cannot be added across sectors without transport. With
scale `X=10^(p+delta)` and a crossing increment `I`, the new chart satisfies
`X'=10^[f=9] X` and `H'=H−I+X'`. For example, `199991 → 200003` changes
headroom from 9 to 99997, not −3. Positive headroom alone also fails to prove
unique continuation: 199918 has two children. These are counterexamples to
the omitted-rebase and weakened-guard summaries, not to the full cylinder.
[Independent chart regressions](../../tests/sequences/comma/test_boundary_chart.py)
check the exact canonical moves against literal child enumeration.

The checked [chart-action theory](../../devtools/proofs/isabelle/comma_chart_action/Comma_Chart_Action.thy)
represents `(X,H) ↦ (lambda*X,H+a*X+b)` using the shared skew algebra.
It transports affine guards contravariantly, preserving comparison relations,
event decorations and chronological order. Its canonical transition lemmas
derive the source digit from the actual chart. They do not grant admission to
an arbitrary supplied digit or erase exponent/weight occurrence data.
The checked [weighted-round constructor](../../devtools/proofs/isabelle/comma_weighted_round/Comma_Weighted_Round.thy)
composes these germs to the first decisive event and retains at most nine
Entry weight pieces. At an admitted exponent of at least five, matching
phase yields an exact literal path. Its counted terminal observation is a
definitional projection with checked composition rules. Finite rank instances
can evaluate that projection without rebuilding exact weights and guards for
each source; the generic weighted refinement remains required. Whole-round guard reduction across
different sources remains a separate obligation.

The cutover order is therefore: exact local run, chart transport and ordered
guards, executable weighted round, decade totality, boundary losing/winning
classification, then the infinite return and weighted scheduler consumer.
The 84,084-state constructor rank and the 14,784-state future-safety rank
answer different questions. Neither a control-only round nor guard truth at
one bound source establishes admission equivalence for another source.
The checked `comma_boundary_macro_exists` theorem now connects a decreasing
decade rank to successful boundary construction. Uniqueness makes the macro
independent of the particular successful fuel value; the concrete rank remains
an obligation. This semantic definition alone is not an executable constructor.
Keep the source sector and digit fiber in admission: `(X,H)` alone does not
identify them. A tropical minimum may replace guards only after a separate
equivalence theorem preserves strictness, equality and event identity.

**Checked control normalization.** `comma_normalized_step_commutes` in
[the finite transition theory](../../devtools/proofs/isabelle/comma_cutover/Comma_Finite_Transition.thy)
proves that replacing the chart's absolute gain by `(residue+delta) mod 924`
commutes with one canonical control move, including terminal outcomes.
This observation forgets exponent gain: weighted application must retain it
separately. It is not a termination or infinite-path theorem.

The named theorem `comma_decade_state_future_congruent` in
[the decade-control theory](../../devtools/proofs/isabelle/comma_decade/Comma_Decade_Control.thy)
lifts this erasure to an entire round from an Entry-1 occurrence. Its result
observes terminal residue phase and normalized crossing state. Raw fork gains
0 and 924 are different, even when these observations agree; weights, absolute
endpoints and scheduler authority are not identified by the theorem.

**Implemented construction and checked local theorem.** For each
catalog displacement `P`, the eventual power period `T(P)` lies in
`{1,2,3,6,22,28}` and divides 924. The finite Entry evaluator uses

\[
10^{5+((r+919)\bmod T(P))}\bmod P,
\qquad r=(p+\delta)\bmod924,
\]

whose exponent is at most 32. The theorem
[`comma_power_residue_correct`](../../devtools/proofs/isabelle/comma/Comma_Power_Residue.thy)
proves equality to `10^(p+delta) mod P` for every admitted exponent.
Finite residue tests are separate from that kernel-checked theorem. Making
Entry inexpensive does not prove that every boundary macro terminates: the
total constructor theorem must remove the successful-run premise before
ranked termination or infinite continuation can authorize branch pruning.
The checked [short-phase transport](../../devtools/proofs/isabelle/comma_short_phase/Comma_Short_Phase.thy)
permits Entry arithmetic reuse at phase `(r+delta) mod T(P)`, with the output
gain restored by the transport. The power lookup itself uses the rotated index
`(r+delta+919) mod T(P)`. There are 116 power observations; the finite catalog
contains 7,019 Entry classes for offsets 0–98, while decade starts use 0–90.
Neither catalog size proves the full rank instance or its verification cost.
Construction and formal-validation evidence belongs in the
[weekly chart-unification record](../../results/current/2026-W39/README.md#comma-chart-unification).

Constructor measurements and the cutover disposition are recorded in the
[weekly boundary-quotient work](../../results/current/2026-W39/README.md#comma-boundary-quotient).

## First-fork index discrepancy

The published first-fork value is `19999999918`, with children `19999999999`
and `20000000000`. The paper/OEIS gives index **412987860**. Our guarded
constructors and a separate literal C enumerator, initialized explicitly at
`k=20,n=1`, reach it at **412987859**. This is a disagreement with the published
anchor, not a convention change. The preceding value is checked in the
arithmetic tests; no later branch is chosen by a fixture.
The checked theorem `comma_source20_to_fork` in
[the source-entry theory](../../devtools/proofs/isabelle/comma_entry/Comma_Source_Entry.thy)
now establishes a literal path of exactly 412,987,858 transitions from 20 to
that value, and `comma_source20_first_fork_children` proves the complete child
set. The separate theorem `comma_source20_to_fork_unique` in
[the uniqueness theory](../../devtools/proofs/isabelle/comma_unique/Comma_Source_Unique.thy)
proves that every preceding transition has exactly one child. These finite
prefix results do not establish an infinite continuation after the fork.
The first excluded child is `20000000000`; its complete finite forest forces
the other child, `19999999999`, at index 412987860. That agrees with the first
decision in [A399179](https://oeis.org/A399179). The other 29 published decisions
do not automatically extend the admitted production boundary.

Reproduction and frozen measurements belong in the
[weekly implementation record](../../results/current/2026-W39/README.md#a367620-integration).
Public acceptance, finite arithmetic, certificate soundness and performance
remain separate gates.
