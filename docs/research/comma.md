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
The guard is the shared `PrefixSafety(-P,-G)` action on headroom. Production
evaluates its strict floor/clamp count directly after validating the phase
transfer; it no longer allocates an action to rediscover that count.
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

### Punctured decimal ports

- **Implemented local constructor:** the ordered root residual factors into
  a port `(f,d)`, `1 <= f,d <= 9`, and an occurrence row `m`. The port has
  81 possibilities. Its low residual is `(d+f+1) mod 10` for `f<9`, and
  `(d+9) mod 10` for sector nine. The predecessor is signed modulo ten,
  skipping zero; truncated natural subtraction is not equivalent.
- **Checked local theorem:** `comma_port_pumped_first_hit` proves the first
  crossing for every admitted row, and `comma_port_pump_refines_ordered_roots`
  connects it to the ordered roots. See
  [Comma_Root_Pair_Port](../../devtools/proofs/isabelle/comma_vieta_root/Comma_Root_Pair_Port.thy).
- **Checked weighted coverage:** `comma_port_weighted_cycle` proves return
  within nine ports with dwell sum equal to the existing physical period
  displacement divided by ten. `comma_port_weighted_locator_coverage` gives
  a selected interval for every admitted diagonal row. These do not identify
  that row with an arbitrary source's headroom without an anchoring theorem.
- **Separate units:** a port's dwell counts diagonal translations by ten.
  Physical transition count is recovered from the source phase. For `f=1`,
  `H=460`, the first physical transition leaves `H=459`; the complete interior
  prefix has nine physical transitions and ends at `H=91`.
- **Conditional consumer refinement:** `comma_port_validation_refines_prefix`
  proves a validated physical prefix agrees with the Near semantics, under
  the authenticated phase/chart and `H<=540` assumptions. The scheduler also
  checks the source sector, displacement and strict seam guard before use.
- **Checked Entry conjugacy:** [the focused anchor theory](../../devtools/proofs/isabelle/comma_entry_port/Comma_Entry_Port_Anchor.thy)
  proves signed source-to-row transport, weighted-row admission and periodic
  root transport. Its lifted weighted-root invariant counts one or two raw
  root crossings, including the zero root. `comma_entry_weighted_target`
  identifies the selected interval with the exact Entry target. The
  [nine-action refinement](../../devtools/proofs/isabelle/comma_entry_port/Comma_Entry_Port_Refinement.thy)
  retains both weighted inequalities and returns terminal headroom directly,
  without calling the old Near consumer in its conclusion.
- **Open global obligation:** local port closure does not prove complete Entry
  transport, complete macro termination, the losing classification, or the
  repeating winning branch. It supplies no authority to remove forest
  admission or claim the 314-fork return.

**Pair-field scope.** Retain the raw predecessor `v=(d-f) mod 10`, including
zero. The two fields `(d+v,d-v+9)` reversibly encode the 81 ports, without a
separate puncture bit. This is an encoding, not a smaller behavior count.
The second *adjacent* root uses `v`: `A=10d+f`, `B=10v+f`, and
`A+B=10(d+v)+2f`. Substituting the punctured successor for `v` is invalid:
`f=d=1, u=3` crosses gaps 11 and 1, leaving 1; the incorrect second gap 91
predicts only one crossing. The checked `comma_port_last_row` theorem already
uses the raw predecessor. This is a counterexample to that proposed local
formula, not to the complete cylinder or the 17-cycle decomposition.

**Nine shared arithmetic kernels.** With `g=gcd(f,10)`, `L=10/g`, `a=f/g`
and `d=o+gj`, the normalized phase and carry are `(j+a) mod L` and
`(j+a) div L`, independent of `o`. The full weight still has
`P/10=L o+5(L-1)+a`. Production modular powers now use the nine coprime
cores `{1,3,7,11,13,21,23,27,29}`, retaining the primary lift and full
displacement. Equal cores do not imply equal weighted Entry occurrences.
This arithmetic reduction alone supplies neither macro termination nor
future branch safety.

**Weighted versus control equivalence.** Reflection pairs the control kernels
`{1,9}`, `{2,8}`, `{3,7}`, `{4,6}`, `{5}`. Their dwell weights still differ:
the 17 occurrence cycles have distinct total weights. Thus this control
sharing does not identify the nine weighted actions. Digit 9 remains selectable
even where its first residual is zero. The finite ordered locator preserves
both prefix bounds before subtracting the selected lower bound.

The core evaluator uses halfcycles for 7, 13 and 23, short affine residues
for 11 and 27, and a seven-phase/four-rotation product for 29. Core 21 lifts
the shared mod-7 residue by its mod-3 constraint. These formulas retain the
full physical displacement's primary lift. They do not classify future branches.

The remaining **Python physical-clock refinement** has a concrete target. For
`1<=f<=9`, let `e=[f<9]` and assume `H>e`. Put `o=(-H) mod 10`,
`g=gcd(f,10)`, `L=10/g`, and let `c=10-f+(o mod g)` be the canonical
nonzero predecessor of the orbit residue. With `D_j` the physical phase displacement,
define

\[
\bar H=1+e+(H-1-e)\bmod P,\qquad
j_0=((c-o)/g)(f/g)^{-1}\bmod L,
\]
\[
H_0=D_{j_0}+10c+f+e-\ell(f,c),\qquad
m=((H_0-\bar H)/10)\bmod(P/10).
\]

The obligation is to connect weighted selection at row `m` to the authenticated
physical phase and headroom, including complete-cycle removal. Differences and
division here use signed integers; truncated natural subtraction changes the
anchor. Python checks the returned displacement and terminal guard at runtime.
The Isabelle row-coverage theorem alone does not prove this anchor equation.

Bounded independent tests enumerate all 450 admitted diagonal rows and compare
physical prefixes with literal children. Measurements and implementation
history belong in the [weekly record](../../results/current/week-of-2026-09-27/comma.md#punctured-port-construction-and-physical-prefixes).

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
The [residual core](../../devtools/proofs/isabelle/comma_decade_residual_core/Comma_Decade_Residual_Core.thy)
owns terminal outcomes, exact summaries, chronological blocks and the local
classifier recurrence independently of rank checking.
`comma_boundary_macro_exists_from_residual_classifier` connects a classifier
satisfying that recurrence to successful boundary construction. This is a
**conditional theorem**: the concrete source classifier is still required.
Rank corollaries live downstream in `Comma_Fast_Decade_Rank`; generic summary
transport and powered-boundary consumers do not import them. Uniqueness makes
the macro independent of a successful fuel value, but that semantic definition
is not yet a fuel-free executable constructor.
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
[weekly chart-unification record](../../results/current/week-of-2026-09-20/comma.md#comma-chart-unification).

Constructor measurements and the cutover disposition are recorded in the
[weekly boundary-quotient work](../../results/current/week-of-2026-09-20/comma.md#comma-boundary-quotient).

## Packed temporal control (candidate)

The development constructor now factors the one-decade control through
\(\kappa(x)=((x-(5d^2-4d))\bmod460)/10\), with \(d=x\bmod10\)
and integer division by ten. Subtraction is signed before reduction. The
91 admitted offsets have 46 fibers. This is a **control** quotient: offsets
`0,1,12,33,64` share a fiber but require different numbers of chart positions.
Literal weights, actual exponents and source authority remain separate.

The oracle-free endpoint check and `comma_decade_control_orbit_congruent` in
[the orbit theory](../../devtools/proofs/isabelle/comma_decade_orbit/Comma_Decade_Orbit_Quotient.thy)
establish this control equality for every phase. They supply no numeric
terminal table and do not equate literal weights.
`comma_decade_power_orbit_congruent` extends the equality to every dyadic
power. `comma_orbit_masks_refine` connects recursive mask squaring to those
same canonical blocks; higher powers do not invoke the raw block evaluator
in the packed recurrence.

- **Implemented research construction:** a postorder DAG shares `Entry(f,x)`
  clauses. Each clause branches on its short cyclotomic period, then intersects
  packed phase masks. It does not discover a complete round at each of the
  924 phases. The period catalog has one owner in production arithmetic.
- **Temporal composition:** a mask uses the convention
  `rotate(M,n)[r] = M[(r+n) mod 924]`. Right blocks and losing-child predicates
  therefore use the positive receiving-phase advance. Terminal leaves retain
  both their label and exact first-stop height.
- **Finite experiment:** five squares leave no live B32 control; a Boolean
  fixed point finds 14,470 losing boundary states. The remaining 314 states
  form the source cycle with exponent gain 924. These computed results are
  not proof premises or runtime branch authority.
- **Checked guard construction:** the 62 short-period residue guards are
  constructed by binary joins of periodic bit patterns. A checked short-phase
  substitution removes the need to rotate the full 924-bit word for each
  guard. This certifies the guards, not the complete response partition.
- **Checked Entry diagonal:** for decimal period `P=10M` and power residue
  `10v`, write `x=10q+d` and `eta=(q-v) mod M` using signed subtraction.
  `comma_entry_diagonal_refines` in
  [Comma_Frobenius_Entry](../../devtools/proofs/isabelle/comma_frobenius_entry/Comma_Frobenius_Entry.thy)
  factors the admitted sector endpoint through `(f,d,eta)`. The existing Near
  cache already shares the corresponding `(f,headroom)` arithmetic; an extra
  diagonal cache duplicated this work and was rejected after measurement.
  This theorem does not erase the digit-orbit position or certify the proposed
  450-state control reduction.
- **Candidate orbit reduction:** the research coordinate audit checks the
  450 `(f,orbit,innovation)` controls and exact occurrence corrections on the
  finite Entry domain. The receiving CRT clock remains necessary: residues
  1 and 23 give the same `(1,0,22)` control and next entry `(2,49)`, but the
  next innovations are respectively 0 and 24. Equal controls also have unequal
  literal weights. Orbit conjugacy, admitted recentering and weighted lifting
  are separate formal obligations.
- **Checked Frobenius recurrence:** for every admitted displacement `P`, put
  `M=P div 10` and `nu(r)=comma_power_residue P r div 10`.
  [Comma_Frobenius_Recurrence](../../devtools/proofs/isabelle/comma_frobenius_recurrence/Comma_Frobenius_Recurrence.thy)
  proves decimal divisibility, `nu((r+1) mod 924)=10*nu(r) mod M`, arbitrary
  block transport and `a(2D)=a(D)^2 mod M`. The proof derives these from the
  existing modular-power semantics, not enumerated phase results. Its
  fixed-period theorem justifies the arithmetic owner's direct exponent-five
  seed when the short period is one. Reduced affine conjugacy and half-orbit
  reflection currently have finite differential tests, not Isabelle proofs.
  This local clock law does not select a fork child or prove macro totality.
- **Checked quotient law:** forty-six stored orbit cells recover all ninety-one
  physical offsets, including exact terminal height. This reduces representation
  size without weakening the universal source domain. It does not prove that
  the concrete B5 constructor completes within the release budget.
- **Temporal representation versus source construction:** `comma_word_then`
  already composes complete control results with an external phase shift,
  absorbing left stops and adding the first span to right-stop heights.
  `comma_orbit_word_square` proves that law for the actual orbit owner.
  Encoding the span in binary preserves this arithmetic but does not compute
  the live target, stopping height or terminal kind from a source. The reported
  counts `2,3,5,9,17,27` describe observed elapsed-time outputs, not a complete
  successor action or a checked B5 instance. Literal weights belong to the
  separate weighted-germ refinement.
- **Finite observer experiments:** the reported 15 port classes preserve
  zero/nonzero observations; the same report requires 81 classes when exact
  dwell is observed. Moving dwell into a cocycle requires a joint refinement,
  not erasing it. The 29 homogeneous-run actions are not established as a
  monoid closed under mixed runs: the reported two-run experiment has 44
  distinct transformations. None of these counts is an Isabelle premise.
- **Checked forwarding:** a period-one, noncrossing sector clause preserves
  the entire existing `comma_round_result` function at every phase. Its child
  masks can therefore be reused after exact source rebinding. The theorem
  preserves crossing targets and terminal exponent deltas; it does not assert
  equality of literal weights absent from that result type.
- **Open cutover obligation:** assemble the concrete response-mask DAG and check its coverage
  instance, then its losing/winning induction and occurrence-specific weighted
  application. Coverage must include every phase in a bounded stop mask;
  an empty live mask alone could still hide `Invalid`. Generic mask algebra
  alone does not remove forest admission.

Implementation and bounded reference comparison:
[temporal control compiler](../../devtools/experiments/comma/temporal_masks.py).
Build status, timings and exact scope are recorded in the
[weekly evidence](../../results/current/week-of-2026-09-27/comma.md#comma-packed-temporal-control).

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
[weekly implementation record](../../results/current/week-of-2026-09-20/comma.md#a367620-integration).
Public acceptance, finite arithmetic, certificate soundness and performance
remain separate gates.
