# Decimal comma cylinders and A367620

[Current release gates](../release-status.md) own validation status; this page
records mathematical scope and source connections.

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
[Associated_Action_Pullback](../../proofs/isabelle/integration/associated_actions/integration/Associated_Action_Pullback.thy).
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
  [Comma_Root_Pair_Port](../../proofs/isabelle/families/comma/comma_vieta_root/Comma_Root_Pair_Port.thy).
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
- **Checked Entry conjugacy:** [the focused anchor theory](../../proofs/isabelle/families/comma/comma_entry_port/Comma_Entry_Port_Anchor.thy)
  proves signed source-to-row transport, weighted-row admission and periodic
  root transport. Its lifted weighted-root invariant counts one or two raw
  root crossings, including the zero root. `comma_entry_weighted_target`
  identifies the selected interval with the exact Entry target. The
  [nine-action refinement](../../proofs/isabelle/families/comma/comma_entry_port/Comma_Entry_Port_Refinement.thy)
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
history belong in the [weekly record](../sprints/week-of-2026-09-27/comma.md#punctured-port-construction-and-physical-prefixes).

## Certificates and proof scope

[Comma_Child_Cylinder](../../proofs/isabelle/families/comma/comma/Comma_Child_Cylinder.thy)
models child, phase and interior-guard equations.
[Comma_Root_Forest](../../proofs/isabelle/families/comma/comma_legacy/Comma_Root_Forest.thy)
states the root-exhaustion bridge: global finite-root coverage and finite
child-closed regions for all roots except 20 imply unbounded descendants of 20.
[Comma_Decimal_Parent](../../proofs/isabelle/families/comma/comma/Comma_Decimal_Parent.thy)
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
  [complete child classification](../../proofs/isabelle/families/comma/comma/Comma_Child_Classification.thy)
  proves both candidate directions for every decimal sector at exponent at least
  two. The finite-period theory proves the 17 displacement catalog; the
  power-residue theory proves the 924-period modular law, and the affine-ray
  theory proves transport of sign guards. These
  statements establish local arithmetic, not the full macro checker.
- **Checked conditional constructor:** a successful HOL macro run from an
  admitted sector has an exact literal path with `weight=initial_weight+steps`,
  the correct terminal chart and the complete ordered child set. This is an
  induction over the executable constructor, not merely a composition law.
  [Exact weighted refinement](../../proofs/isabelle/families/comma/comma_scalar/Comma_Weighted_Macro.thy)
- **Checked conditional selection:** the canonical weighted chart and binary
  prefix selector refine every partial literal prefix of a successful trace,
  using the cycle-count/remainder expression for Entry fragments.
  [Whole-macro selection](../../proofs/isabelle/families/comma/comma_literal/Comma_Macro_Selection.thy)
- **Formal frontier:** discharge successful evaluation for every admitted
  boundary state. Only then instantiate the kernel-checked
  losing-rank/winning-cycle proof from that same constructor.
  The Python ray checker is an independent oracle, not a theorem premise. The
  [boundary theory](../../proofs/isabelle/families/comma/comma/Comma_Boundary_Quotient.thy)
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
[weighted-prefix theorem](../../proofs/isabelle/families/comma/comma_round_weights/Comma_Round_Weights.thy)
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

The checked [chart-action theory](../../proofs/isabelle/families/comma/comma_chart_action/Comma_Chart_Action.thy)
represents `(X,H) ↦ (lambda*X,H+a*X+b)` using the shared skew algebra.
It transports affine guards contravariantly, preserving comparison relations,
event decorations and chronological order. Its canonical transition lemmas
derive the source digit from the actual chart. They do not grant admission to
an arbitrary supplied digit or erase exponent/weight occurrence data.
The checked [weighted-round constructor](../../proofs/isabelle/families/comma/comma_weighted_round/Comma_Weighted_Round.thy)
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
The [residual core](../../proofs/isabelle/families/comma/comma_decade_residual_core/Comma_Decade_Residual_Core.thy)
owns terminal outcomes, exact summaries, chronological blocks and the local
classifier recurrence independently of rank checking.
`comma_boundary_macro_exists_from_residual_classifier` connects a classifier
satisfying that recurrence to successful boundary construction. This is a
**conditional theorem**: the concrete source classifier is still required.
The deletion gate is `comma_decade_residual_classifier_ok C` for an executable
compact constructor, with proved totality and exact occurrence reconstruction.
The [partial classifier interface](../../proofs/isabelle/families/comma/comma_compact_classifier/Comma_Compact_Decade_Classifier.thy)
proves successful-result stability and exact-summary soundness. If a refining
one-decade constructor succeeds within 27 inspections on every admitted
source, the interface derives the recurrence and height at most 26. This is a
**conditional theorem**, not a proof that the native constructor terminates. `comma_residual_classifier_B32` supplies powering
once those premises hold; another generic block algebra is unnecessary.
Q15 sharing alone does not preserve Q19 timing (fork coefficients 3 and 6
provide a regression witness). Complement-normalized reset defects likewise
need correlated carry/occurrence transport, not equality of fixed-port outputs.
These are reconstruction obligations, not counterexamples to a complete
transported constructor. M204/T50/M111 class counts cannot discharge them.
**Checked local arithmetic.** The
[pair-field owner](../../proofs/isabelle/families/comma/comma_vieta_root/Comma_Pair_Field.thy)
proves the zero-inclusive center
`mu = (d + 10 - (f+1) div 2) mod 5` by parity and wrap cases.
`comma_pair_center_next` then derives `mu - f` modulo five, or `mu - 2*f`
when the raw predecessor is zero, without unfolding pair-field arithmetic.
The [Schur owner](../../proofs/isabelle/families/comma/comma_schur_carry/Comma_Schur_Carry.thy)
proves the executable binary/radix-five split equals decimal quotient and
remainder, reusing the shared carry monoid. These local laws do not supply the
compact decade classifier or its occurrence reconstruction.
The [Native19 bridge](../../proofs/isabelle/families/comma/comma_native19_carry/Comma_Native19_Carry.thy)
reuses the shared decimal codec; the
[factored port](../../proofs/isabelle/families/comma/comma_factored_port/Comma_Factored_Port_Carrier.thy)
retains sector and orientation for exact zero-inclusive port reconstruction.
The [six-element reset monoid](../../proofs/isabelle/integration/comma_reverse_add/comma_reset_germ/Comma_Reset_Germ.thy)
forgets earlier reset events but cannot erase complete weighted outputs.
The [terminal occurrence bridge](../../proofs/isabelle/families/comma/comma_occurrence_semantic/Comma_Decade_Occurrence_Semantic.thy)
retains literal prefixes and complete fork children without the total-macro
owner. Its extension across decade crossings remains an **open obligation**.

**Checked recursive observation.** The
[pair language](../../proofs/isabelle/families/comma/comma_pair_language/Comma_Recursive_Pair_Language.thy)
composes rightmost carry-reset domain, F2/F5 defect residues and first-defect
center; its all-neutral predicate is derived from the absent first defect.
Append and square laws are proved symbolically, with only length modulo four
needed for F5 transport. Bare residue equality is not weighted-action equality.
The [even-action theorem](../../proofs/isabelle/families/comma/comma_pair_language/Comma_Even_Port_Action.thy)
proves a fixed-sector reduced-response right congruence for every complete even
block. Sector-five aliases share weight but retain different exact endpoints
and partial locators. **Finite experiment:** independent Moore refinement
finds 90 classes at B1 and 86 at B2 through B1024 for the declared weighted
observer. This does not establish native decade refinement or its structural
termination measure. Those remain **open obligations** before forest deletion.


**Temporal observation boundary.** The exact
[port cover](../../proofs/isabelle/families/comma/comma_pair_language/Comma_Temporal_Port_Cover.thy)
retains the admitted orientation sheet over the 86 even-response keys, giving
90 physical ports. Endpoint-only time normalization has 181 arbitrary classes
and 14 dyadic classes; these are not complete branch-action identities.
The [weighted factorization](../../proofs/isabelle/families/comma/comma_pair_language/Comma_Temporal_Action.thy)
separates the exact dwell cocycle from the bounded port remainder. A port move,
a dwell row, a literal child transition and a decimal exponent increment are
different units.

The [radix-nine word](../../proofs/isabelle/families/comma/comma_pair_language/Comma_Radix9_Pair_Word.thy)
uses the existing carry domain: `(domain(s), s mod 9)` decodes a leaf sum
exactly for `0 ≤ s ≤ 18`. Its ordered block merge is
`F9(AB) = (F9(A) + 2^|A| F9(B)) mod 9`; the multiplier needs only length modulo
six. This residue does not recover an arbitrary block or its midpoint.

**Finite experiment:** the bounded joint-observer audit includes endpoints,
nine core responses, Q21, F9, reset and first-defect outputs. Its declared clock
pairs one fixed-sector port move with one harmonic tick. It tests 13,863
arbitrary signatures and 62 dyadic signatures, including the two transient
separation witnesses. The separate 46-orbit-word observer is not included.
These counts are audit evidence, not native decade semantics or a release
certificate. The universal F9 temporal-period theorem and native clock bridge
remain open.

**Cutover obligations.** Construct the native decade classifier and prove its
complete ordered child semantics across chart changes. Prove a structural
termination measure, then derive future live/loser descent and the generated
source-20 return from that owner. Until these are checked, the old decade,
future-rank and run-list owners cannot be deleted merely because a local
observer repeats. An optional observer must not become an eager CLI demand.

The rank-free losing semantics already has a shared owner:
[`comma_all_branches_terminate`](../../proofs/isabelle/families/comma/comma_cutover/Comma_Future_Safety.thy)
and its structural-induction theorem `comma_termination_excludes_infinite_path`.
Reuse these with native children rather than introducing a second losing
predicate. This generic graph theorem does not construct native children,
lift a compressed edge to literal child steps, prove the unique live-child
property, or implement a survivor selector. The current literal boundary
induction still uses `comma_total_macro`. A native recursive classifier also
needs well-founded continuation on its full executable domain, with invalid
states rejected; admitted-only bounded experiments do not establish that.
Classifier failure must remain distinct from a genuine landmine with no children;
mapping an unresolved result to `[]` would falsely prove it losing.

The native replacement has the following dependency order. These are required
interfaces, not definitions already implemented by the local quotient.

| Owner | Required result before replacing release authority |
| --- | --- |
| Native one-decade action | Executable compact arithmetic; exact ordered outcome equals the current reference on admitted states, without calling that reference. |
| Native recursive classifier | Well-founded continuation, explicit invalid-input rejection and admitted totality; derive the height bound of 26 afterward. The old 27-step fold becomes a differential oracle. |
| Native boundary publication | Exact literal prefix, endpoint, transition weight and complete child alternatives, proved across recursive decade crossings without `Comma_Total_Macro`. |
| Future semantics | Instantiate the shared inductive termination predicate with validated native children; prove unique live continuation and the source-20 live/losing pair. |
| Executable survivor selection | Compute the live child and exponent transport from compact coordinates, with all rejected siblings proved losing. A live-state table or a noncomputable choice is not this constructor. |

Numeric rank may be a derived height of a losing proof; it need not be an input
to live/loser semantics. Replacing rank lookup alone does not supply the native
classifier, its termination proof or the executable survivor selector.

### Two-digit carry generator

**Exact arithmetic specification.** For a fixed selected sector `f`, write
`k = 100 H + x`, with `x = 10 t + d < 100`. The low carries are
`c0 = (d + f) div 10` and `c1 = (t + d + c0) div 10`. Both are binary.
On the neutral pair `t+d=9`, sector 5 sends suffix 54 to 99 with
`(c0,c1)=(0,0)`, and suffix 45 to 100 with `(1,1)`. The neutral carry domain
at `t+d=9` transmits `c0`; it does not mean that the carry is zero.

The exact suffix action is `x ↦ 11x+f (mod 100)`. Its CRT coordinates are
`(x mod 4, x mod 25)`, and its power is
`((1+10n)x + f(n+5n(n-1))) mod 100`. The duration phase has period 50;
the exact carry count is separate from that phase. If `D_f(d,n)` is the
existing fixed-sector displacement, then
`N1 = (x + D_f(d,n)) div 100` and `H' = H + N1`.
Complete digit cycles and a tail shorter than ten compute this displacement;
there is no need to retain the represented carry word.

The lower carry is a rational mechanical word (the periodic analogue of a
Sturmian word). The upper carry is generally **not** Sturmian. At elapsed
time `n`, a higher wire `j ≥ 2` fires exactly when the current `c1` fires and
`H + N1 + 1` is divisible by `10^(j-1)`. Thus higher spatial carries demand
a high-prefix residue, not another stored itinerary.

**Scope.** The sector must remain admitted throughout a powered application.
The CRT phase is not a complete decade or future key: identical low suffixes
at different exponent phases can have different Entry targets. For example,
Entry `(1,0,0)` has Near headroom 180 at exponent residue 5 and 420 at
residue 6. Harmonic phase, high-prefix precision and the crossing guard remain
necessary. Q86, Native19 and F9 can be derived local views; deleting their
proof dependencies requires the corresponding projection and continuation
theorems, not merely the 50-phase suffix identity.

### Exact exponent transport across decade re-entry

**Checked occurrence lift, conditional on an exact summary.**
[Comma_Decade_Occurrence_Lift](../../proofs/isabelle/families/comma/comma_decade_occurrence_lift/Comma_Decade_Occurrence_Lift.thy)
proves that `comma_decade_exact_summary s h tau`, together with an admitted
source at physical exponent `p`, yields a literal prefix ending at exponent
`p+h`. Each continuing decade contributes one exact exponent increment.
The terminal children are the ordered N/Z pair at `p+h`, or the empty list
for a landmine. This is induction over the existing semantic summary; it does
not evaluate `comma_finite_run`, supply a fuel bound, or enumerate a rank table.

The resulting phase is `(p+h) mod 924`. It is a projection of exact transport,
not a replacement for it. The runtime `WeightedBoundaryAction` already adds
exact exponent deltas chronologically; the unweighted future Moore observer
erases these coefficients. Exact C1/borrow amounts likewise belong to the
receiving occurrence and cannot be copied between residue-equivalent exponents.

**Checked physical C1 occurrence.**
[Comma_C1_Occurrence](../../proofs/isabelle/families/comma/comma_c1_occurrence/Comma_C1_Occurrence.thy)
connects an admitted fixed-sector powered C1 return to its literal path and
physical endpoint. For two independently admitted durations, the endpoint
high-difference change is the difference of C1 counts plus the source borrow
minus the target borrow. The accompanying suffix-difference theorem proves
that this signed quantity reconstructs the physical integer difference.
These guards do not authorize crossing a sector or identify a whole N/Z macro
with a synchronized local return.

**Open constructor obligation.** The decade lift does not produce an exact summary
for every admitted input. A native classifier must establish that existence
and its recurrence before the global survivor proof can consume it. A macro
edge means a literal prefix followed by a terminal child edge; equating it
with one `comma_child` edge from the starting boundary is incorrect. A C1
suffix re-sector operation also needs a physical seam proof before it can
transport an occurrence across sectors.

### Sibling borrow and survivor observation

For synchronized adjacent sectors `f,f+1`, let
`delta=(x_B-x_A) mod 100`, `d=x_A mod 10`, and `b=[x_B<x_A]`.
The normalized high difference is `D=H_B-H_A-b`. Its signed innovation is
`zeta=c1_B-c1_A+b-b_next`, with the exact local formula

```text
delta_next = (11 delta + 1) mod 100
d_next = (d + f) mod 10
zeta = (11 delta + 1) div 100 - delta div 10 - [d + delta mod 10 >= 10]
D_next = D + zeta
```

The subtraction is signed. Physical `c1` is the two-column addition carry;
`(11x+f) div 100` is not that carry. A powered difference return uses completed
C1 returns and telescoping endpoint borrows. Exact innovation remains an
occurrence quantity, not a finite semantic identifier.

**Checked local refinement.**
[Comma_C1_Borrow_Cocycle](../../proofs/isabelle/families/comma/comma_c1_borrow/Comma_C1_Borrow_Cocycle.thy)
proves the delta and signed innovation laws, connects them to actual admitted
one-step C1 phases (`comma_c1_borrow_innovation_one_step_exact`), and proves
chronological telescoping (`comma_c1_borrow_innovation_add`). Adjacent sectors
and synchronized duration remain essential premises; unequal-duration complete
sibling macros require their separate occurrence transport.

**Finite experiment versus constructor.** The downloaded borrow/Vieta audit
constructs the existing complete boundary graph, chooses representative
exponents, and obtains each carry total from the difference of endpoint high
prefixes. Its pointed-root audit calls the algorithmic losing-rank computation.
It can test the reported partitions; it does not construct a native selector
from the local borrow formula or prove transport to all exponents. For boundary
`(N,2,10 mod 924)`, the reported exact borrow total is
`999800000000000` at exponent 10 and that value times `10^924` at exponent
934. The exact total needs affine occurrence transport, not an unproved
exponent-independent semantic identity. Replacing
named losing subtrees by one dead root changes the observed transition system:
the pointed view retains only the selected live transition.

The constructive revision accumulates carries from sector fragments and uses
greatest-fixed-point pruning without numeric ranks. These improve the audit's
construction boundary, but the fragments and ordered children still come from
the existing macro constructor. Child counts must be evaluated at the actual
receiving exponent: parent `N(5,921)` reaches children with residue 5 at exponent
929. Reusing their exponent-5 counts would replace `90000*10^924` by `90000`
in the sibling innovation. This is an occurrence-transport error, not evidence
against the finite quotient. Cycle traversal, exponent gain and live-fiber
checks remain separate from native all-exponent refinement.

**Conditional checked theorem.**
[The shared selector theorem](../../proofs/isabelle/families/comma/comma_future_selector/Comma_Future_Selector.thy)
proves dead iff terminating, live iff an infinite path exists, and uniqueness
of the nonterminating child. Its locale requires complete admitted children,
a well-founded dead relation, and a successor-closed selected live child with
dead rejected siblings. No concrete comma selector currently instantiates
those obligations. Numeric rank and losing-level stabilization are unnecessary
for this implication, but its premises still require proof.

**Boundary correction.** After removing two low digits from `a*10^p-1` or
`a*10^p`, the uniform nine/zero tail has precision `p-2`. Therefore the simplified
N/Z carry formula is valid only for `2 <= j < p`. The top wire retains the exact
high-prefix residue. For `N(2,5)=199999`, `H=1999`, duration zero and sector one,
wire four fires while wire five does not; extending the uniform-tail shortcut
to `j=p` would incorrectly assert wire five. The
[boundary carry theorem](../../proofs/isabelle/families/comma/comma_c1_generator/Comma_C1_Boundary_Carry.thy)
uses the corrected range.

Rank corollaries live downstream in `Comma_Fast_Decade_Rank`; generic summary
transport and powered-boundary consumers do not import them. Uniqueness makes
the macro independent of a successful fuel value, but that semantic definition
is not yet a fuel-free executable constructor.
Keep the source sector and digit fiber in admission: `(X,H)` alone does not
identify them. A tropical minimum may replace guards only after a separate
equivalence theorem preserves strictness, equality and event identity.

**Checked control normalization.** `comma_normalized_step_commutes` in
[the finite transition theory](../../proofs/isabelle/families/comma/comma_cutover/Comma_Finite_Transition.thy)
proves that replacing the chart's absolute gain by `(residue+delta) mod 924`
commutes with one canonical control move, including terminal outcomes.
This observation forgets exponent gain: weighted application must retain it
separately. It is not a termination or infinite-path theorem.

**Implemented construction and checked local theorem.** For each
catalog displacement `P`, the eventual power period `T(P)` lies in
`{1,2,3,6,22,28}` and divides 924. The finite Entry evaluator uses

\[
10^{5+((r+919)\bmod T(P))}\bmod P,
\qquad r=(p+\delta)\bmod924,
\]

whose exponent is at most 32. The theorem
[`comma_power_residue_correct`](../../proofs/isabelle/families/comma/comma/Comma_Power_Residue.thy)
proves equality to `10^(p+delta) mod P` for every admitted exponent.
Finite residue tests are separate from that kernel-checked theorem. Making
Entry inexpensive does not prove that every boundary macro terminates: the
total constructor theorem must remove the successful-run premise before
ranked termination or infinite continuation can authorize branch pruning.
The checked [short-phase transport](../../proofs/isabelle/families/comma/comma_short_phase/Comma_Short_Phase.thy)
permits Entry arithmetic reuse at phase `(r+delta) mod T(P)`, with the output
gain restored by the transport. The power lookup itself uses the rotated index
`(r+delta+919) mod T(P)`. There are 116 power observations; the finite catalog
contains 7,019 Entry classes for offsets 0–98, while decade starts use 0–90.
Neither catalog size proves the full rank instance or its verification cost.
Construction and formal-validation evidence belongs in the
[weekly chart-unification record](../sprints/week-of-2026-09-20/comma.md#comma-chart-unification).

Constructor measurements and the cutover disposition are recorded in the
[weekly boundary-quotient work](../sprints/week-of-2026-09-20/comma.md#comma-boundary-quotient).

## Packed temporal control (candidate)

The development constructor now factors the one-decade control through
\(\kappa(x)=((x-(5d^2-4d))\bmod460)/10\), with \(d=x\bmod10\)
and integer division by ten. Subtraction is signed before reduction. The
91 admitted offsets have 46 fibers. This is a **control** quotient: offsets
`0,1,12,33,64` share a fiber but require different numbers of chart positions.
Literal weights, actual exponents and source authority remain separate.

The oracle-free endpoint check and `comma_decade_control_orbit_congruent` in
[the orbit theory](../../proofs/isabelle/families/comma/comma_decade_orbit/Comma_Decade_Orbit_Quotient.thy)
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
  [Comma_Frobenius_Entry](../../proofs/isabelle/families/comma/comma_frobenius_entry/Comma_Frobenius_Entry.thy)
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
  [Comma_Frobenius_Recurrence](../../proofs/isabelle/families/comma/comma_frobenius_recurrence/Comma_Frobenius_Recurrence.thy)
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
  distinct transformations. Those historical counts are superseded for the
  NC5 future alphabet by the executable audit below. None is an Isabelle premise.
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
[weekly evidence](../sprints/week-of-2026-09-27/comma.md#comma-packed-temporal-control).

## First-fork index discrepancy

The published first-fork value is `19999999918`, with children `19999999999`
and `20000000000`. The paper/OEIS gives index **412987860**. Our guarded
constructors and a separate literal C enumerator, initialized explicitly at
`k=20,n=1`, reach it at **412987859**. This is a disagreement with the published
anchor, not a convention change. The preceding value is checked in the
arithmetic tests; no later branch is chosen by a fixture.
The checked theorem `comma_source20_to_fork` in
[the source-entry theory](../../proofs/isabelle/families/comma/comma_entry/Comma_Source_Entry.thy)
now establishes a literal path of exactly 412,987,858 transitions from 20 to
that value, and `comma_source20_first_fork_children` proves the complete child
set. The separate theorem `comma_source20_to_fork_unique` in
[the uniqueness theory](../../proofs/isabelle/families/comma/comma_unique/Comma_Source_Unique.thy)
proves that every preceding transition has exactly one child. These finite
prefix results do not establish an infinite continuation after the fork.
The first excluded child is `20000000000`; its complete finite forest forces
the other child, `19999999999`, at index 412987860. That agrees with the first
decision in [A399179](https://oeis.org/A399179). The other 29 published decisions
do not automatically extend the admitted production boundary.

Reproduction and frozen measurements belong in the
[weekly implementation record](../sprints/week-of-2026-09-20/comma.md#a367620-integration).
Public acceptance, finite arithmetic, certificate soundness and performance
remain separate gates.


### Normalized interior-cycle return

**Checked arithmetic refinement.** For an admitted decimal phase `(f,d)`,
let `L=10/gcd(f,10)` and let `P` be its complete-cycle displacement.
For positive `c`, the complete repeated action has the normal form
`(c L, c P, c P + [f<9])`: literal duration, displacement and strict guard.
[Comma_Normalized_Cycle](../../proofs/isabelle/families/comma/comma_interior_cache/Comma_Normalized_Cycle.thy)
proves equality with the exact phase displacement and maximum prefix guard,
chronological joining and receiving-headroom admission. Zero repetitions use
the separate identity action.
Its `comma_normalized_cycle_gcd_normalization` theorem also proves that
complete-cycle summaries depend on the entering digit only through its residue
modulo `gcd(f,10)`. Actual phase admission remains occurrence-specific.

The formula takes a fixed number of integer operations; operand sizes remain
part of its cost. It does not establish a finite future-branch quotient,
all-source macro termination, or infinite continuation. The implementation and
measurements are recorded in the
[September 30 sprint](../sprints/week-of-2026-09-27/comma.md#september-30--normalized-cycle-reuse-and-proof-memos).

### Executable future-observer audit

**Finite experiment, not runtime branch authority.** The explicit
[quotient checker](../../devtools/verification/comma_semantic_quotients.py)
reproduces Q15 (81 nonzero ports), Q19 (90 zero-inclusive ports), T3279
(3,279 future classes) and M4986 (4,986 classes retaining Q19 observations).
The complete 14,784-state graph has 14,470 losing states, maximum rank 136,
and 314 survivors. The selected cycle advances the exponent by 924.
Homogeneous runs yield 31 distinct actions, including identity and common dead
action: `0^13` and `1^18` are dead. This is not a closure claim for arbitrary
mixed runs. Physical child slots remain ordered `(N,Z)`; the experiment's
logical symbols map `0` to Z and `1` to N.

These partitions erase exact weights and guards; equal classes cannot transfer
an occurrence's displacement. Tables are built only by explicit developer
checks, never by package import or CLI execution. M4175/R29 were not reproduced.

**Direct spatial constructor.** The [Q19 arithmetic owner](../../src/number_compiler/sequences/comma/cycle_spatial.py)
classifies one port without a graph or minimization. Put `g=gcd(f,10)` and
`L=10/g`. If `g` divides `d`, its class is `(L,j)` with
`j=(d/g)*(f/g)^(-1) mod L`; otherwise its class is `(L,None)`.
The observation is `(j=1,L)`. A punctured move sends phases 0 and 1 to
`L-1`, decrements other phases, and preserves `None`. There are ten classes
at period 10, six at period 5 and three at period 2. Zero remains a transient
source. Exact weights, fork coefficients and decade continuation are not part
of this observation. The Python owner powers these cyclic moves by modular
arithmetic. This is port-move time, not decimal-exponent phase.
The [Q19 theory](../../proofs/isabelle/families/comma/comma_cycle_spatial_moore/Comma_Cycle_Spatial_Moore.thy)
contains the corresponding inverse-based classifier, finite port checks and
source-iteration refinement; build evidence is recorded separately in the sprint.

**Summary versus source constructor.** The supplied T50/M204/M111 reconstruction
reads candidate heights and terminal labels, then forms countdown descriptors.
Its radial check encodes an already-known fork coefficient as `9*(11-a)` and
inverts that encoding. It does not yet compute that cocycle from the source.
Sources `(r,x)=(1,0)` and `(13,0)` both have summary `(2,Landmine)` and the same
reported M111 class, but their first B1 live fibers are 12 and 23. A replacement
observer therefore needs independently constructed occurrence transport as well
as the summary class. This witness does not rule out such a complete quotient.
The expanded B1 Moore census is available only by explicitly requesting
`--expanded-moore-baseline` from the developer audit; it is not a production
classifier or a default minimization pass.

**External selector clock.** The [clock owner](../../src/number_compiler/sequences/comma/cyclotomic_clock.py)
stores occurrence characters `(r mod 4,r mod 3,r mod 7,r mod 11)`. The local
periods 1, 2, 3, 6, 22 and 28 are projections of that clock, not six action
identities. Exact CRT projection feeds the existing nine-core residue owner;
no endpoint-specific phase table is needed. This selector does not replace
elapsed-time weights or source-dependent guards. In particular, equal phase
modulo 22 need not give equal phase modulo 28. The
[endpoint refinement](../../proofs/isabelle/families/comma/comma_decisive_endpoint_quotient/Comma_Decisive_Endpoint_Quotient.thy)
connects the core/clock key to the exact Entry endpoint on `x≤89+f` and proves
fuel-free sector recursion equivalent to B1. Sparse B1 publication and future
observer minimization remain separate obligations; neither a small core catalog
nor a downstream summary census proves them.

**Terminal control and occurrence weight.** For a valid terminal summary, put
`J=a-2` for `Fork a` (`2≤a≤9`) and `J=8` for Landmine. The exact sector-level
first-hit weight is `D=9*H+J`, where `H` counts complete continuing decades.
It reconstructs `H=D div 9` and the terminal from `D mod 9`; composition after
`n` continuing decades adds `9*n`. The
[weighted-stop theorem](../../proofs/isabelle/families/comma/comma_terminal_weight/Comma_Terminal_Weight.thy)
defines these rules inductively and proves equivalence to the exact summary:
source control has no height coordinate, and `D` is the returned occurrence
weight. This is not a one-state ordinary Moore quotient, and `D` is not the literal sequence
transition count. Neither storing `D` instead of `(H,terminal)` nor a small
terminal alphabet by itself reduces the number of distinct exact output rows.
The [terminal audit](../../devtools/verification/comma_b1_terminal_audit.py)
constructs the weight from source transitions without rank/terminal tables:
`python -m devtools.verification.comma_b1_terminal_audit --full --full-future`.
Its finite experiment and the weighted refinement remain distinct from global
infinite-path admission and sparse-publisher performance.

**C1 landmine recognition.** The checked Near theorem uses `B=h-1` and proves
that sector 9 is terminal Landmine exactly when `18≤B≤81` and `B mod 9=0`,
for admitted Near headrooms. Inside that band only the residue test remains;
outside it the bounds cannot be dropped. The Python endpoint owner applies
this shared arithmetic predicate before allocating a generic boundary chart.
The returned Landmine control contains neither headroom nor complete-decade
height. Exact source headroom remains occurrence data, and terminal distance
remains the returned weight `D=9H+8`.


**Checked conditional sparse consumer.** The
[sparse summary theorem](../../proofs/isabelle/families/comma/comma_native_summary/Comma_Native_Summary.thy)
assumes complete B32 partial certificates over every phase of all 46 fibers,
and that each retained label is `Stop h terminal` with `h≤26`. It then proves
that executable lookup returns an exact decade summary for every admitted
`(phase, offset)`. The
[occurrence corollary](../../proofs/isabelle/families/comma/comma_native_summary_occurrence/Comma_Native_Summary_Occurrence.thy)
preserves the literal prefix, exact exponent gain and ordered terminal children.
These assumptions concern the checked constructor output, not an external table.
The concrete base-mask/power instance remains an open performance and kernel gate.
Independent finite reconstruction agrees on all 84,084 admitted states, but
cannot discharge that gate or authorize runtime branch selection.

**Unchecked global theorem layer.**
[Comma_Global_Future_Safety](../../proofs/isabelle/families/comma/comma_future_global/Comma_Global_Future_Safety.thy)
specializes the rank and cycle checker to source-20 infinite existence and
first-fork uniqueness. Its concrete checked-instance prerequisite still times
out; registration does not establish those statements. Earlier-root exclusion,
the replacement executable macro owner and weighted production admission remain
separate obligations. See the
[integration evidence](../sprints/week-of-2026-09-27/comma.md#september-30--executable-future-quotients-and-phase-reuse).

### First-crossing global-root reduction

- **Proposed checked theorem:** every infinite path from a listed decimal root
  first crosses `10^5` at `100000+x` for `0 <= x <= 90`. Strict child growth
  guarantees a crossing; the receiving leading digit is 1, tightening the
  increment bound to 91 and hence the offset bound to 90.
- **Finite experiment:** the existing chart arithmetic and least-rank audit leave
  exactly offsets `{3,34,75}` open. Both children are retained in the check; their
  ranks are `(None,7)` after exponent gain 5 at `a=2`. Literal source-20 controls
  contain all three entries consecutively.
- **Pending kernel proof:**
  [Comma_Global_Root_Safety](../../proofs/isabelle/families/comma/comma_future_global/Comma_Global_Root_Safety.thy)
  combines the 91-entry B32 check, deterministic parent descent and imported
  rank/literal-path theorems. Its `comma_global_release_safety` statement is about
  listed decimal roots and source 20's first choice. The imported global rank
  checker must finish before this result can authorize forest deletion.
- **Scope:** the reduction removes the need for 49 separate root-tree arguments.
  It does not itself remove finite-run fuel, extend emitted indices, establish
  all-exponent runtime refinement, or make the 14,784-state rank check redundant.

Implementation and build evidence belongs to the
[September 30 root-entry record](../sprints/week-of-2026-09-27/comma.md#september-30--global-root-entry-reduction-and-forest-cutover-audit).
