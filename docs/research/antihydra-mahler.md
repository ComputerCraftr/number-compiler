# Antihydra arithmetic, literal machine, and Mahler action

[Current release gates](../release-status.md) own validation status; this page
records mathematical scope and source connections.

Status: **Finite arithmetic and safety laws are checked; complete literal/macro
refinement and the source-7 all-time barrier remain open.**

## Reading guide

- **Definitions:** total arithmetic starts at `a=8` and applies `a <- a + floor(a/2)`. The ledger starts at zero and changes by `+2` for even `a`, `-1` for odd `a`; centered state is `D=a-1`.
- **Checked theorem:** finite arithmetic composition and minimum-prefix guards preserve their stated semantics.
- **Implemented construction:** arithmetic images and demanded support fragments retain source authority; guarded physical execution remains a separate consumer.
- **Open obligation:** source-7 non-halting, complete literal/macro refinement and arbitrary-horizon retention bounds remain unresolved.

## One scheduler for arithmetic and finite Mahler safety

**Implemented:** [Mahler actions](../../src/number_compiler/sequences/antihydra/mahler_action.py)
are lazy projections of the same authenticated arithmetic image used by value
and ledger queries. The skew and pinned centered `11` prefix determine the
finite cap law. Source, action, extent, law and tail-offset checks remain
required. Hensel is a separate observation; neither requests physical roofs.

**Checked finite root chart:** with `theta=2t=r²`, the source-selected action is
`theta'=(3/2)^n theta-2C`. The root-shell lemmas in
[Mahler_Source_Event_Safety](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Source_Event_Safety.thy)
preserve chronological guards and the event interval `1 ≤ (3/2)^q theta < 3/2`.
The CLI Mahler packet exposes exact rational radicand coefficients and guards
from its admitted image. This is an observer, not a new source constructor or
an all-time safety proof. [Implementation evidence](../sprints/week-of-2026-09-20/shared.md#root-shell-and-consumer-relative-moore-integration).

Binary point requests use the shared affine point germ with its independent
blank cutoff, without materializing the arithmetic endpoint or requesting
first-failure descent. Ordinary value output requests the endpoint directly;
ledger, physical and Mahler information still consume the same admitted image
through their own safety predicates. A current-point germ is not sufficient
to replace that support or prove future safety. The
[integration record](../sprints/week-of-2026-09-20/shared.md#affine-point-germ-consumers)
separates these demand savings from unchanged cold source discovery.

The public aggregate omits support handles. The scheduler retains one saturated
image and expands chronology only for a demanded physical consumer. Short or
homogeneous centered runs use exact affine powers; long mixed horizons use the
shared balanced constructor to avoid growing-integer run replay. The Mahler
packet exposes its centered carry `C`, source residue, and rational real guard
from this same image. The pinned source's Mahler margin fails at return
two, where its Antihydra ledger remains safe. These predicates are distinct.

**Proof scope:** finite associated-action laws are checked in
`Associated_Action_Core` and `Antihydra_Mahler_Integration`. The downstream
`Balanced_Dyadic_Integration` connects the shared numerical worklist to actual
Antihydra source bits, finite ledger guards and Mahler's demanded coefficients;
see the [executable refinement map](../proofs/balanced-dyadic-refinement.md).
Python publication/retained-ID refinement, resource bounds and a source-global
invariant remain open. Dated validation belongs in the weekly record.

[Implementation and validation record](../sprints/week-of-2026-09-20/antihydra-mahler.md#one-scheduler-for-arithmetic-and-finite-mahler-safety).

## Joint future-observer experiment

### Recursive source pullback and coupled boundary

**Exact algebra; bounded validation:** an admitted width-`D` occurrence has
`X=r+2^D u` and `Y=t+3^D u`. Its inverse is
`X=(2/3)^D Y+r-(2/3)^D t`. For the composed predicate
`F(m)=min(C,A*m+B)`, `A=(3/2)^D`, the affine offset is
`B=3*A*r-3*t`. Thus `Z=m+3X` removes that offset; only the cap carries
independent predicate information beyond the exact occurrence.

For an ordinary finite source covered by the input width, subsequent source
chunks are zero. The translated midpoint still need not have zero high bits.
The normalized interval is `(3*t/A, (C+3*t)/A)`; positivity is equivalent to
`C>0`. The [independent bounded check](../../tests/validation/proofs/test_mahler_recursive_boundary.py)
verifies the cancellation, ordered interval nesting and the `39 → 6 → 0`
survivor counts at widths 8, 16 and 32 for sources 1–255.

**Constructor candidate:** the downloaded recursive selector composes D8 source
blocks without calling the primitive source builder after bootstrap. Its poison
tests pass, but a cold source-53 probe still creates `D/8-1` wider compositions.
This supports finite balanced construction, not logarithmic total construction
or a proved asymptotic bound. The candidate is not the production scheduler.
**Open theorem:** every positive finite source must eventually leave the nested
interval. Monotonicity alone does not prove crossing, and Mahler failure still
does not imply Antihydra ledger failure.

[Patch review and validation](../sprints/week-of-2026-09-27/antihydra-mahler.md#mahler-recursive-source-pullback-review).

### Earlier joint-observer audit

The [joint audit](../../devtools/experiments/antihydra/joint_future_quotient.py)
combines suffix, prime buckets and deck/chart views of admitted source edges.
High-fiber and fractional probes range over finite initial families, not a
single blank-tape trajectory. Full keys observe a completed edge and are tested
against subsequent continuation; they do not predict that edge without construction.

**Finite evidence:** the full-prime depth-32 sample has 1,377 rows, 254 repeated
keys and no coarse conflicts, but 476 exact-continuation differences. A
three-prime depth-8 sample has eight coarse conflicts. At source 13, width 4,
exponent 3 and suffix `(1,2)`, fractions `885/2048` and `1935095/4194304` share
the current clause but disagree on next-event safety. Sources 20 and 46,676
also share a finite key while reaching 230 and 531,671. These witnesses refute
those observer identities, not the complete parameterized cylinder.

**Checked algebra:** [Mahler_Joint_Quotient_Algebra](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Joint_Quotient_Algebra.thy)
proves suffix composition, base-three encoding modulo 729 and distinct lane
laws. Partition completeness and legal-continuation closure remain open;
no experiment publishes a pump or merges production sources.

[Implementation and validation record](../sprints/week-of-2026-09-20/antihydra-mahler.md#joint-future-observer-experiment).

## Bounded projection publication

The projection adapter references the cursor's sealed bounded image; it checks
source, action, projection and exact endpoint before publication. Eliminating
a duplicate roof chain does not eliminate bounded physical discovery or prove
the source-7 barrier.

[Implementation and validation record](../sprints/week-of-2026-09-20/antihydra-mahler.md#bounded-projection-publication).

## Checked arithmetic and cylinders

[`Antihydra_Family_Iteration.thy`](../../proofs/isabelle/families/antihydra/antihydra/Antihydra_Family_Iteration.thy)
proves the total skew equation, centered orbit, block composition, exact minimum
prefix guard, and guarded agreement before the first failed block. The latter is
conditional on remaining before failure and does not prove all-time safety.

**Checked named-event contraction:** for `D=2^k(2M+1)`, the centered word
`0^k1` returns `3^(k+1)M+(3^(k+1)+1)/2`, with ledger delta `2-k` and minimum
`-k`. The three `antihydra_punctured_event_*` lemmas in
[`Maximal_Run_Arithmetic`](../../proofs/isabelle/integration/dyadic/integration_dyadic/Maximal_Run_Arithmetic.thy)
reuse the homogeneous run and source-step owners. They justify one admitted
event; they do not prove future event discovery or identify anonymous roots
with ordered successor occurrences.

[`Antihydra_Arithmetic_Cylinder_Lift.thy`](../../proofs/isabelle/families/antihydra/antihydra/Antihydra_Arithmetic_Cylinder_Lift.thy)
identifies family bits with a dyadic source word and proves exact demanded
cylinder composition, split, bit, and ledger projections. These results assume
the admitted arithmetic source; they do not generate a literal macro word.

[`Antihydra_Mahler_Skew.thy`](../../proofs/isabelle/families/antihydra/antihydra/Antihydra_Mahler_Skew.thy)
proves centered return, numerator and minimum-prefix composition, and the
one-return kernel coefficients. The associated-action refinement
[`Antihydra_Mahler_Associated_Action.thy`](../../proofs/isabelle/integration/antihydra_mahler/integration_mahler/Antihydra_Mahler_Associated_Action.thy)
proves source coefficients determine the defined Mahler action. It also proves
that the centered word `11` has distinct Mahler and ledger outcomes, so a Mahler
failure must not be reported as Antihydra halting.

**Checked finite-action theorem:** `mahler_centered_11_actual_tail_cap`
proves that every finite continuation by legal bit actions after `11` retains
the cap `3/2 * scale + offset < 0`. Its induction uses
`mahler_negative_cap_preserved`; it concerns the actual capped actions, rather
than an uncapped replacement tail. This supports the root-action cap reduction.
The source-to-action constructor and cache publication invariant still require
their own refinement; the theorem makes no all-time safety claim.

## Shared Collatz F5 spatial action: checked transfer

The shared [carry/F5 owner](../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py)
applies to `D=a-1` with `D'=floor((3D+1)/2)` and `a'=D'+1`.
Its 15 leaf and 17 spatial classes observe carry response and additive phase;
that phase is not a whole-numeral jet or a source identity.

For `D=u+2bv`, let `e=(3u+1) mod 2b` and `c=(3u+1) div 2b`. Then

\[
D'=\lfloor e/2\rfloor+b(3v+c),\qquad a'=D'+1.
\]

`mahler_spatial_low_block_transport` and
`antihydra_centered_spatial_low_block_transport` in
[Mahler_Spatial_Carry_Pump](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Spatial_Carry_Pump.thy)
prove this complete low-block/high-boundary transport; radix 64 uses `b=32`.
Supplied repeated spatial blocks admit powering. This does not select future
source events or prove the Python F5 tables' complete temporal refinement.

The bounded Mahler source observer now folds its column maps through this same
carry/F5 owner. Temporal jet forgetting also holds before further shared
continuations; ordered safety remains a separate consumer. See the
[transfer and verification record](../sprints/week-of-2026-09-20/antihydra-mahler.md#f5-observer-and-safety-transfer).

For an odd centered source `U`, with `a=v2(3U+1)`, the next odd event is

\[
U'=3^{a-1}(3U+1)/2^a,\qquad E'=E+3-a.
\]

The extra factor distinguishes this law from accelerated Collatz. Fractional
safety, ledger safety and all-time non-halting remain separate obligations.

[Implementation and validation record](../sprints/week-of-2026-09-20/antihydra-mahler.md#shared-collatz-f5-spatial-action-checked-transfer).

## Literal and barrier boundary

[`Antihydra_Literal_TM.thy`](../../proofs/isabelle/families/antihydra/antihydra/Antihydra_Literal_TM.thy)
checks startup and the exact halt boundary.
[`Antihydra_Macro_Grammar.thy`](../../proofs/isabelle/families/antihydra/antihydra/Antihydra_Macro_Grammar.thy)
proves length, shift, directional clock, and admitted terminal cases for supplied
macro words. The missing bridge is a source-generated macro word with reads,
overwrites, startup invariant, powered image, and first-failure refinement.

[`Antihydra_Source_Barrier.thy`](../../proofs/isabelle/families/antihydra/antihydra/Antihydra_Source_Barrier.thy)
proves `source_bound_barrier_soundness` for a supplied valid barrier.
`source_seven_all_time_barrier_exactly` is an equivalence: it does not construct
the barrier. No accepted source-7 all-time certificate or source-reachable
counterexample is currently present.

## Production boundary

The [shared temporal-reuse adapter](collatz.md#shared-temporal-effect-reuse)
now shares complete admitted cylinder effects across compatible source
occurrences. The minimum-prefix ledger and first-failure descent remain part
of the reused support. A synthetic repeated negative-ledger macro still fails
at its first return while total arithmetic continues exactly.

[`mahler_action.source_action`](../../src/number_compiler/sequences/antihydra/mahler_action.py)
now reads the authenticated root skew from `arithmetic_workspace.summary()`.
It no longer recomposes every retained segment to recover that same action.
The ledger reports `mahler_source_composed_image_reads`; the retired
`mahler_source_cylinder_compositions` count stays zero. Source validation,
fractional predicates and ledger safety remain distinct checks. This eliminates
the redundant arithmetic fold, not all source validation or rational-integer work.

Complete-effect reuse on aligned sources does not establish F5-based
normalization across changing source residues. Measurements of a particular
blank source belong to the dated evidence, not a permanent production status.

Finite `--nth` arithmetic and selected projections are available with bounded
ownership. Reusing retained parity avoids rediscovery, but folding every
retained step is still linear in the represented source. Batch aliases share
one authenticated discovery result; Hensel and Mahler packets remain distinct.

Finite bounded barrier searches and observed nonhalting prefixes are evidence
only. They neither prove all-time nonhalting nor refute a future source-global
certificate.

## Original Mahler fractional safety

### Signed current-tail boundary

For a chronological bit word of length `n`, let
`C = sum(e_j 3^(n-1-j) 2^j)` and `N = 3^n - 2^n - 2C`.
This is a projection of the existing source skew, not another source state.
A tail with remainder in `[-1,1]` lies in
`[(N-2^n)/3^n, (N+2^n)/3^n]`:

- `N > 2^n`: the **current tail** is positive for every such remainder.
- `N <= -2^n`: the current tail is nonpositive.
- Otherwise: refine the cylinder. Endpoint equality stays unresolved on the
  positive side; nonempty binary words exclude both equalities by parity.

The cone coordinates `A=N+2^n`, `B=2^n-N` obey
`0: (A,B) -> (3A,2B-A)` and `1: (A,B) -> (2A-B,3B)`.
Their homogeneous run powers use only `2^k` and `3^k`; the implementation
reuses shared binary composition and preserves the original fractional guard.
It powers a supplied run, without claiming to discover future source runs.

**Checked finite algebra:**
[Mahler_Cyclotomic_Boundary](../../proofs/isabelle/integration/antihydra_mahler/mahler_safety/Mahler_Cyclotomic_Boundary.thy)
proves the signed-source bridge, enclosure, absorbing sign regions, cone/run
laws, the Vieta identity and boundary-exit selectors. Its three-word six-bit
lemma retains an explicit no-adjacent-ones assumption; a separate finite lemma
partitions the existing 18 survivor residues into 15 positive and three boundary
cases. The bounded-remainder premise remains explicit. It is not a proof
that every source has a globally admissible infinite continuation.

**Finite experiment:** the six-step census reproduces 15 positive
current tails and boundary residues `{9,13,45}`; twelve steps split into 198
positive tails and `{521,777,2569}`. Boundary-only refinement through depth 500
keeps two to five cylinders from depth six onward. Neither a uniform frontier
bound nor exclusion of positive natural sources follows from this experiment.

Use the existing research driver for the sign query:

```console
python -m devtools.experiments.antihydra.barrier_search --mode tail --depth 500 --max-nodes 20000
```

Positive current-tail terminals must **not** replace all-shift fractional
safety: the word `0011` has a positive time-zero tail but an empty fractional
guard. The full interval census below remains a separate oracle and theorem.
[Implementation and verification](../sprints/week-of-2026-09-27/antihydra-mahler.md#signed-mahler-current-tail-boundary).

### All-shift fractional intervals

The supplied September 20 research folder contains a separate, exact safety
result for real numbers. Write `x = D + t`, with `0 ≤ t < 1/2`. Safety through
`N` means `frac(x (3/2)^n) < 1/2` for every `0 ≤ n ≤ N`. It is equivalent to
the interval constraints

\[
D_n\le x(3/2)^n<D_n+1/2,
\qquad D_n=\operatorname{mahler\_orbit}(D,n).
\]

- **Finite cylinder classification:** 46 of the 64 integer-part residue
  cylinders are empty after six steps; 18 survive. The rejection includes
  every high fiber `D = r + 64k`, rather than only 64 individual integers.
- **Necessary all-time condition:** every scaled value of a candidate must
  have its integer part in one of the 18 surviving residue classes.
- **Uniqueness:** each half-unit cell contains at most one all-time candidate.
  This does not establish that it contains none.
- **Open obligation:** exclude all positive candidates, or supply one;
  the surviving residues are not a closed autonomous transition system.
  For example, sources `0` and `64` have the same initial residue, but their
  sixth iterates have residues `0` and `25`. Symbolic high-fiber information
  determines which transition is taken.

The adapted [safety theory](../../proofs/isabelle/integration/antihydra_mahler/mahler_safety/Mahler_Safety_Cylinders.thy)
uses the existing `mahler_orbit` and `mahler_D_step`, without duplicating the
source recurrence. [The 64 interval certificates](../../proofs/isabelle/integration/antihydra_mahler/mahler_safety/Generated_Mahler_Safety.thy)
are propositions replayed by Isabelle, not trusted numerical table entries.
Their upstream file hashes are recorded in their headers. The owning session
is `Mahler_Safety_Cylinders`; the [proof index](../proofs.md) gives its build.
The finite certificate session and oracle audits are checked; focused build
evidence remains distinct from aggregate release validation.

[Dated evidence](../sprints/week-of-2026-09-20/antihydra-mahler.md#original-mahler-safety-build-evidence).

**Predicate separation:** all `7 ≤ x < 7.5` fail fractional safety within two
steps, while the source-seven Antihydra ledgers at those steps are `0, 2, 4`.
[The separation theory](../../proofs/isabelle/integration/antihydra_mahler/mahler_safety/Mahler_Safety_Ledger_Separation.thy)
states this exact witness. Consequently `source_seven_not_Z` is neither a
halting witness nor a non-halting certificate for Antihydra. Production
certificate verification and its all-time source obligation remain unchanged.

Provenance: adapted from `outputs/antihydra_mahler_joint/proofs/` in the local
folder `referenced-chatgpt-conversation-this-is-an` dated 2026-09-20. Its
`SAFETY_PROOFS.md`, `REFINEMENT_STATUS.md` and `CAPABILITY_STATUS.md` explicitly
leave the source-to-branch bridge, global Mahler theorem and Antihydra
non-halting open. Later carry-transfer and tree-address experiments in that
folder also leave legal-continuation closure open. Their finite results are
not evidence of a checked global barrier.

## Joint source, prime and carry transport

The [source-safety prototype](../../devtools/experiments/antihydra/source_safety.py)
now constructs a block for the entire family
`x = r + 2^n k + t`, with natural `k` left symbolic. It retains the exact
half-open interval for `t`, the integer endpoint at `r`, the affine fractional
action, and the distinct ledger minimum/delta. It uses the existing
`SaturatingAffineAction`, primitive Antihydra arithmetic kernel and resource
ledger. An iterative worklist constructs requested source residues; no
diamond-tree event menu is supplied to it.

To compose blocks with endpoints `d` and `e`, it solves the routing equation

\[
d+3^n\ell=s+2^m h,
\qquad 0\le\ell<2^m.
\]

The composed input residue is `r + 2^n ℓ`, endpoint is `e + 3^m h`, and
its guard is the first interval intersected with the affine pullback of the
second. The solver checks the routing equation before publication. Empty
guards stay empty; equality at the lower bound remains admitted and equality
at the upper bound remains rejected. All parenthesizations are checked
against the same canonical source/extent key. This is an executable finite
research constructor, not a replacement production scheduler or a proved
arbitrary-horizon compression bound.

### Source-selected diamond events

For a positive centered source `D = 2^k u`, with `u` odd, the source parity
block is **k zeros followed by one**. Its length is `q = k + 1`. This differs
from the odd-then-zeros convention used by the earlier Hensel event observer.
With `w = 4t`, the exact affine endpoint and complete fractional guard are

\[
w'=(3/2)^q w-2,
\qquad 2\le(3/2)^q w<3.
\]

The guard checks intermediate times, not only the endpoint. The original
diamond tree's `(2,6)` guard for this scaled quantity is larger. At `w=1`,
`D=2` admits `q=2`, while `D=4` and `D=8` fail their source-selected `q=3`
and `q=4` prefixes. The `q=3` endpoint alone is inside the fractional-safe
interval, making it an explicit regression for omitted intermediate guards.
These are scoped source/guard comparisons, not a refutation of a complete
source cylinder or an identification of the archived difference-field root
with the Antihydra source.

The [transport theory](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Source_Cylinder_Transport.thy)
uses the existing `mahler_orbit` and proves source routing, chronological guard
composition, endpoint composition and arbitrary natural high-fiber transport.
The [event-safety theory](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Source_Event_Safety.thy)
states the exact source-selected event guard. Both belong to
`Mahler_Source_Transport`, a focused child of `Mahler_Safety_Cylinders`.
They formalize the mathematical constructor rules; they are not a proof of
the Python runtime, its full worklist implementation or a production CLI cutover.
Both transport theories have checked focused-session evidence; they do not
certify a production worklist or an arbitrary-horizon construction bound.

[Dated evidence](../sprints/week-of-2026-09-20/antihydra-mahler.md#source-cylinder-transport-build-evidence).

### Conditional prime and carry observations

[The joint observer](../../devtools/experiments/antihydra/source_observers.py)
reproduces the supplied 67 stable prime possibility buckets and uses the
compiler's actual multiply-by-three and pair-sum carry functions. Every lane
consumes the **same source-selected q**. The prime buckets do not independently
choose phases. Carry observations retain emitted-value and subtraction
dependencies, with an explicit column budget and work counters.

The imported prime bank applies to dyadic `w=A/2^Q`. Its exact action is
`A' = 3^q A - 2^(Q+q+1)`, with `Q' = Q+q`; prime-lane results are checked
against that same rational endpoint. The interval transport covers arbitrary
real `t`, but a residue of an arbitrary real number is not silently assigned
to this rational observer. No prime-bucket pruning of general real candidate
families has been justified. Bucket and carry equivalence are finite executable
checks, not a claimed Isabelle safety quotient.

### Bounded refinement and the all-time boundary

Use the existing search tool to compose only surviving source intervals:

```console
python -m devtools.experiments.antihydra.barrier_search --mode fractional --rounds 4 --max-nodes 100000
```

This covers all high fibers of every retained residue, without enumerating
every integer source. It reports work and partial results on budget refusal.
Its result remains `FINITE_PREFIXES_ONLY` or `BUDGET_EXHAUSTED`, never an
all-time safety or non-halting certificate.

The bounded refinement census preserves full high fibers but grows the
number of retained cylinders. It is finite constructor evidence, not a
compression theorem.

[Dated evidence](../sprints/week-of-2026-09-20/antihydra-mahler.md#fractional-refinement-census).

For every finite horizon `N`, the positive real `x_N=2^N` is safe through
`N`: each observed value is the integer `2^(N-n)3^n`. The witness changes
with `N`. Consequently extending a uniform finite census until all positive
sources disappear cannot complete the global proof. A source-dependent
well-founded exclusion or a realizable all-time invariant remains necessary.
The separate Antihydra ledger barrier also remains open.

### Reachable event grammar and candidate pumping

- **Implemented bounded construction:** [future_grammar.py](../../devtools/experiments/antihydra/future_grammar.py)
  extends the source-safety workspace. An edge labelled `q` restricts the
  *current* integer source to `2^(q-1) mod 2^q`, solves that restriction on the
  original high fiber, and intersects the complete chronological guard.
- **Joint observations:** deck, original high fiber, telescoping coefficients,
  diamond event, prime buckets, cyclotomic phases and multiplication/subtraction
  carry domains are bound to one concrete witness of the complete prefix.
  These observations remain projections; equality does not merge source clauses.
- **Exploration scope:** event exponents above the configured bound are reported
  `UNEXPLORED`. Samples are separate finite-family witnesses, not one common
  infinite source. The zero integer orbit has no first odd event and is outside
  this positive-integer event grammar.
- **Cost status:** binary repetition composes a supplied clause through the
  existing workspace. This does not discover an arbitrary future word cheaply.
  Carry readouts remain explicitly bounded references and are evaluated only
  when requested. Source blocks, edge retention, operand sizes, phase work and
  witness construction have counters; no arbitrary-horizon compression bound
  or complete Python allocator bound is claimed.

For a width-`L` clause with canonical source residue `r` and endpoint `d`, set

\[
P=3^L,\quad Q=2^L,\quad J=Qd-Pr\ge0.
\]

Its concretization retains every natural high fiber and the exact half-open
fractional guard `I`:

\[
\Gamma=\{r+Qk+t:k\in\mathbb N,\ t\in I\},\qquad
D'=(PD+J)/Q,\quad t'=(Pt-J)/Q.
\]

The event edge is a source restriction, not authorization to choose `q`
independently in the different observers. Cyclotomic lanes use the common
composed map `u'=P/Q*u-2J/Q` for `u=2t`. A rational fixed point is reduced
modulo a research-bank prime only when its denominator is invertible; otherwise
that lane is unavailable. Multiplier order and full affine order are separate:
when the multiplier is 1 and the translation nonzero, the affine order is the
prime itself. These conditional rational observations do not prune
arbitrary real members of `I`.

**Repetition obstruction.** A fractional cycle alone cannot admit a pump.
Define `H=(P-Q)D+J` for a positive integer source. Repeating the *same complete
clause* `n` times requires

\[
Q^n\mid H.
\]

Indeed `Q H(D')=P H(D)`, and `P,Q` are coprime. Here `H>0`, so arbitrary
repetition is impossible. The executable necessary bound is
`n <= floor(v2(H)/L)`. Independent bounded parity references also check the
reported maximal repetition count. This statement concerns a literal repeated
finite parity block. It does **not** exclude parameter-changing pumps, aperiodic
safe paths, or a quotient whose shared structure carries a changing source
parameter.

For example, the `q=3` clause has `P=27`, `Q=8`, `J=4`. Its fractional fixed
point `t=4/19` satisfies the full clause guard and survives every repetition of
that abstract fractional map. Starting at integer `D=4`, however, `H=80` gives
only one admitted repetition. The next source is `14`, which selects `q=2`.
Every finite repeated-clause cylinder can still have other positive witnesses;
changing those witnesses is precisely the source escape a pump must rule out.
The prime-19 fixed-point lane is unavailable because the denominator is 19,
not evidence of a vanishing residue. Its multiplier order is 1, but its
nonzero translation has affine order 19.

[Mahler_Reachable_Repetition.thy](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Reachable_Repetition.thy)
formalizes the telescoping obstruction and applies it to the existing
`mahler_orbit`, under the exact source-clause equation checked by the executable
constructor. It does not formalize the Python valuation routine, prove a general
future-language quotient, or decide original Mahler safety. The public CLI and
Antihydra ledger/non-halting gates are unchanged.

Reproduce the bounded grammar and its joint finite witnesses with:

```console
python -m devtools.experiments.antihydra.barrier_search --mode grammar --rounds 4 --max-event 4 --max-nodes 100000
python -m devtools.checks.release --suite unit --select tests/validation/proofs/test_mahler_future_grammar.py
```

Finite grammar validation includes supplied-word powering and exact source
obstructions. Larger event exponents remain unexplored; the source-seven
certificate and reverse/add construction failures were retained.

[Dated evidence](../sprints/week-of-2026-09-20/antihydra-mahler.md#reachable-grammar-validation-evidence).

**Open construction:** find and verify a parameter-transport rule preserving
source realizability, chronological guards and subsequent consumers through
all repetitions. No cycle in a derived carry/prime/fractional view is promoted
to that rule by this search. A successful general grammar closure and its
construction bound remain obligations, as they do for the unfinished 196
pumped grammar.

## Production and reproduction

### Source parameters and finite safe/fail queries

The reachable grammar now retains each edge's high-fiber map explicitly.
For a prefix of width `L` followed by a source-selected event of width `q`,
the original free parameter restricts to `lift + 2^q*j`, and its value at the
event boundary becomes `high + 3^L*j`. The retained child residue and endpoint
must agree with these same maps. Prime, carry and cyclotomic readouts remain
projections of this admitted family; matching one witness does not merge two
families.

The finite transport model spells out the computed modular lift, high fiber
and strict affine interval pullback in
[`Mahler_Source_Cylinder_Transport.thy`](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Source_Cylinder_Transport.thy).
Its executable route theorem consumes an explicit inverse and the same
inverse/routing checks as the constructor. It does not prove Python's modular
inverse algorithm, the entire deterministic worklist, or the cost of discovering
the next source event. Those distinctions remain part of the proof boundary.

**Implemented finite production-algebra bridge:** `SourceBlock.skew` now uses
the production `SkewTransfer` type. Chronological source construction calls
its `then` operation, and the fractional affine action is derived from that
same transfer. Leaves reuse the production Antihydra arithmetic kernel.
The chart `a=D+1` sends centered residue `r` and high fiber `k` at precision
`N` to `((r+1) mod 2^N, k+(r+1) div 2^N)`; the wrap at the all-ones residue
is retained. `centered_finite_cylinder_conjugacy` in the same theory proves
the finite orbit identity, including the moving high fiber for every `n<=N`.
Bounded differential tests compare all residues through eight bits, all their
chronological splits, and selected 16/32/64-bit cylinders with the production
`ArithmeticCylinder`. Separate witnesses prevent equating fractional safety
with physical ledger admission. This connects actual arithmetic construction;
it does not yet make the research worklist a production scheduler adapter or
construct the proposed multiplication macrotiles.

`finite_repeated_clause_transport` composes a supplied finite event clause and
retains its half-open guard. This is **finite reparameterization**, not an
invariant pump: repetitions of the `q=3` clause select original source classes
`4+8j`, `20+64j` and `404+512j`. Binary composition uses logarithmically many
combines, while the exact integers require linearly growing bit storage.

`first_failure` checks a fixed source and fractional coordinate against a
finite admitted block. It skips a safe block or descends to the first failing
child. Discovery of a previously unbuilt child remains charged. A reported
failure residual is relative to the canonical ceiling-integer trajectory;
after failure it need not be the ordinary fractional part. Research workspaces
and grammars now expose idempotent disposal and invalidate disposed handles.

The repetition theory also excludes an eventually repeating finite parity
word for a positive integer source. This does not exclude nonperiodic future
grammars. Total finite safe/fail coverage does not require every source to
survive forever: compact construction of source-derived changing events,
complete executable refinement, and all-time safety are distinct obligations.

### Spatial carry pumping and shared safe kernels

For a radix block of modulus `b`, value `u`, and multiplier `M`, write
`M*u = q*b+r`. Its complete multiplication effect on an incoming carry `c` is
`emit(c)=(r+c) mod b`, `carry(c)=q+(r+c) div b`. Both results are retained in
the [spatial constructor](../../devtools/experiments/antihydra/spatial_carry.py).
The carry function alone is insufficient: multiplying base-64 blocks 0 and 1
by 3 has the same all-zero outgoing carry map, but different emitted blocks.
For multiplier 729 on one base-64 limb there are more than two possible
outgoing carries; the implementation uses the general floor-affine map.

**Checked spatial pumping theorem:** once an identical repeated block has a
fixed carry `M*u+c=e+b*c`, then for every repetition count `n`,
`M*repeat_b(u,n)+c = repeat_b(e,n)+b^n*c`. The emitted numeral lies below
`b^n`, so this certifies both complete output and outgoing carry. See
`spatial_fixed_carry_repeat_complete` in
[`Mahler_Spatial_Carry_Pump.thy`](../../proofs/isabelle/integration/antihydra_mahler/mahler_transport/Mahler_Spatial_Carry_Pump.thy).
It applies to supplied repeated spatial blocks, not repeated temporal events.

**Transient bound, proof sketch:** write `M*u=(b-1)h+s`. After `n` identical
blocks the carry is `h+floor((c-h+s*(1+b+...+b^(n-1)))/b^n)`.
If `s>0`, a geometric sum at least `M` puts this at `h`; if `s=0`, the
eventual value is `h` or `h-1` according to the incoming side. Thus
`ceil(log_b M)+1` is sufficient for valid ports. The implementation checks
the actual fixed point before publishing a repetition; the logarithmic
transient bound itself is not yet an Isabelle theorem. Finite tests cover all
64 one-limb values and all incoming ports for multipliers 3 and 729; supplied
repetitions of length `10^12` need at most two or three transient steps in the
tested cases. This helper is not yet a production source-SLP consumer.

**Implemented safe-consumer sharing:** `ReachableFutureGrammar.first_failure`
uses interned translated safe-block kernels. Finite width-6, 8 and 10 censuses
contain respectively 18, 40 and 90 live source occurrences but only 12, 18 and
26 shared kernels. All source blocks and failure paths remain retained; these
counts measure reuse of derived kernels, not a reduction in total baseline
storage or a bound on future grammar growth. At width 4, residues 5 and 14
share a normalized safe kernel, yet fractional input zero first fails at
steps 1 and 2. This regression prevents treating safe-kernel equality as
complete future equivalence. The translated interval/output identities are
checked in the same spatial theory.

### Exact next-event range before child construction

The [event-domain constructor](../../devtools/experiments/antihydra/event_domain.py)
transports the admitted block's fractional guard to its endpoint, then uses
`w=4t` on `[l,u)`. A positive exponent `q` has a nonempty chronological guard
exactly when `2*(2/3)^q < u` and `l < 3*(2/3)^q`. The intersection criterion
is checked by `event_exponent_interval_admission` in the spatial theory.
The exponent predicates are monotone, so charged exact cross-products and
binary search return one contiguous integer range. A zero lower endpoint
gives an exact unbounded tail; a positive lower endpoint gives a finite upper
bound. This does not choose `q` for a fixed source: each demanded child still
requires the source-congruence construction.

The research search applies this range before child construction, avoiding
provably empty children. Bounded differential and poison tests support the
implementation; complete binary-search worklist refinement and all-time
closure remain open.

[Dated evidence](../sprints/week-of-2026-09-20/antihydra-mahler.md#next-event-domain-pruning-measurements).

## Primary literature and a mixed-coordinate grammar

Research review: 2026-09-20. These external results guide the next construction;
they have not been imported as Isabelle axioms or promoted to source-7 safety.

| Primary paper | Applicable result | Integration boundary |
| --- | --- | --- |
| Kopra, [Multiplication cubes and multiplication automata](https://arxiv.org/pdf/2211.15293), Theorems 4.11, 4.40 and Corollary 4.41 | Valid multiplication tessellations have endpoint-dependent path integrals. Natural-matrix macrotiles give surjective factors, and conjugacies when every row participates. | A mixed `(2,3)` tessellation is a candidate spatial owner for multiplication by `3/2`; admissible tiles and complete boundary labels must first be connected to our actual source transport. Endpoint integrals alone do not determine the interior or its first failure. |
| Kopra, [On the Trace Subshifts of Fractional Multiplication Automata](https://arxiv.org/abs/2005.05112) | For coprime `p>q>1`, multiplication by `p/q` in base `pq` has a trace conjugate to rational-base numeration; the full trace is not synchronizing and is not sofic. | Rules out an unrestricted finite-state presentation of that trace language. It does not rule out a parameterized source grammar, a restricted source trajectory, or compact finite blocks. |
| Akiyama–Frougny–Sakarovitch, [Powers of rationals modulo 1 and rational base number systems](https://perso.telecom-paristech.fr/jsaka/PUB/Files/RBNS-rev.pdf), Proposition 13 in this PDF | For coprime `p>q>1`, conversion from a fixed finite digit alphabet containing the canonical alphabet uses a finite sequential right transducer, with letter-to-letter transitions and a final-output function. The canonical integer language is nevertheless nonregular. | Supplies an independent spatial normalization specification after proving the encoding. It is not already the repository's binary or radix-64 transducer, and says nothing by itself about source-safe temporal pumping. |
| Akiyama–Marsault–Sakarovitch, [On subtrees of the representation tree in rational base numeration systems](https://arxiv.org/abs/1706.08266) | Source-rooted subtrees are distinct; branch evaluations form intervals, and bottom-word succession uses an infinite sequential transducer. | Supports retaining the source parameter alongside interval guards and high-fiber transport. Sharing normalized arithmetic does not identify source-tree nodes. |

The multiplication-cube paper also gives a precise encoding constraint
(Theorem 5.14): on the full two-sided configuration spaces, a continuous
value-preserving map from base `N1` to base `N2` cannot exist if `N2` has a prime
factor absent from `N1`. Thus a base-64 observer cannot be assumed to provide
a local, value-preserving base-6 reconstruction on that whole space. This
does **not** forbid exact conversion of finite source integers or a proved
restricted-source encoding. It does require an explicit bridge before a
radix-64 packet is used as authority for the mixed-coordinate dynamics.

### Next executable refinement target

The proposed research object is a source-bound mixed-coordinate macrotile,
not an observer-class identifier. It must retain:

- the exact source occurrence and rectangle/chart in the `(2,3)` lattice;
- compatible boundary labels and an admitted multiplication-tile derivation;
- the strict safe/fail guard, high-fiber affine transport and event extent;
- a shared interior derivation or equivalent complete consumer action that
  preserves first-failure descent; boundary integrals alone are insufficient.

Spatial composition must prove boundary agreement and tessellation validity.
Temporal composition must also prove that the transported source and guard
select the actual next event. The existing `FiberTransport` and exact
`event_domain` are components of this bridge; they do not yet construct these
macrotiles. A paper's macrotile factor map does not bound the work needed to
discover a source's demanded tile.

Only after this refinement should radix-64 Hensel/carry views be obtained as
demanded projections of the admitted object. A repetition certificate must
transport the positive source parameter and strict guard for every admitted
repeat count. A periodic fractional trace alone is insufficient. Mahler
positivity, Antihydra ledger safety and all-time non-halting remain separate
predicates and obligations.

- **Implemented owner:** [sequences/antihydra/arithmetic_images.py](../../src/number_compiler/sequences/antihydra/arithmetic_images.py).
- **Checked theorem:** the repository Isabelle results named earlier apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits. They do not yet refine the proposed mixed-coordinate tile or formalize the external papers.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Composed arithmetic and retained projection fragments do not prove cheap all-time source discovery or non-halting.

Run the current support/projection checks (including validation-marked assertions).
These do not validate the proposed mixed-coordinate bridge:

```console
python -m devtools.checks.release --suite unit --select tests/api/test_antihydra_support_cache.py --select tests/api/test_antihydra_projection_occurrences.py
```

## Demanded history and the shared joint-adic chart

Arithmetic and Mahler consumers use the authenticated aggregate without copying
chronological segments. Physical/support demands retain those segments' source,
overwrite and first-failure checks. Zero copied segments is not zero retained
source support or zero construction work.

`source_macro_projection_correct` and `six_step_constant_three_lift` prove
finite endpoint/gain projection and six-step high-fiber multiplier 729.
`six_step_three_adic_high_fiber_forgetting` removes its contribution modulo
`3^h` for `h<=6`. It does not remove the integer high fiber, source-selected
offset or fractional guard. These projections cannot authorize successor
substitution or an all-time certificate.

[Implementation and validation record](../sprints/week-of-2026-09-20/antihydra-mahler.md#demanded-history-and-the-shared-joint-adic-chart).

## Recovered bounded tree-choice observer

The shared [branch quotient algebra](../../src/number_compiler/arithmetic/fields/branch_quotients.py)
retains at most six sibling indices from `{1,2,3}`. Length plus ternary code
preserves leading choice-1 symbols, giving 1,093 encodings. Composition keeps
the last six symbols; it neither selects an unbounded `q` nor admits an edge.

The 67 Mahler buckets sum 20 prime-lane partitions, not their joint product.
Sources 3 and 7 share a mod-5 bucket and Collatz gap 1, but targets 5 and 11
have different buckets. This rejects that single observer as a deterministic
successor identity. Archived suffix/bucket experiments also had continuation
conflicts; injectivity after adding supplied menu data did not prove closure.

The combined source-bound experiment is now implemented, with its limited
scope stated [above](#joint-future-observer-experiment). The earlier proposal
and archive audit are retained in the dated record. The shared minimum-prefix
and affine-threshold actions preserve the distinction between Mahler positivity
and Antihydra ledger safety.

[Implementation and validation record](../sprints/week-of-2026-09-20/antihydra-mahler.md#recovered-bounded-tree-choice-observer).

## Safety residual versus occurrence ports

For the finite Mahler safety consumer, the semantic residual is `FORBIDDEN`,
positive infinity at the empty prefix, or the exact positive rational margin.
An appended bit acts by
`m' = min(c_e, 3/2 (m-e))`, with `c_0=9/4`, `c_1=3/4`.
Nonpositive margins are forbidden, including equality at zero. The nonpositive
offset of every Mahler bit action makes failure absorbing under continuation.

**Implemented research construction:** the source-cylinder workspace now
composes this predicate action using the production `SaturatingAffineAction`
owner. Source residue, deck/lift and recursive occurrence ports remain
separate. Equal margins can have different ports without contradicting
right-congruence for the safety consumer. The public source-seven observer
already uses the same action algebra; this change does not add a second
production executor.

**Scope:** exact rational margins do not establish a finite all-depth state
bound. The downloaded depth-500 counts and the first-lift-bit repair concern
their finite corpus, not an unconditional Mahler or Antihydra safety theorem.
Those reports do not replace the source-global reachability obligation.

[Independent recurrence checks and patch audit](../sprints/week-of-2026-09-27/shared.md#recursive-dyadic-report-integration).
