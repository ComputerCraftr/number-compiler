# Antihydra arithmetic, literal machine, and Mahler action

Status: **finite arithmetic and demanded-cylinder laws are checked; the
source-7 all-time barrier and complete literal/macro refinement remain open**.

Antihydra has three related semantics that must remain distinct: the total
arithmetic family, the guarded ledger computation, and the literal six-state
machine. Mahler/Hensel outputs are projections of authenticated arithmetic
source data; they are not alternate evidence that the literal machine never
halts.

## Reading guide

- **Definitions:** total arithmetic starts at `a=8` and applies `a <- a + floor(a/2)`. The ledger starts at zero and changes by `+2` for even `a`, `-1` for odd `a`; centered state is `D=a-1`.
- **Checked theorem:** finite arithmetic composition and minimum-prefix guards preserve their stated semantics.
- **Implemented construction:** arithmetic images and demanded support fragments retain source authority; guarded physical execution remains a separate consumer.
- **Open obligation:** source-7 non-halting, complete literal/macro refinement and arbitrary-horizon retention bounds remain unresolved.

## Checked arithmetic and cylinders

[`Antihydra_Family_Iteration.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Family_Iteration.thy)
proves the total skew equation, centered orbit, block composition, exact minimum
prefix guard, and guarded agreement before the first failed block. The latter is
conditional on remaining before failure and does not prove all-time safety.

[`Antihydra_Arithmetic_Cylinder_Lift.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Arithmetic_Cylinder_Lift.thy)
identifies family bits with a dyadic source word and proves exact demanded
cylinder composition, split, bit, and ledger projections. These results assume
the admitted arithmetic source; they do not generate a literal macro word.

[`Antihydra_Mahler_Skew.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Mahler_Skew.thy)
proves centered return, numerator and minimum-prefix composition, and the
one-return kernel coefficients. The associated-action refinement
[`Antihydra_Mahler_Associated_Action.thy`](../../devtools/proofs/isabelle/integration_mahler/Antihydra_Mahler_Associated_Action.thy)
proves source coefficients determine the defined Mahler action. It also proves
that the centered word `11` has distinct Mahler and ledger outcomes, so a Mahler
failure must not be reported as Antihydra halting.

## Shared Collatz F5 spatial action: checked transfer

The September 21 [Collatz spatial patch](collatz.md) applies to the centered
Antihydra/Mahler coordinate through the **same production carry/F5 owner**:
[`collatz_f5_quotient.py`](../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py).
No second F5 alphabet or source recurrence is needed.

- **Exact arithmetic:** for `D=a-1`, the next centered state is
  `D' = floor((3D+1)/2)`, and the next Antihydra value is `D'+1`.
  This also holds for even `D`; the extra one is discarded by division.
- **Spatial projection:** a radix-64 cell uses the same five complete
  multiplication carry actions on incoming ports `0,1,2`. The joint
  carry/phase leaf alphabet has 15 classes and its spatial compositions reach
  17. The phase is the additive sum of the fixed incoming-one leaf `phi5`
  observations. It is **not** the whole numeral's carry jet, and actual
  inter-cell carries still travel through the complete carry action.
- **Division boundary:** the existing directional F5 views pair adjacent raw
  multiplication outputs after a one-bit shift. They observe the exact next
  centered cell without identifying its source with a class ID.
- **Conditional spatial pumping:** a supplied repeated block can use shared
  binary composition. The new tests power every radix-64 leaf through
  `5^64` spatial repetitions and compare all three carry ports with Mahler's
  independently checked fixed-carry compression. Composition count is
  `bit_length(n)-1+bit_count(n)`; no repeated numeral is expanded.

The [spatial theory](../../devtools/proofs/isabelle/mahler_transport/Mahler_Spatial_Carry_Pump.thy)
adds `mahler_spatial_low_block_transport` and
`antihydra_centered_spatial_low_block_transport`. For `D=u+2bv`, write
`e=(3u+1) mod 2b` and `c=(3u+1) div 2b`. They prove

\[
D'=\lfloor e/2\rfloor+b(3v+c),\qquad a'=D'+1.
\]

At radix 64, `b=32`. This transports both the emitted block and its high
boundary, for arbitrary high part `v`. It reuses the existing centered-step
and carry-conservation lemmas. The owning `Mahler_Source_Transport` session
passed its oracle audits on September 21 in 8.81 seconds with 1,672,236,704
sampled peak bytes, within the unchanged 35-second/4-GiB limit. These are
checked arithmetic transport lemmas, not a formal refinement of the Python
F5 tables or a complete temporal constructor.

The [production bridge tests](../../tests/validation/proofs/test_mahler_f5_production_bridge.py)
check every two-cell residue at both a small high fiber and `2^80+37` against
`admitted_arithmetic_cylinder`. They also compare spatial carry actions with
the independent Mahler multiplier reference and preserve the observer
collision `67,75 -> 101,113`. That collision concerns the reduced spatial
observation, not the complete source-bound cylinder.

**Temporal boundary:** for an odd centered source `U` and
`a=v2(3U+1)`, Antihydra's next odd event is

\[
U'=3^{a-1}(3U+1)/2^a,\qquad E'=E+3-a.
\]

The extra `3^(a-1)` distinguishes it from an ordinary accelerated Collatz
event. Bounded tests compare this law, the actual parity word, and the
minimum-prefix ledger with production cylinders for every odd source from
5 through 4095. The fractional-safe guard remains a separate consumer.
Neither the 17 spatial classes nor fast powering of a supplied repeated
block proves a source-compatible temporal grammar, a CLI speedup, Mahler's
global exclusion, or the Antihydra source-7 barrier.

Reproduce the bridge with:

```console
python -m pytest -q -o addopts='' tests/validation/proofs/test_mahler_f5_production_bridge.py tests/validation/proofs/test_mahler_centered_production_bridge.py tests/validation/proofs/test_mahler_spatial_carry.py
isabelle build -d devtools/proofs/isabelle Mahler_Source_Transport
```

Local validation evidence and its source fingerprint are retained under
`results/current/mahler-f5-bridge-2026-09-21/`. Historical measurements do not
certify subsequent edits or the aggregate release.

## Literal and barrier boundary

[`Antihydra_Literal_TM.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Literal_TM.thy)
checks startup and the exact halt boundary.
[`Antihydra_Macro_Grammar.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Macro_Grammar.thy)
proves length, shift, directional clock, and admitted terminal cases for supplied
macro words. The missing bridge is a source-generated macro word with reads,
overwrites, startup invariant, powered image, and first-failure refinement.

[`Antihydra_Source_Barrier.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Source_Barrier.thy)
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

The blank source's 1,024-step measurement still constructs 31 distinct support
nodes with no complete-effect reuse. General F5-based normalization across its
changing source residues remains an open construction obligation; the positive
aligned-source result does not close it.

Finite `--nth` arithmetic and selected projections are available with bounded
ownership. Reusing retained parity avoids rediscovery, but folding every
retained step is still linear in the represented source. Batch aliases share
one authenticated discovery result; Hensel and Mahler packets remain distinct.

Finite bounded barrier searches and observed nonhalting prefixes are evidence
only. They neither prove all-time nonhalting nor refute a future source-global
certificate.

## Original Mahler fractional safety

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

The adapted [safety theory](../../devtools/proofs/isabelle/mahler_safety/Mahler_Safety_Cylinders.thy)
uses the existing `mahler_orbit` and `mahler_D_step`, without duplicating the
source recurrence. [The 64 interval certificates](../../devtools/proofs/isabelle/mahler_safety/Generated_Mahler_Safety.thy)
are propositions replayed by Isabelle, not trusted numerical table entries.
Their upstream file hashes are recorded in their headers. The owning session
is `Mahler_Safety_Cylinders`; the [proof index](../proofs.md) gives its build.
**Checked theorem status:** the integrated session passed on 2026-09-20 in
22.36 seconds under the unchanged 35-second/4-GiB guard, including its oracle
audits. Local evidence is `results/current/mahler-safety-integration-2026-09-20/`
(`final-build.log` and `final-build.json`). This is focused proof
evidence, not an aggregate release result.

**Predicate separation:** all `7 ≤ x < 7.5` fail fractional safety within two
steps, while the source-seven Antihydra ledgers at those steps are `0, 2, 4`.
[The separation theory](../../devtools/proofs/isabelle/mahler_safety/Mahler_Safety_Ledger_Separation.thy)
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

The [transport theory](../../devtools/proofs/isabelle/mahler_transport/Mahler_Source_Cylinder_Transport.thy)
uses the existing `mahler_orbit` and proves source routing, chronological guard
composition, endpoint composition and arbitrary natural high-fiber transport.
The [event-safety theory](../../devtools/proofs/isabelle/mahler_transport/Mahler_Source_Event_Safety.thy)
states the exact source-selected event guard. Both belong to
`Mahler_Source_Transport`, a focused child of `Mahler_Safety_Cylinders`.
They formalize the mathematical constructor rules; they are not a proof of
the Python runtime, its full worklist implementation or a production CLI cutover.
**Checked theorem status:** both theories passed Isabelle and their oracle
audits on 2026-09-20. The focused child-session build took 7.56 seconds under
the unchanged 35-second/4-GiB limit. Local evidence is
`results/current/mahler-joint-transport-2026-09-20/final-proof.log` and
`final-proof.json`; the earlier six-step certificate session is its checked
parent.

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

The four-round run on 2026-09-20 retained 18, 201, 2,291 and 26,111 nonempty
cylinders at horizons 6, 12, 18 and 24. It constructed 45,259 retained blocks
in 1.05 guarded seconds, with a sampled peak of 57,639,440 bytes. Twelve-step
classes were exhaustively compared with an independent rational reference;
the larger census is composed-constructor evidence. Work counters include
composition attempts, source worklist visits, memo reuse, operand bits and
retained integer bits. They are not a complete Python allocator model or a
proved arbitrary-horizon complexity bound. Evidence is the local
`results/current/mahler-joint-transport-2026-09-20/validated-refinement.log` and
`validated-refinement.json`.

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

[Mahler_Reachable_Repetition.thy](../../devtools/proofs/isabelle/mahler_transport/Mahler_Reachable_Repetition.thy)
formalizes the telescoping obstruction and applies it to the existing
`mahler_orbit`, under the exact source-clause equation checked by the executable
constructor. It does not formalize the Python valuation routine, prove a general
future-language quotient, or decide original Mahler safety. The public CLI and
Antihydra ledger/non-halting gates are unchanged.

Reproduce the bounded grammar and its joint finite witnesses with:

```console
python -m devtools.experiments.antihydra.barrier_search --mode grammar --rounds 4 --max-event 4 --max-nodes 100000
python -m pytest -o addopts='' tests/validation/proofs/test_mahler_future_grammar.py
```

**Validation (2026-09-20):** the bounded event search at depths 1–4 and
`q <= 4` retained 4, 12, 24 and 48 source families. It found respectively
2, 4, 8 and 16 fractional-cycle clauses; these are word candidates, not a
count of distinct cyclotomic orbits. The source obstruction prevents each
from becoming an all-time positive-source repetition. The run retained 167
source blocks and 498 ledger entries in 0.19 guarded seconds. Larger events
remain unexplored. A separate poison test composes 512 copies of a supplied
three-step clause with 10 compositions and no new source-leaf discovery;
this is a supplied-word result, not arbitrary future discovery.

The focused Isabelle session and its oracle audits pass. The selected Python
checks have **220 passes and two retained release failures**: the existing
196 powered-construction failure exposed by the proof-import firewall test,
and the missing source-seven non-halting certificate. All 18 new grammar
checks pass. Full strict typing, Ruff, formatting, repository policy and
proof/documentation indexes pass. Evidence is local under
`results/current/mahler-future-grammar-2026-09-20/` (`validated-*` and
`validation_scope.json`), on authored-source fingerprint
`18d66988222d91c9b0c12cc06b1d44318a36e6950dc9d0ebdf1554f987f5deb9`.
The full suite and aggregate all-session release validation were not rerun.

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
[`Mahler_Source_Cylinder_Transport.thy`](../../devtools/proofs/isabelle/mahler_transport/Mahler_Source_Cylinder_Transport.thy).
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
[`Mahler_Spatial_Carry_Pump.thy`](../../devtools/proofs/isabelle/mahler_transport/Mahler_Spatial_Carry_Pump.thy).
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

The canonical research `barrier_search --mode grammar` now uses this domain
before constructing children. In the four-level, `q <= 4` comparison, both
versions retain 4, 12, 24 and 48 reachable families, but domain pruning avoids
76 empty children. Source blocks fall from 167 to 91 and entries from 498 to
270; composition attempts fall from 168 to 92. Domain work adds 129 exact
comparisons and 1,498 summed operand bits. Finite witness and cycle-observer
results agree. A poison test rejects construction of any excluded child.
These are measured bounded reductions; the unexplored larger-event frontier
and all-time claims remain open. The binary-search implementation has bounded
differential tests, not a complete Isabelle worklist refinement.

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
python -m pytest -o addopts='' tests/api/test_antihydra_support_cache.py tests/api/test_antihydra_projection_occurrences.py
```

## Demanded history and the shared joint-adic chart

Antihydra arithmetic results and Mahler associated actions now consume the
same authenticated dyadic summary without copying its chronological segments.
`AntihydraArithmeticTerm.segments` is an explicit lazy demand; physical and
support observations still obtain the exact bounded cylinders. A failed
segment publication releases its new entries and can be retried without
invalidating the arithmetic result. Payload audits inspect retained state
without causing materialization.

The Mahler source-prefix check uses the pinned source `h=8`, centered `D=7`,
source precision and arithmetic law. It does not trust a caller-supplied odd
state or rebuild the segment sequence merely to check the initial `11`.
Mahler's existing associated-action projection remains distinct from the
Antihydra ledger predicate.

`source_macro_projection_correct` and `six_step_constant_three_lift` prove
finite endpoint/gain projection and the six-step high-fiber multiplier 729.
`six_step_three_adic_high_fiber_forgetting` proves its contribution vanishes
modulo `3^h` when `h <= 6`. This does not remove the integer high fiber, the
source-selected offset, or the fractional-safety guard. The shared Collatz
carry/F5 observer and Mahler prime/deck restrictions remain projections with
their existing admission conditions. They are not interchangeable source
identities or an all-time safe/fail certificate.

Tests poison segment extraction during public digit, Mahler, metrics and
payload-audit queries. Explicit physical/support demands retain their source,
overwrite and first-failure checks. Python construction/refinement and a global
source-compatible safety invariant remain separate obligations.

At fingerprint `6560841b95ca428e64f941235defc4318cec58b9cfe2f56e9cec7086a894443d`, the 1,024-return probe retained zero copied
segments after digits and after Mahler demand. Explicit segment demand created
16 entries and validated all 16. Total ledger nodes were 7,266 after digits,
8,169 after Mahler and 8,185 after segment demand. Underlying authenticated
source support remains counted; zero copied segments is not zero retained
source history or zero construction work. The endpoint matched an independent
bounded recurrence. Evidence is local under
`results/current/joint-cylinder-2026-09-22/`.
