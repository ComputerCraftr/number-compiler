# Reverse/add source-bound temporal construction

Status: **component arithmetic and restricted clauses are checked; the generic powered constructor is not complete**.

This synthesis is the maintained research account for decimal reverse/add and
the powered 196 cutover. It keeps source authority, forcing bases, carry
direction, radial sign extraction, temporal closure, and restricted chambers
in one place so a component theorem cannot be mistaken for the final result.

## Reading guide

- **Definitions:** `P` is the symmetric pair field, `Delta = P - 9 E_m` its centered residual, and `beta` the carry-induced innovation. The derivative `(1-z)Delta` is a different object.
- **Checked theorem:** local carry, normalization, radial transport and supplied-word transduction have the scoped proofs below.
- **Implemented construction:** authenticated primitive publication and restricted clauses are available; carry moves only from LSD to MSD.
- **Open obligation:** construct the source-derived compressed residue grammar and its complete temporal return with successful work and storage bounds.

## Source authority and publication

### Admitted source pair

For the decimal reverse/add source, a pair cell is

\[
P_j = x_j + x_{m-1-j},\qquad 0\le P_j\le18.
\]

The carry is physical and directional:

\[
c_0=0,\quad y_j=(P_j+c_j)\bmod 10,\quad
c_{j+1}=\lfloor(P_j+c_j)/10\rfloor.
\]

`source_prefix_step` in
[`Cylinder_Source_Coboundary.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_Source_Coboundary.thy)
uses the explicit premise `j < length ss`. `source_pair_valid_of_valid_pair`
requires the source digits to satisfy the digit predicate; its 196 corollary is
specialized to that valid source. `source_coboundary_emit` assumes both source
validity and the index bound before identifying the emitted digit with the
source coefficient plus the carry coboundary.

[`Cylinder_Source_Publisher.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_Source_Publisher.thy)
proves support, symmetry, normalization, and `source_cylinder_next_step` for a
valid source pair. The theorem is a one-step publisher. It does not recursively
build the next admitted source object.

### Arithmetic objects and authority

The symbolic innovation arena transports exact expressions through reflection,
translation, doubling, addition, and residue projection. The corresponding
identities in
[`Cylinder_Innovation_Transport.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_Innovation_Transport.thy)
are unconditional algebraic equalities. They do not prove that an arbitrary
arena node is a source occurrence.

Source authority therefore travels separately from the expression. A complete
certificate must bind at least:

- the original source atom and its occurrence;
- orientation and chart;
- radial exponent and precision;
- both exterior carry ports;
- active extent and growth seam;
- all thirteen typed output channels used by the next publisher.

The complete-interface model in
[`Reverse_196_Complete_Interface_Substitution.thy`](../../devtools/proofs/isabelle/temporal_clocks/Reverse_196_Complete_Interface_Substitution.thy)
proves simultaneous substitution reads one frozen environment and preserves
channel order and count. `reverse_196_two_publisher_steps_refine_two_steps`
assumes a valid source pair. These are refinement laws for an admitted packet,
not a constructor that produces every later packet.

### Checked implementation boundary

The installed code has exact source atoms, source carry ports, symbolic local
channel substitution, and rejection for stale or foreign handles. Arithmetic
projections may forget dependencies after an exact cyclotomic annihilation, but
that forgetting does not create source authority.

The missing theorem and implementation are one constructive statement: from an
admitted source occurrence, build the complete next temporal packet, prove it
has the source provenance listed above, and bound construction, demand, and
retained memory without evaluating the represented digit interval.

### Scope of negative results

Failures of an expression-only normalizer show that the attempted
representation was incomplete. They do not refute the complete source-bound
cylinder. Likewise, a local channel equality or polynomial identity cannot
authorize temporal substitution when extent, ports, orientation, or source
occurrence are absent.

## Forcing bases and live reduction

### Keep the bases distinct

Let `P` denote the pair field, let `beta` denote its forcing innovation, and let

\[
H=(1-z)\Delta
\]

denote its discrete derivative. The seven-symbol forcing alphabet belongs to
`beta`. It must not be silently assigned to `H`; integration would require a
modular prefix state in addition to the carry state.

[`Cylinder_Forcing_Alphabet.thy`](../../devtools/proofs/isabelle/temporal_forcing/Cylinder_Forcing_Alphabet.thy)
proves:

- `forcing_no_growth_beta_in_alphabet` for source values bounded by 18;
- `forcing_no_growth_values_exact` for the exact no-growth values;
- `forcing_growth_beta_in_alphabet` for inputs `x,y <= 18`;
- `forcing_beta_difference_alphabet_exact` for the separate derivative
  alphabet.

The explicit theorem `reverse_196_beta_difference_counterexample` rejects one
incorrect identification of the derivative alphabet with the beta alphabet.
Its scope is exactly that identification. It is not a counterexample to a
complete cylinder with a valid integration state.

### Live modular reduction

At `bits` bits of precision, radial terms can be discarded only under the
stated divisibility assumptions. In
[`Cylinder_Live_Forcing_Reduction.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_Live_Forcing_Reduction.thy),
`live_radial_scale_pruned` assumes `bits <= q`; `live_exponent_bounds` assumes
`q < bits` and `r <= 3 * (q + 1)`. The resulting
`live_growth_certificate_bounds` is therefore conditional on those exponent
bounds.

The actual-source premise now has a separate checked proof in
[`Reverse_Growth_Run_Admission.thy`](../../devtools/proofs/isabelle/reverse_growth/Reverse_Growth_Run_Admission.thy).
For every valid symmetric pair field, `source_radial_growth_bound` proves
`r <= 3*(q+1)` for the actual trajectory. During growth its edge coefficient
`e` changes to `1 + e mod 10`. The rank assigning 3 to 18, 2 to 9, 1 to
10–17 and 0 otherwise decreases by one at each growth and increases by at
most three at a no-growth step. Summing this potential proves the bound.
`source_196_live_radial_age` consequently proves that a modulo-32 contribution
with fewer than five doublings is younger than 20 steps, including at later
196 occurrences. This bounds the age of a live contribution, not the number
of newly created innovations or residue-run boundaries.

Terminal growth does not require the first outgoing carry to be one:
`[9,18,9]` has incoming/first outgoing carry zero, grows, and produces pair
field `[10,8,8,10]`. The proof and executable regression retain this case.

For decimal pair cells, `live_pair_residue_exact` assumes `pair <= 18` before a
mod-32 residue determines the exact small value. `live_local_carry_from_pair`
then recovers the physical carry. A numeric residue in `0..18` is not, by
itself, a certificate that the residue came from an admitted source pair.

Cyclotomic projection may prune a dead radial subtree before visiting its
unresolved atoms when exact transport proves the factor vanishes. A shared node
that also has a live occurrence remains live. This is dependency forgetting in
an arithmetic projection; it does not promote the projection to a source
certificate.

### Consumer contract

The residue/carry transducer consumes a supplied compressed word of **pair
values modulo 32**. It does not consume `H`. A future direct consumer of `H`
would need a finite kernel containing at least the mod-32 prefix state and the
two carry states, plus a proof that the initial prefix and terminal boundary
match the admitted beta word.

The missing bridge is a source-authorized constructor for the compressed
`P mod 32` word over the full live extent. Once supplied, the existing finite
transducer can compute carry behavior without walking represented positions.

### Exact finite centered constructor; temporal pump still open

The research-only
[`CenteredFutureGrammar`](../../devtools/experiments/reverse_add/centered_future.py)
closes the finite arithmetic loop: symbolic centered residual, modulo-32
interval quotient, reset/birth recovery, reflected innovation, next residual
and output. Original source geometry and every published state are bound to
scoped handles. The former carry-SLP-to-polynomial round trip has been removed
from this consumer. The polynomial laws are in
[`Reverse_Centered_Future_Grammar.thy`](../../devtools/proofs/isabelle/temporal_forcing/Reverse_Centered_Future_Grammar.thy);
they do not refine the entire Python constructor or establish temporal pumping.

**Implemented direct recovery:**
[`recover_centered_carry_events`](../../src/number_compiler/arithmetic/fields/live_carry_projection.py)
applies the existing three-element carry monoid once per cancelled residue
interval. On a non-neutral interval the first coordinate resets the carry;
all later coordinates have the same outgoing carry. A neutral interval
transports its incoming carry. It emits only signed changes
`R_i = c_(i+1)-c_i`, merges adjacent carry-one domains across differing pair
residues, and constructs `(z-10)Q` from their symbolic intervals. No represented
pair/carry word, carry SLP, or per-position scan is constructed. At physical
incoming zero, the terminal carry is the leading-one growth event.

The exact relation `(1-z)Q = R + c_0 - c_m z^m` retains the terminal seam;
the reset polynomial by itself omits that seam. Reflection acts on the
correction's coordinate chart and never reverses physical carry. Exact recovery
requires the admitted source bound `0 <= P_i <= 18`; a finite jet or a numeric
residue-range check alone cannot establish it. Arbitrary arithmetic packets
remain inadmissible as successor images.

The checked spatial obligations are constant-run carry idempotence,
`residue_constant_run_first_reset`, interval concatenation and
`residue_initial_carry_zero_correction` in the theory above. These concern
supplied spatial runs. They do not prove source discovery, the full executable
constructor, or a temporal compression bound. Tests poison the old SLP owner,
compare bounded literal orbits, and check a span of `2^200` with four domain
actions and two signed resets. The canonical diagnostic is
`python -m devtools.benchmarks.field_image_growth_probe --research-events --seed 196 --horizon 20`.

On source `605e76066c6f`, five fresh-arena trials per horizon measured:

| Horizon | Median construction seconds | Retained innovation nodes | Domain actions |
| --- | --- | --- | --- |
| 20 | 0.103 | 305 | 124 |
| 64 | 0.803 | 1,376 | 946 |
| 128 | 2.563 | 3,687 | 3,530 |

The preceding same-host carry-SLP round-trip comparison had five complete
20/64 trials, with medians 0.146/1.370 seconds and 285/1,149 retained nodes.
Direct recovery reduces time but retains extra signed-reset expressions. The
comparison's aggregate 35-second guard expired during its 128-step baseline;
that incomplete group is not performance-acceptance evidence. The final
direct-event trials completed separately, with observation, rendering and
literal-reference costs reported apart. All still perform one chronological
advance per step. Neither these diagnostics nor the checked spatial laws
establish temporal powering, the full 16–1024 release manifest or CLI cutover.

**Earlier measured limitation (before direct recovery):** fresh research constructions at depths 20, 40 and 80
inspect 124, 394 and 1,428 carry runs, and 1,006, 3,699 and 16,345 packet stencil
terms. Construction takes approximately 0.17, 0.52 and 2.12 seconds in these
single diagnostic trials. Each performs exactly one `advance` per step and
retains 21, 41 and 81 states. D20 emits `70446464506`, but this is not a
production cutover or a successful complexity gate. The full-extent run
construction can hide quadratic work even without a per-digit loop. The
missing component remains a source-admitted parameter-changing temporal
normal form with a successful construction bound.

Reproduce bounded correctness with
`python -m pytest -o addopts='' tests/validation/proofs/reverse_add/test_centered_future_grammar.py tests/validation/proofs/reverse_add/test_source_growth_admission.py`.
Diagnostic evidence is local under
`results/current/future-grammars-agents-2026-09-20/`; the
[weekly record](../../results/current/2026-W38/README.md) separates it from
release evidence and preserves the source fingerprint.

### Spatial pair grammar and the repunit clause

The subsequent research prototype
[`PairSLPTransducer`](../../devtools/experiments/reverse_add/pair_slp_transducer.py)
uses the existing SLP arena for an exact pair-alphabet word. A spatial Mealy
transduction preserves emitted digits for both possible incoming carries;
structural reversal and synchronized addition then produce the next pair
grammar. All traversals use explicit work stacks. Equal carry maps never
merge distinct emitted words. Slicing a repeated child inside a single copy
has an explicit regression: it must not concatenate two overlapping pieces.

The executable six-step candidate for the actual decimal repunit family is
`2^m -> 661 · 2^(m-4) · 166` for `m >= 4`, where powers mean spatial repetition
and the field is written LSD first. Growth is two. The core returns to symbol
2 but its boundary has changed; this is **not** an invariant temporal pump.
Exact structural checks include `m=2^30`, and bounded literal checks cover
196 and seed 1. The Python grammar has no complete Isabelle refinement or
production source-occurrence authority.

Single cold research probes on the `2^30`-cell field retain 80, 305, 1,290 and
5,504 nodes after 6, 12, 24 and 48 steps. The corresponding final reachable
grammars have only 10, 17, 37 and 67 nodes. Construction takes about 0.0012,
0.0040, 0.016 and 0.063 seconds. Thus represented spatial width is compressed,
but cumulative construction is still roughly quadratic in time. For 196,
depths 20, 40 and 80 take about 0.0065, 0.024 and 0.079 seconds and retain
541, 1,751 and 6,539 nodes. These are finite research diagnostics, not CLI
latency or the unchanged five-trial release workload. The small final grammar
does not erase construction or retained-work costs.

## Carry transduction and event boundaries

### One physical carry direction

Decimal addition has one physical carry direction, from least significant to
most significant position. Reflected contexts are views of that same scan, not
a second physical carry. The append and projected-join laws in
[`Bilateral_Carry_Residual.thy`](../../devtools/proofs/isabelle/temporal_clocks/Bilateral_Carry_Residual.thy)
make this distinction explicit. `no_two_step_carry_on_unchanged_primitive_boundary`
has the narrow premise that the primitive boundary is unchanged; it is not a
general temporal-collapse theorem.

[`Bilateral_Cascade_Scan.thy`](../../devtools/proofs/isabelle/temporal_clocks/Bilateral_Cascade_Scan.thy)
proves that the finite-word bilateral summaries equal sequential folds and
emission. [`Cascade_Output_Elimination.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cascade_Output_Elimination.thy)
proves two-stage semantic equality only when the component soundness and
coverage assumptions hold. Functional overlap is proved separately.

### Compressed residue transducer

For pair residue `p` in `0..18` and incoming carry `c` in `{0,1}`, the local
step uses `centered_carry_fn(p - 9)` and returns the outgoing carry. An SLP node
stores the result for both possible incoming carries. Concatenation composes
those two-state functions; repetition uses binary powering and never walks the
represented positions.

[`Cylinder_Residue_Carry_SLP.thy`](../../devtools/proofs/isabelle/temporal_forcing/Cylinder_Residue_Carry_SLP.thy)
proves append, associative summary composition, repeat, and power laws under
the carry-bit premise. `residue_interior_jumps_telescope` covers the interior
sequence `c_(i+1)-c_i`. `residue_closed_jumps_exact` adds the terminal
`-c_m`; `residue_empty_high_closed_boundary` records that an empty word with
incoming carry one has the boundary word `[-1]`.

That final boundary cannot be dropped. If

\[
Q(z)=\sum_{i=0}^{m-1} c_{i+1} z^i,
\]

then the closed jump polynomial is

\[
J(z)=(1-z)Q(z)-c_0
    =\sum_{i=0}^{m-1}(c_{i+1}-c_i)z^i-c_m z^m.
\]

For a separate incoming carry `c`, the full carry event is
`C_Q = J + c` at degree zero. Thus an all-neutral run has
`C_Q=c(1-z^m)` while `J=-c z^m`. The two objects coincide only when the root
incoming carry is zero.

### Centered event laws

[`Cylinder_Centered_Clock.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_Centered_Clock.thy)
proves the carry bit/range laws and `centered_self_advance` for positive length.
The first-reset, tail, outgoing, and jump-splitting lemmas assume the displayed
factorization of the run; they do not discover that factorization. The source
run results additionally assume valid source digits and index bounds.

Neutral spatial segments preserve carry. They are identities for spatial
composition, but elapsed temporal length and the terminal carry boundary remain
observable. This is why neutral-run cancellation alone cannot close the
publisher.

## Radial sections and sign extraction

### Finite radial sections

A radial packet has the form

\[
2^q(1+z)^r z^s P(k),
\]

with a bounded rational polynomial weight `P`. In
[`Cylinder_Radial_Sections.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_Radial_Sections.thy),
truncation is proved in a ring satisfying `(2::'a)^bits = 0`.
`signed_section_chart` and `cartier_chart_transport` assume chart slope `+1` or
`-1`. These identities justify fixed-precision sections; they do not enumerate
or certify every integer coefficient of an unbounded source.

### Exact sparse zero certificates

[`Cylinder_Radial_Event_Clock.thy`](../../devtools/proofs/isabelle/temporal_radial/Cylinder_Radial_Event_Clock.thy)
proves exact zero certificates for grouped finite radial bases. The gap-worklist
soundness theorems are conditional: a successful search result is sound, and
prior blocks must already carry zero certificates. They do not prove that a
search succeeds or that every nonzero block can be localized cheaply.

Production uses the sound part: compatible packets with the same source atom,
orientation, chart and radial scale may cancel by exact polynomial identity.
A nonzero remainder is left unresolved. Polynomial identity testing does not
imply temporal closure.

### Common-growth elimination

For `h_(r,s)(k) = binom(r,k-s)` and pivot weight `P_p`, the first-order operator

\[
L_pf(k)=P_p(k)(k+1-s_p)f(k+1)
       -P_p(k+1)(t_p-k)f(k),\quad t_p=r_p+s_p,
\]

annihilates the pivot packet. Acting on `P_i h_(r_i,s_i)` yields

\[
\frac{N_i(k)}{r_i+1}h_{r_i+1,s_i-1}(k),
\]

where

\[
N_i=P_p(k)(k+1-s_p)P_i(k+1)(t_i-k)
 -P_p(k+1)(t_p-k)P_i(k)(k+1-s_i).
\]

The leading terms cancel, so `deg N_i <= deg P_p + deg P_i + 1`.
[`Cylinder_Radial_Hypergeometric_Elimination.thy`](../../devtools/proofs/isabelle/temporal_radial/Cylinder_Radial_Hypergeometric_Elimination.thy)
checks the shifted-binomial identity, common-growth sum rule, pivot elimination,
and an absolute-value propagation bound under the pivot-support premise.

Arbitrarily shifted binomial packets with differing growth parameters do not
form one blanket Chebyshev family over every overlap. The ratio

\[
\frac{h_{r_1,s_1}(k+1)}{h_{r_1,s_1}(k)}
\Big/\frac{h_{r_2,s_2}(k+1)}{h_{r_2,s_2}(k)}
=\frac{(r_1+s_1-k)(k+1-s_2)}
       {(k+1-s_1)(r_2+s_2-k)}
\]

need not be monotone with one orientation across arbitrary parameter choices.
The mixed-growth elimination operator remains exact algebra, but it does not by
itself isolate signs.

### Modular sign oracle

Lucas reduction computes each binomial coefficient modulo bounded small primes
without constructing the row. Chinese remaindering determines the signed
coefficient only under a supplied hypothesis `|a_k| <= B` and a combined
modulus `M > 2B`. Congruence cannot validate a false bound. The oracle is an
auxiliary arithmetic query: it has no source authority, and its tables, digit
work, integer bits, and retained memory are explicitly bounded.

For repeated common-growth elimination, the currently propagated bound has the
form `B_(j+1) = B_j (r+j+1)` on a positive pivot cell. A complete solution still
needs that initial bound and every transformation bound derived from the
admitted source, followed by a finite sign-isolation algorithm whose work does
not scale with the represented row length.

### Counterexample scope

Finite-jet examples only show that the chosen finite projection does not locate
all future signs. They are not counterexamples to a complete cylinder carrying
the source, boundaries, and enough state. Mixed-growth total-positivity failures
reject a blanket sign-variation argument, not the exact elimination identity.

## Complete temporal closure contract

### Composition law

[`Reverse_196_Complete_Interface_Substitution.thy`](../../devtools/proofs/isabelle/temporal_clocks/Reverse_196_Complete_Interface_Substitution.thy)
proves that all replacements read one frozen source environment. It also proves
composition and final restriction for a complete admitted packet, chronological
extent injectivity, one-step observer refinement, and two publisher steps under
source validity. A future implementation must refine this complete interface;
agreement of a subset of observers is insufficient.

The local Python channel pullback follows the same simultaneous-substitution
rule. Its extent and growth outputs are local activity predicates. They are not
whole-word length or cumulative growth, so composing local expressions alone
does not produce the complete packet.

### What the existing pieces establish

- Source carry and one-step publication are exact for valid, bounded source
  indices.
- Innovation transport and radial sections are exact algebraic projections.
- Pair-residue SLP summaries execute a supplied compressed word for both carry
  inputs and preserve the final boundary.
- The event normalizer can remove certified-zero radial blocks.
- Restricted D2, D4, and uniform regions have explicit arithmetic theorems.

None constructs the arbitrary-duration source grammar required by the next
step. In particular, first-nonzero discovery in `H=(1-z)Delta`, reconstruction
of the complete carry event, and publication of the next source occurrence must
be connected by one authenticated algorithm.

### Required constructive theorem

A sufficient result would provide an algorithm `build_packet(source, n)` and a
proof with all of these clauses:

1. it terminates or returns an explicit resource refusal before uncharged work;
2. success yields the complete interface above;
3. evaluation of every channel equals `n` sequential reverse/add steps;
4. the packet is admitted from the original source occurrence;
5. composition of successful packets preserves that admission;
6. construction, requested observation, and retained storage satisfy stated
   bounds without coefficient traversal, nonzero enumeration, temporal replay,
   or a hidden scalar future callback.

The production cutover cannot accept weaker premises. A proof of an algebraic
identity, a conditional carry consumer, or an exact result on one chamber is a
component, not this theorem.

### Rejected approaches and their scope

- A deferred symbolic normalizer remained open and exceeded the guarded budget.
  This rejects that prototype, not complete cylinders.
- A projected Mealy state omitted source and interface data. Its collision is a
  counterexample to that projection only.
- A source-ray cascade-output proposal lacked the full publisher refinement.
  Its failure does not show that source-bound temporal closure is impossible.
- Treating the derivative alphabet as the beta alphabet is contradicted by the
  checked 196 witness. Adding a valid modular integration state remains a
  separate possible construction.
- Polynomial zero certificates remove zero blocks but do not locate all
  nonzero events or prove their signs.

These boundaries are deliberate. Negative experiments should narrow the next
representation without being promoted to impossibility results.

## Restricted cylinders and production boundary

### Checked restricted regions

[`Cylinder_D2_Edge_Interior.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_D2_Edge_Interior.thy)
fixes the source form and assumes `m >= 3` for the chamber carry admission. It
proves exact first and second successors, reflection, and directional output in
that chamber.

[`Cylinder_D4_Carry_Admission.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_D4_Carry_Admission.thy)
splits the small lengths and proves `d4_q2_forward_admitted` under `m >= 3` and
`5 <= a <= 8`. The third carry theorem inherits the source specialization.
[`Cylinder_D4_Source_Formulas.thy`](../../devtools/proofs/isabelle/temporal_clocks/Cylinder_D4_Source_Formulas.thy)
gives the corresponding explicit formulas; its terminal and growth statements
carry the same region assumptions.

[`Uniform_Pair_Field_Grammar.thy`](../../devtools/proofs/isabelle/temporal_clocks/Uniform_Pair_Field_Grammar.thy)
proves successor formulas for uniform pair values at most nine and for the high
uniform branch. `uniform_no_growth_horizon` is conditional on
`uniform_no_growth_admissible`; it is not an unconditional horizon for every
source.

These theorems are useful grammar clauses. They cover their stated chambers and
can be selected after source authority establishes the premises. They do not
cover every later 196 packet, nor do they prove that a finite set of chambers is
closed under arbitrary temporal composition.

### Production admission rule

The installed publisher should admit only a clause with:

1. exact source provenance;
2. mechanically checked region premises;
3. the full interface output, including both ports and growth;
4. a successor result that remains in the grammar or carries an explicit next
   clause;
5. charged construction and retention.

A restricted clause may safely refuse outside its region. It may not route to a
per-digit replay, causal image reconstruction, a future-data callback, or a
special seed table. Removal of an old executor and proof of refusal are useful
cleanup, but they are separate from powered-output acceptance.

### Current production boundary

The repository now contains exact arithmetic owners for source carry,
innovation transport, radial sections, event normalization, modular signs under
a supplied bound, and compressed carry transduction. The generic scheduler does
not yet receive a complete source-derived forcing grammar. Consequently the
canonical powered 196 cutover remains deliberately red.

The restricted clauses should be retained as proved building blocks. Their
assumptions must remain visible in code and documentation so a chamber theorem
is never relabeled as generic closure.

## Historical carry-slab owner and the correct temporal acceptance target

The archived [carry/event account](../archive/reverse-add/CARRY_EVENT_FORMULA_RESULTS.md)
records a decimal `H=20` carry-field reconstruction window. The
[generalized-power account](../archive/repository-and-algebra/GENERALIZED_POWER_RESULTS.md)
records native slab morphisms and guarded `32->65` and `64->128` jumps without
ordinary replay, while explicitly leaving temporal closure open. These concern
the carry/event owner, not the old digit/wreath executor or the recent pair-SLP
spatial prototype. The pair-SLP measurements below cannot establish a lower
bound or a regression result for that different construction.

The supplied [v0.12.0 carry-slab report](../archive/reverse-add/CARRY_SLAB_JUMP_RESULTS.md)
is now preserved verbatim. Its SHA-256 is
`e5a4e9bb00d4391b6c6e99c35b3fb1ef8570d75dbf13189ed349338a9a6bc310`.
The following are historical measurements from that report, not current-source
measurements. The report does not include a source fingerprint, executable,
raw per-trial evidence or measurement environment; the local Git history search
did not recover the retired slab modules.

| Power | Nodes | References | Description bits |
| --- | --- | --- | --- |
| D4 | 79 | 255 | 2649 |
| D8 | 111 | 463 | 4441 |
| D256 | 2095 | 13359 | 182340 |
| D1024 | 8239 | 53295 | 832674 |

All eleven tabulated powers, D1 through D1024, satisfy **exactly**
`nodes = 8N + 47`, `references = 52N + 47`, and `depth = 3N + 3`.
These equalities were checked against the supplied table; they are not a proof
for unmeasured powers. The node fit near `N^0.933` should not obscure the simpler
linear relation including its fixed overhead. Description bits grow somewhat
faster (the report fits `N^1.094`). These are representation measurements, not
counts of all construction operations or cold-runtime measurements.

### Comparison with the current output-morphism gates

| Question | Historical carry-slab report | Current acceptance |
| --- | --- | --- |
| Object being powered | Fixed-H carry reconstruction, carry scan and active-domain growth; five pair-bit projections share one core | An admitted complete source-cylinder output return, composed by the existing scheduler |
| D4/D8 representation | 79/111 nodes, without expanded Boolean decision cones in powered roots | Generic D4 range construction and D4/D8 CLI output still fail; there is no successful current complete-return size to compare |
| Exact execution evidence | Guarded `32->65` and `64->128` jumps; reported forbidden-operation maps empty | Positive digit, width and point checks with causal execution and temporal continuations poisoned |
| Output accounting | Both roots materialized **outside** the powered guard and compared with an independent oracle | CLI tests cover requested digit emission; generic-range tests also check width, points, streaming and demand order |
| Temporal reduction | About one nonlinear slab generation survives per represented step | Requires complete-effect normalization; a small wrapper around unresolved generations is insufficient |
| Cost evidence | Linear retained node/reference/depth tables; two closed-jump measurements | Construction, demand and rendering must be measured separately under the unchanged resource gates |

The two historical closed jumps used 5,162 and 18,218 bit evaluations, taking
1.717 and 5.921 seconds respectively. The advance changes from 33 to 64 and
target width from 32 to 58. These two different workloads do not establish an
evaluation complexity bound; they do demonstrate why linear representation
size must not be labeled linear end-to-end work. No D4/D8 cold-construction or
final-materialization timings are supplied.

The report nevertheless records a concrete capability missing from the current
generic production route: exact guarded carry-domain jumps with a compact
representation. It is a historical capability baseline, and the quadratic
pair-SLP experiment cannot be used to dismiss it. Conversely, neither a recent
single-coordinate circuit benchmark nor a local thirteen-channel test measures
that historical whole-cylinder capability. Reproduction should preserve the
historical representation columns while adding cold construction, demanded
output and cumulative work, rather than replacing them with an unrelated DAG
node count. Recovering or replacing that capability is an integration target;
the stronger temporal quotient remains a separate target.

### Complete-effect squaring gate

The next D4/D8 constructor check must build `D2=NF(D1 star D1)`, then
`D4=NF(D2 star D2)` and `D8=NF(D4 star D4)` on admitted source cylinders.
The normalized D4 result must be the input to the D8 composition. A supplied
repeated word or a fresh chain of primitive successors is not that experiment.

During temporal construction require zero future digit-grammar or pair-grammar
creation, ordinary successor steps, temporal point queries, causal
reconstruction and universal wreath contexts. Original source admission and
final demanded output are measured separately. Preserve existing positive CLI
tests as well; absence of forbidden operations does not establish correctness.

Report these distinct populations, including cumulative construction costs:

- raw slab occurrences and surviving nonlinear action occurrences;
- newly constructed normalized complete effects;
- checked rebase, reflection, growth-chart and innovation aliases;
- arithmetic work, source reads, peak/retained storage and final demand work.

A small wrapper around four or eight unresolved slab generations does not
close this gate. Demonstrate actual residual reduction or a proved parameter
pump, with exact output/growth and subsequent-consumer equivalence. Alias
counts alone are not a correctness certificate.

### Replacing persistence of the slab

The checked forcing cutoff supplies a way to discard old modular contributions
before traversal. The replacement should retain normalized live forcing and
its admitted chart/effect, rather than make historical slab planes permanent
semantic state. This still needs a substitution rule preserving the influence
already transmitted into later carry and growth decisions. In particular, the
20-step lifetime bound alone does not collapse D4 or D8: those horizons can
contain distinct live nonlinear actions. Their reduction must come from the
complete-effect equivalence or pump being tested.

Thus **carry-domain jumping** and **quotienting the repeated nonlinear carry
action** have different evidence. Recovering and refining the former is the
appropriate baseline for the latter. Neither restoration of the removed slab
backend nor success of the spatial pair grammar is the required production
cutover.

## CLI re-entry measurement

The current pair-SLP constructor remains research-only. The exact zipper now
shares commutative operand pairs, but its chronological constructor still calls
one spatial successor per time step. Structural validation visits are counted
explicitly; cold construction, observation, rendering and warm re-demand are
reported separately. Warm reuse allocates no new grammar nodes but still
performs validation work.

Five fresh-process trials at each horizon from 16 through 1024 were measured
for seed 196 on authored source `42862bb0f8c9`. Selected results:

| Steps | Output digits | Median construction seconds | Retained grammar nodes |
| --- | --- | --- | --- |
| 256 | 113 | 0.706 | 63,672 |
| 512 | 222 | 2.859 | 254,754 |
| 1024 | 421 | 11.311 | 994,782 |

At 1024 the final pair root reaches only 439 nodes, but total retained ledger
entries are 2,326,043. Reporting only the final graph would hide construction.
The approximately fourfold increase on horizon doubling does not establish
subquadratic temporal work. It is not fourfold growth on each individual
successor. All rendered terms in these trials match an independent bounded
integer reference.

The experiment also rejected eagerly retaining every inverse-reversal memo:
it increased ledger retention by about 9.5% at 1024 while barely reducing
reverse work. That change was removed. Only exact commutative zipper reuse
remains; its small improvement is not a temporal-compression claim.

Reproduce one bounded trial through the existing measurement tool:

```console
python -m devtools.benchmarks.field_image_growth_probe --research-pair --seed 196 --horizon 1024
```

This mode explicitly reports `production_cutover_complete=false`. Returning
the constructor to the CLI still requires source-bound scheduler publication,
complete consumer refinement and the unchanged work/retention gates. The
source-specific temporal grammar remains the missing construction.

## Primary literature and the remaining grammar theorem

Research review: 2026-09-20. These are external theorems, not additional
Isabelle results or evidence that the production cutover passes. An SLP is a
grammar representing one finite string; a small supplied SLP does not explain
how to construct the next temporal SLP cheaply.

| Primary paper | Applicable result | Integration boundary |
| --- | --- | --- |
| Bojańczyk–Lohrey, [Transducers on Compressed Strings, ICALP 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.170), Theorems 6 and 10 | Rational and regular string functions can be evaluated on SLP inputs with polynomial compressed construction. | Supports the fixed physical carry/output transducer on a supplied pair field, and reversal. It does not automatically cover synchronized mirror pairing or give a uniform bound for a binary-encoded number of iterations. |
| Ganardi, [Compression by Contracting Straight-Line Programs, ESA 2021](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2021.45) | A size-`g` SLP can be converted in linear time to an equivalent size-`O(g)` contracting SLP with constant-length rules; each subtree has logarithmic height in its represented length. | Candidate infrastructure for slicing and alignment in `pair_slp_transducer.py`. It controls navigation depth, not the number of newly created alignment pairs or temporal effects. |
| Gawrychowski et al., [Optimal Dynamic Strings, SODA 2018](https://arxiv.org/abs/1511.02612) | Locally consistent parsing supports efficient concatenation, splitting and string queries. Update guarantees use randomized constructions. | Useful if a reachable-source theorem first bounds the number of changing boundary neighborhoods. It neither supplies mirror zip nor proves that bound; deterministic/certified naming is a separate requirement. |
| Lifshits, [Processing Compressed Texts: A Tractability Border, 2007](https://logic.pdmi.ras.ru/~yura/papers/lifshits2007processing.pdf), Theorem 1 | Hamming distance between two independently supplied equal-length SLP strings is #P-complete. | Our inference: an unrestricted polynomial-time, polynomial-size pointwise zip constructor would allow counting unequal binary pairs by grammar dynamic programming. This is a barrier to a generic arbitrary-input zipper, **not** a counterexample to reachable 196 cylinders. |

### Source-specific integration contract

The next constructor should exploit the admitted reverse/add language rather
than generalize arbitrary compressed-string zip. The existing pair-SLP
experiment gives an exact spatial reference; it does not establish the
following proposed invariant:

1. **Aligned source grammar:** source pair fields admit a shared contracting
   parse under reflection, with explicitly parameterized boundary types.
2. **Successor closure:** carry normalization, the leading-one boundary and
   changed reflection extent preserve that language and its complete output
   effect. Physical carry still moves only LSD to MSD.
3. **Temporal transport:** boundary parameters, innovation and growth admit
   simultaneous substitution closed under squaring. Equal current output is
   insufficient to merge source occurrences.
4. **Construction bound:** count newly introduced alignment pairs and boundary
   effects, as well as their integer sizes. Balancing or a small final root
   cannot conceal a large construction history.

The checked modulo-32 live-age bound of fewer than 20 steps and growth degree
at most 15 limits each live radial contribution. It does **not** bound how many
new contributions or boundary types appear. Combining it with the forcing
alphabet is a candidate route to item 1, not a proof of finite closure.

No paper above supplies items 1–4 for this source language. Their role is to
provide spatial primitives and sharpen the exact source-specific theorem to
prove. The observed temporal node growth remains a release blocker.

## Archived output quotient: implementation connection

Audit date: 2026-09-20. The
[decimal pair quotient review](../archive/reverse-add/DECIMAL_PAIR_QUOTIENT_RESEARCH.md)
specifies more than the three-element carry monoid. Its complete local output
contains the F5 phase and both binary channels. The following pieces already
exist; the remaining constructor must reuse them.

| Review component | Executable owner | Checked statement or boundary |
| --- | --- | --- |
| `S = alpha + 5 beta + 10 nu`, normalized phase and binary wrap | `arithmetic/formula/decimal_pair_coordinates.py` | `Reverse_Factored_Channels.normalization_gate_exact` |
| F5 addition and binary full-adder output | `decimal_add_normalized`, `decimal_add_factored`; symbolic `ReverseActiveOutputArena.pair` | `full_adder_gate_exact`, `full_adder_domain_exact`; exhaustive symbolic local-law test |
| Frobenius transport, birth cancellation, complete local interning | `CenteredF5Transport`, `ReverseActiveOutputArena.transported_alpha`, `from_coordinates` | Transport requires admitted growth counts; F5 equality alone does not identify complete output |
| Simultaneous symbol/port substitution in all thirteen local channels | `ReversePrimitiveOutputMorphism.pullback_channels` | Correlated-input and partial-admission tests; local activity is not cumulative temporal extent |
| Consumer-relative successor substitution | `ReverseContextualResidualArena.pullback`, `certify` | Certification covers the supplied continuation profile, not an unspecified whole-field continuation |

The production connection currently loses information at
[`ReverseMorphismTransferArena`](../../src/number_compiler/hashlife/execution/reverse_morphism_transfer.py):
its leaf compiler evaluates the primitive output at known producer ports and
retains `ReverseBoundOutput`, a carry-consumer projection. Its spatial joins
retain that projection. This is correct for its stated consumer, but cannot
serve as an exact recursive output morphism for subsequent temporal actions.
`ReverseImagePayload` still contains an action rather than such a complete
admitted return, and its generic chronological hook refuses construction.

The missing integration therefore needs a source-bound recursive range
identity preserving coordinate output, the complete channels, and input/output
extent and chart transport. Temporal substitution must construct that return
without interpreting future points or constructing midpoint words. Simply
retaining more leaf data establishes neither this substitution nor its cost
bound. `Decimal_Publisher_Constructor` explicitly excludes recursive occurrence
substitution and first-use DAG bounds from its 25-slot theorem.

Do not replace the existing symbolic pair operation merely because it uses a
local decimal-digit sort: that finite function is not a materialized digit
word. A rejected native-channel rewrite produced the same local function but
raised cold four-port construction from 489 to 1,198 ledger nodes. It was
removed. Neither that rewrite nor the original local implementation establishes
generic D4/D8 temporal closure; those acceptance assertions remain active.

The audit rerun on source fingerprint
`605e76066c6f4bb1b9427a360e0dc2edc85a57eb732e40893a3a6787b7403efc`
reported **24 passed, 26 failed** in 20.95 seconds for
`test_active_output_morphisms.py`, `test_symbolic_primitive_channels.py`,
`test_contextual_residual.py`, `test_reverse_generic_range_constructor.py`
and `test_reverse_temporal_publisher_cutover.py`, with pytest's default
exclusions disabled. Failures comprise twelve generic-range cases and the
fourteen existing CLI cutover cases. The 35-second/1-GiB guard measured
21.65 seconds and 88,719,960 peak bytes. Local evidence is
`results/current/future-grammars-agents-2026-09-20/output-quotient-audit-tests.{log,json}`;
these ignored artifacts are not portable downloads. This is failed cutover
evidence, not release acceptance.

## Pullback implementation milestone: 2026-09-21

The first prerequisite is implemented in the existing
[`SymbolicInnovationArena`](../../src/number_compiler/arithmetic/fields/symbolic_innovation.py):
`substitute_many` transports primitive-atom expressions through multiple
innovation roots in one frozen environment. It uses an iterative postorder
worklist and one shared memo, rebuilding through the existing radial, chart
and signed-sum normalizers. It never evaluates coefficients, projects a
polynomial, or recursively rewrites replacement expressions.

Environment, memo and frame storage are ledger owned and released on both
success and refusal. Already interned arithmetic nodes remain valid and
charged after a failed request; no result tuple is returned. Counters separate
attempts, root/binding checks, traversal frames, distinct nodes and memo hits.
The tests cover simultaneous swaps, cancellation, growth/reflection transport,
independent residue-environment evaluation, thirteen shared roots, a depth-1100
DAG, binary-encoded huge extents/powers, foreign handles and budget cleanup.

This is an arithmetic prerequisite, **not yet a production consumer** of the
complete thirteen-channel return. The existing finite-function substitution
and this innovation substitution still need a shared admitted cylinder
environment. Next are predicate/growth transport and complete-effect
normalization, followed by D2/D4/D8 and scheduler publication. The current
chronological refusal and all cutover assertions remain unchanged. The
[proof index](../proofs.md) distinguishes the checked substitution specification
from the unproved executable-worklist and temporal-constructor refinements.

Validation at source fingerprint
`c724147015087bf0e15df3ec67fb11d4502169a30242c11669e7e3c6f7be5165`:
the eight new substitution tests, existing innovation/local-output tests and
unchanged range/CLI cutover selections produced **56 passes and 26 failures**.
All failures are the twelve generic-range and fourteen CLI cutover cases.
The 35-second/1-GiB guard recorded 18.16 seconds and 92,979,800 sampled peak
bytes. Local evidence is
`results/current/reverse-pullback-2026-09-21/final-substitution-and-cutover.{log,json}`.
The aggregate Isabelle memory refusal is recorded separately in the proof
index; this milestone is not release closure.

## Production and reproduction

- **Implemented owner:** [sequences/reverse_add/source_images.py](../../src/number_compiler/sequences/reverse_add/source_images.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Generic temporal closure and a successful construction bound remain open. These positive acceptance tests must fail until the constructor exists.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/validation/proofs/test_reverse_generic_range_constructor.py tests/validation/proofs/test_reverse_temporal_publisher_cutover.py
```
