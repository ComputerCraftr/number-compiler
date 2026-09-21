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

## Production and reproduction

- **Implemented owner:** [sequences/reverse_add/source_images.py](../../src/number_compiler/sequences/reverse_add/source_images.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Generic temporal closure and a successful construction bound remain open. These positive acceptance tests must fail until the constructor exists.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/validation/proofs/test_reverse_generic_range_constructor.py tests/validation/proofs/test_reverse_temporal_publisher_cutover.py
```
