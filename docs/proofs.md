# Proof index and acceptance

The Isabelle sources are registered in
[`devtools/proofs/isabelle/ROOT`](../devtools/proofs/isabelle/ROOT). Registration
is the acceptance boundary: a theory file is not considered checked merely
because it exists in the tree or is imported by an editor session.

## Canonical spatial and finite-clock lemmas

[`Reverse_Boundary_Germ_Local`](../devtools/proofs/isabelle/Reverse_Boundary_Germ_Local.thy)
in `Reverse_Residuals` checks the finite Q95 boundary encoding, blank rejection,
threshold carry, equality wire, reflected edge ordering and symbol-complement
carry conjugacy. Its successor-factor theorem requires agreement on every
admitted pair of occurrences; finite doubled-clock agreement is insufficient.
The explicit pair-field counterexample concerns a bare three-cell observation,
not an occurrence-parameterized temporal transformer. See the
[candidate audit](research/reverse-add.md#three-cell-temporal-boundary-candidate)
for the separate seed-196 clock/germ experiment.

[`Mirror_Pair_Step`](../devtools/proofs/isabelle/Mirror_Pair_Step.thy) owns
`palindrome_nth_reflect`; both publisher and growth branches import it. Its
assumptions are palindrome admission and an in-range index. It is a spatial
lemma, not temporal constructor refinement.

[`Runtime_Cylinder_Refinement`](../devtools/proofs/isabelle/etale/Runtime_Cylinder_Refinement.thy)
proves finite semantic observer equations and bounded counterexamples.
`reassociation_preserves_clock_transfer` and
`event_clock_s_arithmetic_exponents` concern its event-word model; they do not
bind the production source or supply terminal primality evidence.

## Finite saturated threshold actions

`Associated_Action_Core` now depends directly on HOL. Its scalar algebra never
needed the decimal temporal constructor. The optional
`Source_Chart_Selector_Fusion` theory remains registered in
`Decimal_196_Integration`, with its original temporal dependencies. No theorem
or aggregate acceptance target was removed.

The new
[Collatz_Saturated_Threshold_Composition](../devtools/proofs/isabelle/integration/Collatz_Saturated_Threshold_Composition.thy)
connects the shared skew endpoint and finite inverse-threshold envelope:

- `saturated_endpoint_then` and `saturated_safety_then` state chronological
  endpoint composition and contravariant threshold pullback, including the
  empty envelope.
- `saturated_finite_descent` equates a finite union of strict line comparisons
  with comparison against the envelope. Interpreting those lines as trajectory
  descent additionally requires their source-prefix inverse-map construction;
  equality is not strict descent.
- `equal_slope_elimination` and `middle_line_dominated` justify the two
  deletion rules used by the rational upper-hull normalizer.
- `high_fiber_deck_25` reduces a supplied six-event high-fiber multiplier
  729 modulo 64. Source selection remains a separate prerequisite.

These are finite algebra and rewrite lemmas. Full Python hull-stack refinement,
canonicality, source-selector refinement and a bound on source application are
not implied. Oracle audits cover the exported results. Build the registered
core and Mahler consumer with:

```sh
isabelle build -d devtools/proofs/isabelle -o threads=1 -o parallel_proofs=0 Associated_Action_Core Antihydra_Mahler_Integration
```

## Inventory and existing branches

`Collatz_Cylinder_Refinement` checks
`collatz_physical_admitted_leaf_loop_refinement` and
`collatz_physical_d4_base_refinement` in
[Collatz_Physical_Cylinder_Lift](../devtools/proofs/isabelle/temporal_collatz/Collatz_Physical_Cylinder_Lift.thy).
The model matches the shared residue owner's bounded generator updates for
the physical Collatz law: current value, affine numerator/denominator, branch
labels, odd count, delta and minimum. Existing dyadic lift/split theorems justify
the transported right source. This does not prove the complete Python worklist,
resource accounting or a sublinear cold constructor; see the
[D4 sprint record](../results/current/2026-W39/README.md#bounded-d4-bases-and-larger-transported-powers).

The `Reverse_Digit_Terminal` session also checks
`streamed_digits_refines_terminal` in
[Reverse_Digit_Terminal_Refinement](../devtools/proofs/isabelle/reverse_terminal/Reverse_Digit_Terminal_Refinement.thy).
It proves the single-carry streaming fold used by the D1/D2 output iterators
equals the existing digit normalizer for admitted pair coefficients below 19.
It does not construct those coefficients or prove arbitrary temporal closure.
The [weekly validation record](../results/current/2026-W39/README.md#temporal-production-agent-wave)
records the registered build and its scope.

Run the fast structural check with:

```console
python -m devtools.checks.isabelle_proof_index
```

The checker reads the actual session graph and theory headers. It rejects a
missing or duplicate registered theory, a theory unreachable from registered
session roots (including a disconnected import cycle),
a registered theory without an explicit `Thm_Deps.all_oracles` audit, and stale
counterpart paths. This static inventory recognizes the repository’s explicit null-oracle/error audit form; it does not execute ML or certify a proof. Only a successful Isabelle build supplies that evidence. `--json PATH` writes the complete generated index, including
direct imports, reverse imports, audited theorem names, each theory's first
scope statement, and the deliberately small set of implementation or executable
reference mappings. An empty counterpart list means that the theory is retained
as mathematics; it does not imply a production refinement.

The September 22 carry-quotient reduction adds two scoped connections in
`Reverse_Residuals`:

| Theorem | Implemented consumer | Required input; what it does not construct |
| --- | --- | --- |
| `output_crt_threshold_exact`, `normalized_output_crt_threshold_exact` | `SourceCarryPorts` second-layer carry leaves | Complete normalized F5/parity output channels; arbitrary future output channels remain a constructor obligation |
| `last_five_births_erase_earlier_jet` | `PrimaryJetAffineMorphism` constant-right reduction | The same last five births on both sides; neither birth discovery nor a source-global safety threshold follows |
| `at_least_five_births_source_independence`, `annihilated_jet_future_consumer` | Primary-jet observations through subsequent supplied actions | At least five multiplication births in the nilpotent quotient; future births must be shared, and past safety guards are not discarded |

Both reuse existing lemmas and are included in their theory's oracle audit.
Build the owning session with
`isabelle build -d devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0 Reverse_Residuals`.
Serial proof evaluation keeps the same statements and checks every proof.

The generator-macro continuation additionally checks
`nonempty_generators_idempotent`, `f5_spatial_length_transport`,
`f5_spatial_alphabet_card`, `f5_spatial_macros_closed`, and
`f5_spatial_repeat_closed_form` in `Collatz_Harmonic_Ports`. These use the
shared `carry_then_apply` law, moved from `Reverse_196_Two_Port_Refinement`
into `Reverse_Residuals` without changing its statement. Length-phase
transport is part of the spatial macro contract; 17 effects at different
lengths need not be the same set. Exact recursive occurrence minimization
and temporal source-only construction are not consequences of these laws.

The focused sessions separate three independent branches from the larger temporal
suite:

- `Cylinder_Radial_Algebra` proves sparse radial certificate and binomial pivot
  algebra. Its comments explicitly exclude temporal closure and source
  admission.
- `Cylinder_Forcing_Automata` proves the local decimal forcing alphabet and
  residue-carry scan laws, plus the carry-SLP polynomial append/repetition
  laws. `Reverse_Centered_Future_Grammar` also proves constant-run reset
  idempotence, first-reset emission, signed-reset telescoping and the exact
  `(z-10)Q` correction, supporting direct recovery from residue boundaries.
  These statements concern supplied spatial runs; they do not prove the
  complete executable temporal constructor or a bound on discovered boundaries.

- `Reverse_Growth_Admission` derives `r <= 3*(q+1)` from the actual valid
  reverse/add trajectory and an edge potential. Its modulo-32 live-age
  corollary is a source theorem, not a grammar-size or pumping theorem.
  Verify with `isabelle build -d devtools/proofs/isabelle Reverse_Growth_Admission`.
  Its `source_four_step_no_growth` and `source_block_parity_forcing`
  corollaries establish that every admitted block of at least four steps
  loses its homogeneous F2 source contribution; `source_196_block_parity_forcing`
  specializes this to the seed-196 trajectory. The forcing's source dependence
  is preserved. The 2026-09-21 build passed in 7.89 seconds / 1,341,738,464 sampled
  peak bytes; this is not a complete-cylinder or worklist-refinement theorem.

- `Collatz_Cylinder_Refinement` contains the finite cylinder, physical lift,
  cycle, source Hensel and inverse-three branches without the decimal temporal
  constructor dependency. Its source/admission assumptions remain unchanged.

`Temporal_Clock_Jumps` depends on all three sessions, so its aggregate build retains
their acceptance coverage. A proof change should build its smallest owning
session first. Release validation still builds the aggregate sessions. Every
session keeps `quick_and_dirty = false`, and theorem-level oracle audits remain
part of the theory sources.

Python reference code under `devtools` is independent evidence. The production
import firewall in `tests/repository/test_proof_production_boundary.py` prevents
those references from becoming runtime dependencies. Failed powered-construction
and cutover tests remain release blockers; the proof index does not reinterpret
an arithmetic lemma as successful construction.

The shared balanced dyadic constructor now has an executable postorder model,
bounded exact memo, numerical source refinement and finite safety bridge.
The [theorem-to-runtime map](proofs/balanced-dyadic-refinement.md) identifies
each checked statement and the Python publication, retained-ID and cost
obligations it does not discharge. Its downstream family session is
`Balanced_Dyadic_Integration`; validation evidence is recorded by source
fingerprint in the weekly sprint.

The shared `Dyadic_Source_Lift` theory additionally proves
`dyadic_source_orbit_lower_bound` and `dyadic_high_fiber_excludes_small_states`.
Together with the existing word/endpoint lift, they justify the mathematical
conditions used by
[`dyadic_return_reuse.py`](../src/number_compiler/hashlife/execution/dyadic_return_reuse.py).
The cache must still check source/action bindings, exact residue and precision,
and singleton-cycle authority. Bounded adversarial tests cover that runtime
connection; no full Python worklist refinement or general grammar-size bound
is claimed. The September 21 focused rebuilds passed for `Shared_S_Arithmetic`,
`Antihydra`, `Collatz_Cylinder_Refinement`, `Mahler_Safety_Cylinders` and
`Mahler_Source_Transport`, under 35 seconds / 4 GiB per invocation. The initial
combined parent/safety build exceeded the memory cap; its failed evidence is
retained alongside the successful focused runs. Aggregate release acceptance
remains separate.

The September 22 source-macro additions extend that theory with
`source_macro_correct`: exact dyadic right-residue transport and binary
composition preserve the endpoint, gain and ordered generator word. Its
counterpart is `dyadic_return_transport.residue_macro`, shared by Collatz and
Antihydra. The recursive arithmetic specification is checked; equivalence of
the Python ledger/memo worklist is supported by differential tests, not yet a
complete Isabelle implementation refinement.

`Reverse_Threshold_Cocycle.native_step_refines` and `native_macro_refines`
prove the native domain/F5/parity step and D4-based squaring equal the literal
pair recurrence. `native_terminal_emission_refines` separately covers the
normalized digit channels retained by each macro. These word semantics specify
the research rope gates; they do not establish rope-size compression or
production admission. `Shared_S_Arithmetic` and `Reverse_Residuals` passed
their scoped builds. The latter used task-local smaller JVM/ML heaps and took
24.86 seconds / 993,365,256 sampled bytes under the unchanged 35-second/4-GiB
guard. Earlier memory failures remain in local evidence under
`results/current/source-macros-2026-09-22/`. No new axiom, skipped proof or
theorem oracle is used.

The subsequent spatial residual normalization is specified in
`Reverse_Factored_Channels`: `plane_cofactor_entry_refines` preserves complete
finite-function tables after simultaneous constant/alias substitution;
`plane_cofactor_undefined_exact` preserves undefined inputs;
`plane_complete_residual_bisimulation`, `plane_projection_elimination` and
`plane_constant_elimination` justify sharing equivalent spatial effects.
`plane_cofactor_spatial_split` and `plane_cofactor_interval` cover the interval
consumer. `automatic_sweep_charged_to_insertions` bounds one automatic memo
cleanup by twice the entries inserted since its preceding sweep, under the
stated doubling premise. These are local semantic/accounting lemmas, not a
temporal compression theorem or full Python worklist refinement.
`Reverse_Residuals` passed in 26.69 seconds / 1,015,434,144 sampled bytes under
the unchanged 35-second/4-GiB guard; local evidence is
`results/current/plane-bisimulation-2026-09-22/proofs.log`.

`Cylinder_Innovation_Transport` now specifies the seven symbolic innovation
node kinds and simultaneous primitive-atom substitution. The theorems
`innovation_substitute_semantics`, `innovation_substitute_identity`,
`innovation_substitute_composition` and `innovation_substitute_many_semantics`
establish its arithmetic meaning, including replacement environments that are
not recursively rewritten. The Python counterpart is
`SymbolicInnovationArena.substitute_many`. These statements do **not** yet
refine its normalized memo/worklist implementation, source admission, the
thirteen-channel complete return, or temporal grammar size.

On 2026-09-21 the exact modified theory passed a focused HOL session with its
oracle audit, in 8.64 seconds and 1,385,024,896 sampled peak bytes. The owning
`Temporal_Clock_Jumps` build exceeded the unchanged 4-GiB cap at 28.91 seconds
(4,363,065,632 sampled peak bytes). The focused result does not close that
aggregate gate. Local logs are retained under
`results/current/reverse-pullback-2026-09-21/`.

## Mahler safety and the Antihydra ledger

`Mahler_Safety_Cylinders` extends `Antihydra` with real fractional safety,
64 exact six-step interval certificates, and explicit separation from ledger
safety. Its integer orbit is the existing Antihydra source owner. It proves
finite exclusions and necessary all-time conditions, not a global decision.

```console
isabelle build -d devtools/proofs/isabelle Mahler_Safety_Cylinders
```

Use the existing 35-second/4-GiB process guard for acceptance. The three
theories audit their exported results with `Thm_Deps.all_oracles`. A successful
focused build does not replace aggregate release validation.

`Mahler_Source_Transport` is a focused child session for exact symbolic
high-fiber routing, fractional-guard composition, source-selected diamond
events, source-repetition obstructions and spatial carry pumping. Its four
theories retain the strict original safety predicate. The cylinder theory's
`centered_finite_cylinder_conjugacy` explicitly connects the centered source
to Antihydra's arithmetic orbit, including canonical residue wrap and the
transported high fiber. This theorem does not identify fractional safety with
TM ledger safety. Python uses the shared production skew algebra, but full
research-worklist/scheduler refinement remains open.

The same session's `mahler_spatial_low_block_transport` and
`antihydra_centered_spatial_low_block_transport` connect spatial multiply-by-three
carry/output to the existing centered arithmetic step and its divide-by-two
boundary. They quantify over the high source part, without substituting a
spatial observer for source authority. The September 21 build passed in
8.81 seconds / 1,672,236,704 sampled peak bytes. The production comparison is
[`test_mahler_f5_production_bridge.py`](../tests/validation/proofs/test_mahler_f5_production_bridge.py);
it uses the shared Collatz carry/F5 owner and Antihydra arithmetic cylinders.
F5 table refinement, temporal grammar closure and non-halting remain separate.

```console
isabelle build -d devtools/proofs/isabelle Mahler_Source_Transport
```

## Joint-adic arithmetic and history-free projections

The shared session now includes:

| Theorem | Exact scope | Executable counterpart |
| --- | --- | --- |
| `shared_integer_fiber_rebase` | Origin and stride divisibility give an exact integral affine fiber action | `integer_dyadic_fiber_action` and its production endpoint consumer |
| `source_macro_projection_correct` | The recursively defined endpoint/gain pair equals the existing source macro projection without constructing its label list | Shared dyadic endpoint/gain semantics; Python worklist/seals not refined by this statement |
| `source_macro_projection_constant_gain` | Constant branch gain gives the corresponding power | Antihydra arithmetic branch gain 3 |
| `six_step_constant_three_lift` | Six steps transport a source lift of 64 to a target lift of 729 | Fixed six-step centered arithmetic, not six accelerated odd events |
| `block_three_adic_high_fiber_forgetting` | `3^(6*b)*fiber mod 3^h = 0` for `h <= 6*b`; the six-step theorem is its specialization | Finite modular projection; the integer high fiber remains |

The family source-lift interpretations already discharge their one-step laws.
The new results do not prove source discovery is logarithmic, identify observer
equality with source authority, or establish an all-time safe/fail invariant.
The shared session's oracle audit includes the new lemmas. Reproduce with:

```console
isabelle build -d devtools/proofs/isabelle Shared_S_Arithmetic
```

Validation at `6560841b95ca428e64f941235defc4318cec58b9cfe2f56e9cec7086a894443d`: the generalized shared session and Antihydra
session passed together in 26.14 seconds with 4,287,568,280 sampled bytes under
the existing 35-second/4-GiB limits. The separate Collatz session attempt
exceeded 4 GiB while rebuilding `Reverse_Residuals` (27.93 seconds;
4,341,701,064 sampled bytes). It remains an unsuccessful validation attempt.
Local evidence: `results/current/joint-cylinder-2026-09-22/proofs-final` and
`collatz-proofs`, each with log and guard report. The successful scope does
not replace all-session release acceptance.

## Complete finite-interface admission

[Reverse_196_Complete_Interface_Substitution](../devtools/proofs/isabelle/temporal_clocks/Reverse_196_Complete_Interface_Substitution.thy)
models complete partial images. `canonical_partial_guard_extensional` identifies
undefined and false rejection guards; `saturated_image_chronological_composition`
connects simultaneous output substitution with chronological partial application.
`complete_image_right_congruence` assumes equality of complete functions, not
agreement at one occurrence. The bounded divergence witnesses state that distinction.

The Python connection is `BitFunctionArena.complete_transform`: admission is
totalized before canonical publication and checked before composition. Exhaustive
one-bit partial-action tests check future composition and D2/D4/D8 without
midpoint evaluation. These tests and lemmas do not construct recursive Q95
source images, establish circuit-size bounds, or refine the complete Python
worklist. Additional observers outside the output tuple cannot authorize a
successor merge.

Owning session: `Temporal_Clock_Jumps`. Run
`isabelle build -d devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0 Temporal_Clock_Jumps`.
The [weekly record](../results/current/2026-W39/README.md#temporal-patch-cutover-audit)
separates its timed-out build from the checked exact-body focused diagnostic.

## Completed spatial streaming

`Reverse_Cylinder_Range_Geometry.spatial_branch_range_refines_point` proves
that a cropped spatial branch stream uses the same sibling-boundary transport
and right-coordinate rebasing as point observation.
`spatial_branch_range_emission_count` gives exactly `hi - lo` emitted values.
The executable correspondence is `RecursiveCoordinateMorphismArena.iter_observe_range`;
its input must be a completed spatial image. Temporal witnesses are rejected,
including witnesses in undemanded siblings. The theorem does not prove temporal
closure, source extent, the iterative Python worklist or its complexity bound.

Verify the focused theory with:

```console
isabelle build -d devtools/proofs/isabelle Reverse_Cylinder_Length_Refinement
```

For **all repository sessions and their dependencies**, use:

```console
isabelle build -D devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0
```

The macrocell integration guard is 60 seconds / 4 GiB. `-d ... -a` instead
selects every installed session, including unrelated Isabelle examples; a
result from that broader invocation is not the repository aggregate check.

## Comma arithmetic and boundary cutover

`Comma_Arithmetic` checks the local arithmetic. Its child session
`Comma_Cylinder` retains the complete boundary-cutover acceptance target.
The split allows focused feedback without omitting parent obligations:

| Theory | Statement and assumptions | Implementation connection |
| --- | --- | --- |
| `Comma_Child_Cylinder` | Decimal carry/phase equations; fixed-leading-digit iteration and displacement; phase closure; a guarded block stays in its sector and refines a literal child path. | Local laws in `sequences/comma/arithmetic.py`; not yet full Python scheduler/worklist refinement. |
| `Comma_Decimal_Parent` | Decimal leading digit, predecessor descent and the finite root classification. | Independent root-forest tooling; does not check the compressed termination forest instance. |
| `Comma_Root_Forest` | Finite child-closed regions for excluded roots plus global root coverage imply infinitely many descendants of root 20; finite compressed-region closure is sound. | Runtime certificate specification; the concrete production certificate instance is not yet kernel-checked. |
| `Comma_Boundary_Quotient` | Fork/landmine normal forms under the stated seam hypotheses; the 17 possible cycle displacements; `10^(p+924) mod P = 10^p mod P` for `p>=5` and every catalog displacement. | Arithmetic ingredients of `boundary_quotient.py`; modular periodicity alone is not macro or successor refinement. |
| `Comma_Affine_Ray` | Sign and zero guards for affine expressions on an entire increasing decimal-exponent ray. | Inequality obligations checked by `macro_lifting.py`; does not yet connect its fragment worklist to literal paths or elapsed weights. |
| `Comma_Child_Classification` | For every `p>=2`, the two adjacent leading-digit candidates are all literal children; exact iff headroom conditions cover interiors, forks, crossings and 9-sector landmines. | Complete alternatives used by production `comma_children`, the boundary constructor and development ray checker, not merely correctness of a selected child. |
| `Comma_Exact_Phase_Guard` | A strict maximum-prefix guard admits the exact fixed-phase endpoint and its displacement; each represented step has exactly one literal child. | Exact safety condition used by the bounded cycle transfer. Repeated-cycle floor count and affine-fragment worklist refinement remain separate. |
| `Comma_Period_Guard` | Phase periodicity, displacement transport, the repeated maximum guard, maximal floor/clamp count, and refinement of every admitted cycle prefix to the unique literal path. Zero repetitions are handled separately. | `safe_complete_cycles` arithmetic; does not by itself refine the cross-sector constructor or select an infinite fork child. |
| `Comma_Finite_Period` | Numerical cycle-period formula, catalog membership, repeated 924-period transport and exact modular entry headroom. | Arithmetic used by the finite transition model. Does not establish that all boundary macros terminate within their fuel. |
| `Comma_Macro_Constructor` | Boundary-state enumeration and complete ordered large-decimal children; defines a fuelled executable macro. | Model for `boundary_quotient.py`. Its constructor definition is not yet a proof of totality, elapsed weight or partial selection. |
| `Comma_Macro_Refinement` | Complete-cycle displacement and singleton-step chart transport, including decimal crossings. | Local refinement lemmas for the executable macro, without a source-20 or infinite-continuation conclusion. |
| `Comma_Weighted_Macro` | Given an admitted sector with exponent at least two and a successful macro result, `comma_macro_run_literal_refinement` proves an exact literal path with `weight=w+n`, terminal chart and complete ordered children. Also proves exact cycle weights and valid-state set cardinality 14,784. | Successful evaluation is still a premise: totality within the fuel bound, affine fragment selection and the Python consumer are not discharged by this induction. |
| `Comma_Finite_Transition` | Executable entry/near-boundary transitions, fuel monotonicity, trace-checker soundness, Near delta transport and Entry phase transport. A 92-position trace checks the macro from `N(2,10)` to the next fork at `(7,12)`. | Those are abstract positions, not literal steps. Its outcome omits literal weight and the landmine's exact endpoint; no all-state classification or weighted-model equality follows from this example. |
| `Comma_Future_Safety` | Losing-level induction and an infinite selected path in a closed, stable finite complement. | Conditional graph lemmas; no concrete comma classification is assumed or certified by these statements. |
| `Comma_Checked_Ranks` | A checked rank witness proves all-branch termination of ranked states, unique unranked continuation and the bounded losing fixed point. | Checker soundness only. A concrete instance must check every outcome of the executable transition; a generated rank table alone supplies no theorem. |

Build with `isabelle build -d devtools/proofs/isabelle -o threads=1 Comma_Cylinder`.
Each theorem-owning theory audits its exported results for oracles. The
executable boundary constructor, finite classification instance,
infinite-path/lexicographic-prefix bridge and scheduler cost proof remain
distinct obligations. The current forest route is scheduled for deletion only
after these replacement obligations pass. The generated
[proof inventory](../devtools/checks/isabelle_proof_index.py) records imports
and exact theorem names; registration alone never certifies a successful build.
See the [research scope](research/comma.md) and the
[weekly validation record](../results/current/2026-W39/README.md#a367620-integration).
