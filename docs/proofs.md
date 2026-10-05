# Proof index and acceptance

The Isabelle sources are registered in
[`proofs/isabelle/ROOT`](../proofs/isabelle/ROOT). Registration
is the acceptance boundary: a theory file is not considered checked merely
because it exists in the tree or is imported by an editor session.

Run all builds through `python -m devtools.checks.release --suite proofs`,
optionally selecting registered sessions with `--session SESSION`. Each session has a native 60-second timeout, with four prover threads and one
session building at a time under an aggregate 6-GiB process-tree guard; see [the validation policy](development.md#reproducible-release-commands).
Historical timings and limits below describe their recorded source and run;
they do not change the current validation configuration.

## Canonical spatial and finite-clock lemmas

[`Reverse_Boundary_Germ_Local`](../proofs/isabelle/Reverse_Boundary_Germ_Local.thy)
in `Reverse_Residuals` checks the finite Q95 boundary encoding, blank rejection,
threshold carry, equality wire, reflected edge ordering and symbol-complement
carry conjugacy. Its successor-factor theorem requires agreement on every
admitted pair of occurrences; finite doubled-clock agreement is insufficient.
The explicit pair-field counterexample concerns a bare three-cell observation,
not an occurrence-parameterized temporal transformer. See the
[candidate audit](research/reverse-add.md#three-cell-temporal-boundary-candidate)
for the separate seed-196 clock/germ experiment.

[`Mirror_Pair_Step`](../proofs/isabelle/Mirror_Pair_Step.thy) owns
`palindrome_nth_reflect`; both publisher and growth branches import it. Its
assumptions are palindrome admission and an in-range index. It is a spatial
lemma, not temporal constructor refinement.

[`Runtime_Cylinder_Refinement`](../proofs/isabelle/etale/Runtime_Cylinder_Refinement.thy)
proves finite semantic observer equations and bounded counterexamples.
`reassociation_preserves_clock_transfer` and
`event_clock_s_arithmetic_exponents` concern its event-word model; they do not
bind the production source or supply terminal primality evidence.

The common forward-carry append law is owned by
[`Reverse_Residuals`](../proofs/isabelle/Reverse_Residuals.thy), beside `carry_out`.
Publisher and two-port proofs reuse it; the harmonic port folds reuse HOL's
`fold_append`. Comma's scale-100 borrow equations remain separate because they
express a different recurrence.

[`Comma_Sector_Rows_Core`](../proofs/isabelle/comma_decade_masks/Comma_Sector_Rows_Core.thy)
owns row coverage, restriction, joins and nonzero filtering. The generic
[`response projection`](../proofs/isabelle/comma_response_base/Comma_Response_Rows.thy)
proves that filtering zero masks preserves the complete response. This is a
root publication interface, not a concrete fast constructor: the old sparse
base instance still owns production proof construction. The rejected parent-row
prototype and its unused normalization/instrumentation code have been removed.

## Finite saturated threshold actions

`Associated_Action_Core` now depends directly on HOL. Its scalar algebra never
needed the decimal temporal constructor. The optional
`Source_Chart_Selector_Fusion` theory remains registered in
`Decimal_196_Integration`, with its original temporal dependencies. No theorem
or aggregate acceptance target was removed.

The new
[Collatz_Saturated_Threshold_Composition](../proofs/isabelle/integration/Collatz_Saturated_Threshold_Composition.thy)
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
python -m devtools.checks.release --suite proofs --session Associated_Action_Core --session Antihydra_Mahler_Integration
```

## Inventory and existing branches

`Collatz_Cylinder_Refinement` checks
`collatz_physical_admitted_leaf_loop_refinement` and
`collatz_physical_d4_base_refinement` in
[Collatz_Physical_Cylinder_Lift](../proofs/isabelle/temporal_collatz/Collatz_Physical_Cylinder_Lift.thy).
The model matches the shared residue owner's bounded generator updates for
the physical Collatz law: current value, affine numerator/denominator, branch
labels, odd count, delta and minimum. Existing dyadic lift/split theorems justify
the transported right source. This does not prove the complete Python worklist,
resource accounting or a sublinear cold constructor; see the
[D4 sprint record](sprints/week-of-2026-09-20/shared.md#bounded-d4-bases-and-larger-transported-powers).

The `Reverse_Digit_Terminal` session also checks
`streamed_digits_refines_terminal` in
[Reverse_Digit_Terminal_Refinement](../proofs/isabelle/reverse_terminal/Reverse_Digit_Terminal_Refinement.thy).
It proves the single-carry streaming fold used by the D1/D2 output iterators
equals the existing digit normalizer for admitted pair coefficients below 19.
It does not construct those coefficients or prove arbitrary temporal closure.
The [weekly validation record](sprints/week-of-2026-09-20/shared.md#temporal-production-agent-wave)
records the registered build and its scope.

Run the fast structural check with:

```console
python -m devtools.checks.isabelle_proof_index
```

The checker reads the actual session graph and theory headers. It rejects a
missing or duplicate registered theory, a theory unreachable from registered
session roots (including a disconnected import cycle), local session dependency
cycles, a reachable local theory (including imported helpers) without an
explicit `Thm_Deps.all_oracles` audit, and stale counterpart paths. External
Isabelle session parents remain allowed. This static inventory recognizes the
repository’s explicit null-oracle/error audit form; it does not execute ML or
certify a proof. Only a successful Isabelle build supplies that evidence.
`--json PATH` writes the complete generated index, including
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
`python -m devtools.checks.release --suite proofs --session Reverse_Residuals`.
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

Within `Reverse_Residuals`, `Reverse_Uniform_Runs` now proves demanded spatial
carry-run output/exit, chronological spatial joins and digit-emission refinement.
The mapped implementation is the research Q95 plane evaluator. It does not
prove the missing reverse temporal normalizer or authorize CLI admission.

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
  Verify with `python -m devtools.checks.release --suite proofs --session Reverse_Growth_Admission`.
  Its `source_four_step_no_growth` and `source_block_parity_forcing`
  corollaries establish that every admitted block of at least four steps
  loses its homogeneous F2 source contribution; `source_196_block_parity_forcing`
  specializes this to the seed-196 trajectory. The forcing's source dependence
  is preserved. The 2026-09-21 build passed in 7.89 seconds / 1,341,738,464 sampled
  peak bytes; this is not a complete-cylinder or worklist-refinement theorem.

- `Collatz_Cylinder_Refinement` contains the finite cylinder, physical lift,
  cycle, source Hensel and inverse-three branches without the decimal temporal
  constructor dependency. `Hensel_Cylinders` belongs to `Shared_S_Arithmetic`;
  Collatz no longer inherits `Reverse_Residuals` just to access that generic
  theory. Its source/admission assumptions remain unchanged.

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

`Maximal_Run_Arithmetic` adds exact homogeneous Collatz and Antihydra run
endpoints, source parity words and finite ledger guards to that session. The
named zero-to-one event lemmas contract a run and its terminating branch with
the exact endpoint and minimum prefix; no anonymous fiber supplies the source.
The refinement map states their production use and the separate run-discovery,
publication and complexity obligations. Root-sum coefficient arithmetic does
not discharge those obligations or an all-time safety theorem.

`Dyadic_Balanced_Arithmetic.arithmetic_leaf_same_cylinder` and
`arithmetic_leaf_block_compose` justify the finite arithmetic memo and its
transported block composition. They preserve complete finite effects, including
prefix minima. The shared production mapping above separates these numerical
laws from Python cache authority and general temporal pumping.

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
python -m devtools.checks.release --suite proofs --session Mahler_Safety_Cylinders
```

Use the shared release runner and current per-session policy for acceptance. The four
theories audit their exported results with `Thm_Deps.all_oracles`. A successful
focused build does not replace aggregate release validation.

The same session includes
[`Mahler_Cyclotomic_Boundary`](../proofs/isabelle/mahler_safety/Mahler_Cyclotomic_Boundary.thy):

| Result | Assumptions / scope | Executable connection |
| --- | --- | --- |
| `mahler_source_signed_bridge` | Any natural source and finite length | Existing source skew projected by `SourceSafetyWorkspace.tail_boundary` |
| `mahler_current_tail_safe`, `mahler_current_tail_fail` | Explicit enclosure of one real tail | Strict/non-strict sign classification; not all-shift safety |
| `mahler_boundary_zero_run`, `mahler_boundary_one_run` | Supplied bit and natural repetition count | `extend_run` uses shared binary composition; source discovery is separate |
| `mahler_six_bit_boundary` | No adjacent ones in the six-bit word | Independent bounded source census; no global continuation assumption discharged |
| `mahler_six_survivor_tail_partition` | Existing finite six-step survivor set | Exact 15 positive / 3 boundary partition; enclosure is required for the real-tail corollary |
| `mahler_safe_all_extensions`, `mahler_fail_all_extensions` | Initial signed threshold inequality | Terminal current-tail queries stop refinement |

Python handle, worklist and resource accounting refinement remains outside these
algebraic theorems. The [research synthesis](research/antihydra-mahler.md#signed-current-tail-boundary)
and weekly evidence distinguish these scopes.

`Mahler_Source_Transport` is a focused child session for exact symbolic
high-fiber routing, fractional-guard composition, source-selected diamond
events, source-repetition obstructions and spatial carry pumping. Its five
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
python -m devtools.checks.release --suite proofs --session Mahler_Source_Transport
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
python -m devtools.checks.release --suite proofs --session Shared_S_Arithmetic
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

[Reverse_196_Complete_Interface_Substitution](../proofs/isabelle/temporal_clocks/Reverse_196_Complete_Interface_Substitution.thy)
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
`python -m devtools.checks.release --suite proofs --session Temporal_Clock_Jumps`.
The [weekly record](sprints/week-of-2026-09-20/reverse-add.md#temporal-patch-cutover-audit)
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
python -m devtools.checks.release --suite proofs --session Reverse_Cylinder_Length_Refinement
```

For **all repository sessions and their dependencies**, use:

```console
python -m devtools.checks.release --suite proofs
```

The shared runner enforces the current per-session validation policy. `-d ... -a` instead
selects every installed session, including unrelated Isabelle examples; a
result from that broader invocation is not the repository aggregate check.

## Comma arithmetic and boundary cutover

`Comma_Arithmetic` checks the local arithmetic. Its child session
`Comma_Cylinder` checks the weighted/control model. Its literal bridge and
the separate source-prelude session are also required; a core pass is not the complete
boundary-cutover acceptance target. The split provides focused feedback:

| Theory | Statement and assumptions | Implementation connection |
| --- | --- | --- |
| `Comma_Child_Cylinder` | Decimal carry/phase equations; fixed-leading-digit iteration and displacement; phase closure; a guarded block stays in its sector and refines a literal child path. | Local laws in `sequences/comma/arithmetic.py`; not yet full Python scheduler/worklist refinement. |
| `Comma_Decimal_Parent` | Decimal leading digit, predecessor descent and the finite root classification. | Independent root-forest tooling; does not check the compressed termination forest instance. |
| `Comma_Root_Forest` | Finite child-closed regions for excluded roots plus global root coverage imply infinitely many descendants of root 20; finite compressed-region closure is sound. | Runtime certificate specification; the concrete production certificate instance is not yet kernel-checked. |
| `Comma_Boundary_Quotient` | Fork/landmine normal forms under the stated seam hypotheses and definitions of the finite displacement catalog. | Arithmetic ingredients of `boundary_quotient.py`; these local laws do not establish macro or successor refinement. |
| `Comma_Affine_Ray` | Sign and zero guards for affine expressions on an entire increasing decimal-exponent ray. | Inequality obligations checked by `macro_lifting.py`; does not yet connect its fragment worklist to literal paths or elapsed weights. |
| `Comma_Child_Classification` | For every `p>=2`, the two adjacent leading-digit candidates are all literal children; exact iff headroom conditions cover interiors, forks, crossings and 9-sector landmines. | Complete alternatives used by production `comma_children`, the boundary constructor and development ray checker, not merely correctness of a selected child. |
| `Comma_Exact_Phase_Guard` | A strict maximum-prefix guard admits the exact fixed-phase endpoint and its displacement; each represented step has exactly one literal child. | Exact safety condition used by the bounded cycle transfer. Repeated-cycle floor count and affine-fragment worklist refinement remain separate. |
| `Comma_Period_Guard` | Phase periodicity, displacement transport, the repeated maximum guard, maximal floor/clamp count, and refinement of every admitted cycle prefix to the unique literal path. Zero repetitions are handled separately. | `safe_complete_cycles` arithmetic; does not by itself refine the cross-sector constructor or select an infinite fork child. |
| `Comma_Power_Residue` | `comma_power_residue_correct` proves the catalog-specific exponent reduction to 5–32 equals `10^p mod P` for every `p>=5`; periods divide 924. | `cycle_power_residue` in `arithmetic.py`, used by Entry. Kernel-checked arithmetic only; no all-state totality or branch-safety claim. |
| `Comma_Finite_Period` | Numerical cycle-period formula, the complete 17-displacement catalog derived through that formula, repeated 924-period transport and exact modular entry headroom. | Arithmetic used by the finite transition model. Does not establish that all boundary macros terminate within their fuel. |
| `Comma_Macro_Constructor` | Defines the older fuelled scalar macro using the neutral boundary arithmetic. | Bounded scalar reference, outside the weighted constructor's dependency chain. |
| `Comma_Boundary_Primitives` | Canonical boundary states, complete ordered children, cycle admission and singleton chart transport. | Neutral arithmetic shared by weighted and scalar reference models; no scalar run owner. |
| `Comma_Literal_Path` | Literal paths, append/snoc, fixed iteration and guarded-cycle path refinement. | Neutral path lemmas used by both constructor proofs, defined once. |
| `Comma_Weighted_Macro` | Given an admitted sector with exponent at least two and a successful macro result, `comma_macro_run_literal_refinement` proves an exact literal path with `weight=w+n`, terminal chart and complete ordered children. Also proves exact cycle weights and valid-state set cardinality 14,784. | Successful evaluation is still a premise: totality within the fuel bound, affine fragment selection and the Python consumer are not discharged by this induction. |
| `Comma_Finite_Transition` | One weighted Entry/Near constructor; control erasure, exact chart interpretation, closed repeated guard and maximal cycle count, symbolic weight evaluation, and terminal-chart retention. | `boundary_chart.py` owns the corresponding Python moves. `boundary_quotient.py` consumes their emitted weights; finite-graph tooling erases them. Successful bounded evaluation remains a premise of general run results; this theory does not establish all-state totality or the winning-cycle instance. |
| `Comma_Round_Closure` | A well-founded, fuel-free decimal-round constructor. Non-crossing chart moves strictly decrease `(9-f)*1024+600` for Entry and `(9-f)*1024+H` for Near; the result refines an exact canonical trace to a fork, landmine, crossing or invalid input. | Derived control over the same weighted owner. A round stops at the first 9-to-1 crossing; this theorem does not prove termination of repeated rounds, exclude invalid results for all admitted inputs, or justify branch pruning. |
| `Comma_Decade_Control` | Admitted rounds exclude Invalid, preserve the source exponent until crossing, and normalize the crossing target to its residue phase and bounded offset. A checked decreasing rank implies repeated-round termination. | `comma_decade_control` returns only an outcome; operation counts are separate diagnostics. Build `isabelle-163-decade` checks these generic results, not the 84,084-state rank instance or future branch safety. |
| `Comma_Canonical_Domain` | Separates the coarse Entry box from `x ≤ 89+f` sector publication and the sector-1 decade root. Proves canonical `Next` preservation, crossing-to-root conversion and fabricated-root rejection. | The `Comma_Decade_Totality` scoped kernel diagnostic passed under 60 seconds / 4 GiB. These necessary domain bounds do not assert that every admitted chart is globally reachable or prove future branch safety. |
| `Comma_Decade_Observation` | The demanded decade outcome is the weighted round's terminal projection. On admitted states it equals the existing decade control, so checking the observed rank obligations checks that same rank. | Downstream bridge avoids a dependency cycle. The direct evaluator preserves the source equation without reconstructing a scalar round or full weighted certificate per row. |
| `Comma_Decade_Rank_Data` / `Comma_Fast_Rank_Smoke` | The data-only session defines untrusted exact-height candidates. Selected lookup is shared with the one-step checker; the smoke retains all 91 phase-zero rows, numeral-alias coverage and rejection of a flat rank or insufficient bound. | Candidate bytes are independently reproduced for all 84,084 states. A checked first phase is not the full Isabelle instance. The former observed-rank checker and duplicate full instance were removed; their positive canonical rank assertion belongs to `Comma_Fast_Totality`. |
| `Comma_Entry_Port_Anchor`, `Comma_Entry_Port_Refinement` | Signed Entry transport, weighted selection, exact physical phase and direct terminal headroom. The checked 17-tree catalog retains literal digits and both interval bounds; stored-leaf evaluation refines the existing weighted trace without replaying it. | Focused `Comma_Entry_Port` session. `comma_entry_stored_tree_locator_refines_source` and `comma_entry_reduced_key_locator_refines_source` require equality with the authenticated Entry key and concludes the actual Near target without an old Near evaluation. Python inverse-phase/whole-cycle refinement and global branch safety remain separate. |
| `Comma_Pair_Field` | Reversible raw-predecessor encoding, successor closure, adjacent root thresholds and carry decomposition. | `Comma_Vieta_Root` session. Preserves the zero root before puncturing; an encoding of 81 ports, not a claim of 81 fewer behaviors. |
| `Comma_Carry_Core_Quotient` | Orbit-independent normalized carry, occurrence-weight formula and primary/core residue lifting. Recursive halfcycle/rotation evaluation equals `10^t mod c` on all nine admitted cores. | `Comma_Frobenius_Recurrence` session; production counterpart is `recursive_core_residue` and its exact physical lift. This is arithmetic refinement, not a losing/winning classification. |
| `Comma_Total_Macro` | Successful finite runs are unique and stable under added fuel. `comma_boundary_macro_exists` derives successful boundary construction from termination of every admitted decade state; a checked local residual classifier also suffices directly. Rank corollaries are downstream in `Comma_Fast_Decade_Rank`. Weighted existence follows by erasure. Definite descriptions give fuel-independent semantic macros on that proved domain. | Checked generic implications, not a concrete rank instance. `THE` is not a runtime constructor or evidence of admission outside the proved domain. No forest removal follows from these definitions alone. |
| `Comma_Short_Phase` | Entry headroom depends only on the displacement's short cyclotomic phase. Exact move transport restores the original exponent gain after reuse of a delta-zero representative. | Build `isabelle-195-short-phase` passes. Power observations use the rotated index `(r+919) mod T`; the Entry cache phase and power-table index must not be confused. |
| `Comma_Entry_Arithmetic` | Kernel-checked compilation of 90 period equations, 17 short periods and 116 modular powers from the arithmetic definitions. | Proof-evaluator data, not a production transition table. Cache facts must have no premises, hypotheses or oracle dependencies. |
| `Comma_Fast_Arithmetic` | Table-backed cycle lengths, periods, modular powers and Entry headroom equal the canonical arithmetic on admitted inputs. | Kernel-checked in the focused session. Its heap is inherited by Run Germ, avoiding repeated proof-table construction. It does not decide future branches. |
| `Comma_Near_Period` / `Comma_Closed_Near` | Phase/displacement bounds certify a maximal canonical Near prefix. Cycle division and a bounded natural-number residual loop equal the recursive germ, including its decisive terminal event. | Kernel-checked symbolic proofs replace the exhaustive 4,860-case Near certificate. No headroom enumeration, weighted record or per-row occurrence certificate is required. This is local constructor refinement, not all-decade totality or future-branch safety. |
| `Comma_Fast_Control` | Control-only sector and decade evaluation equals canonical control on admitted inputs; nine sector calls suffice for one round. | Kernel-checked against the shared semantic owner. The executable checker does not construct weighted occurrence certificates. The full decade rectangle and runtime cutover remain separate gates. |
| `Comma_Sector_Alphabet` (in `Comma_Fast_Control`) | Entry endpoint factoring through the local offset/short phase, and phase-independent Near endpoint reuse. | Checked local arithmetic projection. Absolute occurrence transport remains outside the shared endpoint key; this does not establish future equivalence or equal literal weights. |
| `Comma_Decade_Helix` / `Comma_Decade_Residual_Core` / `Comma_Decade_Blocks` | Admitted continuations advance phase by one; terminal delta is zero. First-stop composition, dyadic squaring, phase-layer lookup and square correctness refine the exact finite semantics. The paired height/terminal residual has closed block composition and stop/live source refinement; a checked local classifier with height bounded by 26 implies B32 stopping without a rank premise. The core, spatial blocks, summary transport and powered boundary have no rank-checking import. Classifier correctness implies rank validity only in the downstream regression theory; the concrete compact classifier remains missing. | Checked generic refinement. `Stop h terminal` counts decade crossings, not literal comma transitions. Full B5 completeness requires its own concrete check. The layer evaluator now rewrites 91 source offsets through the checked 46-orbit control representatives; exact layer shape and child lookup semantics are preserved. |
| `Comma_Decade_Orbit_Quotient` / `Comma_Orbit_Words` | Signed offset invariant, checked 46 representatives, all-phase control congruence, all-power congruence and recursive packed-mask refinement. | Research `temporal_masks.py`; control equality does not identify literal weights or source authority. Concrete base masks and B32 coverage are separate obligations. |
| `Comma_Sector_Response` / `Comma_Sector_Response_Check` | Short-period sector response equals the canonical round evaluator; mask projection preserves exact outcomes, including malformed-node Invalid behavior. Context-local checked clause memo and rejection smoke. | Construction branches on local periods rather than 924 scalar phases. The HOL response is a specification; the complete shared mask-certificate instance and its cost are not yet established. |
| `Comma_Sector_Mask_Constructor` / `Comma_Sector_Base_Masks` | Complete sparse-row coverage, guarded successor transport, exact-outcome merging and projection to canonical one-decade live/stop masks. | Checked generic refinement; requires actual row certificates and crossing/delta admission. Concrete 46-row construction, B32 coverage and the weighted CLI consumer remain separate gates. |
| `Comma_Sparse_Temporal_Composition` | Sparse chronological composition with positive phase rotation, exact first-stop offsets, complete coverage and binary-power refinement. | Conditional on checked base rows and their admission. It supplies no concrete B32 all-stop certificate or losing/winning classification. |
| `Comma_Mask_Safety` | Simultaneous positive-rotation updates refine canonical losing levels and exclude infinite quotient paths from each admitted losing state. | Conditional on actual constructor refinement. One-way mask soundness proves neither complete classification nor safety of the complement; no concrete 14,470/314 instance is supplied. |
| `Comma_Decade_Layer_Check` / `Comma_Decade_Layer_Smoke` | Postorder construction of checked 91-result layers; arithmetic-only squares; bounded memo ownership and failed-publication cleanup. | Small concrete regressions check repeated requests, wrapped phases, invalid phases and capacity refusal. They do not establish all-state coverage. |
| `Comma_Decade_Layer_Instance` | Positive assertion: all 924 phases and 91 offsets stop within 26 crossings under B5. | Unresolved concrete acceptance gate. Neither the research enumeration nor partial progress is a theorem instance. |
| `Comma_Decade_Orbit_Layer` | `comma_decade_orbit_layer_lookup_correct`, `comma_decade_orbit_layer_square_correct` and `comma_decade_orbit_layer_complete_sound` refine 46 stored orbit cells to all 91 physical offsets. Exact stop heights, phase transport and malformed-input rejection are preserved. | Generic kernel-checked refinement; it does not prove that B5 finishes. Build with `python -m devtools.checks.release --suite proofs --session Comma_Decade_Orbit_Layer`. |
| `Comma_Decade_Orbit_Layer_Instance` | Same all-state B5/height-26 assertion through the 46-cell representation. | Concrete positive gate; timeout remains failure. No imported rank or forest premise. |
| `Comma_Sector_Mask_Constructor`: forwarding | `comma_sector_mask_period_one_forward` proves equality of complete response functions from a checked period-one, noncrossing clause. `comma_sector_rows_rebind` transports row certificates without rebuilding masks. | Checked in `Comma_Sparse_Core`; exact source/target and exponent deltas remain. No literal-weight or global branch-safety assertion. The executable alias is tested with zero parent mask transports. |
| `Comma_Sparse_Checked_Algebra` / `Comma_Sparse_Base_Instance` | The historical partial-row algebra remains a generic audit owner. The replacement base uses a row-data recurrence and root-only refinement; the concrete producer and its generic inductive bridge are still under kernel validation. | Generic laws and the concrete 46-row construction are separate gates. The base instance must complete before any sparse B5 theorem can be exported; diagnostic scheduling is not evidence. |
| `Comma_Native_Summary` | `comma_sparse_lookup_refines_phase` derives exact lookup and coverage from one whole-fiber refinement. `comma_sparse_decade_summary_total_exact` derives admitted summary existence and height bounds from those refinements and Stop≤26 labels. | Kernel-checked conditional refinement in the clean sparse dependency chain. Concrete B32 coverage is not a premise supplied by Python experiments. |
| `Comma_Native_Summary_Occurrence` | Instantiates sparse lookup with exact exponent gain, a unique literal prefix and complete ordered terminal children. The ordinary prefix theorem is a corollary. | Kernel-checked unique-prefix and complete-child refinement, conditional on full coverage and Stop certificates. Concrete B32 and global safety remain separate gates. |
| `Comma_Native_Boundary` | Projects an arbitrary infinite literal path through the exact native occurrence to an admitted child and transported tail. `comma_native_infinite_paths_agree` proves agreement at every literal index by strong induction, preserving exact exponent and phase transport. | Requires concrete sparse refinement/Stop coverage and a checked strict-descent/unique-survivor relation. It neither certifies those instances nor proves infinite-path existence. Source-20 specialization, global root exclusion and runtime cutover remain separate obligations. |
| `Comma_Sparse_Power_Algebra` / `Comma_Sparse_Power_Instance` / `Comma_Native_Summary_Instance` | Generic whole-table powering has a checked inductive refinement. The replacement publisher uses one equation per table level, with no intermediate fiber-equation lists; native summary consumes exact response coverage separately from the concrete Stop-height check. | Concrete instance remains unverified: the prerequisite base-mask constructor exceeds 60 seconds. Neither source registration nor the external 4,535-row audit certifies the instance. |
| `Comma_Powered_Boundary` | One initial round followed by a guarded checked-layer lookup agrees with the semantic total macro. | Checked conditional refinement with no executable outer fuel parameter. All-phase layer correctness/completeness, future classification and weighted production integration remain required. |
| `Comma_Fast_Decade_Rank` / `Comma_Fast_Totality` | One-step rank checks imply canonical rank validity and termination; a bound checked in the same row preserves the 27-inspection assertion. The release instance has disjoint phase ranges and balanced joins. | The full 84,084-state instance remains unchecked under the unchanged 60-second limit. The old `finishes_within` evaluator remains only a bounded regression, outside the release instance. No weighted or Round Witness evaluation occurs in the rank kernel. |
| `Comma_Fast_Kernel` | Closed one-round evaluation and memoization are shared by consumers. Endpoint projection refines the original sector constructor and removes unused count arithmetic. | Caches retain closed, exact-term, oracle-free equalities. This is an evaluator optimization, not a checked full quotient. |
| `Comma_Decade_Summary_Transport` | Exact terminal-summary induction transports actual exponent gain. A boundary constructor uses one initial round and a summary lookup, with equality to the existing semantic total macro. | Conditional on **all** summary rows being checked. There is no concrete terminal-summary instance yet, nor an unconditional future-safety or weighted selection theorem. The separately checked source-20 prelude does not discharge these assumptions. |
| `Comma_Future_Rank_Data` | One canonical N/Z candidate owner; public lookup distinguishes Invalid, Unranked and Value. Raw index overflow is rejected; valid-only adapters are explicit. | Untrusted candidate data, used by both checker routes; not a safety certificate. The generator writes data only, never the authored guard definitions. |
| `Comma_Future_Structural_Check` / `Comma_Future_Descent_Lift` | Strict all-child descent, shared losing-path lifting, and survivor-prefix induction yielding infinitude without a cycle premise. | Generic laws kernel-checked in the [structural integration](sprints/week-of-2026-09-27/comma.md#september-30--structural-future-checker-integration). Exact-rank predecessor laws are not assumed. The [survivor induction](sprints/week-of-2026-09-27/comma.md#september-30--survivor-induction-and-quotient-proof-reuse) also checks source-20 lifting conditionally on the structural witness. |
| `Comma_Decade_Summary_Kernel` | Quotient-proved control keys, occurrence restoration and a checked phase-zero/repeated/foreign-key regression. | Focused kernel passes; 46 constructions replace 91. This does not certify all phases. |
| `Comma_Decade_Terminal_Data` / `Comma_Decade_Summary_Checked` / `Comma_Future_Structural_Instance` | Complete terminal candidates, one-step height/terminal checking, and future structural checking through the certified summary. | Concrete gate remains red: summary evaluation exceeds 60 seconds. The instance inherits the summary heap to prevent certificate replay. Global safety and production admission have not been rebased. |
| `Comma_Future_Check` / `Comma_Future_Checked_Instance` sessions | Kernel-checked generic complete-child rank checking, exact exponent-gain cycle checking, and conditional lifting to positive infinite literal paths and losing-branch exclusion. | Candidate N/Z tables are untrusted definitions. The concrete 14,470/314 partition, maximum rank 136, distinct 314-cycle and infinite-path instance remain unverified. Earlier-root exclusion and production weighted selection are separate gates. |
| `Comma_Unique_Path` / `Comma_Future_Source` | Generic unique-path composition and endpoint lemmas have one owner in Literal Bridge. Source-20 applications depend on that owner downstream. | Generic future checks no longer rebuild the source-20 prelude. Rank candidates belong only to the concrete checked-instance session; moving them does not certify their contents. |
| `Comma_Round_Phase_Slice` | Exact round equations for all 91 offsets at phase five, including complete terminal charts and gains. | Bounded regression only. Its retained round equations do not supply the full 84,084-state rank check or the separate branch-safety classification. Timings and cache measurements belong to the weekly record. |
| `Comma_Round_Weights` | A canonical control prefix has a weighted prefix over the same edges. With matching residue/exponent phase, exponent at least five and an admitted source chart, that prefix refines a literal path. Crossing adds one literal transition; fork and landmine inspections add none. | Build `isabelle-178-round-weights` checks the observation and admitted literal-path corollaries. Entry edges may represent many literal transitions, so control-operation counts cannot be substituted for CLI indices. This does not establish global constructor totality. |
| `Comma_Chart_Action` | Chronological affine chart composition reuses the shared skew action. Guard pullback preserves all five comparison relations, ordered event decorations and the first matching decoration. Canonical Entry, internal Near and seam transitions refine chart coordinates; ordinary and power-of-ten seam regressions are checked. | `Comma_Chart_Action` is a focused session. These are chart and guard laws, not the complete guarded/weighted round constructor, totality instance or infinite-branch theorem. Guards cannot be replaced by a scalar minimum without a further reduction proof. |
| `Comma_Terminal_Event` | Exact Near-event guard classification, canonical chart action, complete ordered children, and zero/unit literal weights. The source digit is derived from admitted headroom. | The focused child session reuses the checked chart heap. Fork/landmine inspection consumes no edge; landmine admission conjoins both walls. This does not establish a complete round or future branch safety. |
| `Comma_Run_Germ` | An executable `(sector, headroom)` Near germ refines the canonical prefix, literal count and first decisive event. Actual signed headroom displacement telescopes to `t-h`. Sector composition refines `comma_round_close` and terminates within nine sector calls on admitted sources. | This is exact control refinement. Its round literal-prefix result provides an existential weight; it is not the complete guarded/weighted constructor or a production weighted selector. |
| `Comma_Weighted_Run_Germ` | Source-bound sector and terminal payloads retain exact Entry weight expressions, unit weights, affine chart transport and ordered guards. Compatible chronological append refines the canonical weighted prefix. | The source and target include the actual exponent gain. Guard truth at the bound source is proved; admission equivalence across sources, full-round selection and global branch safety are separate obligations. |
| `Comma_Weighted_Round` | The complete round composes weighted sector and terminal germs, agrees with the canonical first decisive event and retains at most nine Entry weight pieces. Matching phase, an admitted source and exponent at least five imply an exact literal path. Closed occurrence certificates and a compositional frontier support a forward proof evaluator. A definitionally derived control observation has checked sector, append and stop rules, retaining exact counts without instantiating full weighted records. | These are source-bound round theorems, with checked termination and no fuel premise. They do not establish the all-state decade rank, losing/winning classification, infinite return or public CLI cutover. |
| `Comma_Trace_Regression` | Preserved numeric first-macro examples and trace checks: 93 positions from `N(2,10)`, with the old 92-position trace as its suffix after the first literal edge. | Independent regression session; its witness tables are not prerequisites of the constructor or literal bridge. |
| `Comma_Future_Safety` | Losing-level induction and an infinite selected path in a closed, stable finite complement. | Conditional graph lemmas; no concrete comma classification is assumed or certified by these statements. |
| `Comma_Checked_Ranks` | A checked rank witness proves all-branch termination of ranked states, unique unranked continuation and the bounded losing fixed point. | Checker soundness only. A concrete instance must check every outcome of the executable transition; a generated rank table alone supplies no theorem. |

Build the core with `python -m devtools.checks.release --suite proofs --session Comma_Cylinder`.
The `-b` option saves the checked heap for subsequent child builds. The forest
is isolated in `Comma_Forest_Legacy`; the older scalar macro and its refinement
are isolated in `Comma_Scalar_Reference`. Neither is an ancestor of the weighted
literal bridge. Boundary and literal-path primitives have one neutral owner;
the obsolete `Comma_Macro_Refinement` wrapper has been deleted.
Concrete trace fixtures live in the sibling `Comma_Trace_Regression` session;
moving them does not remove their acceptance assertions.
`Comma_Chart_Bridge` owns Entry/Near refinement and saves that checked heap for
selection development. Its child `Comma_Literal_Bridge` checks
`Comma_Weighted_Selection` and `Comma_Macro_Selection`.
`comma_indexed_trace_whole_macro_point` composes fragment refinement
with binary prefix selection, including both endpoints, conditional on a
successful canonical trace. This remains distinct
from total construction and the Python fragment encoding refinement.
The unused, unbuilt `Comma_Source_Prelude` draft and its 42 scalar checkpoint
rows have been deleted. Its intended literal-path and terminal-child assertions
remain in `Comma_Source_Entry`, which inherits the canonical literal bridge.
Its parent `Comma_Source_Entry_Witness` checks the 230 candidate chart positions
and their exact weights (build `isabelle-170-entry-witness`). Saving that parent
heap avoids repeating those checks during repairs to the downstream source proof.
Build `isabelle-187-source-entry` checks the small-exponent-to-weighted handoff
and a literal path of 412,987,858 transitions from 20 to 19,999,999,918, together
with its complete two-child set. Build `isabelle-201-source-unique` additionally
checks `comma_source20_to_fork_unique`: every preceding transition has exactly
one child, with no remaining premises. Neither result selects the infinite
child at that fork or retires the scalar reference.
The current source proof uses `comma_control_trace_indexed`, an induction on
the checked control trace, rather than `comma_finite_weighted_run`. The source
entry, exact transition count and uniqueness theorems pass the native
proof-dependency audit without a fuel or forest authority. The
[October 4 validation record](sprints/week-of-2026-10-04/validation-policy-git.md)
records the rebuilt sessions and their limits. This removes the source-entry
fuel bridge; it does not establish the concrete B1/B32 global instance.
`Comma_Quotient_Totality` checks the control projection and uses erasure to
transfer successful evaluation to weighted execution. Its checked witness
theorem binds the initial chart, every local edge and the terminal outcome;
coverage of every boundary state is required before the maximum witness depth
becomes a global bound. The tiny `Z(7,5)` instance and corrupted-witness
rejections are checked. No all-state instance or fuel removal follows from
this generic checker alone.
The literal bridge passes build `isabelle-132-selection`; the local witness
checker and preserved regression pass `isabelle-128-witness-regression`.
`Comma_Round_Totality` passes build `isabelle-144-round` and imports the chart
bridge directly, without forest or scalar-reference ancestry. Repeated-round
totality still needs the concrete internal-rank instance; that rank concerns
constructor termination, separately from the losing rank for literal branches.
Source entry and prefix uniqueness are checked; global totality and future
safety are still pending.
Unchecked downstream statements must not be read as release results.
The [weekly review](sprints/week-of-2026-09-20/comma.md#independent-forest-cutover-review)
separates local arithmetic checks, exact-prefix refinement, totality and
unconditional future safety. A cached-parent focused build does not discharge
the aggregate time limit.
Each theorem-owning theory audits its exported results for oracles. The
executable boundary constructor, finite classification instance,
infinite-path/lexicographic-prefix bridge and scheduler cost proof remain
distinct obligations. The current forest route is scheduled for deletion only
after these replacement obligations pass. The generated
[proof inventory](../devtools/checks/isabelle_proof_index.py) records imports
and exact theorem names; registration alone never certifies a successful build.
See the [research scope](research/comma.md) and the
[weekly validation record](sprints/week-of-2026-09-20/comma.md#a367620-integration).

## Comma proof-cache identity layers

The September 30 cache audit covers the mutable memo and theory-publication
owners in the Isabelle tree. Canonicality here means a checked, correctly scoped
key; it is not a claim of a minimal future quotient. In particular, an arithmetic
result, a receiving occurrence and a proof dependency are different objects.

| Object / owner | Identity and authority | Audit result |
| --- | --- | --- |
| [Entry jump and fast control](../proofs/isabelle/comma_fast_control/Comma_Fast_Kernel.thy) | Complete local jump: typed `(f,x,k)` with short phase `k`. Complete decade: typed receiving phase and source; local round continuations are ephemeral. Each engine captures one immutable context. | Jumps retain seam/crossing output; round children demand cached jumps without retaining phase-specific suffix proofs. Successful occurrence restoration precedes publication and hit accounting. Positive Entry offsets normalize to `(r+d) mod 924` and restore the exact result offset. Closed numeric admission guards share proofs by their complete typed propositions within the immutable engine. |
| [Cold return construction](../proofs/isabelle/comma_return_engine/return_check.ML) | Exact source-bound rounds use the checked local phase transport; an explicit worklist composes their kernel theorems. | Completed suffix memo removed after 1,238 publications and zero hits. Only completed boundary traces are retained for downstream consumers. |
| [Imported boundary traces](../proofs/isabelle/comma_return_engine/Comma_Return_Engine.thy) | Closed `comma_round_reaches` facts bind the literal N/Z constructor, digit and phase to `comma_finite_initial q`. Named theorem collections are context-owned; conflicting keys and schematic values are rejected. | The period session inherits the concrete return heap and requires 314 successfully applied boundary hits with zero new rounds before sibling checking. This avoids duplicate arithmetic; it does not prove missing sibling facts. |
| [Sector clauses and guards](../proofs/isabelle/comma_decade_masks/sector_response_check.ML) | Clauses retain `(f,x,k)`; Near arithmetic uses `(f,h)` with checked rebinding. Periodic words use `(period,residue,count)`; packed arithmetic uses complete typed operations. | Arithmetic sharing does not erase the guard or receiving source. Packed caches keep bounded FIFO retention. |
| [Complete guarded rows — audit owner](../proofs/isabelle/comma_sector_mask_audit/sector_mask_constructor.ML) | Rows/plans bind `(f,x)`; output merges occur within that source with proved guard union. Templates bind sector and complete theorem proposition. | Preserved in `Comma_Sector_Mask_Audit`; production base masks import the shared row semantics directly. This older constructor is not native B1 admission. |
| [Summary transport](../proofs/isabelle/comma_decade_summary_kernel/fast_summary_check.ML) | Symbolic offset lens plus receiving phase; only control uses the proved orbit representative. | Height and terminal candidates retain their own occurrence checks. Control equality cannot authorize equal labels. |
| [Weighted round witness](../proofs/isabelle/comma_rank/round_witness.ML) | Separate arithmetic, predicate, terminal and exact `(phase,source)` observation tables under one generation. | Existing checked transport and generation checks remain. Exact weights/guards are not shared using a control-only key. |
| [Raw layers](../proofs/isabelle/comma_decade_layer_check/decade_layer_check.ML) and [orbit layers](../proofs/isabelle/comma_decade_orbit_layer/orbit_layer_check.ML) | `(level,phase)` encoded injectively after admission of `0≤phase<924`; separate owner for each representation. | Invalid phases rejected before lookup; failed construction removes newly published entries. The encoding is local, not a portable semantic ID. |
| [Decade lookup](../proofs/isabelle/comma_decade_rank_data/rank_data_lookup.ML) and [future lookup](../proofs/isabelle/comma_future_rank_data/rank_table_lookup.ML) | Exact typed selected expression, with its defining table captured by the owner. | Rank and terminal definitions cannot share an unqualified integer index. Internal list reuse is data lookup, not a truth certificate. |
| [Shared rank/terminal data loader](../proofs/isabelle/comma_decade_rank_data/candidate_data_definition.ML) | Level and child IDs inside separate, fresh construction arenas; exact ragged 924×91 extent. | Local numeric IDs never cross arenas. No synthetic padding; candidate definitions still require independent semantic checks. Admitted edge/chunk and invalid-domain lookup regressions live in the summary kernel. |
| [Sparse theory publication](../proofs/isabelle/comma_sparse_instance/Comma_Sparse_Base_Instance.thy) | Root word data in theory storage, with source-matched root refinement. | Exact term equality protects merges; registering symbolic terms does not evaluate or certify concrete B32 data. |
| [Dependency auditor](../proofs/isabelle/comma_entry_arithmetic/entry_arithmetic.ML) | Immutable Isabelle proof-node serials, committed after complete successful traversal; roots checked on each call. | Deliberately **not** keyed by semantic conclusion: two proofs of one proposition can have different oracle dependencies. |

[Executable jump regressions](../proofs/isabelle/comma_fast_control/Comma_Fast_Kernel_Smoke.thy)
compare the new constructor against the old sector equations, poison Entry
sector-wrapper evaluation and warm-parent child access, and check changed
phase/depth/source requests. Their session is `Comma_Fast_Control`. The summary
kernel separately rejects foreign transport theorems. Current build evidence and
remaining global obligations are recorded in the weekly comma sprint; this
identity audit does not authorize forest deletion.

## Comma return induction without rank tables

`Comma_Return_Induction` derives repeated legal returns with accumulated exponent
displacement and positive literal length. `Comma_Return_Instance` checks the
314-edge nine-tail return directly from local arithmetic, independently of the
exact-rank and all-decade summary instances. Its candidate branch word supplies
no proof authority. `Comma_Return_Source` connects the return to source 20.
These existence results do not establish lexicographic minimality or earlier-root
exclusion; the separate losing-branch gates remain active. Build commands and
source-specific outcomes are recorded in the
[September 30 sprint](sprints/week-of-2026-09-27/comma.md#september-30--rank-free-nine-tail-return-induction).

`Comma_Branch_Induction` proves local rejected-branch termination for every
admitted exponent in a phase. `Comma_Branch_Instance` checks the first rejected
zero-tail subtree and retains both children at every fork. The
`comma_round_reaches_entry_rebased` theorem transports a completed tail through
phase normalization while restoring its exact occurrence offset. These local
results do not supply the remaining period-wide sibling certificate or
earliest-root proof. See the [cache and branch audit](sprints/week-of-2026-09-27/comma.md#september-30--local-branch-induction-and-semantic-cache-audit).

`Comma_Branch_Period` retains rejected-smaller-sibling termination through safe-return append and repetition. Its concrete period instance is still unverified under the 60-second bound. The existential infinite-continuation corollary does not establish the selected literal choice trace or lexicographic minimality.

[Selected return blocks](../proofs/isabelle/comma_selected_return_blocks/Comma_Selected_Return_Blocks.thy)
retain ordered alternatives and smaller-sibling termination in a compositional
certificate tree. `comma_selected_block_then_certified` requires exact source
adjacency; repetition and squaring require a closed loop. The builder keeps
completed choice subtrees opaque and expands the explicit word only on demand.
`comma_selected_block_literal_application` gives an existential literal weight
bounded below by the fork count, **not** an exact weighted locator. The separate
registered smoke theory tests the actual builder without being imported by the
period checker. This is proof composition, not a production CLI cutover or a
cold-construction complexity theorem.

The existing [Collatz cylinder constructor](../proofs/isabelle/temporal_collatz/Collatz_Cylinder_Constructor.thy) now proves `physical_collatz_distinct_time_actions`: input `2^m` distinguishes every pair of whole time actions with `n < m`. This justifies retaining exact duration in a complete source-independent action ID, while allowing source-bound cycle and high-fiber transport.

The [shared dependency audit](../proofs/isabelle/shared/Proof_Dependency_Audit.ML)
walks named theorem dependencies transitively. Native producer publication rejects
candidate-data and forest/fuel authority; global endpoints reject forest/fuel
authority while permitting checked classifications. Smoke proofs test hidden
dependencies behind an innocently named wrapper. These checks supplement kernel
validation; they do not supply missing concrete instances.
