# Proof index and acceptance

The Isabelle sources are registered in
[`devtools/proofs/isabelle/ROOT`](../devtools/proofs/isabelle/ROOT). Registration
is the acceptance boundary: a theory file is not considered checked merely
because it exists in the tree or is imported by an editor session.

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
