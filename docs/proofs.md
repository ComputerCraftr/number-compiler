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

```console
isabelle build -d devtools/proofs/isabelle Mahler_Source_Transport
```
