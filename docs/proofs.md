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
  residue-carry scan laws. It does not prove the complete 196 trajectory.

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
