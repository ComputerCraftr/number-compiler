# 2026-W38 implementation and research record

Period: 2026-09-14 through 2026-09-20.

Status: **research components advanced; repository and powered cutover remain
red**.

This record consolidates all authored implementation notes and reviewed result
narratives from ISO week 2026-W38. The old path map is in
[documentation provenance](../../../docs/provenance.md). Raw local evidence,
including the repository-hygiene baseline, remains in its original directories.

## Sprint summary

- **Objective:** advance source-bound temporal construction and make the repository's implementation and proof boundaries easy to verify.
- **Changes:** consolidated research and sprint documentation, removed the 757/179 machine and obsolete private interfaces, and repaired ownership/accounting and validation tooling.
- **Established results:** exact local carry, forcing, radial and residue laws; restricted source clauses; separately checked finite family behavior.
- **Rejected approaches:** universal product-state construction, projected-state identities, hidden reconstruction, and treating cleanup as a temporal-grammar proof.
- **Validation:** the pre-cleanup baseline is preserved below; final hygiene evidence is recorded separately on its frozen fingerprint.
- **Remaining work:** generic reverse/add construction and cost bounds, candidate-derived special-number evidence, aggregate proof validation and the separate source-global obligations.

## Provenance

The pre-cleanup repository baseline below uses source fingerprint prefix `51a37da`.
Earlier component measurements retain their own fingerprints and guards where
raw evidence survives. They are not represented as results on the final
fingerprint. The compact evidence capsules in
[documentation provenance](../../../docs/provenance.md#checkpoint-evidence-capsules)
also state when an older authored checkpoint did not record a command, guard,
or independent review; absence is not reconstructed as a pass.

## Shared actions and repository health

Associated-action work unified common skew composition while keeping
family-specific source admission. Antihydra projections began sharing sealed
source fragments; Hensel and Mahler remained distinct packets. Python quality,
ownership, foreign-handle checks, early resource admission, and cleanup improved.
These changes did not provide one universal source constructor.

The pre-cleanup baseline at source fingerprint prefix `51a37da` was:

- unit selection: **6,029 passed, 206 failed**;
- whole-tree strict typing: **88 errors**;
- powered reverse/add cutover: **36 failures**.

These are historical baseline failures. The final hygiene record below distinguishes
repaired tests from retired implementation contracts and remaining release failures.

## Reverse/add powered 196

The week established a precise path from source coefficients toward compressed
carry publication:

1. source pair cells and their one-step carry coboundary have checked authority;
2. the beta forcing alphabet is separate from its discrete derivative;
3. compatible cross-radial zero blocks can be removed by exact certificates;
4. common-growth packets have a checked first-order elimination identity;
5. modular signs can be recovered only when a proved magnitude bound is supplied;
6. a supplied compressed `P mod 32` word can run through the physical two-state
   carry transducer by SLP composition;
7. the closed jump output retains the final carry boundary;
8. complete local interface substitutions read one frozen environment.

The missing result is the source-authorized compressed pair-residue grammar for
arbitrary duration, together with generic sign-run localization, closure of the
complete thirteen-channel packet, and successful construction, demand, and
retention bounds. Production continues to refuse that unsupported route.

Restricted D2, D4, uniform, and parameter-region clauses remain exact under their
premises. They are not generic temporal closure.

## Collatz

Terminal output allocation and ownership were corrected so represented output
length is charged before materialization. Existing physical/event and Hensel
refinements remain exact on admitted sources. This did not prove a new global
Collatz result.

## Antihydra, primes, Goldbach, Fermat, and Mersenne

Shared associated-action integration preserved the family boundaries: the
Antihydra source-global barrier, live finite Goldbach prover and universal G37
claim, and Fermat/Mersenne candidate-derived terminal extractor all remained
open. No classical fallback was added for an unavailable compact certificate.

## Counterexample boundaries

- The checked 196 witness rejects treating `(1-z)Delta` as beta; a valid
  modular-prefix construction is a separate question.
- Projected-state collisions reject those projections only, not complete
  source-bound packets.
- Mixed-growth binomial packets reject one blanket total-positivity argument;
  exact elimination remains valid.
- Failed temporal prototypes were incomplete or over budget, not impossibility
  proofs.
- Mahler failure and ledger failure can differ; neither alone proves literal
  Antihydra halting.
- Zero-root and supplied-root examples reject special-number shortcuts, not the
  indexed transverse criterion.

## Repository hygiene validation, 2026-09-20

Final authored-source fingerprint:
`664702034548ee7ebd8964c65e0f8de127e8090aa8ccab9b5e3d8fd57651a61e`.
This replaces the baseline only for the checks explicitly rerun below. Evidence
is local under `results/current/repository-hygiene-2026-09-20/checks/`; these raw
paths are not portable download links. Configuration, `src`, `tests` and
`devtools` are fingerprinted; documentation is checked separately.

### Changes and retained coverage

- Removed all three `base10_t2_*` assets, the 757/179 builder/loader/emitter,
  Diamond admission and family-recognition hooks, and fixed population metrics.
  The final filesystem audit also removed an ignored stale setuptools package
  copy and retired bytecode containing those assets (`generated-retirement.json`).
  Generic finite effects, primitive carry algebra and Collatz resources remain.
- Migrated stale private-owner assertions to source images, scheduler authority
  and ledger accounting. The public API and positive construction gates remain.
- Repaired Collatz point admission, immutable publication seals, dyadic payload
  audit accounting, failed-workspace disposal and Antihydra fragment retention.
- Consolidated 126 tracked authored reports into research papers and weekly
  records with provenance capsules. Retired 49 result-directory scripts and
  direct-test-call runners; raw non-Markdown evidence remains local.
- Added documentation and proof-inventory checks. The proof inventory records
  16 sessions and 95 theories, including statements, assumptions, imports,
  lexical uses and explicitly limited implementation mappings. Static inventory
  success is not an Isabelle proof verdict.
- Separated radial, forcing and Collatz proof branches without changing their
  theorem statements or removing them from aggregate acceptance.

### Validation

Every expensive command ran serially. Python probes retained 35 seconds / 1 GiB;
Isabelle retained 35 seconds / 4 GiB; the unit run retained 300 seconds / 1 GiB.
Run commands use the development environment's Python and the process guard
shown in [development](../../../docs/development.md).

| Scope | Command / evidence stem | Result and measured guard cost |
| --- | --- | --- |
| Whole-tree quality | Ruff check/format, strict mypy, repository policy, documentation and proof index; `final-quality` | PASS; 1,429 typed files, 1,552 formatted files; 13.96 s, peak 570,770,824 bytes |
| Unit selection | `python -m pytest -q --durations=25 --junitxml=NEW.xml`; `final-unit-3` | 6,086 passed, 42 failed, 1,545 deselected; pytest 229.28 s, guard 230.44 s, peak 746,718,288 bytes |
| Explicit P0 | The unchanged generic-return, publisher-cutover, output-absorption, shadow-primality and family-digit selections; `final-p0-2` | 44 failed, 6 passed; 36 reverse cutover and 8 shadow-primality failures remain |
| Repository and phase profile | `pytest tests/repository -p devtools.benchmarks.pytest_timing`; `final-repository` | 168 passed, 1 deselected; 15.56 s, peak 611,058,672 bytes |
| Installed wheel | `python -m devtools.checks.installed_distribution WHEEL`; `final-installed-wheel` | PASS; 4.86 s, peak 114,788,416 bytes; exact package bytes, absent retired modules/assets and runtime import boundaries checked |
| Focused proofs | `isabelle build -d devtools/proofs/isabelle Cylinder_Radial_Algebra Cylinder_Forcing_Automata Collatz_Cylinder_Refinement`; `final-isabelle-focused` | Incremental PASS; 5.99 s, peak 648,726,736 bytes |
| Temporal aggregate | `isabelle build -d devtools/proofs/isabelle Temporal_Clock_Jumps`; `final-isabelle-aggregate` | PASS; 29.57 s, peak 722,356,672 bytes |
| Explicit temporal heap preparation | `isabelle build -b -d devtools/proofs/isabelle Temporal_Clock_Jumps`; `final-isabelle-temporal-heap` | TIMEOUT at 35.08 s, peak 670,534,992 bytes; does not close all-session acceptance |
| All registered sessions | `isabelle build -d devtools/proofs/isabelle -a`; `final-isabelle-all` | TIMEOUT at 35.12 s, peak 690,556,288 bytes; incomplete all-session acceptance |
| Growth manifest | `python -m devtools.benchmarks.causal_tile_growth_runner --output NEW.json`; `final-growth` | RED; all 105 requested trials attempted, 80 measured and 25 timed out; unchanged source and complete requested manifest |

The Isabelle invocations additionally use `-j1`, `threads=1`,
`parallel_proofs=0`, the existing `NumberCompilerHypergeom` identifier and a
512 MiB Java heap. Focused incremental success is not a clean-build latency
claim. Earlier aggregate timeouts and the interrupted growth run remain in the
raw evidence; they were not overwritten by later results.

The repository phase profile records collection 0.085 s, setup 0.055 s,
execution 14.514 s and teardown 0.100 s. It shares no warmed production query
state between tests and supplies no universal runtime claim.

### Independent review and remaining obligations

Independent reviewers checked production reachability and packaging, source
and seal authority, accounting, oracle independence, theorem assumptions,
proof-session reachability, guarded worker launch/evidence, documentation
claims and baseline-node disposition. Review found and the authors repaired:
missing memory samples accepted as complete growth evidence, unreachable
unregistered theory cycles, lost worker working-directory binding, incomplete
local absence coverage, nine stale disposition entries, inconsistent carry
indexing in the synthesis, and overstated historical provenance. The coordinator
also corrected an incorrectly transcribed external-document checksum. All 126
removed tracked report hashes match the captured baseline copy; the preserved
external paper matches the original inventory (`provenance-integrity.json`).

Of 206 baseline failing cases, 121 retain their names: 79 now pass and 42 fail.
The other 85 were retired or rewritten and are **not counted as fixed by
removal**. The [test-by-test disposition](../../../docs/hygiene-disposition.md)
maps their retained behaviors or explicitly retired private contracts.

All 42 final unit failures are reviewed production obligations: 41 need the
reverse/add temporal return or sector pullback, and one needs Fermat F4 to
resolve from candidate evidence. The eight positive shadow-primality release
assertions also remain red. Antihydra's 1,024-step arithmetic regression fits
its unchanged budget after seal compaction; reviewed larger-horizon probes
still exceed the 8,224-node budget at 1,536 and 2,048 steps. No all-time barrier
or arbitrary-horizon retention bound follows from that local improvement.

Historical provenance remains limited where ignored authored summaries had no
recoverable baseline copy. Missing commands and review conclusions are labeled,
not reconstructed. Cleanup does not supply the missing temporal grammar,
compact terminal extractor, source-global certificate or complete performance
and all-session proof acceptance.

### Final growth evidence

The canonical driver retained horizons 16, 32, 64, 128, 256, 512 and 1,024,
five fresh processes per sample, and the original three scenario matrices.
All 105 trials ran. Eighty completed with memory samples; 25 reached the
35-second deadline. Measured trials peaked at 121,963,072 bytes. Timeouts do
not become zero-work samples, and `collection_complete` remains false.

- Fixed-width temporal depth: five measured trials at each depth through 512;
  all five at 1,024 timed out.
- Fixed-depth spatial width: all 35 trials measured, but 24 existing
  logarithmic-increment envelopes failed, including causal frames, memo work,
  boundary traversal and validation visits.
- Growing 196: depths 16, 32 and 64 measured; all five trials at each depth
  128, 256, 512 and 1,024 timed out.

This is the existing causal-growth diagnostic, with construction, observation,
diagnostic, work and retention fields kept distinct. It does not certify the
public reverse/add source-image cutover, warm latency or an arbitrary-duration
bound. Public cutover assertions remain independently red. The failed
measurement and work-growth gates remain active and unchanged.
