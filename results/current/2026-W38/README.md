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

## September 20: original Mahler safety proof integration

- **Objective:** inspect the supplied `referenced-chatgpt-conversation-this-is-an`
  folder for a complete safe/fail decision and an Antihydra non-halting proof.
- **Changes:** integrated three theories in `Mahler_Safety_Cylinders`, inheriting
  the existing Antihydra source orbit. Removed the external package's duplicate
  recurrence and parity proof; retained its exact 64 interval certificates.
  Added 66 independent rational-arithmetic regressions and proof navigation.
- **Established results:** 46 residue cylinders are rejected after six steps;
  every all-time candidate must stay in the 18 survivors; each half-unit cell
  contains at most one candidate. The separation theory proves that fractional
  failure on source seven coexists with the safe ledger prefix `0, 2, 4`.
- **Rejected inference:** neither these exclusions nor later finite carry/tree
  experiments decide Antihydra non-halting. Low residues alone lose the high
  fiber needed to choose the next residue. This is a scoped observation, not
  a counterexample to a complete source cylinder.
- **Remaining work:** source-compatible all-time safety/ledger bounds and the
  literal-machine refinement remain open. No production certificate verifier
  or release assertion was weakened.

Final authored-source fingerprint:
`c46c9dc834fe52387f9b5dfb2928f2f1cd00fb38f1a4b2d4a7118f049e3bd2f1`.
Local evidence lives in `results/current/mahler-safety-integration-2026-09-20/`.
It is not a portable download or an aggregate release certification.

| Evidence | Scope and command | Limit | Outcome |
| --- | --- | --- | --- |
| `final-build` | `isabelle build -d devtools/proofs/isabelle Mahler_Safety_Cylinders`; theorem oracle audits enabled | 35 s / 4 GiB | PASS, 22.36 s, 2,796,163,152 sampled peak bytes |
| `final-tests` | Unfiltered pytest selection: new safety certificates, Mahler API, proof index and proof/production boundary; exact selectors retained in JUnit/log | 35 s / 1 GiB | 111 passed, one existing reverse/add N=20 construction failure; 3.71 s |
| `quality` | Full Ruff, formatting, strict mypy, proof index, documentation and repository policy | 35 s / 1 GiB | PASS, 10.98 s; 17 sessions, 98 theories |
| `build` | Initial broad `-D` selection also selected unrelated sessions | 35 s / 4 GiB | Memory limit; not acceptance evidence |

Upstream theory hashes were verified against the supplied manifest and retained
in the imported file headers. Initial local separation-proof errors were fixed
before the final checked build. The broader suite and all-session release gate
were not rerun to completion for this addition; their earlier failures remain
recorded under their original fingerprint.

## September 20: joint Mahler source-cylinder transport

- **Objective:** use the prime-bucket, diamond-path and carry research together
  under the original source/fractional safety predicate.
- **Changes:** added a ledger-owned bounded research constructor. It composes
  source congruences and exact half-open guards, leaves the natural high fiber
  symbolic, and reuses the production affine action and one-step arithmetic
  kernel. The existing barrier-search tool gains a fractional-refinement mode.
  Prime and carry readouts consume one source-selected event and retain their
  explicit dyadic/finite-bank and observation-budget restrictions.
- **Established results:** the new `Mahler_Source_Transport` session proves
  integer/fractional transport, source routing and guard composition. For a
  centered source `D=2^k u` with odd `u`, it proves the event length `q=k+1`
  gives `w'=(3/2)^q w-2` for `w=4t`, with exact safety guard
  `2 ≤ (3/2)^q w < 3`. It also proves a positive finite-prefix witness `2^N`
  for every horizon `N`; these are different witnesses, not one all-time source.
- **Rejected approaches:** independently selected prime phases; supplying a
  diamond menu as source authority; checking only an event endpoint; assigning
  arbitrary real fractional states residues from a dyadic prime observer;
  treating finite surviving cylinders as a non-halting certificate.
- **Remaining work:** full executable/worklist refinement, a justified global
  safety abstraction and source-dependent exclusion or all-time invariant.
  Antihydra literal refinement and the separate source-seven ledger barrier
  remain open. The public production CLI and its release assertions were not
  changed by this research prototype.

Final authored-source fingerprint:
`e499946ef7653f0c9b85c5c6efa451e4bb5c3f5acd1a5557f96aca7228f7e81d`.
Local evidence is under `results/current/mahler-joint-transport-2026-09-20/`.
Theory hashes, executable hashes and evidence scope are recorded in
`validation_scope.json`; these files are local evidence, not portable downloads.

| Evidence | Scope | Limit | Result |
| --- | --- | --- | --- |
| `final-proof` | `isabelle build -d devtools/proofs/isabelle Mahler_Source_Transport`; source/event theories and oracle audits | 35 s / 4 GiB | PASS; 7.56 s, 1,472,187,968 sampled peak bytes; checked parent certificate session reused |
| `validated-tests` | Source transport, independent rational references, source-bound prime/carry observers, existing Mahler API, source-counterexample rejection, proof index and the explicit non-halting P0 | 35 s / 1 GiB | 192 passed; one FAIL: no accepted source-seven certificate; 2.63 s |
| `validated-refinement` | Four six-step refinements; exact source guards, 100,000-node cap | 35 s / 1 GiB | 18 / 201 / 2,291 / 26,111 nonempty families at 6 / 12 / 18 / 24 steps; 45,259 retained blocks; 1.05 s; 57,639,440 sampled peak bytes |
| `final-quality` | Full strict mypy, Ruff, formatting, proof/documentation indexes and policy | 35 s / 1 GiB | PASS; 11.53 s; 1,434 typed files, 1,557 formatted files; 18 sessions and 100 theories |

Initial theory edits failed or hit the guard before the final checked proof;
those raw attempts remain in the evidence directory. The event theory is in a
focused child session to avoid rebuilding the 64 base certificates on every
edit. This does not change the aggregate acceptance target. Larger refinement
counts are composed-constructor measurements, not independent exhaustive
literal checks or an arbitrary-horizon compression theorem. No all-time gate
was closed, skipped or converted into an expected failure.

## Mahler reachable future grammar (2026-09-20)

- **Objective:** combine source deck/high fiber, telescoping transport, diamond
  events, prime phases and carry domains before admitting future repetitions.
- **Changes:** the existing source workspace now has a bounded event-grammar
  consumer and a `--mode grammar` search. Each edge constrains the original
  source; one dyadic finite witness feeds all demanded observations. Repetition
  uses binary composition of admitted clauses. Multiplier and complete affine
  phase orders are recorded separately.
- **Established results:** Isabelle proves the source-clause repetition
  obstruction `2^(nL) | (3^L-2^L)D+J` and excludes an all-time literal repeated
  clause for a positive integer source. The theorem uses the existing
  `mahler_orbit` and the constructor's checked clause equation. For `q=3`,
  the guarded fractional fixed point `4/19` coexists with the one-repeat
  source limit at `D=4`. Modulo 19 the multiplier order is 1, while the
  full translated action has order 19.
- **Rejected approaches:** accepting a fractional/carry/prime cycle as a source
  pump; ignoring the translation when testing phase closure; assigning a
  modular lane to a rational with noninvertible denominator; treating the
  configured event bound as exhaustive or changing finite witnesses as one
  infinite source.
- **Remaining work:** a source-compatible parameter-changing pump, general
  grammar closure and its bound, full executable refinement, and the separate
  Antihydra literal/ledger/non-halting obligations. This excludes fixed repeated
  clauses, not all future quotients or nonperiodic paths.

Authored-source fingerprint:
`18d66988222d91c9b0c12cc06b1d44318a36e6950dc9d0ebdf1554f987f5deb9`.
Evidence and file/input hashes are local under
`results/current/mahler-future-grammar-2026-09-20/`; `validation_scope.json`
records exact scope. The supplied review is the local attachment
`cdca45fa-051b-40d2-9159-77428c35c3fa/Pasted text.txt`.

| Evidence | Scope | Limit | Result |
| --- | --- | --- | --- |
| `proof-9`, `validated-proof` | Compile the new repetition theory, then verify the final focused `Mahler_Source_Transport` build and oracle audits | 35 s / 4 GiB | PASS; final checked-heap build 6.60 s, 1,166,576,520 sampled peak bytes |
| `validated-tests` | 18 new grammar tests, existing Mahler references/API, proof index, production firewall and explicit non-halting P0 | 35 s / 1 GiB | 220 PASS; two existing FAILURES: reverse/add D20 constructor and source-seven certificate; 4.26 s |
| `validated-grammar` | Four events, exponents 1–4; 100,000-node cap | 35 s / 1 GiB | 4 / 12 / 24 / 48 live source families; 30 fractional-cycle candidates with source obstruction; 167 source nodes, 498 entries; 0.19 s |
| `validated-quality` | Full strict mypy, Ruff, formatting, policy and proof/documentation indexes | 35 s / 1 GiB | PASS; 1,436 typed files, 1,559 formatted files, 18 sessions / 101 theories |

Initial proof/serialization/typing failures remain in the raw evidence. No test
was skipped or changed to expected failure. The full unit suite, production
performance workloads and aggregate all-session release build were not rerun
for this bounded research change. General powered production release remains
blocked.

## 2026-09-20: future grammar agents and spatial pumping

- **Objective:** continue source-bound 196 and Mahler pumping research;
  reduce future construction through exact spatial effects and admission.
- **Changes:** agent-owned finite centered-residual constructor; iterative
  pair-SLP carry/output/reflection zipper using the existing SLP arena;
  Mahler source-parameter transport, finite first-failure descent, disposal,
  normalized safe-kernel interning, and full multiplier block effects.
  Exact event-exponent domains now prune the canonical bounded grammar search
  before child construction.
- **Primary-literature follow-up:** the maintained
  [reverse/add paper](../../../docs/research/reverse-add.md#primary-literature-and-the-remaining-grammar-theorem)
  now maps compressed transduction, contracting SLPs and locally consistent
  parsing to the missing reachable mirror-alignment invariant. The
  [Mahler paper](../../../docs/research/antihydra-mahler.md#primary-literature-and-a-mixed-coordinate-grammar)
  maps rational-base source trees and multiplication macrotiles to a proposed
  mixed `(2,3)` source chart. Independent research agents reviewed primary
  sources. Generic compressed-zip hardness and non-sofic trace results are
  explicitly scoped; neither refutes a restricted source grammar. These
  literature results do not close temporal construction or non-halting.
- **Established results:** checked actual-source reverse growth potential
  `r <= 3*(q+1)` and live modulo-32 age below 20; checked spatial fixed-carry
  repetition preserves both output and carry; checked translated safe
  intervals/output and exact event-range intersection criterion. Mahler
  inverse/route refinement consumes explicit checks matching Python. These
  are scoped mathematical/component results, not full runtime extraction.
- **Spatial findings:** the executable repunit-family clause is
  `2^m -> 661 · 2^(m-4) · 166` after six steps, with growth two. The boundary
  changes, so it is not an invariant temporal pump. For a `2^30`-cell repeated
  field, 48 chronological spatial successors retain 5,504 construction nodes
  and only 67 final reachable nodes. Retained work still grows roughly
  quadratically in temporal depth. Mahler's four-level search keeps exactly
  the same 4/12/24/48 live families while reducing source blocks 167→91,
  entries 498→270, and composition attempts 168→92; 76 empty child branches
  are excluded by 129 exact domain comparisons. Larger events remain outside
  that finite search.
- **Rejected approaches:** merging carry-only effects; treating equal safe
  kernels as equal failure paths; treating finite horizon source classes as
  one invariant pump; a two-output carry formula for multiplier 729 on a
  base-64 limb; a parallel recursive SLP representation; uncharged/mutable
  source metadata. Adversarial review found and fixed a same-copy REPEAT
  slicing defect, forged-state authority, allocation rollback, strict endpoint
  equality and source inverse/route mismatches.
- **Remaining work:** canonical temporal squaring of changing 196 boundaries
  with a successful construction bound; general source-derived Mahler event
  grammar closure; complete executable/worklist refinement; production
  integration; separate all-time Mahler and Antihydra obligations. No positive
  construction assertion was weakened and no research loop entered production.

Final authored-source fingerprint:
`e4267e386d6ead4a3b2f5a34e27aea9673dfdfda6cd648ba7e0bf8089982e681`.
Evidence is local under `results/current/future-grammars-agents-2026-09-20/`.
Earlier failed builds and diagnostic trials remain available; historical
probes are not five-trial release performance acceptance.

| Evidence | Scope | Limit | Result |
| --- | --- | --- | --- |
| `baseline` | Prior focused grammar and explicit cutover/non-halting checks | 35 s / 1 GiB | 24 PASS, 15 FAIL |
| `final-focused` | Finite grammar, spatial, growth, source/guard, lifecycle and retained P0 checks | 35 s / 1 GiB | 286 PASS, 15 FAIL; 14 reverse cutover cases plus missing source-seven certificate |
| `final-proofs` | `Reverse_Growth_Admission`, `Cylinder_Forcing_Automata`, `Mahler_Source_Transport`; oracle audits active | 35 s / 4 GiB | PASS, 7.04 s |
| `final-mypy` | Whole-tree strict typing | 35 s / 1 GiB | PASS, 1,445 source files |
| `cold-*`, `pair-*` | Single cold research constructors, bounded 196 and large repeated spatial field | 35 s / 1 GiB each | Exact checks pass; roughly quadratic retained temporal work remains |
| `domain-before`, `domain-after` | Same finite grammar workload before/after exact admission pruning | 35 s / 1 GiB each | Same live families/witnesses; fewer constructed source blocks |

Ruff, formatting (1,568 files), structural policy, documentation links and the
proof index (19 sessions, 104 theories) pass. The full unit suite, installed
wheel, five-trial 16–1024 manifest and aggregate all-session build were not
rerun: this is research integration, with production release still blocked.

### Existing cylinder geometry and reverse/add CLI re-entry review

- **Objective:** connect finite Mahler grammar construction to the existing
  Antihydra cylinder algebra and test whether the new reverse/add constructor
  has earned production re-entry.
- **Changes:** centered source blocks now compose through production
  `SkewTransfer.then`; fractional transport is derived from the same transfer.
  The authenticated `a=D+1` chart handles residue wrap into the high fiber.
  Stored-payload accounting excludes derived views. The pair-SLP zipper now
  shares commutative demands; validation visits and weighted retention are
  exposed in the existing field-image growth probe.
- **Established result:** Isabelle's `centered_finite_cylinder_conjugacy`
  proves the actual finite arithmetic orbit connection and moving high fiber.
  Bounded tests compare all source residues and splits through eight bits,
  plus selected production cylinders through 64 bits. Fractional safety and
  TM ledger safety retain separate witnesses and predicates.
- **Rejected optimization:** eager inverse-reversal memo publication raised
  retained entries by about 9.5% at horizon 1024 while removing negligible
  work. It was removed. Raw diagnostic runs remain available.
- **Measured outcome:** all 70 fresh-process research trials completed:
  seeds 196 and 1, horizons 16–1024, five trials per source/horizon. The
  processes do not use the process cache; each includes cold construction and
  a separately measured warm final demand. The 196 median construction times
  at 256/512/1024 were 0.706/2.859/11.311 seconds, with
  63,672/254,754/994,782 retained grammar nodes. Seed 1 showed the same trend
  (0.682/2.754/11.277 seconds). At 196/1024, the 439-node final pair graph
  still retains 2,326,043 ledger entries; median digit rendering is 0.000188
  seconds. Warm demands create no new nodes but still validate structure.
- **Remaining work:** source-specific temporal squaring and its work bound;
  authenticated scheduler publication and complete consumer refinement. The
  measured construction remains roughly quadratic, so reverse/add was not
  reintroduced through this research executor. No public CLI/API behavior or
  release assertion changed.

Frozen authored source:
`42862bb0f8c90a8a298dd8da585a69d6ab96f3a65b82549c756b277ccb5ee8c1`.
Evidence remains under `results/current/future-grammars-agents-2026-09-20/`.
The interrupted `geometry-pair-*` series predates weighted-retention reporting
and is not final acceptance evidence; use `geometry-pair-final-*`.

| Evidence | Scope | Limit | Result |
| --- | --- | --- | --- |
| `geometry-final-tests` | Geometry, research constructors, production Antihydra support/projections and unchanged selected P0 cases | 35 s / 1 GiB | 362 PASS, 15 FAIL; 14 reverse/add cutover cases and the missing source-seven certificate; 3.34 s |
| `geometry-final-proofs` | Three focused sessions, including the centered-cylinder theorem; oracle audits retained | 35 s / 4 GiB | PASS, 6.49 s |
| `geometry-final-quality` | Whole-tree strict mypy, Ruff, formatting, policy and documentation/proof inventories | 35 s / 1 GiB | PASS; 1,447 typed files, 1,570 formatted files, 19 sessions / 104 theories; 8.68 s |
| `geometry-pair-final-measurements.json`, `geometry-pair-final-*` | 70 independent research trials; construction, observation, rendering, reference and warm-demand costs | 35 s / 1 GiB per trial | All complete; maximum guarded duration 12.17 s and sampled footprint below 436 MB; temporal scaling gate remains unmet |

Independent reviewers signed off on the frozen source's centered bridge and
zipper/probe scope, including corrected weighted storage reporting. These
research trials do not replace installed-CLI or full release-manifest checks.
The full unit suite and aggregate all-session build were not rerun.

### Carry-slab baseline correction

The follow-up review distinguishes the historical native `H=20` carry/event
morphism from both the retired digit/wreath executor and the measured pair-SLP
prototype. Archived carry/event and generalized-power notes record the finite
carry window and guarded non-replaying `32->65` / `64->128` jumps. The supplied
D4/D8 representation counts and fitted size exponents are kept explicitly
separate from reproduced current-source timings. The maintained reverse/add
paper now specifies normalized complete-effect squaring, prohibited construction
paths, and separate raw-occurrence/effect/alias populations. No implementation
or proof gate was marked complete by this documentation correction.

### Direct quotient recovery of carry reset and birth events

- **Objective:** derive forcing from the existing cylinder residue boundaries,
  without converting a carry grammar back to a polynomial.
- **Changes:** `recover_centered_carry_events` applies the existing carry monoid
  once per residue interval, emits signed resets, merges carry-one domains and
  derives the forcing correction and terminal growth. `CenteredFutureGrammar`
  consumes those handles directly. Boundary storage is pre-admitted by a
  scoped lease; refused allocation and failed-consumer cleanup are tested.
- **Established results:** bounded literal comparisons, all pair symbols and
  both incoming ports, cancellation, terminal seam, neutral spans, source
  rejection and poisoned carry-SLP construction pass. A `2^200` span needs four
  domain actions and two signed resets. Isabelle checks constant-run reset
  laws, interval composition and the exact carry coboundary; these are spatial
  theorems, not full constructor or source-admission refinement.
- **Measurements:** five fresh-arena seed-196 trials at horizons 20/64/128
  have median construction times 0.103/0.803/2.563 seconds and retained
  innovation-node counts 305/1,376/3,687. The earlier same-host round-trip
  baseline completed five 20/64 trials at 0.146/1.370 seconds; its aggregate
  guard timed out during 128 and that incomplete group is not acceptance.
  Direct recovery retains additional reset expressions, so node counts rise
  from the baseline's 285/1,149 at 20/64 despite less execution time.
- **Remaining work:** every finite advance still discovers the next live
  boundaries. There is no proved temporal pump or bound preventing temporal
  work growth; no CLI re-entry, scheduler cutover or release closure is claimed.

Frozen authored source:
`605e76066c6f4bb1b9427a360e0dc2edc85a57eb732e40893a3a6787b7403efc`.
Evidence is local under `results/current/future-grammars-agents-2026-09-20/`.

| Evidence | Scope and result | Guard |
| --- | --- | --- |
| `direct-events-frozen-tests` | 217 PASS, 14 unchanged reverse/add production cutover FAIL; all four other-family digit cases PASS | 35 s / 1 GiB; 2.77 s |
| `direct-events-proofs-v8` | `Cylinder_Forcing_Automata` PASS, explicit null-oracle audits; previous v1–v7 are failed development builds | 35 s / 4 GiB; 8.39 s |
| `direct-events-frozen-measurements` | 15 fresh-arena direct-event trials complete; separate construction/observation/render/reference cost | 35 s / 1 GiB; 17.94 s |
| `direct-events-frozen-quality` | Strict mypy (1,447 files), Ruff, formatting (1,570 files), policy, docs and proof index (19 sessions / 104 theories) PASS | 35 s / 1 GiB; 8.82 s |

The independent arithmetic and ownership audit found a preallocation accounting
issue, which was fixed and re-reviewed. A boundary lease is borrowed for its
context; the internal consumer does not retain its tuple after exit. Full-unit,
installed-wheel, all-session and full growth-manifest validation were not rerun.

## Additional dated evidence

These relocated records supplement the topic summaries above.

### Centered carry recovery measurements

Relocated evidence from the reverse-add synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

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
[weekly record](README.md) separates it from
release evidence and preserves the source fingerprint.

</details>

### Pair grammar spatial versus temporal cost

Relocated evidence from the reverse-add synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

Single cold research probes on the `2^30`-cell field retain 80, 305, 1,290 and
5,504 nodes after 6, 12, 24 and 48 steps. The corresponding final reachable
grammars have only 10, 17, 37 and 67 nodes. Construction takes about 0.0012,
0.0040, 0.016 and 0.063 seconds. Thus represented spatial width is compressed,
but cumulative construction is still roughly quadratic in time. For 196,
depths 20, 40 and 80 take about 0.0065, 0.024 and 0.079 seconds and retain
541, 1,751 and 6,539 nodes. These are finite research diagnostics, not CLI
latency or the unchanged five-trial release workload. The small final grammar
does not erase construction or retained-work costs.

</details>

### Historical carry-slab comparison

Relocated evidence from the reverse-add synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

The archived [carry/event account](../../../docs/archive/reverse-add/CARRY_EVENT_FORMULA_RESULTS.md)
records a decimal `H=20` carry-field reconstruction window. The
[generalized-power account](../../../docs/archive/repository-and-algebra/GENERALIZED_POWER_RESULTS.md)
records native slab morphisms and guarded `32->65` and `64->128` jumps without
ordinary replay, while explicitly leaving temporal closure open. These concern
the carry/event owner, not the old digit/wreath executor or the recent pair-SLP
spatial prototype. The pair-SLP measurements below cannot establish a lower
bound or a regression result for that different construction.

The supplied [v0.12.0 carry-slab report](../../../docs/archive/reverse-add/CARRY_SLAB_JUMP_RESULTS.md)
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

#### Comparison with the current output-morphism gates

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

</details>

### Reverse CLI re-entry measurements

Relocated evidence from the reverse-add synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

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

</details>

### Archived output quotient audit validation

Relocated evidence from the reverse-add synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

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

</details>

### Original Mahler safety build evidence

Relocated evidence from the antihydra-mahler synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

**Checked theorem status:** the integrated session passed on 2026-09-20 in
22.36 seconds under the unchanged 35-second/4-GiB guard, including its oracle
audits. Local evidence is `results/current/mahler-safety-integration-2026-09-20/`
(`final-build.log` and `final-build.json`). This is focused proof
evidence, not an aggregate release result.

</details>

### Source-cylinder transport build evidence

Relocated evidence from the antihydra-mahler synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

**Checked theorem status:** both theories passed Isabelle and their oracle
audits on 2026-09-20. The focused child-session build took 7.56 seconds under
the unchanged 35-second/4-GiB limit. Local evidence is
`results/current/mahler-joint-transport-2026-09-20/final-proof.log` and
`final-proof.json`; the earlier six-step certificate session is its checked
parent.

</details>

### Fractional refinement census

Relocated evidence from the antihydra-mahler synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

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

</details>

### Reachable grammar validation evidence

Relocated evidence from the antihydra-mahler synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

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

</details>

### Next-event domain pruning measurements

Relocated evidence from the antihydra-mahler synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

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

</details>
