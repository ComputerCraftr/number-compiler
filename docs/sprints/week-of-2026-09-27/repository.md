# Repository, tooling and validation

Period: 2026-09-27 through 2026-10-03 (Sunday–Saturday).

[Week index](README.md)

## Objective

Prepare 0.60.0 with bounded compact indices, canonical proof ownership, current documentation and reproducible evidence. Preserve unresolved production assertions.

## Changes

- Add `--nth-power10 K` and common index admission.
- Move formal sources to `proofs/isabelle`, Python verifiers to `devtools/verification`, and reviewed records to Sunday-start `docs/sprints`.
- Centralize schema 8 documentation, capability examples, fresh run manifests and serialized release commands.
- Set package metadata to 0.60.0; no tag or publication.

## Established results

- Formal migration preserves all 227 Isabelle files byte-for-byte.
- Every former Python proof file has a canonical verification owner.
- Index queries retain integer execution and compact presentation; no symbolic scheduler is claimed.
- Independent audits retain source-authority checks and positive cutover assertions.

## Rejected approaches

- Treating historical fingerprints as evidence for the migrated source.
- Retaining per-topic Git exceptions or putting authored fixtures in generated results.
- Replacing a failed construction assertion with successful refusal.
- Counting a focused proof build as aggregate acceptance.

## Validation provenance

The September 29 record below distinguishes baseline, intermediate fixes, frozen-source validation and reviewer scope. Raw evidence remains ignored/local.

## Remaining work

Existing reverse/add construction, special-number recovery, Collatz executable refinement, comma proof and global non-halting obligations remain active. Aggregate acceptance is required before publication.

## September 29 — 0.60.0 documentation and launcher disposition

Date: 2026-09-29 (America/Phoenix). Objective: separate authored proof and sprint sources from raw runs while preserving exact semantics and historical evidence.

**Changes:** formal sources move to `proofs/isabelle/`, Python verification owners to `devtools/verification/`, and reviewed weekly summaries to `docs/sprints/`. The Sunday calendar, original record anchors, dates, fingerprints and outcomes remain intact. Current guides use schema 8 metrics. The CLI capability table comes from the admitted registry; its examples are parsed without executing arithmetic. The scaffold registers new categories and refreshes generated topic links/counts without replacing authored topics. Superseded release rows are retained in the [historical ledger](../history/release-status-through-2026-09-27.md).

**Launcher disposition:** 26 ignored Python launchers were inspected. Quality/final-check wrappers map to `devtools.checks.release`; wheel wrappers map to `devtools.checks.package_release`. Growth wrappers call the maintained `collatz_temporal_power_probe` and `production_p0_probe` owners. Focused historical selections remain recorded commands, not new release gates. Original raw scripts and payloads remain at their local historical paths.

The useful current public output and point-demand comparison logic from `wide_cli.py` and `point-germ-bench.py` is maintained in `devtools.benchmarks.public_query_comparison`. Its family, horizons, trials, modes, seed, output bases and point coordinate are configurable. Cold CLI samples include interpreter startup; point timings include public projection construction. Warm priming and every measured sample are retained, including a mismatched sample before rejection. It checks public-route agreement against a separate public API owner; that reference is not an independent literal oracle. The old private direct/cursor threshold override is not carried forward.

Historical previous/current Antihydra leaf, comma phase-prefix, modular-residue and locator-walk micro-comparisons remain retired experiments. They depend on previous implementations or one-off instrumentation; their old timings retain only their recorded source and scope. Downloaded Mahler input/archive scripts remain review evidence and do not authorize restoring rejected constructors or absolute Downloads imports. The custom Collatz CLI case wrapper duplicates configurable current public-query measurements.

**Validation provenance:** the relocation audit accounted for all 317 formerly tracked proof-tree files: 90 Python, 214 theory, 12 ML and one ROOT file. Formal sources and session registration are byte-identical; Python content differs only by canonical namespace/path substitution. Production identity sealing and proof-payload admission retain their original checks. Focused boundary/package/proof-index tests passed 96 cases, with one validation case deselected, in 17.48 seconds. Documentation tooling passed 15 tests; comparison tooling passed two tests, including mismatch retention. Strict scoped mypy, Ruff and formatting passed. These scoped checks are not aggregate release evidence. Final source fingerprints and full gate outcomes are recorded by the [current release ledger](../../release-status.md).

**Remaining work:** all mathematical, generic construction and runtime release blockers remain active. No theorem assumption, session, positive assertion, threshold or release claim was weakened by this migration.


### Assertion and source-ownership disposition

- The repository metadata test retains its exact version contract, updated from 0.59.9 to 0.60.0. The successor-congruence probe compares its reported version to the canonical metadata helper.
- The Collatz population test now counts `source_image_demanded_composite_applications`, the current demanded-publication path. The temporal reporting test expects `collatz-dyadic-source-image` and checks its action/image/projection publications and absence of retired parent construction instead of requiring tile-leaf work. Both keep `bounded_temporal_runtime_cutover_complete == 1` and an empty blocker; `dyadic_worklist_refinement_pending` still fails them.
- All 90 Python proof/reference files were accounted for; shared research oracles remain under `devtools/verification`, while independent test-only support remains under `tests/support`. The 214 theory files, 12 ML files and ROOT are unchanged. No dependency leaf was deleted as presumed dead.
- Clean-wheel verification checks developer/formal-file exclusion and 27 cold CLI contracts. Its Antihydra ledger assertions apply only to the command that requests ledger information; value-only compact queries retain their separate output assertion.
- The release runner preserves seven P0 module selections, guarded collection, exact JUnit identities, source revision checks and the 300-second unfiltered evidence gate. A restored source edit invalidates evidence even if the bytes match again.

### Validation inventory

The pre-edit baseline is HEAD `37ee4d3945683ab063f13e552a8909a4c40dc736`, with an initially clean tracked tree. Its version-4 fingerprint is `748666a2de9ebf37aa154478d30ba76d1ae608788f726336d6a9221a2907d718`. Local baseline evidence is `results/runs/20260930T010227Z-cbab1a85c2/`: 7,454 unit passes, 42 failures and 1,989 deselections; 13 P0 passes and 50 failures. The exact node lists and messages are retained in its `unit-failures.json` and `p0-failures.json`.

Intermediate validation found two packaging-harness defects: an unavailable parent-environment setuptools backend, corrected by isolated builds using declared build requirements, and an observation parser incorrectly applied to value-only Antihydra output, corrected by checking the requested observation. The first migrated full-unit run added one stale 0.59.9 assertion failure; its expectation was updated without removing the test. These intermediate runs do not certify the final source.

Final authored-source fingerprint version 5: `f64b7e72d16ed3fa7c365138ab5978b23002e1587429b00793f09b42dc68c1a9`. It covers project metadata and authored `src`, `tests`, `devtools` and `proofs`; documentation provenance is checked separately. All jobs are serialized. Probe/quality guards remain 35 seconds/1 GiB, proof guards 60 seconds/4 GiB, and units 300 seconds/1 GiB. No skip, expected failure, theorem assumption or threshold was added to make acceptance pass.

Independent review covered byte-preserved proof relocation and namespaces; installed-package contents and smoke assertions; compact index admission/presentation/laziness; source revision/fingerprint authority; and equivalent diagnostic migrations preserving the red cutover gate. The final quality/wheel evidence is `results/runs/20260930T014635Z-c54bb7492b45442fa4242eaa1bb11790/`.


### Frozen validation results

Commands use `.venv/bin/python -m devtools.checks.release --suite SUITE`; proof focus adds `--session Prefix_Effect_Core --session Shared_S_Arithmetic`. Run-directory names below are relative to local ignored `results/runs/`. Each parent manifest records unchanged version-5 source `f64b7e72d16ed3fa7c365138ab5978b23002e1587429b00793f09b42dc68c1a9`, tool versions, commands, per-step limits and outcomes.

| Selection | Result | Guarded wall time / sampled peak | Local run directory |
| --- | --- | --- | --- |
| `quality` | Strict mypy (1,561 files), Ruff, formatting, policy, docs, proof index and clean wheel pass | Each step <35 s / 1 GiB; wheel 30.640 s / 119.88 MiB | `20260930T014635Z-c54bb7492b45442fa4242eaa1bb11790` |
| `unit` | 7,582 passed, 42 failed, 1,989 deselected | 268.878 s / 805.92 MiB | `20260930T014738Z-8c952fd010bb4a9b97ea4bd8bc9e3318` |
| `p0` | 13 passed, 50 failed | 2.106 s / 85.05 MiB | `20260930T015227Z-3600864e23b24b4a89bab5493531b41d` |
| focused `proofs` | Prefix_Effect_Core and Shared_S_Arithmetic pass; current heaps reused | 5.371 s / 1,121.88 MiB | `20260930T015255Z-ae3b0957f48b443f802f0fc2c5b42a50` |
| aggregate `proofs` | TIMEOUT at 60-second limit; Comma_Cylinder completed, Comma_Chart_Bridge had started | 60.179 s / 2,538.49 MiB | `20260930T015353Z-0abce566cc804de7be693693bea15b73` |

The earlier focused run rebuilt Shared_S_Arithmetic and Prefix_Effect_Core successfully in approximately 25 seconds; the final check reused those unchanged heaps. Aggregate acceptance is not inferred from incremental progress. The fast formatting process ended before a memory sample: its peak remains null rather than a fabricated zero. The nested wheel manifest describes itself as unguarded; its parent release record supplies the actual 35-second/1-GiB external guard. Actual validation tools are Python 3.14.7, pytest 9.1.1, mypy 2.3.1, Ruff 0.15.22 and Isabelle2025-2; declared dependency minimums were not rewritten to match this host.

**Individual failure disposition:** the final unit run's `failure-disposition.json` stores every failed node, exact message, baseline identity and reviewed obligation, including the P0 rows. All 42 unit failures match baseline identities: 41 reverse/add temporal publisher/sector-construction failures and one special-number concrete-resolution failure. All 50 P0 obligations remain: 35 reverse/add, six Collatz executable-refinement, eight special-number shadow recovery, and one source-7 non-halting certificate. The reporting test's Collatz parameter label changed from `collatz-tile-hashlife` to `collatz-dyadic-source-image`; its baseline mapping is explicit and its positive cutover assertion still fails. The counter taxonomy repair exposes that same pending-refinement failure at horizon 128. No baseline failure was hidden, removed or reclassified out of the selection.

Hygiene implementation, package preparation and focused migration checks are complete. Release acceptance remains blocked by the listed unit/P0 obligations and aggregate proof timeout. The unfiltered `all` suite and five-trial growth manifest are not certified by these unit/P0 runs. No release tag or publication was created.


## September 29 — Executable source-policy enforcement

Date: 2026-09-29 (America/Phoenix). Objective: replace the descriptive repository rules document with source-level gates.

**Changes:** delete `REPOSITORY_RULES.md`; the README links directly to the policy implementation and its tests. The common 1,000-physical-line check includes Python/stubs, Isabelle theory/ML and ROOT/ROOTS sources. Python call-graph checks now cover local callable aliases, lambdas, async functions and renamed method receivers; parameter shadowing has a negative regression. Existing static-call-analysis limitations are documented, not presented as a universal runtime proof.

The new shared AST clone owner checks complete bodies, nested suites and contiguous three-statement windows. A report requires at least 24 expression/statement nodes and three executable statements. It normalizes lexical local bindings and preserves parameter position, shadowing, constants, operators, attributes and free names. Hash matches are verified by complete token equality. Tests cover renamed bodies, shared internal blocks, distinct operations, scopes and a deliberately colliding digest. No path allowlist, suppression or accepted-debt baseline was added.

**Rejected approaches:** retaining the rules document as an enforcement mechanism; equating same-shaped expressions after erasing constants/free names; accepting a digest match without equality checking; sharing a production algorithm into its independent test oracle just to clear a finding; increasing the guard to accommodate a slow checker.

**Performance and evidence:** an initial combined scan exceeded 35 seconds. Profiling isolated AST normalization; cheap size admission, specialized name/constant tokens, fixed-width statement windows and path-indexed coverage checks removed repeated work. The first complete quality run is local `results/runs/20260930T021521Z-2c6897255b194ab786609396424b6cbd/`, fingerprint v5 `0a3b63817a68766dffd4027c78a79a0449123ac9d10b72262104804e5588b47d`. Its policy scan took 26.307 seconds with 670,516,184 sampled peak bytes under 35 seconds/1 GiB. Strict mypy checks 1,563 source files; typing, Ruff, formatting, documentation, proof index and clean installed wheel pass. The policy command exits nonzero.

**Established result and remaining obligation:** there are no current line-cap, resolved-recursion or package-boundary violations. The newly enforced clone gate reports **706 groups**, containing reported occurrences in production, developer tools and tests. Its JSON contains the full file/function/line locations. These are structural duplicate findings, not proofs that the algorithms can be substituted without reviewing their contracts. Duplicate cleanup remains required; the findings are neither suppressed nor mislabeled as a clean repository. The earlier 0.60.0 full-unit/P0/proof results belong to fingerprint `f64b7e72…dc68c1a9`, not to this new policy source. No production arithmetic or Isabelle theorem changed in this follow-up.


**Final policy validation:** source fingerprint v5 `93dd29a3d6cee220e67cae26fe2ec4e8d00e019a30b04871af2e4882e4a88187`. The current quality run is local `results/runs/20260930T021947Z-c70b7e41f59c4e56aaa025ce59cc9a75/`: all checks except the duplicate-code gate pass; that scan completes in 25.837 seconds and reports the same 706 groups. The focused policy-test run is `results/runs/20260930T022107Z-ae2a4e3995924479ab794edecaf70e8e/`: **55 passed, one failed**. The sole failure is the repository's actual duplicate-logic gate; its 53 behavioral regressions and both live line/recursion gates pass. Both manifests record unchanged source and retain the 35-second/1-GiB limits. A mistaken capture-producing rename in a test fixture was corrected and retained as an explicit negative case. No duplicate finding was allowed away. Full production units, P0 and Isabelle compilation were not rerun for this tooling-only follow-up; their earlier evidence remains tied to its original fingerprint.

## September 29 — Adversarial policy and memo audit

Date: 2026-09-29 (America/Phoenix). Objective: challenge static policy coverage and exact cache authority before publication.

**Changes and established results:** separate workers audit clone normalization, static recursion resolution and observation-cache admission. Collatz event cocycle lowering previously accepted a foreign arena's event with the same integer node ID: after caching valuation 1, lowering a foreign valuation 3 returned the cached shift 1. The lowering, exact application and metrics consumers now validate arena ownership; numeric ID aliases are rejected. Warm lowering consumes the admitted cocycle before traversing or composing children.

Microblock publication snapshots bounded scalar key/program/payload fields. Returned payloads cannot alias the retained record, and subclasses cannot override key or payload admission. Tests explicitly exercise low-level `object.__setattr__` corruption of frozen caller records; ordinary frozen assignment was already prohibited. Existing replacement, reservation, eviction and failure rollback contracts remain. Retained logical entry and encoded-payload accounting is unchanged; this is not a new heap-allocation accounting theorem.

**Rejected approaches:** trusting an arena-local integer without its owner; treating a digest alone as clone evidence; broadening static resolution without negative shadowing tests; clearing existing duplicate findings through allowlists. The audit does not prove arbitrary dynamic Python call behavior or erase the independent production release obligations.

**Checker findings:** the clone audit fixes same-line span collisions, substantial single-expression omissions, local class bindings, enclosing capture identity and substantial standalone lambdas. Canonical token bytes are retained once and compared exactly after digest matches, avoiding repeated whole-file binding reconstruction. Recursion fixes distinguish lexical and comprehension scopes, callable aliases and actual method receivers; negative tests accompany broadened resolution. These remain static structural checks, not semantic equivalence or dynamic-dispatch proofs.

**Validation and remaining work:** source-bound validation is recorded below. The pre-existing duplicate-logic gate remains active, as do all mathematical and construction gates.


**Frozen quality evidence:** fingerprint v5 `7cf3196cca1dbffaf03397fabeddf12c6992f08f7cb26aac375cabcaa51d2873`, local run `results/runs/20260930T024531Z-1837fa0405e846da8a848ea154ce52b7/`. Strict mypy (1,563 sources), Ruff, formatting, documentation, proof inventory and the clean installed-wheel contracts pass. The policy scan completes in 27.628 seconds with 803,800,120 sampled peak bytes under the unchanged 35-second/1-GiB guard. It reports zero line-limit, resolved-recursion and package-boundary violations and **711 structural duplicate groups**; that gate fails normally. Expanded scope checking does not create an allowlist. A probe during concurrent edits (`20260930T023727Z-e0c43d7d217a4f139879929d635bd848`) was rejected as `source_changed` and supplies no acceptance evidence.

**Targeted regression evidence:** local `results/runs/20260930T024657Z-ec898babb3ae433790bec988c810568a/` records **208 passed, one failed** on the same frozen source, 28.880 guarded seconds and 832,423,040 sampled peak bytes. The sole failure is the live duplicate-code gate; checker fixtures and scoped cache/port authority, replacement, eviction and rollback regressions pass. The pre-existing HigherTemporalImage workspace now binds its consumer and active source extent; this audit did not find a new stale-consumer defect there. Independent cache review additionally required per-descendant validation during the already-required exact event traversal; no extra full-tree pass was introduced.

**Final consolidation and freeze:** the new gate identified one copied comprehension-scope block inside the checker itself; list/set/generator and dictionary comprehensions now share that traversal. An in-progress unit run (`20260930T024748Z-14cdf011263c494098d1ee239ee4c15b`) was explicitly interrupted before this source edit, not accepted as a pass. Final fingerprint v5 is `da1d32975c9f064269a1ecbbecc2c13da821897b9fc0a16d3a6e84d67e3d888b`. Quality run `results/runs/20260930T024952Z-fa744bdfb5b94f98ada48f422165aee2/` passes all owners except the active clone gate, now **710 groups**. Its policy scan takes 27.739 seconds and 801,260,624 sampled peak bytes. There are zero line-limit, resolved-recursion and package-boundary findings. All 81 isolated checker fixtures pass; the live clone assertion remains unmodified. No skipped tests, suppressions or increased limits were introduced.

**Final full-unit evidence:** `results/runs/20260930T025105Z-a831a6925cba484da8c837fd427f84ab/`, unchanged final fingerprint `da1d3297…e3d888b`. The suite reports **7,646 passed, 43 failed, 1,989 validation tests deselected** in 281.62 pytest seconds (283.119 guarded seconds), with 1,014,220,072 sampled peak bytes under 300 seconds/1 GiB. The local `failure-disposition.json` maps all 43 failures: all 42 earlier production failure identities remain, and the only additional failed identity is the active structural-duplicate gate. No baseline failure disappeared. This is failed release evidence, not a successful all-tests result. P0 and Isabelle results remain scoped to their earlier fingerprints; no formal source changed and no proof rebuild is claimed by this audit.


## September 29 — source-policy cleanup and regression review

**Date range:** 2026-09-29 (local); final validation artifacts use September 30 UTC timestamps.

**Objective:** clear every source-policy failure without changing the checker, exclusions, complexity thresholds, resource limits or positive production assertions.

**Changes:** workers consolidated shared finite arithmetic, automaton construction, iterative dependency scheduling, publication and audit logic into canonical owners. Tests and probes share scenario fixtures and bounded literal references outside the installed package. Independent oracles remain separate from the production operations they verify. No existing unit case was removed.

**Established results:** the unchanged whole-repository checker now reports zero substantial alpha-equivalent duplicate groups (previously 710), zero resolved recursion cycles, zero source-line violations and zero package-boundary violations. Strict mypy checks 1,601 sources; Ruff, formatting, documentation, proof indexing and 27 installed-wheel CLI contracts pass.

**Adversarial review and repairs:** independent reviewers checked source/handle authority, chronological composition, cache zero/None handling, fixture assertions, poison timing and oracle independence. Snapshot fault injection exposed reservation leaks in completed-result, fused-interface and behavior publication; these now release or avoid reservations before failed publication. Four new unit cases cover those failure paths. Review also caught lost sorted edge deduplication and misleading per-side builder timings in shared developer helpers; both were repaired, with two research regressions covering remapped-arc deduplication.

**Rejected implementation:** an intermediate lazy-carry helper collapsed raw monoid code 2 (force one) into code 1 (identity). The first full run exposed five newly failing recurrence cases. The helper now returns the raw code and leaves carry decoding after the identity test; a focused regression protects that distinction. The earlier claim that the `(9,10,10,9)` scan failure predated cleanup was incorrect and is superseded by this finding. The intermediate source is not final acceptance evidence.

**Validation/provenance:** final authored-source fingerprint v5 is `795bca0f2d26d766644b1514c02923c4310e8b06edc7589fef55eed994cbe9c1`. Commands are `.venv/bin/python -m devtools.checks.release --suite quality` and `--suite unit`, serialized on the frozen tree. Quality/probes retain 35 seconds/1 GiB; units retain 300 seconds/1 GiB. No formal source changed in this cleanup and no new Isabelle build is claimed.

| Evidence | Source | Result | Local evidence directory |
| --- | --- | --- | --- |
| Starting unit baseline | `da1d3297…e3d888b` | 7,646 passed; 43 failed, including 710 clone groups | `results/runs/20260930T025105Z-a831a6925cba484da8c837fd427f84ab/` |
| Intermediate full run | `168d87f5…22fa66a` | 7,646 passed; 47 failed; five introduced carry-tag failures caught and repaired | `results/runs/20260930T043806Z-1105d22ffdb043758ac6c640e2ab9479/` |
| Final quality | `795bca0f` | All gates pass; policy 30.296 seconds, 791,528,504 sampled peak bytes | `results/runs/20260930T044540Z-0558aeff074b43b89bd3dbc6cb6a323e/` |
| Final full units | `795bca0f` | 7,652 passed; 42 existing failures; 294.455 guarded seconds, 991,085,816 sampled peak bytes | `results/runs/20260930T044657Z-e74c99d279b047aaad7b03bb4bd8c293/` |

The final local `failure-disposition.json` maps every failure to its exact baseline identity, records all newly added cases and confirms no removed unit identities. All 42 original production failures remain; the structural-clone failure is resolved. No skips, expected failures, suppressions or relaxed limits were introduced. Raw evidence remains ignored local storage.

**Remaining obligations:** source-policy cleanup is complete. Release remains blocked by the 41 reverse/add construction cases and one special-number concrete-resolution case in the unit selection, along with separately recorded P0, mathematical, performance and aggregate-proof obligations. Consolidation does not establish the missing temporal grammar or authorize publication.

## October 1 — test ownership and runtime naming audit

**Objective.** Attribute runtime failures to their real family and distinguish
runtime validation from executable proof, without relaxing release assertions.

**Changes.** Reverse/add cases formerly under Collatz move to reverse/add owners;
cross-family cache and output checks move to shared HashLife/runtime modules.
Runtime publication/replay checks leave `validation/proofs` and retain explicit
validation membership. The canonical `release.P0` selection follows the moved
cases. Shared source-image assertions and independent literal arithmetic have
one support owner rather than copied family implementations.

The mixed idempotent-output module is split into field-arithmetic, projection,
and special-number compiler tests. All eight original bodies are preserved; the
compiler test name now identifies its demanded-concrete-output contract. The
source-image benchmark replaces the misleading linear-bisimulation name. The
Collatz C4 developer reference and its metrics class identify their family and
reference-only scope; production import-firewall and poison paths follow the
rename. Collatz source-word comparison tests no longer use “reverse” to mean
backward traversal of a Collatz source word.

**Assertion disposition.** P0 runtime cases retain their assertions, parameter
coverage, validation selection and inherited accounting selection. Their former
implicit `proof` marker is
removed because they execute runtime checks, not theorem builds. Historical
records retain their original names and fingerprints. The adversarial registry's
four nonexistent function selectors and one deleted module are replaced as follows:

| Retired selector contract | Current assertion owner |
| --- | --- |
| Reverse probe interval/discovery reporting | `test_reverse_release_probe_requires_measured_source_image_execution` |
| Bounded application versus recursive history | `test_reverse_production_requires_exact_output_and_source_image_evidence` |
| Reverse interval/carry metric labels | `test_reverse_source_image_reports_exact_output_and_publications` |
| Action composition/discovery metric labels | `test_action_metrics_report_image_publication_and_warm_response_reuse` |
| Deleted global source-handle audit module | Recursive field-image authority suite plus foreign dyadic handle/composite-source audits |

The retired metric labels are not reintroduced. Their replacements check exact
output, actual source-image publications, forbidden interpreter work, accounting
and warm reuse. No missing selector is silently ignored, and no passing report
is inferred from a renamed case.

**Rejected approaches.** Keeping reverse failures under a Collatz module;
retaining a proof label on runtime checks; importing helpers from test modules;
renaming public term APIs; rewriting historical evidence as current evidence.

**Validation/provenance.** Frozen source v5
`f37500e1f794b43bc7d6ba7f7bb534fe385f1dd17854715dcbf6e80ec063aeca`.
Evidence is local at
`results/runs/20261001T205338Z-64257e7f879c4b48b63a40cd6c50e278`,
with affected-test confirmation at
`results/runs/20261001T210124Z-424fb43101be44f2a2d2df53afcdbe91`.
Typing (1,657 sources), Ruff, formatting, source policy, docs, proof inventory and
installed-wheel checks pass. All 597 adversarial selector nodes resolve. The
explicit relocation map preserves every one of 8,296 unit and 60 P0 instances;
P0 outcomes are unchanged at 33 passed / 27 failed. Affected units are 182 passed
and the existing special-number compiler failure; 63 Collatz reference-poison
cases pass. Full units hit the unchanged 300-second limit after 98% progress,
so no full-suite pass or unchanged full-suite outcome is claimed. No theorem
source changed, and Isabelle builds were not repeated for naming-only changes.

Independent review checked assertion bodies, reference-firewall names and private
comparator calls. A dropped post-demand family assertion was restored before
validation. The final explicit validation decorators and the conftest path marker
were checked; a stale intermediate warning about missing validation marks did not
apply to the frozen files. The three relocated cases that lost filename-derived
accounting markers now carry explicit accounting marks. Earlier runs stopped for
a missing package initializer or a changed source and are not passes.

**Remaining obligations.** This ownership repair does not close the reverse
constructor, special-number recovery or non-halting failures. Those positive
gates remain active under their corrected owners.
