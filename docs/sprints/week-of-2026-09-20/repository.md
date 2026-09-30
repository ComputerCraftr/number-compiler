# Repository, CLI and validation

Period: 2026-09-20 through 2026-09-26 (Sunday–Saturday).

## Objective

Record the scoped implementation and research work below without extending its claims to later source.

## Changes

The dated records retain the authored changes and original section anchors.

## Established results

Each result below applies only to its stated source, assumptions and run.

## Rejected approaches

Rejected proposals and withdrawn findings remain in their original records.

## Validation provenance

Original dates, fingerprints, commands, outcomes and raw evidence paths are preserved below. An exact day is not inferred when only the weekly context was recorded.

## Remaining work

Open obligations retain their recorded scope; consult [current release gates](../../release-status.md) for the current disposition.

[Week of 2026-09-20](README.md) · [Documentation index](../../index.md)

## Records

- [Repository hygiene validation, 2026-09-20](#repository-hygiene-validation-2026-09-20)
- [Documentation consolidation, September 22](#documentation-consolidation-september-22)
- [Adversarial ownership and duplicate cleanup](#adversarial-ownership-and-duplicate-cleanup)
- [CLI selector and reporting audit](#cli-selector-and-reporting-audit)

## Provenance

Original records and caveats follow. Their evidence certifies only its recorded
source and scope. Records without a precise day retain their original weekly
context; listing order is not evidence of execution order.

## Repository hygiene validation, 2026-09-20

Record period: 2026-09-20.

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
shown in [development](../../development.md).

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
removal**. The [test-by-test disposition](../history/hygiene-disposition-2026-09-20.md)
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


## Documentation consolidation, September 22

- Moved 34 implementation/evidence records from four research papers into
  W38/W39. Research prose fell from 3,092 to 2,087 lines across the six papers
  (about 32%); mathematical scope and open obligations remain explicit.
- Added topic navigation, expandable historical detail, provenance mapping and
  a documentation-placement rule. Preserved existing incoming section anchors.
- The documentation checker and its six regressions pass. Both preserved
  external reverse/add archive hashes are unchanged.
- Authored code/proof fingerprint remains
  `a7b76d65ad48bb81284a90e21a552ab739e33f7e2fc262d8f0755d73cf65a1b3`.
  No runtime, proof or performance gate was rerun or closed by this edit.

Reproduction:

```console
python -m devtools.checks.docs_index
python -m pytest -q -o addopts='' tests/repository/test_docs_index.py
```


## Adversarial ownership and duplicate cleanup

Record date: exact day not recorded; retained in its documented weekly context.

**Objective:** remove unused execution owners and duplicated arithmetic/proofs,
while retaining positive tests for the incomplete powered constructors. Three
agents audited continuation ownership, family algebra and theory dependencies;
the continuation and algebra owners then reviewed each other's changes.

| Component | Disposition | Verification scope |
| --- | --- | --- |
| `virtual_field_provider.py` | Deleted its 154-line unreferenced implementation | No repository imports, dynamic names, facade exports, tests or proof consumers; absence added to the existing retired-module test |
| Antihydra total/guarded cylinder joins | One CRT/source-chart/skew helper | Both consumers retain their own semantics; high-fiber composition, ledger threshold and physical identity regressions |
| Arithmetic-only Antihydra queries | Physical roof translation remains lazy | Independent review caught and removed an extra bigint calculation introduced during consolidation |
| Private Collatz compiler forwarding method | Removed; dispatcher calls the canonical implementation directly | Public compilation API and explicit orbit semantics unchanged |
| Palindrome reflection proof | One `Mirror_Pair_Step.palindrome_nth_reflect` | Publisher and growth proofs reuse the same assumptions/conclusion; no new import edge |
| Finite event-clock claims | Names and scope corrected | `reassociation_preserves_clock_transfer` and `event_clock_s_arithmetic_exponents` do not claim CLI refinement |
| Higher temporal/provider contracts | Retained, with narrower ownership descriptions | Still used by tests/proof oracles; a generic executor or point observer does not supply the missing reverse D4+ constructor |

The central Isabelle parser inventories 19 sessions and 106 theories. Its
remaining exact-statement duplicate is a named one-line Collatz corollary, not
a second independent proof. A theory's leaf position alone did not justify
deletion. No tests, release assertions, public term APIs or resource limits
were removed or weakened.

The F5 audit found one canonical `radix64_phi5` definition. Directional
observers and delegated centered/spatial transports have distinct roles and
were retained. The higher temporal provider's sole binding validator fixes
its producer action and checks the exact compiled source/output. No admitted
collision was reproduced in 20 singleton and 400 pair probes; this finite
check is not a proof of successor right-congruence.

Evidence is local under `results/current/adversarial-ownership-cleanup/`
(`scope.json`, guarded logs and JUnit reports); the central-parser inventory
is under `results/current/proof-hygiene-audit/inventory.json`. Authored-source
fingerprint: `6e61aa4d41d992d540316ea1bb6f5a58494b257abc766df6368a2994b66661d0`.

The combined reverse/étale proof invocation exceeded the unchanged 35-second
limit after rebuilding `Reverse_Residuals` in 25 seconds. The separately
guarded `Etale_Primary_Carry` build passed in 18.72 seconds. This is focused
proof evidence, not an all-session acceptance result. Missing complete reverse
construction, classification and source-global safety obligations remain open.

The first wheel check rejected a real stale build product: setuptools had
repackaged the deleted provider from ignored `build/`. After confirming that
`build/` contained no tracked files, that generated tree was removed and the
wheel rebuilt. Raw failure evidence remains in `installed-wheel.log`; the
source/package equality check was retained unchanged.

### Collatz validation-owner migration

The fresh cutover run disproved an audit inference from historical output:
`direct_powered_point_queries` is now correctly one. The three live failures
were retired tile/radix-4 counters and schema 6 expected from a schema 7 probe.
The migration is limited to `test_collatz_block_power.py` and its existing
`collatz_temporal_power_probe.py`; no production executor changed.

| Previous assertion | Current acceptance | Preserved requirement |
| --- | --- | --- |
| Positive bounded-local-interface applications at N256 | Positive admitted source-image, postorder, primitive and bounded-base work | Exact digit and width, no temporal leaf execution, direct demand and <25,000 measured operations |
| Exactly one radix-4 source morphism at N64 | Positive dyadic action, image and projection publication | Exact digit, old radix-4 codec poisoned, no scalar generation |
| Schema-6/tile-counter report | Schema-7 source-image report with required instrumentation | Original horizons and numerical doubling envelopes; audited entries and nodes, separate operation/operand-bit/seal-byte measurements |

The finite 16/32 workload passes its measured envelope while the report stays
RED for the unresolved global source-construction bound. The independent
positive `cutover_complete == 1` tests were not changed to expected failure or
expected refusal. A new poison regression removes mandatory instrumentation
and requires rejection; missing measurements cannot be treated as zero work.
The old source-image-unconnected provider contracts remain explicitly scoped
as tested primitives, not evidence that the reverse CLI cutover is complete.

Final authored-source fingerprint after this validation-owner migration:
`7562db08d01b1abd53d7c91007aa457daf7e5b023c99f37ae1a46e174a6bd2a3`.
The initial 6,484-pass/42-failure run belongs to the preceding cleanup
fingerprint above; final reports use the `frozen-` evidence prefix.

Final validation on the final fingerprint:

| Check | Result | Evidence and limit |
| --- | --- | --- |
| Full unit selection | 6,485 PASS / same 42 FAIL | `frozen-unit`; 202.00 s / 813,220,968 sampled bytes, within 300 s / 1 GiB; no new failed node IDs |
| Migrated Collatz checks | 7 PASS | `frozen-collatz`; includes missing-instrumentation poison |
| Expanded reverse/family/Collatz cutover | 14 FAIL / 13 PASS | `frozen-cutover`; three obsolete Collatz tests migrated, every reverse assertion retained |
| Separate positive Collatz cutover | 5 FAIL | `frozen-positive-cutover`; original tests remain active and unchanged |
| Strict mypy, Ruff, format, policy, docs, proof inventory | PASS | `frozen-quality-v3`; 1,474 files, 19 sessions / 106 theories |
| Focused Isabelle | PASS | `Reverse_Residuals` and separate `Etale_Primary_Carry`; no skipped proofs or new axioms |
| All registered Isabelle sessions | TIMEOUT | `frozen-proofs-all`; 35.07 s / 733,745,472 sampled bytes under 35 s / 4 GiB |
| Clean installed wheel | PASS | `frozen-installed-wheel`; source/package equality and 15 CLI contracts |

The full unchanged Collatz probe (`frozen-collatz-probe`) reports RED with
`source_image_work_exceeds_doubling_envelope` and
`source_global_powered_construction_bound_unproved`. Its source-image operation
counts at N=16/32/64/128/256 are 326/368/434/1,165/1,719. In particular,
1,165 exceeds the preserved `2*434+64` envelope. The smaller 16/32 test's
finite PASS is not the full probe's result. Operand-bit and seal-byte volumes
are separate columns rather than being counted as operation counts.

This audit removes confirmed unused code and duplicate ownership. It does not
close the reverse temporal constructor, F4 terminal resolution, the broader
performance gates or aggregate proof acceptance. Remaining tested provider
primitives have explicit conditional scope; their presence is not a production
cutover certificate.


## CLI selector and reporting audit

Record date: exact day not recorded; retained in its documented weekly context.

- **Objective:** align common information columns and eliminate execution caused
  only by reporting. Three agents audited selectors, resource extraction and
  cross-family output independently.
- **Changes:** common CLI packets now carry `family`, `kind`, `index`,
  `index_unit` and `status`. Selector units distinguish Collatz physical ticks
  from accelerated events and Antihydra post-startup return coordinates.
  Collatz event queries reject unused radix/output controls; family help and
  listing expose selector-specific choices. An unresolved special-number factor
  request now retains UNKNOWN and exit 3.
- **Reporting:** reverse/add, Collatz and Antihydra share the scalar-ledger
  schema-eight snapshot. CLI reporting never runs semantic payload audits or
  inventory callbacks. Observer packets omit unsolicited work-counter copies;
  direct Python APIs preserve their detailed default reports. Extraction counts
  are separate from computational counters; dictionary conversion and JSON
  serialization are not claimed as measured execution work.
- **Validation work:** Antihydra authority checks stream retained segments,
  rejecting the first mismatch without allocating a second complete tuple.
  Reconstruction counts and operand-bit work are exposed. Repeated validation
  across separate public trust boundaries remains required; this change does
  not introduce an unauthenticated shortcut or establish constant-time sealing.
- **Assertion mapping:** CLI raw work maps move to explicit `--info metrics`.
  Physical clock publication and Antihydra return/Mahler assertions remain.
  Installed event safety keeps its exact output checks and inspects the actual
  published production support for discovery accounting. Detailed Python audit
  inventory checks remain separate from the poisoned CLI audit path.
- **Scope:** no mathematical indices, recurrence, constructor, proof assumption,
  or positive reverse/add release assertion changed. Event metrics remain
  unsupported by the existing selector contract and are identified as such in
  help. No new temporal cutover or performance-bound claim follows.

Local evidence: `results/current/cli-schema-audit/`. The final validation record
and fingerprint are in `validation.json` and `source-fingerprint.txt`; raw logs
are local evidence, not portable download links. Prior failing constructor tests
remain active. Isabelle theory sources were not edited in this audit.

Validation on `c471e9e126d7787536f97f3d2be8700897abe16328159dca134127458d447ccf`: full units **6,536 PASS / same 42 FAIL**,
1,893 validation deselections; zero added or removed failure node IDs.
The full run took 221.16 s and 795,214,976 sampled bytes under 300 s / 1 GiB.
Installed-wheel inventory, CLI and source-owner checks passed in 5.18 s.
Quality, documentation and proof-index checks passed; Isabelle builds were not
rerun because this audit did not edit theorem sources. The first wheel command
lacked a local setuptools backend; isolated wheel building succeeded without
changing repository dependencies.
