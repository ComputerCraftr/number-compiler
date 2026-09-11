# Causal reuse checkpoint — release RED

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../README.md).

The requested plan is **not complete**. Private P⁴/P⁸ causal execution and additional reuse/accounting regressions pass. Public reverse and Collatz builders still route deep observations through higher continuations. Cold causal work remains superlinear in the measured growing-196 range.

Source fingerprint: `7c150a182c8ff17eb4aff18b61d61a5a45dcda8263a075b636ccdaa395e6fb3a`.

## Implemented in this pass

- Added completed interface-only observation bindings and directed primitive-transfer bindings under the existing `CompletedResultArena` owner. Warm hits precede child construction and reduction. No additional semantic arena or competing execution-memo owner was added.
- Added an early completed boundary-parent probe. A repeated dyadic boundary demand can return its completed result with producer scans, leaf evaluation, and output joins poisoned.
- Moved causal spatial buffers, task memos, active requests, primary frames, and directed auxiliary stacks into charged index-owned workspace. Spatial reference collection uses append-based buffers instead of repeated tuple copying. Reservations precede publication, and focused budget/exception tests verify cleanup.
- Reused normalized boundary pieces across dependency continuations, and replaced redundant temporal-spine alphabet validation with the admitted local alphabet witness.
- Preserved strict scoped IDs and repaired prepared directed-transfer validation against same-object numeric-alias mutation. Result-lease inspection remains read-only while request/lookup/publication validation stays counted.
- Extended independent inventory checks and fresh-process evidence reporting. Reports separate work units, live populations, cumulative spatial-buffer allocation, peaks, timing phases, raw values, increments, doubling ratios, and effective exponents.
- Fixed benchmark acceptance: a custom prefix cannot report a release-range pass. Required/requested/observed/missing manifests and diagnostic status are explicit. Missing measurements and timeouts are not zero-valued successes.
- Rejected an unsafe blank-prefix shortcut. Existing blank-tail metadata establishes output-padding readiness, not a general directional carry reset. Noninitial-port counterexamples are retained.

The ten tests in `tests/test_powered_output_absorption.py` are unchanged; their SHA-256 remains `e26bd38d306b0a3165beceb9374250f1a7168d010f0f66f4a72f54c19817745a`.

## Frozen validation

| Gate | Result |
|---|---|
| Serial, unfiltered pytest | **4,564 passed; 10 failed; 742.13 seconds** |
| Full-run process wall time | 743.143 seconds |
| Ruff | Passed |
| Strict mypy | Passed, 625 source files |
| Recursive structural checks | No recursion cycles; no source above 1,000 lines |
| Fixed five-process radix fixture | Passed; cold median 0.00015554s, repeat median 0.00007517s |
| Public powered-output absorption | Failed, all ten preserved tests |
| Complete N=16…1024 five-process growth manifest | Not completed |
| N=1024 growing-196 attempt | Timed out at the unchanged 35-second watchdog; one attempt, not a five-trial sample |

The ten failures enter `FieldImageApplication`, `ReverseRecursiveImageRuntime`, and higher continuation evaluation after those routes are poisoned. The new lease-inspection regression from the earlier frozen run is fixed. The final slowest-20 testcase total is 379.392 seconds.

The fixed radix timing result is expressly limited to its existing one-step original-source fixture. It does not demonstrate deep Collatz/radix tile-runtime migration.

## Cold measurements: work is still superlinear

Five fresh worker processes were used for each prefix point, with fresh index-owned runtimes and no response-register or microblock acceleration in the causal probe. Setup, observation, diagnostics, and subprocess wall time are separate. These are **private causal-runtime measurements**, not evidence that public family routing has changed.

Growing-196 uses the original symmetric pair source, `P^(N-1)` followed by digit normalization, and coordinate zero. Source import uses canonical padding; it does not build a width-sized padding word.

| N | Scheduler frames | Frame doubling ratio | Effective frame exponent | Task evaluations | Live canonical tiles, source + future | Cold median seconds |
|---|---:|---:|---:|---:|---:|---:|
| 4 | 690 | — | — | 149 | 29 | 0.9258 |
| 8 | 3,264 | 4.730 | 2.242 | 635 | 83 | 1.9245 |
| 16 | 12,804 | 3.923 | 1.972 | 2,397 | 267 | 4.3460 |
| 32 | 44,121 | 3.446 | 1.785 | 8,146 | 938 | 13.2909 |

At N=16→32, frames increase 3.446× and live tiles increase 3.513×. Temporal action nodes increase only 9→11. Compiler size therefore does not establish efficient execution. The measured frame and retention series are superlinear, not an observed sublinear release result.

The fixed-width temporal probe and fixed-depth spatial probe remain separate series in the raw JSON/CSV. The latter has frame counts 833, 1,533, and 2,937 at widths 16, 32, and 64: increments 700 and 1,404 are consistent with approximately linear spatial construction over that short range. It is not evidence of universal logarithmic point work.

Wall-clock spread is substantial in several samples and host load varies. No asymptotic timing claim is made from those medians. Non-timing counters are checked for consistency across the five fresh processes. N=64…512 are not measured in this prefix diagnostic; N=1024 has only the separately recorded watchdog attempt. The report remains RED for missing release coverage and observed growth-envelope violations.

## Remaining implementation blockers

1. **Public cutover:** reverse and Collatz builders still construct higher-semantic/recursive-image executors and install temporal evaluators. The legacy cold image path requests both spatial children. The tile scheduler is not yet the public replacement. Collatz, radix, accelerated views, and compatibility migration therefore remain unfinished.
2. **Distinct causal-context work:** adversarial instrumentation found 2,397 distinct task keys for 2,397 task evaluations at N=16. Much of the cold cost is unique output/advance/residual bindings, rather than late duplicate discovery. Existing completed-result and interface hits do not remove that cost.
3. **Boundary normalization and overlap:** the transient task memo can be probed before a clipped boundary view is canonicalized. The completed boundary probe handles a single canonical dyadic piece; persistent multi-piece region reuse is unfinished. Normalization must preserve both temporal contracts and exact geometry.
4. **Certified reductions and symmetry:** primitive-pair finite transfers remain useful, but arbitrary-depth reduction and certified mirror/conjugacy request normalization are not integrated. Current causal signatures admit identity wiring. Blank-padding readiness cannot be substituted for a reset certificate.
5. **Mixed action aliases:** homogeneous powers have canonical kernel/exponent identity; heterogeneous composition remains syntax-dependent. Associative equivalent mixed derivations need correct canonicalization without flattening a temporal itinerary.
6. **Complete causal-coverage accounting:** retained-result interval diagnostics are explicitly incomplete. Full dependency-reason traces, requested spatial/semantic coverage unions, repeat-coverage ratios, and recreation attribution across every execution route are not yet implemented. The current diagnostics must not be described as a complete allocation/coverage proof.
7. **Release performance:** the under-300-second suite, full cold envelopes, production poison gates, and deletion of superseded execution have not passed. Proof/test optimization and old-executor deletion cannot stand in for the missing public route.

No new theorem or perfect whole-trajectory fingerprint is asserted as a prerequisite here. These are remaining execution, normalization, ownership/reporting, and integration tasks. Equal boundary carry behavior still cannot authorize merging different exact outputs.

## Evidence

- `pytest.log`, `pytest.xml`, `validation.json`, `suite-summary.json`: complete serial test evidence and slowest tests.
- `checks.json`: Ruff, strict mypy, and recursive structural output.
- `growth-prefix.json`, `growth-trials.jsonl`, `growth-summary.csv`: five-process prefix measurements, raw trials, medians/spreads, and work ratios.
- `growth-1024-attempt.json`: preserved timeout with unavailable execution counters.
- `radix-five-process.json`: unchanged dedicated radix timing fixture.

Earlier evidence remains in `results/causal-reuse-d540da93f6c9f2e9` (complete earlier run with the subsequently repaired lease-inspection failure) and `results/causal-reuse-e280cf1e52dd0ca4` (explicitly interrupted run). No historical results were overwritten.
