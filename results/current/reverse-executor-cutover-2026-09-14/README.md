# Reverse/add production cutover repair — September 14

This repair prioritizes exact CLI digits and removes the higher publisher from
ordinary reverse/add execution. Primality, checked factor reporting and
non-halting remain explicitly requested extras; their research gaps are not a
reason to route finite digit queries through a retired executor.

## Implemented path and ownership

The editable `reverse_image_worker` owns reverse/add routing tests and migration
of the old publisher to a bounded development oracle. The coordinator owns
shared dispatch, metrics, Isabelle registration, terminal proof and serialized
validation. A second editable agent could not be created because of the session
agent-thread limit. The existing proof reviewer supplies read-only adversarial
review, not an implementation claim.

Production now routes both certified reverse/add and Collatz through:

`runtime_router.build_certified_field_application → build_tile_projection →
LazyProjection → TileApplication → TileScheduler`.

`HashLifeBlockIndex` accepts the canonical lazy tile application. The legacy
`ReversePublisherProjection` is only in
`devtools/proofs/oracles/reverse_publisher.py`, and no production module imports
it. A source/action wrapper around the higher semantic evaluator was rejected
before integration. The extra admission shim was also removed: existing router
admission remains the authority.

The finite primitive decimal-pair optimization uses
`ReverseMorphismTransferArena`. Demanded point tests poison higher evaluation and
`complete_temporal`, compare every active digit and width for generations
1/2/4/8/16, and require zero exact endpoint nodes. The existing T1–T32 reference
control remains in the suite. The step-64 warm point query retains its original
digit workload and counters. Authority tests continue to reject forged source,
action and signature bindings before warm lookup.

## Checked proof scope

`Reverse_Digit_Terminal` proves terminal decimal normalization agrees with
`digits`, then connects it to the raw two-port pair scan, including growth and
padded no-growth output. Its state models carry, the first blank and the sink.
The theory checks oracle dependencies and introduces no skipped proofs or axioms.

This is a terminal-consumer refinement. It is **not** a proof of the complete
Python causal worklist, runtime transfer records, source-tree authority or
arbitrary-size powered construction. The second scan consumes the first scan's
output image; the two complete scans do not generally share the same carry state.
The next executable theorem must express that image relation and transported
ports, not assume carry equality between distinct scans.

## Validation

The final source fingerprint is in `validated-source.json`; earlier snapshots
are retained separately, so pre-repair or pre-test-migration results are not
presented as one fully validated final release. Guard reports retain
elapsed time, peak sampled memory and incomplete outcomes. Tests/probes use
35 seconds / 1 GiB, Isabelle 35 seconds / 4 GiB, and the full ordinary suite
300 seconds / 1 GiB. The completed checks are:

| Check | Result | Guard seconds | Peak sampled bytes |
|---|---|---:|---:|
| Final cutover and repaired metric consumers | 10 passed | 26.738 | 168,165,976 |
| Authority and canonical routing | 35 passed, 1 validation control deselected | 17.507 | 105,595,408 |
| Bounded relocated oracle | 33 passed | 23.813 | 88,113,680 |
| New terminal Isabelle session | Pass | 7.658 | 1,203,948,664 |
| Isolated wheel inventory and existing CLI contracts | Pass | 6.938 | 114,460,352 |
| Isolated nonzero digits, seven family names, plain/JSON | 14 passed | 8.527 | 109,266,624 |
| Authored-tree typing, Ruff, structural policy | Pass | reports linked by filename | measured |
| Full ordinary unit selection | Timeout at 300 seconds | 300.095 | 658,441,128 |
| Combined 22-case explicit P0 selection | Timeout at 35 seconds | 35.054 | 182,420,056 |
| P0 complement excluding the eight cutover cases | 4 passed, 10 failed | 28.699 | 169,165,376 |

The full-unit attempt used the pre-final-test-migration fingerprint `a4249bf9…`.
It recorded 4,368 result markers before termination, including three failures.
The mirror and reverse action-accounting failures expected retired raw metric
names; both are repaired and included in the ten-test final cutover pass. The
other failure is the existing F4 forced-classification result remaining guarded.
The incomplete run supplies no full-suite success. Its unexecuted remainder is
still unvalidated as a whole. The subsequent oracle-only lint correction preserves
all calls and assertions; final typing/Ruff and all 33 oracle tests pass.

The first wheel check rejected one stale generated `build/lib` publisher file.
That artifact was removed and the wheel rebuilt; the final inventory verifies
exact equality with production sources. The final wheel SHA-256 is in
`validated-source.json`. No production behavior changed after that build.

The final 14-case installed digit check includes 196 at index 16, reverse/add
seed 89 at index 1, Collatz seed 27 at index 10, prime index 100, Fermat index 5,
Mersenne exponent 131 and Antihydra index 10. Both output formats produce the
expected exact values and no unsolicited stderr output.

Across the separate completed P0 selections, the same 22 cases now have
12 passes and 10 failures. Five prior reverse/add failures pass. The remaining
failures are the Antihydra source-7 certificate, eight candidate/CLI shadow-jet
classification cases and F4 forced-classification resolution. This split result
does **not** turn the combined 35-second P0 timeout into a passing run.

The initial broad focused batches (`cutover`, `core-cutover`, and
`integration-focused`) exceeded their 35-second guards. They are incomplete
runs, not passes. The core cutover and authority/routing selections were split
into bounded jobs without relaxing their assertions. Earlier proof attempts
included a parent-inclusive timeout; the successful scoped terminal session uses
already-built dependencies. This does not assert a fresh dependency-inclusive
build meets the same time bound.

## Remaining holds

The worker's scoped review confirms canonical routing and preserved workloads.
Independent `isabelle_action_audit` review of fingerprint `a4249bf9…` signs off
the direct router and raw padded terminal theorem, confirms no duplicate/orphan
session, and leaves the runtime source/tree/consumer refinement open.
It explicitly leaves cold work/retention and the full executable refinement open:
the existing tile route still performs thousands of causal/completed-result
operations at generation 32. No new arbitrary-size image constructor is claimed.
The prime shared successor owner, common Collatz event/physical construction,
Antihydra composed projection construction, full projection refinements and the
optional special-number terminal/non-halting obligations retain their existing
release status. The full 16–1024 five-trial growth manifest and fine paired
latency comparisons have not been rerun for this repair.
