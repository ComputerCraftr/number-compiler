# Active-behavior HashLife release blockers — September 9, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This tracker follows the seven production connections identified by the
[disconnected-quotient audit](../disconnected-quotient-audit-2026-09-09/README.md).
It is an acceptance checklist, not a release declaration. A compiled summary,
an intern hit, or represented extent counts as useful only when the live
scheduler uses it to avoid measured descendant work.

## Blockers and executable gates

| # | Production connection | Current status | Acceptance evidence still required |
|---:|---|---|---|
| 1 | Active consumer-profile behavior in `tile_causal` | **Open.** The published future-behavior class is still the certified quiescent blank class. Primitive reverse bound-output consumption is narrower than successor closure for a composite consumer. | A certified nonblank class and transition must be looked up before exact boundary construction. P4/P8 witnesses must succeed with that construction poisoned. Report classification, refinement, transition hits, failed work, and exact fallback independently. |
| 2 | Decimal sector forcing and component-specific Frobenius death | **Partial, with an authenticated H=20 connection.** Executed carry interfaces produce bounded sector summaries. The H=20 plan proves the component bound using `q >= floor(N/4)`; the authenticated observer uses that proof to elide initial source-sector arithmetic after all four source components die. The aligned local-forcing observer is also implemented. The final interface remains required, and neither operation discharges an arbitrary pending composite temporal dependency. | The active transition must consume aligned interval forcing before causal construction. Tests must preserve exact output dependencies outside the proved dead component and distinguish plan composition, successful source elision, local-forcing evaluation, and executed transition work. |
| 3 | Collatz bounded algebra in the shared scheduler | **Partial.** Public powered observations use the tile scheduler and the first-event root matcher is memoized. General cross-event affine, character, valuation, and frame behavior is not a successor-closed active class. | Even starts, long valuations, partial events, and cycle phases must reuse one certified transition without a second runtime or finite-residue-as-tail shortcut. Physical ticks, event weights, and frame shifts must agree with exact oracles. |
| 4 | Physical Collatz parent observation | **Focused integration present.** Low-boundary event metadata and root matching avoid some descent. | Cold and warm tests must show actual parent/root hits, zero invented event weight, and counted declines/fallbacks on unsupported contexts. Broader execution scaling remains a separate gate. |
| 5 | Closed small-radix division admission | **Focused integration present.** The immutable arithmetic law now admits small and wide radices through the same closed interface. | Exact 3/6/12 and 256/257 boundary differentials, numeric-alias rejection, bounded allocated population, and zero division cocycle must remain green in the full release tree. |
| 6 | Radix completed-stage and width reuse | **Partial.** Completed stages are available and scalar validity can avoid an unconditional exact width in supported cases. Isolated and dense observations still need controlled evidence that they do not replay division stages. | With acceleration disabled, adjacent digits must consume completed quotient stages or certified transitions. Report stage hits, binary/source reads, division work, width work, and exact out-of-range behavior separately. |
| 7 | Complete certified request symmetry | **Open.** Exact mirror tiles are cached, but complete action, producer/consumer contract, operand, orientation, coordinate, and result normalization is not yet a certified shared request transform. | A symmetry-related warm parent must bypass descendants and reducers, preserve distinct exact mirrored `TileID`s, and invert ports, coordinates, halos, and cocycles. Only the proved mirror/conjugacy subgroup may be named; full D4 requires additional certificates. |

## Required ordering and accounting

For active reverse dependencies the scheduler probe order is:

1. completed exact result;
2. certified active behavior transition;
3. completed fused or concrete interface observation;
4. completed exact causal region;
5. cached midpoint;
6. unresolved descendants.

The blocking regression must prove this ordering. It prepares a certified active
transition, poisons exact boundary construction and primitive descendant work,
then requests the same consumer dependency. A separate cold test permits genuine
classification and leaf work. A separate warm test requires zero classification,
refinement, reduction, and exact construction. Unsupported profiles retain the
canonical exact fallback and increment decline/failure work rather than reporting
a behavioral discharge.

Metrics must keep these units separate:

- classification and refinement requests, evaluations, failures, publications,
  aliases, and warm hits;
- behavior-transition requests, evaluations, failures, publications, and hits;
- exact boundary requests, evaluations, publications, and represented extent;
- extent discharged by certified behavior or a bounded transfer;
- scheduler frames, reductions, primitive decisions, allocations, retirement,
  and recreation.

Represented or discharged extent is geometry, not executed work. It must not be
added to work totals. Failed classification and reduction remain charged even
when publication rolls back. Compiler-only Frobenius plan counters cannot satisfy
runtime transition or annihilation gates.

## Preserved red evidence

- The accepted exact causal reverse route at N=32 used **44,692 causal frames**
  and about **4.30–4.75 seconds** in the recorded single diagnostics.
- The rejected unrestricted deep-summary route used **169,794 frames** and
  **10.08 seconds** at N=32 while discharging only one 63-cell dependency.
- Earlier N32→N64 reverse measurements grew from **47,962 to 176,753 causal
  frames (3.69×)** and from **19,808 to 87,853 concatenation frames (4.44×)**.
- The N=128 width probe exceeded the 35-second guard.
- The serial suite exceeded **300 seconds** in both preserved attempts; the later
  run reached roughly 42 percent. No under-five-minute result exists.

These measurements use intermediate source fingerprints and remain diagnostic,
not comparable timing distributions. They are retained so a lower tile count,
high leaf hit rate, or new counter name cannot erase the known repeated work.

The focused cProfile N=32 run completed under the guard in 17.28 seconds and
recorded 50.1 million calls (15.83 profiled seconds). The largest avoidable
validation costs were 212,845 action validations at 2.97 cumulative seconds and
66,677 finite-port validations at 1.73 cumulative seconds. This confirms that
warm semantic admission is itself a material cost, alongside the 44,692 causal
frames. Any validation cache must retain scoped liveness and immutable
publication-integrity checks; caching a successful Boolean would fail the
existing post-publication mutation adversaries. The complete profile and raw
counters (local artifact: `cprofile-growing-196-n32.log`) and its process-guard
record (local artifact: `cprofile-growing-196-n32.guard.json`) are preserved with this tracker.

A subsequent direct-parent transfer diagnostic reduced boundary-transfer
requests from 7,672 to 1,080 and boundary-transfer frames from 16,326 to 9,734.
Total causal frames stayed **44,692**, and the single cold time was **4.46
seconds**. This is useful attribution for one traversal layer, but it is not a
measured end-to-end speedup or evidence of sublinear growth.

## Frozen diagnostic checkpoint

The source fingerprint for the following evidence is
`a07f7af3a9fd78bc618a950b3f95b5fa9cf01e3a8fd9fa5e4212168aedae7910`.
Each performance point is one fresh-process diagnostic, not the required
five-trial release series.

| N | Cold seconds | Increment | Ratio | Effective exponent | Causal frames | Increment | Ratio | Effective exponent | Canonical tiles | Increment | Ratio | Effective exponent |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1.7696 | unavailable | unavailable | unavailable | 12,517 | unavailable | unavailable | unavailable | 305 | unavailable | unavailable | unavailable |
| 32 | 4.4740 | 2.7044 | 2.528 | 1.338 | 43,034 | 30,517 | 3.438 | 1.782 | 1,001 | 696 | 3.282 | 1.715 |
| 64 | 14.9713 | 10.4973 | 3.346 | 1.743 | 154,476 | 111,442 | 3.590 | 1.844 | 4,004 | 3,003 | 4.000 | 2.000 |

All three measured series are superlinear over the completed range. The tile
population is exactly quadratic from N=32 to N=64, while time and causal-frame
growth remain well above linear. The measurements therefore reject a current
sublinear claim; they do not identify a universal asymptotic exponent. N=128
timed out after **35.0504 seconds** at an approximately **141 MB** sampled peak
and emitted no completed row, so its ratios and exponents remain unavailable.
Its guard record (local artifact: `frozen-a07f7af3/blockers-frozen-n128.json`) is preserved.

The raw rows include the new direct-parent, boundary-concatenation, reverse
sector, local-forcing, source-elision, interface, behavior, allocation, and
retirement counters. Represented/discharged extent remains excluded from work
totals. The N=16 (local artifact: `frozen-a07f7af3/blockers-frozen-n16.log`),
N=32 (local artifact: `frozen-a07f7af3/blockers-frozen-n32.log`), and
N=64 (local artifact: `frozen-a07f7af3/blockers-frozen-n64.log`) logs are preserved alongside
their process-guard records.

Focused validation at this fingerprint recorded **202 passing tests in 13.89
seconds** with an approximately **88 MB** guarded peak, plus **44 directed tests
in 1.84 seconds** with an approximately **82 MB** guarded peak. Whole-tree
strict typing passed for **1,061 source files in 9.28 seconds**, and recursive
policy checks reported no source-length, recursion, or package violations. The
focused (local artifact: `frozen-a07f7af3/blockers-final-focus-2.log`),
directed (local artifact: `frozen-a07f7af3/blockers-admission.log`),
strict (local artifact: `frozen-a07f7af3/blockers-final-strict.log`), and
structural (local artifact: `frozen-a07f7af3/blockers-final-structural.log`) records are archived.
The earlier midpoint-publication diagnostic is retained as a failure record;
the focused checkpoint contains the corrected accounting regression.

A final combined rerun after the source freeze passed **215 tests in 13.92
seconds**, with a **96.6 MB** guarded peak. Its JUnit
record (local artifact: `frozen-a07f7af3/blockers-frozen-focus.xml`) records identical before/after
source fingerprints; the log (local artifact: `frozen-a07f7af3/blockers-frozen-focus.log`) and
guard (local artifact: `frozen-a07f7af3/blockers-frozen-focus.json`) are preserved. This is selected
regression evidence, not an unfiltered suite pass.

Ruff formatting and checking were clean across the **1,185-file** authored
tree. The default serial, unfiltered suite did **not** pass the release gate: it
collected 4,929 tests, reached approximately 41 percent without an emitted
failure marker, and was terminated by the unchanged cap after **300.0456
seconds** at a sampled peak of **624,921,264 bytes**. Because execution was
incomplete, the passing prefix is not a suite result and no valid complete
JUnit report exists. The partial log (local artifact: `frozen-a07f7af3/blockers-frozen-suite.log`)
and guard record (local artifact: `frozen-a07f7af3/blockers-frozen-suite.json`) are preserved.
The serial release gate remains failed.

The main remaining execution blocker is still the absence of a
successor-closed active class for an arbitrary composite consumer. The H=20
source-elision and aligned local-forcing operations are real authenticated
uses, but they are narrower observations. Exact causal construction remains the
fallback for the deep composite dependency, which is consistent with the
superlinear measurements above.

The rotated reverse review located the implementation boundary precisely:
`reverse_active_transfer.consume_reverse_bound_output` declines a consumer
with temporal children. `ReverseBoundOutput` supplies concrete interval
transfers, while the existing thirteen-channel interface's output observation
is only a scalar edge output. The proposed next component is a
contract-parametric successor-interval bound-output law, using the existing
two-sided primitive-pair substitution equations and seven reduced finite
functions for activity, blank presence, sink state, carry, last symbol, and
forward/backward carry transfer. This is a candidate, not a published
successor-closure certificate. Local leaf/pair checks must be supplemented by
closure for every admitted class and continuation; agreement on a few powered
witnesses alone cannot authorize merging. The exact successor and canonical
tile recurrence already exist. The missing optimization is connecting a
sufficient consumer-visible result to composite transfer reuse, not finding a
perfect finite fingerprint of an entire trajectory.

Release requires all seven connections that apply to a public route, complete
N=16…1024 work/retention evidence, the unchanged five-process radix gate, and a
serial unfiltered suite under 300 seconds on one frozen fingerprint. Finite
samples do not prove a universal sublinear bound.
