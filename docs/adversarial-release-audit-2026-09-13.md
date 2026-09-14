# Adversarial release audit — September 13

**Release remains blocked.** This follow-up audits the causes behind the red
assertions and repairs independently reproduced production defects. It does
not relabel a descriptor, a one-step theorem, or a finite observation as a
completed powered construction.

## Repairs

Antihydra physical results previously authenticated their scalar publication
without authenticating all retained arithmetic support. Mutating a cylinder's
parity word or minimum could therefore leave direct observations and a cached
physical result admissible. `Run.require_source` now validates its exact
arithmetic publication, chronological segments, source residues, and every
cylinder field before admitting a physical observation. An internally
consistent foreign parity word is rejected too. Source parity is derived by
the one canonical bounded constructor in `blocks.py`; the runtime does not
maintain a second admission recurrence. Branch validation, block application,
and operand work remain charged.
Boolean segment coordinates are also rejected by both runtime admission and
the payload audit.

The 196 publisher previously entered higher continuation evaluation while
constructing the publisher, before any output demand. Its source/action and
two-port descriptor now remain separate from first-demand image construction.
Publisher-level metrics do not construct the image. A pending publisher has
`bounded_temporal_runtime_cutover_complete=0` and blocker
`reverse_publisher_image_not_constructed`. First output still performs the
independent primitive-port comparison and all required higher evaluation.
Failed image construction is terminal: retries cannot accumulate additional
arena families. Partially allocated arenas remain registered and charged.

The final independent audit found and retested an additional wrong-result
case: on `ReverseAddPoweredTerm(196, 8)`, replacing the action with the
same-arena identity and rewriting its local binding changed coordinate zero
from 9 to 7. The repaired publisher validates the issued canonical action,
semantic identity, schema, primitive/terminal actions, initial states and
certificate coordinate program before constructing the image. Execution and
reporting share the same read-only action/certificate validator. The exploit,
foreign schemas and replacement certificates are now rejected before image
work. This was a production authority defect, not a mathematical quotient
counterexample.

The real CLI metrics-only poison test confirms that
`196 --nth 32 --no-value --info metrics --format json` enters neither image
construction nor rendering. This preserves the CLI's lazy behavior; it is not
evidence that full output construction has become cheap.

## Why the mathematical and construction gates remain red

| Gate group | Concrete missing integration | Why existing evidence is insufficient |
| --- | --- | --- |
| 196 reachable image and powered cutover | Replace the higher-continuation image evaluator reached through `ReversePublisherProjection._ensure_image` with a source-bound powered image constructor, then refine the executable arena and output consumers. | `Reverse_196_Publisher_Refinement.thy` proves a whole-word one-step publisher for valid pair words, including the 196 trajectory. It does not identify the Python powered image with that publisher or bound source-dependent construction work. The first output still enters higher continuation evaluation. |
| Fermat/Mersenne terminal bit and CLI refinement | Implement the unit/annihilator evaluator behind `build_compact_transverse_pullback`, connect it through `terminal_threshold_probe`, and prove that the CLI consumes that constructed object within the existing budgets. | The production object has absent `unit` and `annihilator`; it is a descriptor. `Transverse_Frobenius_Holonomy.thy` establishes the indexed-product criterion. It does not compute the product compactly. A balanced product tree still enumerates the window. |
| Antihydra all-time result | Produce an accepted source-7 certificate and complete the literal TM/macro/roof and executable-constructor refinements. | `source_seven_all_time_barrier_exactly` is an equivalence. `antihydra_guarded_before_failure_agrees` identifies the defined guarded arithmetic option, not literal six-state TM execution. Neither establishes safety of every source-7 prefix. |
| Shared source construction and complete projections | Finish source-derived publisher/consumer refinement for the common support, including the Collatz production path and Antihydra's demanded projections. | Reusing retained parity avoids macro rediscovery, but Antihydra projections still fold O(N) retained steps. A supplied-word composition law does not bound source discovery. The small release selection does not exhaust these obligations. |

No collision between carry-only, mirror-only, or unrelated source projections
is claimed as a counterexample to the full source-bound cylinder. No new
counterexample or complete non-halting proof was established in this audit.
No LL/Pépin fallback, factor-backed oracle, hardcoded candidate decision,
UNKNOWN-to-success conversion, or weakened release assertion was introduced.

## Performance findings

Antihydra's stronger admission costs approximately 12 microseconds for 64
returns, 110 for 512, and 443 for 2048 in the recorded repeated-call probe.
At 512 returns, clock validates once, Mahler twice and tape three times;
the measured observer costs are 0.112, 0.217 and 0.327 milliseconds.
These repeated checks remain an optimization opportunity. A ledger mutation
epoch is insufficient to cache their validity because mutation of a retained
object can bypass that epoch.

A proposed direct backing-table optimization for `LedgerDict.get` and
membership was rejected and removed. On three fresh Collatz seed-27/N=64
output constructions per variant, the median changed from 3.833 to 4.919
seconds. Output, retained counts and measured execution work agreed, but the
candidate did not demonstrate a speedup. The rejected patch and probe are
retained as evidence, not production code.

Three fresh-process samples of each installed wheel show that the repaired
196 N=8 JSON value query takes a median 0.223 seconds versus 0.215 seconds
before this follow-up. Antihydra N=512 with value, ledger and clock takes
0.0768 seconds versus 0.0765 seconds. Outputs agree exactly. These results
measure the cost of the retained correctness checks; they do not establish
a new end-to-end speedup or discharge a scaling gate.

Validation logs, installed-wheel identity, timing samples and the unchanged
release selection are recorded in the
[evidence directory](../results/current/adversarial-release-2026-09-13/README.md).
The final ordinary-unit run completes within 300 seconds with 5,032 passes
and the same four failing release assertions. The explicit P0 selection has
15 failures and seven passes. Both remain red; no failure was converted into
an expected UNKNOWN result or an xfail.
The existing Antihydra and étale Isabelle sessions pass separate incremental
checks. The combined check times out while rebuilding `Reverse_Residuals`,
so reverse/temporal verification is incomplete in this run. No new Isabelle
theorem or mathematical completion is claimed.
