# Physical Collatz consumer and source-bound clock refinement

The physical clock now comes from the same admitted application used by
`PoweredCollatzTerm`. The CLI command is:

```sh
number-compiler observe collatz 4 --seed 11 --kind physical-clock
```

It reports two odd events and two divisions. This command's index counts
physical ticks, including the `1 -> 4 -> 2 -> 1` cycle. The existing `--kind clock`
continues to count accelerated events and stop at one.

## Actual production connection

`execute_observation` calls `observe_physical_clock`, which constructs
`PoweredCollatzTerm` and demands `s_arithmetic_clock()`. That method uses
`HashLifeBlockIndex.direct_temporal_cocycle()` and
`LazyProjection.temporal_cocycle()` to query `TileApplication.interface()`.
The application authenticates its source, action, ports and lease. It reuses a
completed result when available and otherwise uses the existing causal interface
evaluator. The query does not unconditionally call `complete()` and does not
construct an accelerated event DAG.

For physical ticks `t` and source-bound odd-event weight `o`, the derived view is
`SArithmeticClock(o, t-o)`. It checks `0 <= o <= t` and exact agreement with the
requested duration. The real slope exponents are `(-t+o, o)` at primes `(2,3)`;
the other norm exponents cancel these. These observations remain outside
ActionID. Neither the aggregate clock nor the endpoint determines the whole
symbolic skew polynomial or valuation program.

The CLI reports actual work counters and peak/retained nodes. `nth collatz`
execution metrics now also expose the existing factored-output compilation and
joint-table-elision counters from the same captured resource snapshot. No
counter values or performance assertions were relaxed.

## Formal statements and their boundary

`Physical_Collatz_Bound_Consumer.thy` specifies the actual six-state padded-binary
primitive output selection, including the even adjacent-symbol shift and odd
carry/blank cases. It compares the explicit compiled tables against the
arithmetic publisher for every admitted input and arbitrary output demand.
The left-scan lemmas establish that the first active digit owns the odd event,
nonSTART incoming states contribute none, and blank exterior contributes none.

`Physical_Collatz_Clock.thy` defines a physical matrix action whose branches are
derived from the current source. It proves exact integer affine transport,
diagonal exponents, and chronological append/doubling with the second action
rebased at the first action's endpoint. It does not assume a supplied parity
itinerary or square a sampled carry/clock tuple.

The finite correspondence regression reads the exact three-way table
declarations from the Isabelle theory and compares them with the production
compiler on all 54 port bindings. The CLI regression poisons the old joint
output table and checks actual output and the exposed compiler counters.
Physical-clock regressions poison independent accelerated discovery and
unconditional endpoint completion, check the root/cycle shortcuts, verify
rebasing and reuse, and reject a closed application.

These are completed local proof obligations and executable correspondence
checks, not an extracted or fully verified Python executor. The Isabelle model
still needs a refinement through `BoundaryTileView`, behavior minimization,
causal interface execution, spatial/temporal joins and shortcut publication.
The matrix reference computes source-dependent branches; its definition is not
a proof of cheap branch discovery.

## Adversarial disposition and remaining P0 work

The review rejected an unused numeric source-binding label and removed its
identity theorems. Such a label would not prove runtime source authority. It
also required explicit blank-exterior handling and preserved the difference
between physical and accelerated clocks.

Release remains **BLOCKED**. This change wires the physical S-arithmetic clock
and checks its primitive consumer; it does not complete the universal
shadow-cylinder constructor, arbitrary powered skew/Hensel/tropical pullbacks,
196 publisher refinement, Fermat/Mersenne candidate-derived terminal
construction, or the failed performance and retention gates.

The final `Etale_Primary_Carry` session passes with oracle checks enabled.
The selected regression run passes 116 tests (four validation-marked cases are
deselected); strict mypy checks 1,247 files, and Ruff and the structural policy
checks pass. These results do not replace the unresolved full-release gates.
The [validation record](../results/current/physical-bound-clock-2026-09-12/validation.json)
includes the source fingerprint and guarded logs, including a prior proof-build
memory-limit failure rather than hiding it behind the successful retry.
