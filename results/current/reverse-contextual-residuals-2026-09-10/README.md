# Reverse/add contextual residuals — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Added consumer-relative residual functions for the no-growth, growth-edge and
growth-interior stencils, with physical carries derived from existing domain
actions. Exact factor-through certification includes updated context and
admissibility. Backward refinement compiles a declared finite continuation;
forward transport then consumes only canonical residual IDs.

See the [architecture contract](../../../docs/architecture/reverse-contextual-residuals.md).
The patch is relative to the preceding
[Collatz output-quotient checkpoint](../collatz-output-quotient-2026-09-10/README.md).

## Verification

The focused suite passes **78 tests in 6.38 seconds**. Its default 35-second
guard completes in 7.11 seconds with 96,387,600 bytes sampled peak physical
footprint. Strict nonincremental mypy passes for 1,092 files. Ruff check and
formatting pass. Structural policy reports no source-line, recursion or
package violations.

The unprofiled serial unit suite passes **4,156 tests in 281.34 seconds**, with
918 validation tests deselected. The unchanged 300-second guard completes in
282.14 seconds with 614,646,696 bytes (approximately 586 MiB) sampled peak
physical footprint. Before, after and current source fingerprints match:

```
0f13e7b13fc1eb85056e4c95c081c7a84f34ce6b8d3bd8a6f3d6d80163a0ad36
```

The previous checkpoint took 287.16 seconds; this single comparison does not
establish a unit-suite speedup. This unit run is not complete release-validation
evidence. `unit.log`, `unit.guard.json` and `unit.xml` preserve the final run.
`changes.patch` contains the implementation, tests and documentation changes;
`manifest.json` records changed-file and evidence hashes.

New tests cover all 361 symmetric width-four fields against the independent
pair-step oracle; the no-growth seven-band merge; the growth-interior 7/8
counterexample; simultaneous output/context pullback; and rejection of a
context-only distinction hidden by a constant carry observation. A complete
two-event growth/alignment example retains three classes for five admitted
values and advances with source evaluation and tile construction poisoned.

Budget rejection, foreign ownership and retained-map corruption fail closed.
The independent payload audit checks all 19 primitive bindings without
publishing functions or changing ledger counters. No existing assertions,
test selection, performance limits or ownership requirements were weakened.

## Scope

This supplies a contextual quotient constructor and certified finite successor
transport. Callers must provide the complete next observation/context profile,
pulled back to a common admitted source domain. It does not discover the active
196 growth-adjacency grammar, certify an infinite context graph, or introduce
an active future class into the public powered executor. Those release and
scaling obligations remain open. No public-query or unit-suite speedup is
claimed from this change.

The attachments' exhaustive width-eight results are supplied research evidence,
not an experiment reproduced by this checkpoint. `focused-initial` preserves
the intermediate seven-test pass before the independent audit was added;
`focused` is the final focused run.

The `before-layout` files are intermediate evidence. That unit run was
deliberately interrupted before adding ordered field sorts to context-record
identity and its regression test; it is not a passing suite. The
`invalid-selector` focused attempt used nonexistent test paths and collected
no tests. Both diagnostics are superseded by the final runs.
