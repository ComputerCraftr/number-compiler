# Counted carry-domain controls and contextual fixed points

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This checkpoint implements and validates the supplied positive control. The
full powered 196 quotient remains incomplete. In particular, the existing live
powered tile executor does not pass the large uniform control within the
unchanged resource guard.

## Implemented and checked

* `devtools/proofs/reverse_run_successor.py` advances canonical counted pair
  runs using the existing decimal normalizer and three carry actions. A run
  has at most one exceptional first normalized digit. Remaining digits use
  its idempotent domain action; reverse alignment processes only boundaries.
  No loop iterates over the represented count. The reference API requires
  `exact_oracle()` and introduces no runtime future-state admission.
* `src/number_compiler/arithmetic/functions/finite_observer.py` provides the
  shared fixed-point refinement owner for finite deterministic graphs. The
  existing unary Moore API delegates to it. Ordered successor slots support
  both next context and next residual; initial observations include forbidden
  ports. Numeric targets outside the declared universe fail validation.
  This is a compiler utility, not an authenticity certificate for a supplied
  arithmetic graph. `None` means genuinely forbidden, never unexplored.
* `Reverse_Uniform_Runs.thy` proves the uniform LT law for all coefficients
  below 9 and every length; the GT coefficient-16 growth law; and all four
  repunit transitions for arbitrary positive length. The pair domains are
  LT, LT, LT, GT. There is no width enumeration in these proofs.
* `Reverse_Contextual_Fixed_Point.thy` proves that a stable complete contextual
  signature preserves every finite continuation trace, including rejection
  at forbidden ports. Its signature contains the next context class and next
  residual class. The stability premise is still required for any concrete
  graph; the theorem does not supply the missing 196 graph.

The full Isabelle session builds successfully in 8.47 seconds under the
35-second/1 GiB guard, at 454,348,376 bytes sampled peak physical footprint.
Principal theorems have empty oracle dependency lists, with
`quick_and_dirty = false`. `isabelle-09.log` is the successful build;
earlier numbered logs retain proof-script errors, not accepted results.

## Exact trajectory controls

Every one of 100 successors agrees with the independent `pair_step` oracle:

| Seed | Width after 100 events | Counted runs |
|---|---:|---:|
| 1 | 44 | 43 |
| 1111 | 48 | 41 |
| 196 | 47 | 37 |

These are widths 44 and 48, rather than 4,444 and 4,848. The duplication in
the pasted formatting does not appear in the actual oracle computation.

For length 1,000,000, the four-event control retains respectively 1, 1, 1,
1 and 3 runs, ending in `(7,1), (14,999999), (7,1)`. Tests also use length
`10^100`, with source-field construction and expanded-oracle entry points
poisoned. The length-one result canonically coalesces to `(7,2)`.

The 11 new focused tests take 0.50 seconds. They include 361 two-run-symbol
alignment/carry cases, three 100-step trajectories, invalid input and scope
checks, delayed distinctions, a surviving recurrent merge, context-only
distinctions, and explicit continuation-trace checks on small closed graphs.
None is a long-running release sweep.

## Live executor alternative

`live_uniform_probe.py` builds a uniform `TileArena` node by repeated self-join,
appends a same-width blank node, and invokes the existing `CausalTileEngine`
with `adapter.power(primitive, 4)`. It observes five endpoint positions only.
The source construction uses logarithmically many tile operations.

* Width 8: succeeds in 0.96 seconds, returning `7,14,14,7,blank` at the
  tested edge/interior/padding positions.
* Width 1,048,576: the unchanged 35-second guard terminates the process
  after 35.08 seconds, at 177,898,048 bytes sampled peak. No endpoint result
  was returned. This is a failed execution/scaling probe, not a proven wrong
  arithmetic output or an impossibility theorem.

Ordinary RLE and the existing generic powered execution path therefore do
not finish the requested quotient. The next concrete obligation is to
connect a width-parametric successor representation to the live executor,
then construct and certify the complete fragmented 196 context grammar.
More carry history is not the missing input.

## Reproduction

Run one guarded process at a time and use fresh output paths:

```bash
.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/run-controls.json --report /tmp/run-controls.guard.json -- \
  .venv/bin/python -m devtools.proofs.reverse_run_successor

.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/uniform-live.log --report /tmp/uniform-live.guard.json -- \
  env PYTHONPATH=. .venv/bin/python \
  results/current/reverse-run-controls-2026-09-10/live_uniform_probe.py 20

.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/uniform-isabelle.log --report /tmp/uniform-isabelle.guard.json -- \
  /Applications/Isabelle2025-2.app/bin/isabelle env \
  'ISABELLE_TOOL_JAVA_OPTIONS=-Xms64m -Xmx256m -Xss4m' \
  'ML_OPTIONS32=--minheap 100 --maxheap 450' \
  /Applications/Isabelle2025-2.app/bin/isabelle build \
  -v -j 1 -o timeout=20 -D devtools/proofs/isabelle
```

The full serial unit suite passes **4,167 tests in 273.84 seconds**, with 918
validation tests deselected. The unchanged 300-second guard completes in
274.72 seconds at 563,233,656 bytes sampled peak. Before, after and current
source fingerprints match. Structural policy tests pass as part of this run.
The existing prime/composite unary-minimizer validation also passes separately.

Strict nonincremental mypy passes for 1,098 source files, including the saved
live probe. Repository-wide Ruff checks and changed-file format checks pass.
`manifest.json` records the exact source and evidence identities. The earlier
unit checkpoint took 281.34 seconds; this modest single-run difference is not
evidence of a suite speedup. No production 196 admission gate or resource bound
has been weakened.
