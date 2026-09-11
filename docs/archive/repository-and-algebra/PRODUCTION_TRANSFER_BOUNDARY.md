# Production carry transfers and exact proof oracles

This is the v4 representation-release record. [Early canonical lookup and metrics schema 3](EARLY_CANONICAL_LOOKUP.md) records the subsequent early-evaluation cache changes and corrected legacy accounting. Its v5 results preserve the older measurements below.

The old packed carry cut was a lossless slab encoding, and the old tape-valued carry action retained both exact emitted rows. Neither is a production transfer summary. The previous audit excluded their use by the primary point adapter but did not remove the callable legacy engine from the production namespace. It also missed a temporary carry memo that could hold an entire small future row.

## Representation changes

The exact reverse spacetime engine, slab, packed cut, affine offsets, forcing occurrences, and reset/tape analysis now live under `number_compiler.proof`. Production modules do not import that namespace, including through local or literal dynamic imports. The package root no longer exports the old reverse forcing or tape-analysis types.

Reference callers must explicitly enter `proof.exact_oracle()`. Oracle constructors and operations reject calls outside that scope and reject calls from point/width observers even when an oracle scope was already active. Raw slab round-trip tests are retained as proof tests; they are no longer production quotient tests.

`CarryActionQuotientArena` in the production package now interns finite boundary functions. A pair coefficient induces `CONST0`, `ID`, or `CONST1`. A complete interval effect contains its forward and reflected boundary functions plus a reset count capped at two. These form seven canonical classes. Spatial composition operates on scoped `TransferSummaryID` handles, and each retained interval summary contains one such ID and geometry. The arena has no source-word cache, output tape, slab packing, `project_span()`, or row inverse. It is used directly by the lazy reverse evaluator.

The evaluator retains summaries of disjoint two-cell intervals. It does not retain one output carry per coordinate or overlapping prefixes that recover a carry row. During a query, each active stage has at most two directional carry cursors, with at most `2H` cursors in total; the decimal limit is 40, independent of spatial width. Ambiguous interior queries return to the symbolic program and refine bounded residues only as needed. This replaces the previous coordinate-indexed temporary carry memo.

The output-complete stage/offset program remains separate from the transfer summary. Interior digits are queries against that program. Exact original input and explicitly requested endpoint output have separate representation roles.

Lossless carry-history diagnostics have also left `CanonicalSequenceCompiler`, including its diagnostic mode. For an independent reference report, use `number_compiler.proof.sequence_diagnostics.with_carry_diagnostics(compilation)` inside an oracle scope. This returns a new report without warming or changing the production compilation cache.

## What the non-invertibility test means

Different coefficient words and different emitted carry histories must share the same boundary-transfer ID. Tests check complete collections of interval summaries as well as individual aliases, and verify all 343 associativity cases for the seven classes. For example, coefficient words `(9, 10, 10, 9)` and `(10, 9, 9, 10)` emit different decimal carry histories but have identical collections of complete interval-summary IDs. A production summary has no raw-row reconstruction method.

This assertion applies to the transfer image. The retained original source and executable program can recompute history; that follows from exactness. They must not eagerly evaluate or store that history as slab symbols, carry-output tapes, or a cache of carry values at every coordinate.

Finite spatial transfer equivalence remains distinct from a source-independent, output-complete temporal closure theorem. Nonlinear branch discovery may still be O(N); no logarithmic cold-execution claim is enabled by this change.

## Validation

Final validation passed: **1,221 pytest tests** in 435.65 seconds, with no failures, errors, or skips. This includes **26 repository-policy checks** enforcing no direct or mutual Python recursion and a global maximum of **1,000 physical lines per source file**, with no smaller module limits. **Ruff passed**, and **strict mypy passed for 167 source files**. See the machine-readable validation record (local artifact: `../../../results/production_transfer_validation_v4.json`).

The adversarial gate (local artifact: `../../../results/followup_representation_audit_v4.json`) passed **288 tests across 23 groups**. Every group executed in a fresh pytest process against final production source: 22 groups in the initial final batch and the updated release-probe group afterward. No prior-revision results were reused. Historical v2 and v3 artifacts remain unchanged.

The gates cover proof-oracle rejection before cold/warm/zero-step access, foreign and malformed scoped IDs before mutation, exact-constructor poisoning on public point/width paths, packed-history and proof-object injections into registered stores, and inspection of transient carry-query frames. They also compare actual engine inventories with public metrics.

```sh
ruff check .
mypy --strict src
python -m pytest -q
python bench/action_morphism_adversarial_audit.py --output results/followup_representation_audit_v4.json
PYTHONPATH=src python bench/lazy_resource_audit.py
```

## Cold measurements

The v4 resource matrix (local artifact: `../../../results/lazy_resource_audit_v4.json`) runs each row in a fresh process and checks the requested digit against an independent scalar oracle. All ten rows have matching ledger and independently observed counts, complete audit coverage, zero unowned stores, zero forbidden future payloads, and zero explicit endpoint lowerings. Composition requests equal hits plus evaluations. Slots, payload nodes, and operation counts are separate units; none is a byte-accurate memory measurement.

The public metrics distinguish the three one-symbol carry functions from the seven complete spatial interval effects. The compatibility class-code width is three bits; it is not the storage size of a Python handle and is not a temporal closure bound. The reverse carry cursor peak remains at most 40.

| Family | N | Branch observations | Summary evaluations | Bounded arithmetic operations | Memo/interner slots | Retained payload nodes | Cold seconds |
|---|---:|---:|---:|---:|---:|---:|---:|
| reverse | 16 | 15 | 46 | 12,489 | 211 | 139 | 0.014 |
| reverse | 32 | 31 | 144 | 92,772 | 427 | 305 | 0.110 |
| reverse | 64 | 63 | 508 | 305,811 | 1,021 | 801 | 0.381 |
| reverse | 128 | 127 | 1,922 | 1,095,579 | 2,889 | 2,475 | 1.578 |
| reverse | 256 | 255 | 7,309 | 10,621,780 | 9,178 | 8,378 | 15.349 |
| collatz | 16 | 7 | 9 | 414 | 63 | 41 | 0.001 |
| collatz | 32 | 14 | 16 | 1,814 | 95 | 58 | 0.002 |
| collatz | 64 | 27 | 29 | 9,095 | 153 | 88 | 0.009 |
| collatz | 128 | 42 | 44 | 29,512 | 223 | 124 | 0.024 |
| collatz | 256 | 42 | 44 | 29,470 | 225 | 126 | 0.024 |

These results still show 15/31/63/127/255 reverse branch observations. Removing eager histories does not remove branch discovery, and the measured arithmetic and retention are not logarithmic.
