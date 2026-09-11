# Decimal carry cocycle refinement — September 10

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Implemented the exact parity carrier, local contextual carry-function identity,
and complete finite-interface temporal substitution. The decisive 196 gate is
**not complete**: a source-independent symmetric action reaches four events
with `primitive_successors = 1`, but its eight-event composition exceeds the
fixed 30,000-node probe budget. Larger requested powers are not admitted.
No powered 196 identity or compiler speedup is promoted from these results.

The [architecture contract](../../../docs/architecture/reverse-threshold-cocycle.md)
describes the scalar owner, APIs, residual identity, definedness, coordinate
orientation, resource accounting, and remaining production admission gate.

## Implemented algebra

- The endpoint carrier stores Gamma, F5, and decimal parity epsilon separately.
  Both value channels are affine; epsilon and the previous Boolean-half beta
  coordinate are related by XOR with alpha parity.
- F2 transport uses characteristic-two Frobenius factors. Any no-growth
  doubling annihilates its homogeneous source term. F5 and F2 share the
  output-forcing composition owner.
- `ThresholdCocycleResidualID` identifies an extensional Boolean function,
  including its typed context and definedness. It supports affine-coordinate
  precomposition, restriction, and complete contextual temporal pullback.
  EQ remains a separate predicate on the additive output.
- Complete temporal actions substitute all output ports simultaneously and
  pull back midpoint admissibility. They never invoke primitive successors
  or evaluate a midpoint value. Event counts are diagnostic metadata, not
  part of function identity.
- The bounded arithmetic compiler offers full-field and reversal-orbit
  interfaces. The latter aliases mirrored inputs before constructing carry
  functions, requires even odd-width centers, and maintains width and padding
  through growth. Neither interface is an unbounded recursive spatial grammar.

The growth stencil needs reflected carries: the extended normalized word
uses `D[i] + D[m-i]`. For `(16,16)`, the interior is `7+7=14`; forward
normalization followed by `D[i]+D[i-1]` would incorrectly produce thirteen.
The scalar and bounded arithmetic regressions retain this counterexample.

## Exact controls and proof scope

The primitive consumer is checked on all 100 decimal input pairs. Swapped
arguments intern to the same function. Separate controls prove that equal
kappa does not erase EQ, restrictions affect identity, incomplete substitutions
are rejected, and uninterned residuals cannot bypass resource accounting.

The symbolic control `(x,y) -> (x+y mod 10,y)` with its observed carry consumer
squares from A1 through A1024 with primitive construction and point evaluation
poisoned after A1. Every power agrees with an independent closed form on all
100 input pairs. Its A16 and A256 actions are extensionally identical. This
is an actual function-quotient control, not a 196 result.

The complete bounded reverse/add compiler is checked against the independent
oracle on all 219 admissible symmetric fields through width three, in both
full and reversal-orbit representations. Separate two-step checks poison
primitive execution and midpoint observation, including capacity overflow.
Uniform runs at lengths 1, 4, and `10^100` advance through
`2^L -> 4^L -> 8^L -> 16^L -> 7 14^(L-1) 7` without importing or decoding
pair/digit fields. The three result planes each use at most four DAG nodes.

The installed Isabelle2025-2 session passes all theories, including the new
`Reverse_Threshold_Cocycle`: CRT inversion, additive normalization and output
coordinates, domain recovery, and the decimal carry cocycle identity. The
transitive oracle-dependency check is empty. The guarded build takes 12.142
seconds with a sampled 443,960,824-byte footprint. These are mathematical
scalar theorems, not a refinement proof of Python or a powered 196 theorem.
See `isabelle.log` and `isabelle.guard.json`.

## Powered 196 attempts

Every action is compiled without binding a seed. Seed 196 is supplied only
for indexed output verification after construction. During squaring, the
compiler, both endpoint successor APIs, primitive action construction, and
finite-function point evaluation are poisoned. Oracle work occurs outside
composition; the final probe reports action and oracle-observation time
separately.

The original full-field capacity-four action matched one arithmetic step,
but A2 exceeded the 30,000-node budget. Building symmetry into the interface
allows capacity five to reach A4 under the same limit. The capacity-six
attempt on the final source gives:

| Power | Width for 196 | F5 function nodes | F2 function nodes | Domain function nodes | Interned kappa IDs | Kappa decision nodes | Primitive constructions |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 1248 | 358 | 858 | 43 | 530 | 1 |
| 2 | 4 | 3226 | 988 | 1707 | 46 | 1094 | 1 |
| 4 | 5 | 5078 | 1839 | 2486 | 49 | 1677 | 1 |

A8 fails before allocating node 30,001. The largest successful action took
22.119 seconds of cumulative action construction; independent indexed oracle
observation took 0.0023 seconds. The whole failed attempt stayed within the
35-second/1-GiB process guard (24.762 seconds, sampled 65,389,000 bytes).

The capacity-nine interface needed for the 16-step endpoint exceeds the node
budget while constructing A1. Requested powered rows at N=16,32,64,128,256,512,
and 1024 are therefore unavailable. The capacity-seven attempt also exceeds
the budget at A1. These are bounded implementation failures, not proofs that
the proposed cocycle quotient cannot be compact.

Cocycle-ID counts include all interned roots retained by the probe arena,
not only the three live endpoint roots. Decision-node counts include context
and definedness. Planes can share underlying decision nodes, so their counts
must not be summed as exclusive memory usage. The complete action stores
all value/domain outputs and context predicates; its cost cannot be inferred
from kappa-ID count alone. A zero-source one-cell reverse/add control reaches
A1024, but is deliberately excluded from the 196 evidence.

## Separate primitive endpoint measurements

These rows measure the new parity plane on the actual 196 orbit. Every one of
1,024 primitive successors is checked against the independent pair oracle.
The run is divided into eight checkpointed 128-event processes; each imported
checkpoint is validated against its independently recomputed source orbit.
Counter corruption is rejected. No temporal quotient is used in this run.

| Events | Width | Gamma DAG nodes | F5 DAG nodes | Epsilon DAG nodes | Primitive successors |
|---:|---:|---:|---:|---:|---:|
| 16 | 9 | 4 | 12 | 7 | 16 |
| 32 | 16 | 14 | 15 | 12 | 32 |
| 64 | 31 | 26 | 17 | 12 | 64 |
| 128 | 58 | 35 | 51 | 28 | 128 |
| 256 | 113 | 55 | 86 | 44 | 256 |
| 512 | 222 | 113 | 145 | 76 | 512 |
| 1024 | 421 | 158 | 236 | 119 | 1024 |

At 1,024 events epsilon uses 119 nodes versus 124 for the earlier beta plane;
this coordinate change is not a new semantic quotient. Cumulative measured
chunk execution and validation time is 78.961 seconds, excluding checkpoint
import/oracle replay before each chunk. The longest process takes 19.301
seconds, with a maximum sampled chunk footprint of 60,375,496 bytes.
No runtime speedup follows from these measurements. `endpoint-summary.json`
and the individual logs/checkpoints preserve the evidence.

## Validation

The final focused cone passes **68 tests in 7.04 seconds**, including the
structural repository-policy checks. Strict nonincremental mypy passes for
all 1,125 authored Python files. Ruff lint and changed-file formatting pass.
The complete ordinary suite passes **4,277 tests in 290.97 seconds**, with
970 validation tests deselected. Its unchanged 300-second process guard
finishes in 292.126 seconds with a sampled 579,552,120-byte footprint. Both
JUnit source fingerprints match the frozen tree. `unit-summary.json`,
`final-unit.xml`, and `final-unit.guard.json` preserve that result. This run
does not demonstrate a reduction in unit-suite runtime.
Historical validation results in the earlier factored-carrier checkpoint
retain their original source identity and are not relabeled as new parity
exhaustive evidence.

Final source fingerprint: `64ae3ccfaf6788d9a25c242ba00da3a5db6bd908f3c6e540801def713c2fa049`.
No full unfiltered release-suite result is claimed. The remaining requirement
is a compact recursive spatial/contextual cocycle action that reaches the
nonquiescent 196 powers under the declared resource and correctness gates.
