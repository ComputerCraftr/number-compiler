# 196 consumer schema and harmonic duplication audit

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The growing consumer count mostly reuses a small set of programs: at capacity
nine, A8 and A16 use the same **41 consumer schemas**, despite **924 and 1,844
bound occurrences**. Explicit schema interning now removes duplicated program
tuples. The binding families still grow, and this change does not establish
successor closure or a production compiler speedup.

## What is actually stored

`GeometryAction` contains exact output expressions, their derived threshold
geometry, and admission. It has **no independent H5 or P8 factor**. The H5
projection is computed separately by the harmonic validation probe. There is
therefore no stored Cartesian product of domain, H5, and P8 states to remove
from this action.

The low harmonic projection cannot replace the threshold-visible residual.
The existing regression compares valid symmetric pair fields `8^9` and
`(9,10,10,10,10,10,10,10,9)`: their low harmonic germs agree, while their domains
and successors differ. Retaining their distinction is necessary; the finding
does not imply that an independent P8 coordinate must be introduced.

The F5, F2, and domain expression counts are overlapping reachable sets. Adding
them counts shared expressions more than once. `reachable_expression_nodes`
measures the union instead. At A16 those three counts are 7,279 / 7,251 / 7,459,
but their output-and-admission union has **8,988** expression nodes.

## Program identity versus binding identity

| Power | Bound consumers | Unique schemas | Operand bindings | Translation/reflection families |
|---:|---:|---:|---:|---:|
| 1 | 119 | 25 | 85 | 61 |
| 2 | 234 | 41 | 166 | 142 |
| 4 | 464 | 41 | 328 | 304 |
| 8 | 924 | 41 | 652 | 628 |
| 16 | 1,844 | 41 | 1,300 | 1,276 |

`ConsumerSchemaID` identifies an exact unary table together with its input and
output sorts. Each occurrence separately retains its operand expression. Two
occurrences can now share one program object while producing different values;
the regression explicitly checks that distinction. Temporal substitution
continues to substitute bindings simultaneously.

Before the fix, many equal program tuples already shared Python objects, so
counting one full table per occurrence overstated physical storage. At A16:

| Reachable program storage | Before | After |
|---|---:|---:|
| Distinct table tuple objects | 127 | 41 |
| Entries in those objects | 1,079 | 384 |
| Entries if incorrectly counted once per occurrence | 15,178 | 15,178 |

The complete retained registry has 42 schemas and 395 entries, including one
schema no longer reachable from the current action. The arena retains 9,007
expression nodes and 42 schema nodes, **9,049 total**. Both kinds count against
the unchanged 30,000-node budget. Entry counts measure table storage, not total
heap bytes or end-to-end runtime.

The audit's family normalization factors out structural spatial translations
and reflections, preserving coordinate roles, relative offsets, table laws,
and affine coefficients. It is a diagnostic count under coordinate maps,
not a semantic state key. It neither performs Frobenius family minimization
nor proves equivalence of the resulting successor functions.

## The remaining closure obligation

The local consumer interface has one operand hole, but that operand depends on
up to **16 original input ports** at capacity nine. The complete boundary
interface also has 16 ports. A unary program alone is not evidence that a
bounded temporal interface has been found.

Binding families grow from 628 to 1,276 between A8 and A16. Identifying more of
them requires an exact consumer-context normalization that also respects their
future binding transformations. No successor refinement fixed point is computed
here: `successor_refinement_classes` and `successor_conflicts` are explicitly
unestablished, not reported as zero. Shared schema identity is never admitted
as an occurrence or production quotient identity.

The capacity-sixteen A32 probe still reaches the budget after A16. Schema
storage is now included in that cap: the failure records 29,938 expression
nodes plus 62 schemas, exactly 30,000 nodes. Thus explicit program sharing fixes real
duplication but does not remove the growth of unresolved bound expressions.
The source-independent A16 action is still built with one primitive
construction and primitive/evaluation APIs poisoned during squaring; indexed
observation still evaluates its unresolved consumers.

## Implementation and evidence

- `devtools/proofs/threshold_expressions.py`: one arena-owned schema registry,
  separate bound expressions, exact local composition, schema resource charges,
  and pre-allocation work charges for selection range unions.
- `devtools/proofs/reverse_consumer_audit.py`: separate occurrence, schema,
  binding, family, storage, and interface measurements. Its family work counter
  counts nodes plus argument edges; it is not a complete CPU/hash-cost model.
- `tests/sequences/reverse_add/test_consumer_schema.py`: shared programs with
  distinct outputs, unary composition, ownership, resource accounting, and the
  schema-versus-binding growth regression.
- `before.log` records the original tuple storage. `after.log` records explicit
  schema storage before the subsequent work-accounting adjustment. Neither is
  evidence that the remaining bindings are successor equivalent.
- `audit-final.log` and `a32-final.log` repeat both probes on the final source,
  including selection range-union charges and combined allocation counts.

Adversarial review checked schema ownership, table composition, simultaneous
substitution, family-key scope, and budget accounting. The existing Isabelle
pruning proof is unchanged: it proves range-based spatial pruning, not Python
schema interning or arbitrary powered successor closure. All changes in this
audit remain in research, tests, and documentation.

## Final validation

Source fingerprint:
`7f05bb55e39bb7a7b0bddac62fedc7226257ce2f42229ed5ee05dbb947843339`.

- **209,960 / 209,960** admissible symmetric fields through width eight agree
  with the exact successor oracle. All 44 partitions pass in nine serialized
  guarded runs; aggregate JUnit time is **89.960 seconds**. The reports contain
  exactly 44 distinct partitions and matching before/after source fingerprints.
- **41 / 41** focused and repository-policy tests pass on that same source
  (**6.099 seconds** JUnit time), including A16 with primitive/evaluation APIs
  poisoned, alternate bindings, invalid geometry, and capacity overflow.
- Strict mypy passes all 1,145 source files. Ruff and changed-file formatting
  pass. The final A32 diagnostic completes its process guard but reports a
  construction budget failure; that is not counted as a successful A32 action.
- `validation-summary.json`, the JUnit files, and the guard reports retain
  the measurements. The full ordinary suite was not repeated after this
  research-only schema refactor. Its earlier **4,318-pass** result belongs to
  the separately fingerprinted threshold-geometry checkpoint.
