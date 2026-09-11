# Matched and growth residue consumers

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This research update implements the supplied residue-consumer reduction on
both reverse/add branches. Geometry still determines carry propagation; local
normalization consumes only the residue modulo ten. The successful lowering
shares CRT normalization and emits next domains directly. It does not promote
an incomplete temporal quotient into production.

## Implemented reductions

1. The no-growth correlated consumer uses the exact 30-case map F(r,k), with
   k the sum of its geometry-derived carries. F5 transport is 2alpha+k, and
   old parity cancels before temporal substitution.
2. Its domain projection quotients the ten residues into four response rows:
   `[0..3] -> 000`, `4 -> 012`, `[5..8] -> 222`, `9 -> 210` over k=0,1,2.
   Equal rows share a domain-consumer ID while different exact output values
   remain distinct. This is a consumer quotient, not a merge of current domain
   geometries or complete value states.
3. Both branches normalize through `(r+c) mod 10` instead of reassembling CRT
   from separately normalized F5/parity expressions. Each width branch uses
   its known symmetric source orbits, avoiding unrelated width selections.
4. Growth preserves the adjacent-residue F5 and F2 affine transport and its
   fixed edge 1. `decimal_sum_domain` consumes normalized residues directly,
   eliminating the affine 19-valued sum previously used only by a threshold
   table. Constant edges and identical operands specialize to existing unary
   consumers; whole-interval range pruning stays enabled.

The exact GT^4 growth controls remain distinct:
`(10,10,10,10) -> (1,2,2,2,1)` and
`(10,15,15,10) -> (1,7,12,7,1)`.
They have the same current domains and F5 values but different parity. The
residue quotient applies during growth; parity annihilation does not.

See [the implementation and equations](../../../docs/mirror-pair-residue-quotient.md).

## Measured candidates

The prior geometry-derived carry checkpoint retained 8,953 expression/schema
nodes at capacity nine, A16. The initial literal 30-case full-output node was
correct but increased storage to 10,192 (`a16-first.log`). Projecting directly
to the domain reduced that candidate to 9,664. Using known source orbits in
each width branch gave 9,186. These are diagnostic candidates, not speedups.

Sharing source residues through normalization brought storage to 7,974.
The explicit four-row domain quotient uses 8,056; its extra chart nodes enable
real contextual row sharing. Finally, direct growth-domain emission reduces
the combined action to **7,784** expression/schema nodes.

Thus the improvement comes from interacting and projecting the value consumer,
not merely naming an additional exact local node. Intermediate logs and the
`*.before.txt` / candidate snapshots preserve the rejected constructions.

## Accounting and limits

Unary-table counts exclude native matched/growth consumers. The updated audit
therefore reports native occurrences, their operand tuples, distinct matched
residue-response and carry-sum bindings, and normalized residue bindings for
growth. Total node/argument/range storage includes the native expressions.
The constant local truth tables are shared module-level laws built from the
existing decimal kernel, not one new table allocation per occurrence.

`growth_full19_value_fallbacks` detects full mirror output nodes and 19-valued
sums of normalized operands across the complete action. It is zero in the
measured action. `growth_generic_parity_tables` traverses primitive growth
parity emission expressions, stopping at the existing source parity and carry
ports; it is also zero. The latter does not hide domain computation behind
those carry ports or assert global parity death through powered growth.

The full current `(Gamma,alpha,epsilon)` state remains exact. No independent
carry history or additional parity plane is introduced. Compact local response
rows do not prove compact arbitrary temporal composition or a production
runtime speedup.

## Final measurements

The final capacity-nine A16 action (`a16-final.log`) has:

| Account | Count |
|---|---:|
| Retained expressions and schemas, including auxiliary entries | 7,784 |
| Retained argument edges | 19,158 |
| Retained possible-value atoms | 26,015 |
| Reachable unary consumer occurrences | 1,028 |
| Distinct unary bindings | 516 |
| Native consumer occurrences / operand tuples | 576 / 576 |
| Native matched-domain / adjacent-domain nodes | 384 / 192 |
| Matched residue-response / carry-sum bindings | 80 / 384 |
| Growth normalized-residue bindings | 240 |
| Unary plus native consumer occurrences | 1,604 |

Total retained nodes decrease by 1,169, or **13.1%**, from the preceding 8,953.
The total consumer occurrence count is **1,604 versus the previous 1,556**;
the reduction is in retained expression storage, not the number of all
consumer occurrences. Reporting only the unary binding reduction would obscure
this distinction. No elapsed-runtime improvement is asserted.

At every completed dyadic checkpoint, `primitive_successors=1`,
`growth_full19_value_fallbacks=0`, and `growth_generic_parity_tables=0`.
Composition poisons primitive construction and expression evaluation. The
regression tests separately compare powered outputs against the exact oracle.

The capacity-16 probe (`a32-final.log`) reaches A16 with 20,965 retained nodes,
then fails while constructing A32 at the unchanged 30,000-node ceiling.
The guard completed normally because the probe records the budget exception;
the semantic result is **budget_exceeded**, not a completed A32 action. Zero
fallback counters are established on completed actions through A16, not on a
nonexistent completed A32 action.

## Final verification

- 119 focused ordinary/dependency/policy tests pass; one opt-in validation test
  is deselected from that ordinary selection.
- All 209,960 admissible symmetric pair fields through width eight pass against
  the independent `pair_step` oracle across 44 exhaustive partitions.
- The 163 unique passing test IDs have complete JUnit manifests whose before
  and after fingerprints match the final source. Their selected pytest suite
  times total 92.601 seconds; this is not a full-suite timing.
- Strict mypy, Ruff, and formatting checks pass.
- The full Isabelle `Reverse_Residuals` session passes with the new
  `Mirror_Pair_Step` theory and no oracle dependencies on its audited theorems.
  The final guarded build took 15.748 seconds and peaked at 462,637,984 bytes.
  Earlier failed proof attempts remain in the evidence directory.

All guarded checks used the existing 35-second / 1-GiB limits and ran serially.
The added local tests cover the four-row quotient, fixed-port aliases, native
substitution, all 100 adjacent decimal inputs, growth parity controls, invalid
sorts, and resource enforcement. The exhaustive sweep remains opt-in.

Machine-readable results, native counts, and per-suite times are in
`validation-summary.json` (local artifact: `validation-summary.json`). Final authored-source
fingerprint:
`091ef60815ba042fea4c57d0ba7af2fba32b17db3b3d82932e86ad94fc918b15`.
The validated theory SHA-256 is
`06d5d8ab457846a0ad287ad3faebc67a873bec0de8a40d09c8307482476efe93`.
