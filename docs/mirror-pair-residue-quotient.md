# Residue consumers for reverse/add carry domains

The subsequent [growth-coboundary update](growth-coboundary-directional-quotients.md)
adds a proved optional quotient and removes unused overflow-branch construction
from the default. The counts below describe this earlier checkpoint.

The September 10 update reduces duplicated value-consumer expressions in both
reverse/add branches. Current domain geometry still supplies the carries. Once
those carries are fixed, normalization consumes only `r=S mod 10`:

\[
D_i=(r_i+C_i)\bmod10.
\]

The code now reuses that residue expression and performs addition directly in
Z/10. It no longer reconstructs CRT digits from separately normalized F5 and
parity expressions. Growth uses the same normalized-residue operation; there
is no restoration of the old 19-valued source coefficient.

## Matched residues and the smaller domain observer

Without growth, reflection pairs two copies of the same symmetric source
coefficient. Put k=C_i+C_(L-1-i). The exact local output is

\[
F(r,k)=\begin{cases}2r+k&r<9,\\18-9k&r=9.\end{cases}
\]

`ThresholdExpressions.mirror_pair` specializes the existing decimal kernel's
law on this 30-case interface. Its complete output has 19 possible values.
Holding the carry ports fixed makes S and S+10 equivalent for S=0..8; current
domain geometry must remain distinct because it determined those carries.

The **domain-only** consumer has an even smaller exact quotient. It retains
one of four response rows over k=0,1,2:

| Residue group | Domain row (LT=0, EQ=1, GT=2) |
|---|---|
| 0,1,2,3 | 000 |
| 4 | 012 |
| 5,6,7,8 | 222 |
| 9 | 210 |

Equal response rows merge before temporal substitution. This is a quotient of
the domain consumer, not of the complete output value. A regression gives two
different residue functions the same domain-consumer ID while their complete
output IDs remain distinct. Constant row or carry inputs reduce further through
the existing unary-table owner.

The no-growth channel emissions are constructed directly:

\[
\alpha'_i=2\alpha_i+C_i+C_{L-1-i}\pmod5,
\qquad \epsilon'_i=C_i\oplus C_{L-1-i}.
\]

Old parity has no transport dependency on this branch. The attachment calls
this coordinate beta; the implementation calls it epsilon to distinguish
parity from the older half-digit bit.

## Growth uses adjacent residues and affine parity

Growth appends the fixed normalized digit 1 and reflects at width L+1. The
new edges equal r0+1. The interior pairs residues at adjacent source positions,
with their carries still supplied by the same geometry:

\[
S'_i=((r_i+C_i)\bmod10)+((r_{i-1}+C_{L-i})\bmod10).
\]

Consequently its channel transport is

\[
\alpha'_i=\alpha_i+\alpha_{i-1}+C_i+C_{L-i}\pmod5,
\]
\[
\epsilon'_i=\epsilon_i\oplus\epsilon_{i-1}\oplus C_i\oplus C_{L-i}.
\]

The edge injections are alpha0+1 modulo five and epsilon0 XOR 1. This is the
existing affine adjacent-position transport, not a geometry-only parity law.
The implementation uses the known symmetric source orbit within each width
branch instead of selecting value coordinates through every other width.

`decimal_sum_domain` directly classifies the two normalized residue operands.
It avoids the earlier intermediate affine sum of sort 19 followed by a unary
domain table. Constant edges and identical operands specialize through existing
unary tables, and commutative operands share one canonical native node.
Whole-interval range pruning remains in `ThresholdGeometry`.

The controls `(10,10,10,10)` and `(10,15,15,10)` have equal GT geometry and F5
fields. Their outputs are respectively `(1,2,2,2,1)` and `(1,7,12,7,1)`. Both
must remain distinguishable through the F2 residue plane. A global parity-drop
rewrite would fail this test.

## Measured effect and limits

At capacity nine and A16, the preceding geometry-derived carry implementation
retained 8,953 expression/schema nodes. The combined residue and direct-domain
implementation retains **7,784**. Unary-table bindings decrease from 1,156 to
516, but this excludes native two-operand consumers; the report counts those
separately. Including native consumers gives 1,604 occurrences versus the
previous 1,556; the measured saving is retained expression storage. A32 still
hits the unchanged 30,000-node cap. The matched domain observer has four
response classes, while exact
F5/parity outputs remain available to subsequent steps.

The first literal 30-case-node implementation increased storage to 10,192.
That candidate is recorded, not presented as an optimization. The successful
reduction requires sharing normalization and projecting at the actual consumer
boundary across both branches.

This remains a research compiler experiment. It does not establish a complete
temporal quotient or a production runtime speedup. See the
[dated evidence report](../results/current/mirror-pair-quotient-2026-09-10/README.md)
for A16/A32 results, native-node accounting, exact tests, and formal proof scope.

## Proof and checks

[`Mirror_Pair_Step.thy`](../devtools/proofs/isabelle/Mirror_Pair_Step.thy)
formalizes the matched-residue law and projections, fixed-port high-ten aliases,
branch-independent residue normalization, adjacent growth channel laws, affine
edge injection, and growth counterexamples. The finite four-row table and
Python lowering have executable exact controls; the Isabelle theory is not a
certificate for the complete Python temporal compiler.

The exhaustive symmetric-field successor sweep remains in opt-in validation.
Ordinary tests cover local laws, contextual row sharing, simultaneous
substitution, resource limits, growth controls, and poisoned primitive replay.
`growth_full19_value_fallbacks` counts reachable full mirror values and
19-valued sums of normalized operands (across the whole action, a stronger
zero check). `growth_generic_parity_tables` audits primitive growth parity
lowering between the existing source/carry ports and the emitted parity.
It excludes domain evaluation behind those carry ports; it does not claim
that a powered parity output is independent of all earlier value inputs.
