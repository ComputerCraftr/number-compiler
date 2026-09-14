# Prime-clock descriptor owner — September 13

The fixed-wheel rank/select construction already exists and must not be listed
as missing parent-gap compression. Its canonical owner is
[`PrimeRecursiveWheelIndex`](../src/number_compiler/sequences/prime/wheel_cyclotomic.py),
using `_wheel_count_leq`, now delegated to the shared
[`CoprimeRankDAG`](../src/number_compiler/sequences/prime/coprime_rank.py) owner:

\[
\Phi(x,k)=\Phi(x,k-1)-\Phi(\lfloor x/p_k\rfloor,k-1),\qquad\Phi(x,0)=x.
\]

The implementation evaluates this dependency DAG by iterative postorder.
The traversal stack and per-query memo are local workspace and disappear
when the count returns. Neither is a parent primorial residue or gap cycle.
Extension changes the prime descriptor, modulus and totient length; it does
not evaluate all parent positions. Rank uses the exact count, and select uses
monotone binary rank descent.

This is the transferable distinction: local traversal geometry is not a
retained successor state or a materialized future carrier. Its arithmetic,
temporary workspace and retained cache still have real costs. Releasing the
stack does not erase the work of discovering/evaluating its DAG nodes.

## Reproduced eleven-stage gate

For `(2,3,5,7,11,13,17,19,23,29,31)`, the wheel modulus is 200,560,490,130 and
its period contains 30,656,102,400 coprime residues. The added
[regression gate](../tests/sequences/prime/test_recursive_wheel_descriptor_gate.py)
checks every prefix through 10,000 against direct coprimality, selected
rank/select inverses near and far in the wheel, periodic rank boundaries and
`count_positive_below(1_000_001) == 152_840`.

All parent-gap builders and materializers are poisoned during the test. The
gate passes, with **zero parent gap positions materialized**. The independent
reference stores only the 1,517 survivors in the bounded 10,000-coordinate
prefix, not the wheel cycle. Ten focused wheel tests pass.

The following measurements describe the pre-bridge evaluator, before the exact
depth-one and limit-one shortcuts added during production integration.
The state-count measurement needs its query scope. Profiling the actual
canonical count implementation, without reimplementing its recurrence, gives:

| Workload | Counted states |
| --- | ---: |
| One cold `Phi(1_000_000,11)` query | 1,240 distinct local DAG states; zero pending stack frames at return |
| That query, all prefix checks through 10,000, and six documented prefix selects | 140,747 distinct `(depth,limit)` keys across the batch; 3,024,608 state evaluations |

The cited **120,146** figure is not reproduced by these workloads and is not
asserted as an observed result. It needs the original query/caching schedule
for comparison. In this checkout, the bounded `lru_cache` retains whole-query
answers; intermediate memo entries are shared within a query, not across
different queries. The measured batch leaves 10,027 whole-query cache entries.
Thus cache entries, distinct batch keys, total evaluations and peak live
workspace must be reported separately.

## Production bridge follow-up

The original caller audit found `prime --nth` still using the divisor-lane
compiler. The [production bridge follow-up](prime-source-rank-release-2026-09-13.md)
replaces that selector path with a query-owned Legendre DAG, source-derived
factor stages and singleton rank descent. The compatibility recursive wheel
calls the same evaluator with local per-call workspace.

The fixed wheel through 31 still counts coprime survivors, not all primes up
to a million. Production now discovers the complete prefix through each finite
square-root boundary and charges that discovery. Formal executable refinement
and a bound for unbounded increasing wheel depth remain separate obligations.
No existing cross-family release assertion was weakened.

[Original reproduction logs and probes](../results/current/prime-wheel-owner-2026-09-13/README.md).
