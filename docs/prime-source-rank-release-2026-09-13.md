# Prime source rank/select production bridge — September 13

`number-compiler prime --nth N` now uses the canonical Legendre recurrence for
both source discovery and rank/select. The former selector path through the
residual divisor-lane compiler and final leaf bitmap is removed. Other public
finite prime-block APIs retain their existing owners.

## Construction and ownership

[`CoprimeRankDAG`](../src/number_compiler/sequences/prime/coprime_rank.py) is the
single iterative count evaluator. The compatibility recursive wheel delegates
to it with local per-call memoization. The production
[`selector`](../src/number_compiler/sequences/prime/select.py) retains one ledger
and memo through all ranks and factor extensions, then disposes both states
and factor storage. Traversal frames disappear on each return, including
budget refusal. Descriptor extension preserves the earlier factor prefix, so
existing `(depth,limit)` memo keys keep their meaning.

Production starts from `(2,)`. For a finite inclusive candidate horizon `H`,
it computes `B=isqrt(H)`. If `Phi(B,k)>1`, binary rank descent selects the least
survivor above the last known prime and appends it. The least survivor is prime:
a composite survivor would have a smaller prime divisor which also survives.
The descriptor remains a complete consecutive prime prefix. Stopping at
`Phi(B,k)=1` means only `1` survives, proving coverage through `B`.

For `x` above the last descriptor prime, finite prime count is
`Phi(x,k)+k-1`. For smaller `x`, count uses rank in the already discovered
complete prime prefix. This distinction is necessary when later rank queries
reuse a descriptor constructed for a larger horizon. Inclusive square boundaries
and the distinguished seed prime 2 are covered in independent bounded tests.

Stage discovery, recurrence evaluations, memo hits and rank admission consume
work. States and factors have ledger ownership; pending frames and operand-bit
work are reported separately. No parent primorial gap positions are materialized.
The prime-only state/work/stage controls and their units are documented in
[CLI help and migration notes](family-first-cli.md#prime-rankselect-resource-limits).
Work-step limits are not a proof of logarithmic source discovery or a CPU
bit-operation bound.

## Adversarial evidence

The new tests compare independent bounded prime references across seed, odd/even
start, prime-square and factor-stage boundaries, including the stage after 31.
They poison the old lane compiler, bitmap projector, gap constructors and the
machine-word primality oracle. A spy verifies that wheel and production use the
same evaluator and that a production query shares one workspace. Budget probes
check refusal, released traversal frames and zero owned storage after disposal.

An independent agent reviewed the count offsets, source admission, ledger and
CLI boundaries. It identified repeated descriptor tuple copying, which was
replaced with read-only count/last/rank accessors. A measured initial attempt
charged each compatibility wheel memo insertion through retained storage,
increasing the focused suite to 16.33 seconds; local per-call memoization restored
that suite to 4.25 seconds. The full-unit ownership policy then caught the map
still being attached to the owner object. The final repair makes it genuinely
local to `count()`, keeps the owner memo factory-created in both modes, and
rejects reuse after closure. All 140 focused ownership/prime/policy tests pass.
Exact `x<=1` and depth-one recurrence cases reduce redundant evaluation further.
The initial window is now `max(8,4*(rank+1))` with exact doubling; a caller can
retain a larger initial hint with `leaf_length`. This assumes no density bound.

## Proof and release boundary

The new Isabelle `Prime_Wheel_Bridge` session addresses the mathematical carrier:
source-prefix extension, stop coverage, least survivor and finite prime count.
It builds in 9.46 seconds under the unchanged 35-second/4-GiB guard, with
951,831,288 sampled peak bytes. The exported theorem dependency audit rejects
oracles; the theory adds no axioms or skipped proofs.
The theory explicitly separates these statements from executable Python
refinement. A completed formal bridge must additionally prove the division
bijection for numerical Phi, memo/postorder evaluation, binary selection,
transport to smaller queried bounds under an over-covering descriptor, and
resource claims. Generic finite-set subtraction alone is insufficient.

This change does not discharge the existing 196 reachable-image construction,
Fermat/Mersenne compact terminal evaluator, complete powered/projection
refinements or Antihydra source-7 barrier. Their release assertions and limits
remain unchanged. See the [evidence packet](../results/current/prime-source-rank-2026-09-13/README.md)
for the final test, proof and installed CLI results. The final ordinary suite
has 5,067 passes and the same four existing failures in 250.87 seconds; the
selected P0 gate remains at 15 failures and seven passes. Installed source-byte,
CLI, budget and resource checks pass. Cold nth1000 improves from 123.81 ms to
93.10 ms in the final three-sample comparison; repeated high-start queries
remain slower, as the evidence table explicitly records.

## Exact next formal integration points

A read-only audit of installed Isabelle/HOL found no numerical Legendre/Phi
recurrence theorem to import. The missing arithmetic bridge is the multiplication
bijection between surviving multiples of a new prime `p` in `{1..x}` and
`wheel_sift ps {1..x div p}`. Distinct-prime coprimality is essential. The available
HOL lemmas `coprime_dvd_mult_right_iff`, `less_eq_div_iff_mult_less_eq`,
`inj_on_mult`, `card_image` and `card_Diff_subset` supply the needed steps.
This yields the actual division recurrence used by the Python owner.

After that, the refinement invariant must bind each memo `(depth,limit)` to the
cardinality for that exact descriptor prefix. Appending a source-discovered prime
must preserve existing keys. Pending postorder frames require a dependency-ready
invariant; successful roots and budget failures have different postconditions.
The selector then needs monotonic binary-rank descent, exact window subtraction,
and its two smaller-bound cases. Neither set-cardinality identities alone nor
logarithmic composition of a supplied word establishes these facts.
