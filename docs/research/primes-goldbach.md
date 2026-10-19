# Prime ranks, wheel actions, and Goldbach obligations

[Current release gates](../release-status.md) own validation status; this page
records mathematical scope and source connections.

Status: **deterministic prime rank/select has checked finite refinement;
universal Goldbach multiplicity and its live finite prover remain separate**.

## Reading guide

- **Definition:** `Phi(x,k)` counts positive integers at most `x` coprime to the first `k` primes. Its recurrence is `Phi(x,k-1) - Phi(floor(x/p_k),k-1)`, with `Phi(x,0)=x`.
- **Checked theorem:** a sound complete prefix supports exact rank and binary selection; freshness and stopping conditions are explicit premises.
- **Implemented construction:** numerical counting and demanded descent avoid a materialized parent gap cycle.
- **Open obligation:** finite paired-residue checks do not establish universal Goldbach survival or an arbitrary-target construction bound.

## Prime source and rank/select

[`Prime_Wheel_Bridge.thy`](../../proofs/isabelle/families/prime/prime_wheel/Prime_Wheel_Bridge.thy)
connects a finite wheel descriptor to exact prime prefixes. In particular,
`discovery_stop_constructs_complete_prefix` requires the sound descriptor and
stop condition; `complete_prefix_survivors_are_exact_primes` applies to that
complete prefix. `prime_block_bisection` and
`binary_prime_branch_preserves_target` operate on an already exact rank block.

[`Prime_Wheel_Executor.thy`](../../proofs/isabelle/families/prime/prime_wheel/Prime_Wheel_Executor.thy)
proves the postorder evaluator completes for its finite dependency tree.
The deterministic Python refinements are connected in
[`Prime_Deterministic_Phi_Refinement.thy`](../../proofs/isabelle/families/prime/integration_prime/Prime_Deterministic_Phi_Refinement.thy)
and
[`Prime_Deterministic_Worklist_Refinement.thy`](../../proofs/isabelle/families/prime/integration_prime/Prime_Deterministic_Worklist_Refinement.thy).
The worklist theorem establishes evaluator reachability; it does not by itself
bound arbitrary target expansion.

Odd-window expansion and descent are proved in
[`Prime_Odd_Window_Expansion_Refinement.thy`](../../proofs/isabelle/families/prime/integration_prime/Prime_Odd_Window_Expansion_Refinement.thy):
the step preserves a ranked target under its guard, the loop terminates, and a
ready window descends to the target. Source initialization, prefix extension,
selection, and retained rank each have separate registered refinement theories
listed in the [proof index](../proofs.md).

## Progression and Goldbach views

[`Prime_Wheel_Skew_Actions.thy`](../../proofs/isabelle/families/prime/prime_wheel/Prime_Wheel_Skew_Actions.thy)
proves progression counts from modular inverses and exact finite windows.
`fresh_prime_deletes_at_most_seven` and
`eight_prebirth_survivors_leave_one` are local finite claims with their wheel
premises. They do not prove a universal Goldbach representation count.

The shared ANY/max algebra can express a finite paired-residue consumer, but the
live Python finite prover has not been connected to it. Global Goldbach G37 is
a source-global mathematical obligation, not a consequence of prime rank/select
or a bounded paired window.

## Production boundary and counterexamples

Prime enumeration must use the deterministic admitted source and charged
worklist. A finite comparison against a classical oracle is validation only.
An incomplete prefix, forged rank, or unsupported large target must not be
published as exact.

Failure of a proposed paired-residue quotient says only that the omitted phase,
rank, or window boundary matters. It is not a counterexample to Goldbach. A
finite successful corpus likewise cannot be promoted to universal multiplicity.

## Production and reproduction

- **Implemented owner:** [sequences/prime/coprime_rank.py](../../src/number_compiler/sequences/prime/coprime_rank.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Count-state discovery and rank/select descent remain charged separately from action composition. A finite timing result is not an arbitrary-target bound.

Run the exact executable checks (including validation-marked assertions):

```console
python -m devtools.checks.release --suite unit --select tests/sequences/prime/test_image_consumers.py --select tests/sequences/prime/test_prime_automaton.py
```
