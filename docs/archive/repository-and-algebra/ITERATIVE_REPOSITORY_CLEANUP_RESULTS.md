# v0.57.0 iterative repository cleanup results

## Global structural rules

- Repository-authored source code files are limited to **1000 physical lines**. This is the only line-count limit: there are no module-specific caps, and documentation or generated data has no line-count restriction.
- Direct recursion and mutual recursion are forbidden across repository-authored Python. Under the same static checker the v0.56 baseline has 69 call-graph SCCs; v0.57 has 0. Recursive tree/DAG structures remain valid, but traversal/evaluation uses explicit stacks, queues, bottom-up dynamic programming, or iterative binary powering.
- `bench/repository_policy.py` statically builds the repository call graph and detects recursion SCCs with iterative Kosaraju traversal. `tests/test_repository_policy.py` is the release gate.

## Refactors

- Converted powered block/runtime, HashLife, SLP/RLSLP, program-word, formula evaluation/building, decision DAG/MDD, cascade, Collatz, prime wheel/radix/lane, cyclotomic, and Karatsuba traversals away from Python recursion.
- Converted research product trees, multipoint remainder descent, special-source expression lowering, special automaton reduction, and benchmark cascades to explicit work stacks.
- Consolidated repeated benchmark JSON normalization, symmetric-word generation, and cascade relation-signature logic behind one owner each.
- Renamed the stale `_recursive_wheel_count_leq` implementation to `_wheel_count_leq` after its recurrence was converted to iterative postorder evaluation.
- Compacted four generated metrics JSON files; semantic JSON content is unchanged. Generated data is not subject to the source-code line limit.

## Semantic policy

This release is structural. It does not weaken the v0.56 HashLife budgets, exactness assertions, theorem guards, or fail-closed asymptotic frontiers. Reverse/add HashLife projection remains exact but not certified polylogarithmic; the same Collatz, prime-stage, and special-number theorem frontiers remain open.
