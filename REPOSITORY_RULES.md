# Repository rules

These rules apply to repository-authored code, including production modules,
tests, benchmarks, and research utilities.

1. **Source code files may contain at most 1000 physical lines.** This is the
   only file-size limit; there are no stricter module-specific caps. A file with
   exactly 1000 lines is allowed, with or without a final newline. Documentation,
   generated JSON, and other non-source files have no line-count limit.
2. **No repository-authored Python function may use direct recursion or mutual
   recursion.** Tree/DAG traversals use explicit stacks or queues; recurrence
   evaluation uses bottom-up dynamic programming; repeated transforms use
   iterative binary powering. Recursive data structures are allowed, recursive
   Python call graphs are not.
3. **Canonical algorithms have one owner.** Shared helpers are imported rather
   than copied between production, benchmark, and research modules. New
   duplicate implementations must be consolidated before release.
4. Structural policy is executable. `devtools/checks/repository_policy.py` performs the
   source-file line-count and Python call-graph checks; `tests/repository/test_repository_policy.py`
   is a release gate.
5. Refactors must preserve exact semantics and existing performance/accounting
   gates. A policy cleanup may not weaken a theorem, budget, or fail-closed
   release assertion to make the structural gate pass.
