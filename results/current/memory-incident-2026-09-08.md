# Diagnostic worker memory incident — 2026-09-08

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../README.md).

This record concerns an unfrozen working tree, not a release benchmark.

## Observed failure and containment

Eight orphaned repository Python heredoc workers were stopped:
46278, 46378, 45597, 46219, 46322, 45865, 45632 and 46025. The final two
workers were verified to have the repository as their current directory.
Subsequent process checks found no remaining Python workers.

Before termination, macOS `vmmap` reported:

| PID | Virtual total | Resident total | Swapped total | Allocation evidence |
| --- | --- | --- | --- | --- |
| 45632 | 11.3 G | 132.2 M | 10.2 G | 14,149,485 malloc allocations; 9.1 G allocated |
| 46025 | 2.8 G | 241.6 M | 1.6 G | 139,710 malloc allocations; 354.5 M allocated |

These are rounded values copied from the observed tool output, not exact byte
measurements or an independently retained raw `vmmap` artifact. RSS alone hid
most of the footprint. The combined memory peak across all eight processes was
not captured and remains unknown.

The worker owner identified the unfinished commands as wide-radix probes,
including radix `2**63 - 25`, Collatz inputs `2**120 + 27` and `2**40 + 27`
at three physical steps, and related direct projection probes. Generic parent
composition over the symbolic 64-bit remainder interface was the implicated
allocation path. Compact primitive admission did not prevent enormous composed
decision DAGs. This is not evidence attributing the allocations specifically to
the decimal 196 Frobenius implementation.

The process-management error compounded the algorithmic problem: a tool's
30-second yield was treated as termination, leaving workers alive. Multiple
subsequent probes ran concurrently. These jobs must not be counted as completed
timings, successful memory tests or evidence for scaling.

## Required fixes

1. Use one guarded diagnostic worker group at a time. The shared
   `devtools.checks.process_guard` measures macOS physical footprint, enforces a
   default 1 GiB sampled limit and the existing 35-second probe deadline, and
   cleans up the group on exit. Sampling permits overshoot; it is not an arena
   allocator budget or a hard OS memory cap. Do not detach children from the
   supervised group. Reports distinguish completion, timeout, memory/output
   limits, instrumentation failure and interruption.
2. Replace universal wide-port decision-DAG parent expansion with bounded
   algebraic or concrete carry/remainder composition in the existing scheduler.
   No fallback to a flat digit scan or retired continuation backend is allowed.
3. Reserve actual construction workspace and semantic nodes before allocation.
   Track declared interface cardinality separately from retained nodes, total
   allocations, live footprint, and reduction work. A residue bound is not a
   memory bound on an arbitrary representation of its functions.
   Static inspection found that `semantic_function_transactions._Transaction`
   appends temporary nodes and hash maps before the final publication reservation.
   That accounting gap must be repaired independently of the process watchdog.
4. Replace the independent quadratic source-affine prefix scan with canonical
   carry-prefix summaries. Repeated output requests cannot reprocess the entire
   earlier prefix.
5. Validate small bounded cases first, then increase workload only after memory,
   cleanup and reuse gates pass. Retain the existing performance limits. Apply
   the same controls to decimal 196, Collatz and Frobenius research probes.

Containment does not fix the composed-interface algorithm. The release remains
incomplete until measured execution and memory use satisfy the existing gates.

## Containment validation

Saved diagnostics are in [memory-guard-2026-09-08](memory-guard-2026-09-08/):

- 23 focused tests passed in 2.27 seconds: nine watchdog tests, thirteen
  payload/accounting tests and one bounded symbolic-division admission test.
  The supervised run's sampled group peak was 77,005,328 bytes (about 73.4 MiB).
- Strict mypy passed for 15 changed files. Repository-wide Ruff checking passed.
- Recursive structural checks passed: maximum 1,000 lines, no recursion cycles,
  and no package violations. Its sampled group peak was 386,319,056 bytes.

These measurements include supervision overhead and use a changing working
tree; they do not establish algorithm scaling or a passing full-suite release.
No maximum-radix or large 196/Frobenius workload was rerun for this validation.
The watchdog reports missing samples as unavailable, rejects a leader's apparent
success when live background group members remain, and verifies group cleanup.
It supervises cooperative commands; it cannot prevent deliberate process-group
escape or guarantee cleanup after its own SIGKILL.
