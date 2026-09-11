# Tile boundary, quotient and validation checkpoint — 2026-09-05

**Release incomplete.** This pass does not finish arbitrary-depth demanded
absorption, the public reverse/Collatz/radix cutover, or the five-minute gate.
The final frozen source fingerprint is `64244f87626f30db4d00a14eaee89ab74b36f5d77bccbb23757ea8b3a650d946`.

## Final validation

- Serial, unfiltered pytest: **4,324 passed, 10 failed, 0 skipped** in
  **386.08 seconds** (387.04 seconds process wall time).
- Ruff: passed. Strict mypy: passed, 605 source files.
- Recursive repository structural checks: passed, including no direct/mutual
  Python recursion and at most 1,000 physical lines per production source.
- All ten failures are the existing `test_powered_output_absorption.py` gates.
  That file is unchanged, SHA-256
  `e26bd38d306b0a3165beceb9374250f1a7168d010f0f66f4a72f54c19817745a`.
- The result is slower than the 375.58-second baseline; isolated proof/compiler
  improvements do not establish an overall release performance improvement.

Full validation record (local artifact: `../../../results/hashlife_boundary_quotient_checkpoint_64244f87626f.json`),
JUnit (local artifact: `../../../results/hashlife_boundary_quotient_checkpoint_64244f87626f.xml`),
complete log (local artifact: `../../../results/hashlife_boundary_quotient_checkpoint_64244f87626f.log`), and
static checks (local artifact: `../../../results/hashlife_boundary_quotient_checkpoint_64244f87626f.checks.log`).
Intermediate failed checkpoints `13ad8b326bdb` and `90238b111f2b` remain preserved.
Their six audit regressions and typing error are fixed in this final fingerprint.

## Retained implementation

- Fixed boundary-tile operand pairs in result/interface keys and outgoing
  results, with alphabet/range/scope checks, unique leases, charged reverse
  indexes, retirement and rollback. These are exact spatial operands, separate
  from finite-port variants. Their complete execution propagation remains open.
- Exact iterative `TileArena.mirror()` with canonical child sharing, symmetric
  nonowning transform relations, early warm hits, retirement and independent
  inventory. Distinct mirrored content retains distinct TileIDs. Uncertified
  action/result orientation transforms remain rejected; no full-D4 claim.
- Actual primitive Myhill–Nerode refinement used by kernel admission/emission,
  with output, fixed-cell channels, both directional successors and Collatz
  occurrence observations. Partition equivalence checking is linear. Primitive
  quotient records, residual class populations and work have separate metrics.
- Validated local integer keys for Boolean ITE/substitution memos, with scoped
  public handles and independent alias/ownership/sort audits. Numeric payload
  auditing recognizes these stores only after their dedicated structural audit.
- Per-index finite-lift reuse in C4 semantic compilation, T2 cofactor-output
  reductions before repeated interning, and direct reduction of explicit-source
  cyclotomic coefficients. Compressed source runs retain their symbolic route.
- Audit-local reuse of validation for the same frozen primitive quotient. Fresh
  independent audits revalidate it and detect injected corruption.
- Scheduler demanded-result pin rejection and partial publication now release
  leases and reservations correctly. Forward/cyclic action references reject.
- Shared higher spatial wiring equations were consolidated without claiming
  that their construction alone implements demanded temporal absorption.

The production representation policy remains schema 6,
`canonical-future-tiles-and-boundary-operands-v2`. No fixture, exhaustive matrix,
trace, resource budget or watchdog was relaxed.

## Rejected deep-fusion attempt

The attempted generalization lost nested exterior dependencies by using the
final primitive's interface and resetting producer state at spatial children.
For base 3 and source `(0, 0, 0, 1)`:

| Action | Exact output | Rejected implementation |
|---|---|---|
| P⁴ | `(2, 0, 0, 4)` | `(0, 0, 0, 4)` |
| P⁸ | `(2, 4, 0, 2)` | `(0, 0, 0, 4)` |

That implementation and its midpoint-leaf emissions were removed. Deep demand
continues to reject explicitly. The primitive-pair path remains correct.
The supplied patch's exact macrocell recurrences are useful, but its complete
boundary-output construction cannot be copied as a demanded point evaluator.
This is unfinished integration of the existing equations and boundary operands,
not a request for a new theorem or another representation rewrite.

## Fresh-process execution evidence

Response and microblock acceleration are disabled in the field probes.

| N | Reverse 196 cold point | Collatz 27 cold point |
|---|---|---|
| 16 | 0.1568s | 0.1441s |
| 32 | 0.1969s | 0.1450s |
| 64 | 0.3699s | 0.1734s |
| 128 | 1.0050s | 0.2592s |
| 256 | 3.3696s | 0.4280s |
| 512 | 14.5032s | 0.7559s |
| 1024 | timed_out | 1.4384s |

Reverse N=1024 exceeds the unchanged 35-second worker watchdog. At N=512,
reverse retains 332,255 ledger nodes and 1,237,159 entries and records 2,504,109
internal work units, the same counts as the baseline. Its 164,720 higher-action
continuation requests remain. Both public families report **zero canonical
tile nodes and zero successfully absorbed temporal span** in these probes.
Thus neither family demonstrates the required production tile cutover.

Full field measurements (local artifact: `../../../results/field_boundary_quotient_64244f87626f.json`) distinguish
missing N=1024 reverse data from observed work/retention envelope violations.
No logarithmic execution claim is made. Release spatial-demand gates remain open.

The unchanged five-process radix regression passes: cold median
**0.0001352 seconds**, repeat median **0.00007383 seconds**. This is the existing
original-source ternary identity route, not proof of general powered radix
migration. Radix measurements (local artifact: `../../../results/radix_boundary_quotient_64244f87626f.json`).

## Remaining release work

1. Preserve both nested midpoint dependencies through executable boundary-tile
   operands or compiled boundary functions in the existing scheduler. Do not
   replace them with final-primitive ports or initial-state resets.
2. Pass P⁴/P⁸, noncommuting and noninitial-port demanded tests with complete
   midpoints and higher continuations poisoned. A two-int port tuple does not
   currently distinguish producer and consumer boundary contracts.
3. Cut over reverse, then physical/weighted Collatz, radix and compatibility;
   only then remove their competing continuation/image/provider executors.
4. Certify and apply full inverse transforms of outputs, ports, boundary
   operands and cocycles before enabling symmetry-normalized execution keys.
5. Meet actual cold work/retention envelopes and the serial <300-second gate on
   one passing frozen tree. Current primitive quotient and tile component
   tests are not substitutes for these production gates.
