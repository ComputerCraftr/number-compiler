# Representation boundary implementation

The current validation and the removal of exact slab/tape oracles from production are recorded in the [production transfer-boundary audit](PRODUCTION_TRANSFER_BOUNDARY.md).

This is the initial representation release record. The [follow-up adversarial audit](FOLLOWUP_REPRESENTATION_AUDIT.md) records later fixes for mutable callbacks, factory bypasses, aggregate numeric payloads, low-level construction, and independent ownership inspection. Its separate v3 artifacts supersede the validation claim below without overwriting the original measurements.

The production projection path for reverse/add, physical Collatz and uncertified generic block compositions is point-lazy. Original input data and kernel definitions are separate from future program and transfer-summary objects. Explicit output iteration and materialization cross a separate lowering capability boundary.

## Production changes

- `lazy_compiler.py` compiles immutable composition syntax under the index ledger. It does not enumerate a Cartesian boundary-state domain. This also fixes a constructor hang for non-power-of-two Collatz requests such as 1,000,000,001 physical steps.
- Uncertified generic compositions execute through `DiamondApplication` and its scoped parent/interface stores. The retired lazy-view executor and its parallel range-transfer cache have been deleted.
- `lazy_reverse.py` retains symbolic `Zero`, `Event`, `Transport` and `Add` offsets. Coefficient queries use bounded modular arithmetic and transient carry state. No first-20-row bootstrap or exact offset tape is constructed.
- `finite_port_action.py` represents finite port functions as reduced decision DAGs with iterative composition/substitution. Reverse carry scans compose and apply those handles; factored multi-port cuts do not enumerate a dense product.
- `lazy_collatz.py` retains `Identity`, `Mul3Add1`, `Shift` and `Compose` programs. Carry-range witnesses locate first and last nonzero positions. Valuation discovery and partial physical events do not pack intermediate tails or affine offsets into integers. Fixed-orbit shortcuts include all phases of 1 → 4 → 2 → 1.
- `lazy_radix.py` evaluates nonbinary Collatz points with source-backed division stages and complete bounded range functions. It retains no quotient word, synchronized remainder vector, point-result memo or prefix-result memo. Numeric point ports support radices through `2**63`; larger point radices fail explicitly, while explicit full-output conversion retains arbitrary-radix support.
- `hashlife_projection.py` has no eager tile-execution fallback. Public point and width queries do not receive lowering capabilities.
- `temporal_family.py` requires a compiler-issued certificate bound to operator identity, exponent and source encoding. Identity followed by normalization stays generic and returns 2 on source `(2,)`.
- Finite kernels freeze constructor data and identify their complete behavior with a versioned digest. Equal names cannot alias different behavior.
- Scoped action and summary handles separate owner, kind and local ID. Foreign handles are checked before memo lookup and shortcut paths.
- Immutable source tiles use weak interning with non-recycled IDs. `_LINEAR_CACHE` is removed. Compilation, source geometry and application caches use one index-owned `ResourceLedger`.

## Accounting contract

Schema 2 exposes registered cache/interner slots separately from retained node counts. It reports actual container sizes, independently traversed payloads, unknown audit coverage, per-index work, explicit lowering and arithmetic payload widths. Reservations precede publication; reservations involving multiple containers are atomic. Query-memo eviction releases its charges without evicting reachable canonical programs. Disposal releases actual memo payloads and charges before marking the owner closed; later access is rejected, including warm lookups. Lifetime tests verify that discarded terms and ledgers do not pin their arenas.

The legacy mixed-unit totals remain compatibility fields. New consumers use `resource_ledger_entries` and `resource_ledger_nodes` separately. A zero forbidden-payload count is not a sufficient gate by itself: complete inventory coverage, matching observed counts, and bounded arithmetic observations are also required.

## Validation

The regression suite includes independent arithmetic oracles, foreign-handle probes, false family dispatch, kernel mutation/identity tests, exhausted budgets, weak-source lifetime tests, interleaved-index accounting, poisoned endpoint lowering during point/width queries, and adversarial Collatz tails and event boundaries. The saved pre-fix evidence remains in `ADVERSARIAL_ACTION_AUDIT.md`. The current adversarial gate (local artifact: `../../../results/action_morphism_adversarial_validation_v2.json`) reruns invariant assertions in fresh test processes and rejects missing, failed or skipped coverage.

Final validation: **965 pytest tests passed**, including **26 repository-policy checks**; Ruff passed; strict mypy passed for **156 source files**. The independent saved adversarial gate passed **39 tests across 10 cases**, with no failures, errors or skips. The full run took 476.55 seconds on this machine. Machine-readable validation record (local artifact: `../../../results/representation_boundary_validation_v2.json`).

## Cold measurements

Each row uses a fresh interpreter and one point query. The exact digit is checked against a scalar oracle afterward. All rows have complete registered-payload audit coverage, matching observed ledger counts, zero forbidden future payloads, and zero explicit endpoint lowerings. Full inventories and warm-query observations are in the schema-2 artifact (local artifact: `../../../results/lazy_resource_audit_v2.json`).

| Family | N | Branch observations | Summary evaluations | Bounded arithmetic operations | Memo/interner slots | Retained payload nodes | Cold seconds |
|---|---:|---:|---:|---:|---:|---:|---:|
| reverse | 16 | 15 | 7 | 68,442 | 158 | 93 | 0.039 |
| reverse | 32 | 31 | 25 | 285,354 | 294 | 179 | 0.180 |
| reverse | 64 | 63 | 104 | 1,259,091 | 603 | 390 | 0.622 |
| reverse | 128 | 127 | 434 | 4,872,539 | 1,387 | 980 | 2.472 |
| reverse | 256 | 255 | 1,734 | 19,845,208 | 3,589 | 2,796 | 9.704 |
| collatz | 16 | 7 | 9 | 414 | 63 | 41 | 0.001 |
| collatz | 32 | 14 | 16 | 1,814 | 95 | 58 | 0.001 |
| collatz | 64 | 27 | 29 | 9,095 | 153 | 88 | 0.005 |
| collatz | 128 | 42 | 44 | 29,512 | 223 | 124 | 0.013 |
| collatz | 256 | 42 | 44 | 29,470 | 225 | 126 | 0.015 |

The largest observed arithmetic payload was 9 bits for reverse and 3 bits for Collatz. Reverse arithmetic work grows roughly quadratically in these samples. Elapsed times are observations from this machine, not complexity bounds. Ledger bookkeeping and Python object overhead are not payload-node or memo-slot units.

## Remaining proof and performance milestone

Cold nonlinear branch discovery can remain O(N). Canonical program syntax and finite carry-port effects are not a proof that the complete nonlinear temporal action is successor-closed. The source-independent, output-complete logarithmic cold-powering claim remains disabled. Explicit endpoint output remains proportional to the amount of requested output.
