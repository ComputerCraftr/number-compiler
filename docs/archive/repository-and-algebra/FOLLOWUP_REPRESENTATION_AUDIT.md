# Follow-up representation audit

This is the historical v3 record. The [production transfer-boundary audit](PRODUCTION_TRANSFER_BOUNDARY.md) addresses two gaps found afterward: callable exact slab/tape engines remained in the production namespace, and a transient carry memo could retain an entire small future row. Its v4 evidence supersedes this record without changing the historical measurements below.

This audit addresses the seven findings in the follow-up review and additional bypasses reproduced while implementing the fixes. It strengthens the representation and accounting boundary; it does not establish a successor-closed temporal quotient or logarithmic cold execution.

## Findings and fixes

| Finding | Enforced boundary and regression coverage |
|---|---|
| Nonbinary public Collatz points could lower a complete endpoint | Radices 3, 6, and 12 use lazy division programs. Tests poison `digits()`, `materialize()`, and endpoint lowering, including an adversarial 255-bit input. |
| Exact global interning retained discarded outputs | Exact tiles use weak structural interning with monotonic, non-recycled IDs. A fresh-process lifetime probe checks that explicit endpoint nodes disappear after their owners are collected. The computational `_UNIFORM_SYMBOL` cache is removed. |
| A finite kernel retained a mutable transition callback | `FiniteKernel` snapshots every transition during construction and executes its immutable table. Frozen finite block definitions use a versioned behavioral identity. Digest matches are followed by exact structural equality; collision tests prevent semantic aliasing. |
| Canonical IDs could be recycled or mutated | Public program collections expose immutable views. Canonical factory sequences are append-only. Scoped handles validate owner, kind, range, and registered object before warm lookups and shortcut paths. Mutable memo bindings can be evicted without recycling canonical identities. |
| Several bounded limbs could hide a future integer | Aggregate payload inspection follows nested containers, DAGs, and suspended generators. Approved semantic records validate every nested field, state domain, operation, and handle type. Tests inject four limbs into every field across the approved record templates, including forged finite-state and geometry wrappers. |
| Self-registration could miss retained stores | Production execution stores are created by the ledger factory. An independent walk starts at live execution objects and examines fields, slots, callbacks, closures, proxy backing stores, helper objects, and class-level caches. A structural regression rejects persistent bare caches in execution owners. |
| Lowering-only guards missed direct or transient exact-tree construction | Point and width observers run under a source-read scope checked by low-level exact-tree constructors before warm lookup. Original-source construction authority is issued before a point request and bound to the original input. A point callback cannot mint new source or endpoint authority. |

The allocation boundary also rejects direct built-in `dict` and `list` descriptor bypasses: ledger stores wrap private containers instead of inheriting from them. Public iterators cannot expose canonical backing lists, and execution stores reject serialization hooks that exposed their private containers. Batch insertions require sufficient prior reservations before changing any entry. Store ownership metadata cannot be reassigned, deleted, or reinitialized.

The semantic/runtime distinction is explicit. Primitive definitions and `ComposedBlockDefinition` are immutable and cacheless. The legacy `ComposedBlockEffect` interface remains an explicit runtime context; the public point compiler imports its immutable definition into the current index and does not retain that context. Unsupported custom primitives and subclasses cannot enter through a warm semantic-key hit. Generic admission checks every descendant by object identity before allocating retained resources or consulting semantic aliases.

## Accounting and scope

The term creates its ledger before compilation and passes that ledger into the eventual index and child arenas. Factory provenance and actual container contents are checked independently of payload callbacks. Ledger bookkeeping is traversed but is not counted as memo slots or retained program nodes. Those units are not byte-accurate Python memory measurements.

The arithmetic audit distinguishes exact source data, geometry/exponent metadata, immutable kernel constants, bounded finite-state transfers, and numeric payload. It is an executable conservative representation check with negative controls, not a general proof of information provenance for arbitrary Python code.

Point radix ports support radices through `2**63`; larger point radices raise an explicit unsupported-interface error. Explicit full-output conversion retains arbitrary-radix support. Cold nonlinear branch discovery may remain O(N), and explicit output lowering remains proportional to the output requested.

## Validation artifacts

Final validation passed: **1,186 pytest tests**, including **26 repository-policy checks**, with no failures, errors, or skips. Ruff passed, and strict mypy passed for **163 source modules**. The complete pytest run took 369.29 seconds. The global rules remain no direct or mutual Python recursion and at most 1,000 physical lines per source file, with no smaller module limits. See the machine-readable final validation record (local artifact: `../../../results/followup_representation_validation_v3.json`).

The saved adversarial gate (local artifact: `../../../results/followup_representation_audit_v3.json`) records **250 passing tests across 20 groups**. Its provenance is explicit: the initial expensive radix trace passed, and 19 other groups were reexecuted after the final store and admission fixes. The final full-suite run also passed that trace on the final source.

The earlier release results remain in `results/*_v2.json`. Both audit runners protect their historical outputs, and the resource runner now defaults to the v3 path. The public metrics schema remains version 2; v3 identifies this audit revision.

```sh
python bench/action_morphism_adversarial_audit.py --output results/followup_representation_audit_v3.json
PYTHONPATH=src python bench/lazy_resource_audit.py
ruff check .
mypy --strict src
python -m pytest -q --junitxml=/tmp/number-compiler-followup-pytest.xml
```

## Cold measurements

The fresh-process resource matrix (local artifact: `../../../results/lazy_resource_audit_v3.json`) covers reverse/add seed 196 and Collatz seed 27 at N=16,32,64,128,256. All ten rows match independent scalar oracles and report complete audit coverage, matching independently observed counts, zero unowned stores, zero forbidden future payloads, and zero explicit endpoint lowerings. Composition requests equal cache hits plus evaluations.

The source/endpoint lifetime probe returns the exact arena from 0 to 11 to 0 live nodes after explicit lowering and collection. The benchmark inventories distinguish source references from program and summary nodes; weak shared populations are reported separately.

| Family | N | Branch observations | Summary evaluations | Bounded arithmetic operations | Memo/interner slots | Retained payload nodes | Cold seconds |
|---|---:|---:|---:|---:|---:|---:|---:|
| reverse | 16 | 15 | 7 | 68,442 | 158 | 93 | 0.028 |
| reverse | 32 | 31 | 25 | 285,354 | 294 | 179 | 0.121 |
| reverse | 64 | 63 | 104 | 1,259,091 | 603 | 390 | 0.543 |
| reverse | 128 | 127 | 434 | 4,872,539 | 1,387 | 980 | 2.115 |
| reverse | 256 | 255 | 1,734 | 19,845,208 | 3,589 | 2,796 | 8.260 |
| collatz | 16 | 7 | 9 | 414 | 63 | 41 | 0.001 |
| collatz | 32 | 14 | 16 | 1,814 | 95 | 58 | 0.002 |
| collatz | 64 | 27 | 29 | 9,095 | 153 | 88 | 0.007 |
| collatz | 128 | 42 | 44 | 29,512 | 223 | 124 | 0.020 |
| collatz | 256 | 42 | 44 | 29,470 | 225 | 126 | 0.019 |

These samples still show 15/31/63/127/255 reverse branch observations and approximately quadratic bounded arithmetic work. The largest observed arithmetic payload is 9 bits for reverse and 3 bits for Collatz. Neither syntax canonicalization nor these measurements prove source-independent, output-complete temporal closure. Elapsed times are observations from this machine, not complexity bounds.
