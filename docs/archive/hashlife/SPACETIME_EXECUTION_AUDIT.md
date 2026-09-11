# Demand-driven spatial execution audit

The representation checks and the logarithmic-execution requirement are separate gates. The earlier v5 release passed the representation gate but did not satisfy the execution requirement. This audit keeps the performance release blocked while either measured work/space exceeds its stated envelope or an output-complete temporal successor-closure implementation is missing.

## Confirmed findings

- The certified adapters lowered the compiled operator to a step count. Their nonlinear temporal schedules were not applications of a successor-closed temporal action.
- Reverse growth discovery scanned whole widths, and most carry reuse occurred at two-cell occurrences after substantial symbolic dependency traversal.
- Collatz repeatedly flattened composed programs into a primitive streaming pipeline and scanned whole transformed widths for event observations.
- Identical point requests repeated low-level work. The previous warm check only required unchanged branch discovery, which did not detect that replay.
- Compiler composition keys used structural descriptions instead of already admitted scoped child IDs.
- Original source quadtrees were retained but their canonical node identities did not consistently drive application work.
- Reported cursor bounds omitted other transient stacks, dependency collections, and program-port populations.

## Implemented shared changes

Compiler composition assigns scoped canonical child IDs before looking up a parent. Publishing new atoms and a parent uses one reservation across the program array and interner. Family certificates now check the actual kernel DAG and terminal order, as well as semantic identity and exponent; an identity-plus-normalization program cannot receive a reverse certificate.

The application boundary retains and validates the compiler's actual root handle. One bounded response register uses that handle and the requested coordinate before entering the evaluator. It holds at most one scalar, replaces the prior response, reserves before evaluation, and releases on failure or eviction. It is not a coordinate-indexed output field. A→A response reuse is reported separately from A→B→A evaluator reuse.

Original-source queries now use the registered source geometry. Generic finite-interface transfers key aligned source parents by scoped operator ID, source tile ID, side, and incoming state ID before visiting their cells. Foreign source geometry is rejected before application retention.

The rotated review found and fixed additional admission/accounting gaps: unsupported or cyclic imports now reject before retaining a valid sibling; certificates reject mixed alphabets; invalid generic sources reject before reservation; explicit index limits tighten a caller-supplied ledger instead of being ignored. Original-source authority can run its validated allocator inside a point query, but can no longer lend an unrestricted construction scope to caller code.

The final independent pass also reproduced and fixed three boundary defects. Copying a certificate could retain its issuer marker while relabelling the family; certificates now carry immutable issuance claims and validate every claim before dispatch or temporal-key access. Generic program admission now rejects mixed-base or mixed-blank children before any publication. Source-tile queries validate geometry and bound the requested level against the existing root before computing a power of two, so an invalid million-level query cannot allocate a proportional temporary integer.

## Spatial evaluator changes

Reverse growth requests follow the needed terminal carry region instead of scanning every interval in a generation. Demanded dyadic parents compose canonical child effects, and warm parent hits skip child evaluation. Original-source parents use source tile identities. Parents are retained only when requested, including requests arising across identity suffixes; knowing two siblings no longer eagerly publishes all their ancestors. Transport coefficient enumeration stops at the support relevant to the requested coordinate.

Collatz uses canonical range effects and source tile identities, fuses a multiplication and following shift into one symbolic stage, and uses bounded eight-cell finite-port kernels below dyadic parents. Known first/last-nonzero witnesses can answer points without replaying the kernel. A covering parent can answer a truncated event query only when its nonzero support fits that query's extent; the rotated review caught and fixed a cold/warm disagreement in this condition. Unrequested ancestors are not retained.

Independent Collatz range evaluators now issue effect IDs in distinct arenas even when they share an application. Previously their separate interners could assign the same owner/kind/local-ID triple to different functions. Cold and warm regression tests reject these foreign handles before lookup or accounting changes. Source-tile audits check actual membership in the owning geometry, rather than incorrectly comparing globally non-recycled tile IDs with an index's node count.

The Collatz event fallback still scans the event's finite width, and initializing a leaf kernel still creates a transient port for each applicable program stage. Those populations and visits are counted. They are not bounded independently of program depth, and they are not temporal macrocell jumps. No exact future digit tape, carry-row slab, or large affine-offset integer is introduced by these changes.

## Temporal limitation

Retaining a compiled root and caching its last response does not make the arithmetic adapter a temporal HashLife jump engine. The compact compiler DAG represents the operator's syntax. A complete carry boundary function represents only a spatial transfer and its permitted observations.

For example, decimal pair words `(2, 2)` and `(4, 4)` have the same complete two-cell carry effect. Their normalized outputs and their next pair fields differ. Consequently that carry-effect ID cannot identify their output-complete temporal action. A regression verifies this counterexample rather than treating the small number of spatial classes as a temporal closure proof.

No source-independent, output-complete successor-closed temporal action has been established for these adapters. Unknown branch discovery remains a separate algorithmic obligation. The performance gate must remain blocked until that obligation and the measured scaling requirements are met; passing correctness and representation tests does not clear it.

## Cold execution measurements

The v6 matrix (local artifact: `../../../results/lazy_resource_audit_v6.json`) runs each row in a fresh process with one worker. All ten rows match an independent scalar oracle, reconcile retained ownership, and report zero forbidden future payloads and zero explicitly materialized endpoints. Historical v5 artifacts are preserved. Final timing observations overlap repository validation and do not establish a wall-time speedup.

| Family | N | Branch observations | Bounded-limb operations | Summary evaluations | Temporal program nodes | Spatial binding slots | Total cache slots | Retained nodes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| reverse 196 | 16 | 15 | 7,054 | 32 | 71 | 35 | 215 | 126 |
| reverse 196 | 32 | 31 | 50,909 | 97 | 137 | 100 | 398 | 259 |
| reverse 196 | 64 | 63 | 191,582 | 340 | 267 | 343 | 873 | 634 |
| reverse 196 | 128 | 127 | 628,128 | 1,287 | 525 | 1,290 | 2,276 | 1,841 |
| reverse 196 | 256 | 255 | 5,786,760 | 4,901 | 1,039 | 4,904 | 6,797 | 5,971 |
| Collatz 27 | 16 | 7 | 362 | 3 | 14 | 11 | 63 | 45 |
| Collatz 27 | 32 | 14 | 1,677 | 7 | 24 | 22 | 102 | 67 |
| Collatz 27 | 64 | 27 | 8,759 | 20 | 37 | 48 | 172 | 103 |
| Collatz 27 | 128 | 42 | 28,975 | 29 | 56 | 72 | 250 | 146 |
| Collatz 27 | 256 | 42 | 28,933 | 29 | 58 | 72 | 256 | 150 |

At N=256, reverse/add retains 4,865 leaf bindings, 36 demanded parent bindings, and three original-source action bindings. The ten canonical transfer nodes do not account for those occurrence bindings or the millions of evaluator operations. Compared with v5, measured bounded-limb work fell from 7,592,429 to 5,786,760 and retained nodes from 6,525 to 5,971. These are reductions in the measured workload, not logarithmic scaling.

An immediately repeated point adds one response request and one response hit, with no evaluator work or retained allocation. The separate adjacent/revisited query phases still expose replay: reverse N=256 revisiting coordinate zero after coordinate one adds 8,102 bounded-limb operations. Caching the last response therefore does not hide the remaining evaluator cost.

The matrix exposes every recorded work-counter key and each transient maximum independently. Reverse N=256 reaches 110 evaluator stack frames and 92 coefficient dependencies. Collatz N=256 reaches 83 live leaf ports and 84 aggregate carry-payload bits; individual carry states remain bounded, but the collection grows with program depth. These are workspace populations, not additional retained DAG nodes. Process high-water bytes include interpreter, imports, source, retained objects, and transient work, and are explicitly labelled as such. Counters do not measure every internal Python operation, including hashing, equality, and modular-inverse implementation work; CPU and memory observations retain their separate scopes.

The deterministic sampled envelope is `1.25 * (first_value + 1) * (1 + log2(N)) / (1 + log2(first_N))`, with all observed counters and disjoint retained categories included. It is an empirical release criterion, not an asymptotic proof. Reverse has 51 cold and 32 adjacent/revisited metric failures; Collatz 27 has 36 cold and two adjacent/revisited failures. There are no missing required instrumentation fields. The release remains blocked independently by absent temporal successor closure and continuing temporal branch discovery.

## Fixed-source noncycle Collatz probe

Seed 27 reaches the fixed orbit during the standard matrix. The separate noncycle stress matrix (local artifact: `../../../results/lazy_resource_stress_v6.json`) uses the same original source `(1 << 513) - 1` for every horizon. Its independent scalar oracle verifies that all first 128 odd events have valuation one. Each row is exact, has reconciled ownership, and retains no forbidden future payload or materialized endpoint.

| Physical steps | Odd events | Bounded-limb operations | Leaf DAG visits | Peak live carry ports | Spatial binding slots | Total cache slots | Retained nodes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 8 | 18,785 | 65 | 16 | 466 | 549 | 61 |
| 32 | 16 | 71,611 | 257 | 32 | 991 | 1,118 | 92 |
| 64 | 32 | 283,821 | 1,025 | 64 | 2,055 | 2,280 | 158 |
| 128 | 64 | 1,165,585 | 4,097 | 128 | 4,237 | 4,660 | 290 |
| 256 | 128 | 5,007,461 | 16,385 | 256 | 8,830 | 9,448 | 453 |

The source width is fixed; this growth cannot be attributed to progressively larger inputs. The current implementation shows approximately quadratic discovery work and linearly growing transient ports. This orbit has the elementary closed form `3**h * 2**(513-h) - 1` after `h` complete odd/even pairs within the measured range. That formula is an oracle observation, not a production integer materialization. The measured cost exposes missing run compression, not an inherent lower bound or evidence that a faster algorithm is impossible. The stress gate reports 36 cold and eight adjacent/revisited failures, no immediate-repeat failures, and no missing required instrumentation.

## Validation

Final repository validation is recorded after its run finishes. Counts of compiler syntax nodes or spatial carry classes are not substitutes for execution measurements, and passing correctness or representation validation does not accept this performance release.
