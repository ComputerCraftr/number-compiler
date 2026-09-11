# Current release status (2026-09-05)

Latest checkpoint: [two-sided tile execution](HASHLIFE_TWO_SIDED_CHECKPOINT.md),
source `994fa53f9182`: **4,348 passed, ten unchanged absorption failures, 380.09 s**.
Ruff, strict mypy and structural checks pass. Deep absorption, production cutover
and the serial 300-second release gate remain incomplete. Earlier checkpoints
below are historical evidence.


The checkpoint descriptions below are historical. The active implementation and
acceptance contract is [HASHLIFE_CUTOVER_PLAN.md](HASHLIFE_CUTOVER_PLAN.md).
Deep public reverse/add and Collatz observations have not completed their
migration from higher continuation execution to demanded canonical tile
absorption. The latest frozen run is 4,324 passes, ten absorption failures and
386.08 seconds; it does not pass the serial five-minute gate. See
[the current checkpoint](HASHLIFE_BOUNDARY_QUOTIENT_CHECKPOINT.md). Component
quotient, accounting, canonical-ID and compiler optimizations cannot be
reported as that completed production cutover.

The current plan retains TileArena and CompletedResultArena, permits exact
canonical future tiles and spatial boundary-tile operands, and separates exact
output sharing from bounded behavioral interface equivalence. It does not
require a finite quotient of an entire trajectory or a new theorem before
integrating the existing composition equations.

---

# Linear bisimulation checkpoint update (2026-09-03)

**This section supersedes older routing statements below.** The bounded certified
family cutover is complete: decimal reverse/add and physical Collatz use
`ExtensionalFamilyApplication` with verified minimized T^2/C^4 bimachine rungs. The
old sequential family adapters are not selected by `_bounded_temporal_application`,
and recursive radix point/range replay is absent from production. Exact intermediate
future fields/provider histories are not retained.

Fresh validation on the final source tree:

- full pytest: **2,862 passed** in 480.11 s, zero failures;
- checkpoint/representation/accounting batch: **275 passed** in 24.23 s;
- repository structural batch: **67 passed**;
- former profiled C4 fourth RIGHT16 gate: passes unchanged 35-second deadline via
  closed-expression universal compilation (the requested profile remains validated
  and preserved as result metadata);
- N=16/32/64/128/256 evidence: `results/linear_bisimulation_checkpoint_v1.json`.

The checkpoint claims a **linear temporal-machine floor only**. At N=256 it performs
129 reverse T^2 applications and 64 Collatz C^4 applications; full symbol visits still
grow with the changing working-word width. Final logarithmic HashLife remains open
until higher powered machines close under complete output+successor bisimulation and
can be published as canonical parent actions. No provider-history, exact-tape, or
sequential fallback is permitted if a higher rung fails to close.

Static Ruff/mypy binaries were unavailable in this execution environment and could
not be re-run on the final two source edits; their earlier checkpoint results remain
historical rather than being represented as fresh validation.

---

# Diamond implementation status

## Linear bisimulation checkpoint (2026-09-03)

The bounded family checkpoint described in [LINEAR_BISIMULATION_CHECKPOINT.md](../repository-and-algebra/LINEAR_BISIMULATION_CHECKPOINT.md) is implemented. Decimal reverse/add now executes the verified minimized T^2 machine and physical Collatz executes the verified minimized C^4 machine; neither bounded production path advances a generation/event itinerary or retains provider history. The former seed-140137/step-11/radix-3 replay timeout is covered by a fast regression. Final observations use the strictly capped microblock facility; independent auditing reports zero forbidden future payloads.

This is **not** the logarithmic HashLife release. Machine-rung count is linear and full symbol visits still grow faster because each low-power rung scans the bounded working word. Higher-rung `compose -> output/successor bisimulation -> publish` closure remains the next performance gate. The old generic higher-continuation results below are retained as historical evidence, not as the current bounded family executor.

Machine-readable checkpoint evidence: `results/linear_bisimulation_checkpoint_v1.json`.

The **final logarithmic HashLife release remains incomplete**. The checkpoint
closes the sequential family/radix replay blockers and restores a bounded linear
temporal-machine floor, but higher powered parent machines still need complete
output+successor bisimulation closure. Compiler-node counts alone remain
insufficient execution evidence.

The [next implementation plan](HASHLIFE_CUTOVER_PLAN.md) records the higher-rung
quotient work and package reorganization that remain after this checkpoint.

## Historical extensional cutover work (2026-09-03)

The following section records the pre-checkpoint generic quotient work. It is
retained as implementation evidence and must not be read as the current bounded
family routing status.

- `DiamondQuotientArena` is the single complete-effect interner;
  `CompleteMacroActionID` aliases its scoped `DiamondQuotientID`. All thirteen
  required components are checked, normalized for admissibility, and retained
  as canonical factored semantic structures. Syntax/program handles cannot be
  published as completed parents. Compatibility scalar functions normalize to
  the same carrier. The new arena is not yet the production family executor.
- Primitive full dyadic source cells now have an actual complete-effect
  producer, executed by the shared dependency scheduler. All thirteen channels
  use canonical semantic functions, including one coordinate-parametric output
  function. Source bindings and original extent remain outside the quotient
  interner. Distinct source cells with equal complete effects receive the same
  quotient; equal carry exits with different output functions remain distinct.
  Public finite-kernel atom point queries and full-width queries use this path.
  Warm parent and new-boundary tests poison construction and child evaluation.
  This fixed-padded-cell contract does not supply the missing arithmetic-family
  normalization, H-stage, or higher-temporal contracts.
- Structured outputs retain joint outer/bound dependencies, with canonical
  product and function bodies. Type-derived binder bands keep inner selectors
  before enclosing continuation-entry ports. The independent eight-entry mux
  witness now needs 17 reachable Boolean decision nodes instead of 511, while
  preserving all 2,048 entry/selector observations and capture safety.
- Multi-root publication reserves Boolean nodes, factored values, structured
  nodes, semantic interner entries, and parent bindings atomically. Independent
  tests cover exhausted budgets, missing reservations, forged IDs, stale staged
  bases, and canonical identity after memo eviction.
- The shared iterative scheduler compiles primitive and one-pair input codecs.
  It avoids discarded projection/application children and uses correlated
  Boolean substitution rather than treating dependent argument bits as
  independent inputs. More deeply composed input domains remain explicitly
  unsupported. Both preserved C4-fourth-power RIGHT16 constructions now pass
  their unchanged 35-second diagnostic deadlines: the universal-domain check
  passed in a 14.87-second focused batch, and the explicitly certified profile
  check took 31.20 seconds. These are semantic compilation checks, not complete
  physical C^N point/width or logarithmic execution evidence.
- Boolean decision interning now probes canonical child IDs before rebuilding
  dependency metadata. Structured transactions share admissibility circuits;
  correlated substitution keys contain support-aligned integer roots. A
  certified C4-pair source-initial profile has a lazy 11-bit ordinal interface,
  with independently checked complete continuation tables. These changes reduce
  local construction work. Direct admissibility thresholds avoid constructing
  unused subtraction bits. Complete declaration operations now cache canonical
  StructureID/input-signature pairs before rewriting; their result and all
  participating semantic nodes publish under one atomic reservation. This
  removes repeated declaration construction without retaining observed values.
- Schema 5 distinguishes quotient normalization, early canonical-record reuse,
  parent lookup, and reductions discovering an existing result. Independent
  audits inspect typed scalar conversions, codecs, fused radix actions, and
  original-radix encodings. Audit work is timed separately from execution.
- The independent substitution audit was corrected to preserve external
  variable ordering across every live correlated argument. It still rejects
  nonzero result bits on invalid encoded inputs. Primitive inventory auditing
  now checks actual ownership, the complete fixed-cell contract, and original
  extent; named reporting forwards its real lookups, observations, spatial
  compositions, and retained binding counts.
- The unchanged radix-3/digit-3 regression now passes its specific speed and
  resource gates using the universal odd-C1 ternary law over immutable original
  source geometry. Five fresh processes measured median cold query 0.035631 s
  and repeat 0.000032125 s at 143 nodes / 144 entries. Construction and audit
  time are separate. See
  the fingerprinted record (local artifact: `../../../results/radix_regression_probe_v1.json`). This is
  evidence for that regression, not higher-power or general radix cutover.
- Original-radix storage now rejects suffix encodings, including encodings
  that would equal an exact future even-Collatz tail. C/C² source-coordinate
  views use bounded transient carry arithmetic over the full original encoding.
  Wide radix multiplication uses individually checked limbs, never an assembled
  wide prefix. Direct radix entry points reject unadmitted callbacks and numeric
  type aliases before width evaluation or retained mutation. The general radix
  matrix still times out at seed 140137, physical step 11, radix 3.
- An exact request-count diagnostic explains that remaining radix failure:
  the 13 valid ternary digits plus the exterior query entail 134,864,253 binary
  point requests under the current recurrence. Tiny actual executions verify
  the recurrence independently; the large fixture is counted without executing
  it. See the replay work inventory (local artifact: `../../../results/radix_replay_work_v1.json`). This
  exposes remaining work; it does not claim the work has been eliminated.
- Shared test factories and independent oracles replace cross-test imports.
  Audit-report reuse requires passing JUnit evidence with exact source
  fingerprints and the full required test-node manifest. Stale, skipped,
  failed, incomplete, or environment-filtered evidence is rejected.

Historical pre-checkpoint routing still reached the sequential lazy implementations,
and generic higher parents retained closure/program records. Those family/radix
routing statements are superseded by the linear checkpoint above. Complete
higher-rung quotient integration and package reorganization remain unfinished.
Historical measurements below remain unchanged.

### Frozen validation checkpoint (2026-09-03)

The corrected frozen tree ran all 2,870 collected tests without filtering:
**2,869 passed, one failed, no skips or errors**, in 421.65 seconds. The before
and after source fingerprints match. Ruff, strict mypy (244 source files), and
the repository structural checks pass. The sole pytest failure is the unchanged
35-second radix matrix gate for seed 140137, 11 physical Collatz steps, radix 3.
The earlier complete run and both logs are retained; its two additional fixture
mismatches were corrected without changing their semantic assertions.

Both C4-fourth-power semantic compilation gates pass in the full run: universal
input 13.84 seconds and certified profile 31.79 seconds. Five fresh fixed radix
trials report median cold 0.042682 seconds and repeat 0.000041625 seconds, within
the unchanged 0.25/0.01-second limits. Neither result establishes full temporal
quotient execution or logarithmic family scaling.

See the validation inventory (local artifact: `../../../results/extensional_validation_v1.json`),
the complete JUnit record (local artifact: `../../../results/extensional_cutover_full_v2.xml`), and
the fixed radix measurements (local artifact: `../../../results/radix_regression_probe_v2.json`).

## Active execution paths

`HashLifeBlockIndex` now routes uncertified, supported generic compositions to
`DiamondApplication`. The compiler's binary operator DAG reaches the iterative
diamond scheduler; there is no generic eager-midpoint or flattened-itinerary
fallback. Generic point, width and custom finite-kernel regressions poison the
old evaluator and future-tree constructors.

Historical pre-checkpoint certified reverse/add and physical Collatz adapters
routed through their sequential lazy engines. The linear checkpoint above
replaces those bounded production routes with T^2/C^4 bisimulation-machine
execution. The remaining blocker is higher-rung/logarithmic closure, not
sequential-family reachability.

## Implemented corrections

- Scoped temporal, source/image, boundary, context-program and finite-function
  identities reject foreign handles before warm hits and identity reductions.
- Nested images compose their temporal programs before image interning. Parent
  action, image, interner and memo publication share an atomic reservation.
- One production dependency scheduler executes spatial summaries, temporal
  substitutions, context programs and observations. Standalone pair/context
  drivers are poisoned in integration tests.
- Primitive spatial parent summaries are complete finite functions of their
  incoming port. Another incoming state reuses the parent without source reads
  or child evaluation. Higher contexts remain syntax-canonical programs; they
  are not reported as extensional equivalence classes.
- Complete right-state synchronization is proved for primitive interfaces and
  composed symbolically. Its cache normalization erases only the independently
  reset consumer state. For original-source cells, a certified low prefix also
  removes irrelevant suffix identity before lookup.
- Constant continuation arguments and constant complete primitive output
  functions discard unused dependency work before it is scheduled.
- The frozen physical C⁴ kernel has an exhaustive offline equivalence check.
  Decimal T² has a verified factorization and exhaustive output-expression
  oracle. The fully variable T² expression is still expensive; its existence
  is not a performance claim.
- Schema 4 inventories syntax programs, canonical finite functions, distinct
  memo families, original sources, images, explicit endpoints, real traversals
  and transient peaks. Early hits and reductions discovering an existing
  function have separate counters. Original-source immutable populations are
  distinct from index ownership.

## Parametric continuation candidate

The newer `diamond_parametric_query` path compiles complete higher spatial
programs before observing their ports. Opaque closure calls preserve child
program sharing; their evaluation uses the same iterative scheduler. The
reverse integration is available in `DiamondReverseApplication`, with only
initial pair geometry and an explicit endpoint-lowering capability. It is not
the default certified-family adapter.

Primitive continuation reduction recovers complete finite functions of an
already admitted primitive input. Cross-side and cross-kernel maps have explicit
input and output sorts; composition normalizes inadmissible input codes. C⁴
continuation aliases are checked over all 50 left and 90 right states. Higher
structured interfaces still remain programs, not claimed finite quotients.

Adversarial queries found several ways for an observation cache to disguise
future digits: literal carry-state responses, constant or nonconstant finite
functions capturing a closed output computation, opaque closure captures, and
substitution or head-response bindings that removed the capture. These cache
bindings are rejected. `binding_safe` is derived from actual children and
closure bodies when a node is interned, so warm admission does not rescan its
whole program. Reporting independently reconstructs this property and checks
the actual retained key/result pairs.

Finite-function validation is cached separately by primitive input sort,
output sort, and canonical function ID. Its keys have no source, expression,
coordinate, or generation occurrence. A diagnostic N=16 run reduced repeated
result-range validation from 3,983,205 to 90,907 visits; that isolated improvement
does not establish an improvement in total execution scaling.

The adversarial comparison with the old carrier found a precise limitation.
`_block_partition._normalize_partition` merges equal complete continuation
results before parent interning, including structured child states. The current
finite-expression carrier reduces bounded integer outputs. For a nested
continuation `lambda x: pair(A(x), lambda y: G(x, y))`, normalization can reduce
the anchor but declines the inner function when the outer port remains free.
Reduced functions returning structured continuation programs are still missing.
Primitive finite composition and application memos already use canonical IDs;
adding a bound scalar-response cache would recreate the audited tape leaks.

The existing complete right-reset certificate supplies one narrower extensional
law: a primitive transition with radius at most one forgets its incoming right
state for every admissible symbol. The higher scheduler now uses that law to
erase the state before observation-cache lookup and expression construction.
A singleton right domain also erases the symbol dependency. Original request
handles and sorts are checked before either shortcut; published results must
have the expected owner and state sort. Distinct
earlier programs in the nested-reset witness consequently receive the same
complete continuation ID. This does not minimize nonreset two-port functions
or arbitrary higher interfaces.

The reset-proof cache now reserves its owned entry and node before kernel
inspection. Exhausted entry and node budgets perform no primitive proof work;
exceptions release the reservation, and a warm certificate remains usable
with no remaining capacity.

The old higher fallback also obtained aliases by interning exact future
`DyadicTile` outputs. `_block_spacetime_runtime._intern_recursive_residual`
keys those occurrences by the previous residual and exact tile, and
`_eval_recursive_residual` consumes `_output_tile_macro` results. The exact
composition law survives replacing those tiles with programs. Its former
content-based reuse does not follow from syntax interning alone.

## Fresh parametric measurements

The frozen v1 matrices cover N=16/32/64/128/256 and spatial-width probes in
fresh processes, with a 35-second phase deadline and 180,000-entry cap. All
completed observations agree with exact oracles, and available representation
audits pass. Ten phases time out and four reject their resource reservation.
These are failed execution gates, not successful N=256 representation tests.

Reverse 196 times out at N=16 and N=32; N=64/128/256 exceed the cache budget.
Collatz on `(1 << 513) - 1` completes its N=16 point query, but its repeat still
executes 87,179 scheduler transitions, compared with 87,462 cold transitions.
Its N=16 width and N=32/64/128 points time out; N=256 rejects its budget.

The Collatz fixed-N=4 width probes have sampled affine-log query work: scheduler
transitions are 166, 169, 172, 175, 178, and 181 at doubling source widths. Source
construction is accounted separately. Reverse fixed-N=4 repeat-point work is
nearly linear in source width, and width queries time out at widths 64 and up.
No compiler-size measurement substitutes for these execution counters.

See [the measurement report](DIAMOND_PARAMETRIC_MEASUREMENTS.md),
raw reverse observations (local artifact: `../../../results/diamond_parametric_reverse_v1.json`),
raw Collatz observations (local artifact: `../../../results/diamond_parametric_collatz_v1.json`), and
the sampled scaling analysis (local artifact: `../../../results/diamond_parametric_analysis_v1.json`).
The analysis recognizes exact affine-log sequences without relaxing the
existing tolerance; linear and quadratic regression controls still fail.

## Historical candidate measurements

The diagnostic cap below is 180,000 retained entries. A capped case is a
failure to finish, never a zero-work sample or a successful projection. All
listed candidate queries avoid the bounded last-response register.

For the fixed 513-bit noncycle source `(1 << 513) - 1`, fresh C⁴-based diamond
applications gave the following results. Width runs follow the cold point in
the same index.

| N | Point | Width | Retained entries at last phase |
|---:|---|---|---:|
| 16 | 1; 0.436 s | 518; 0.887 s | 38,155 |
| 32 | 1; 0.991 s | 523; 3.209 s | 76,559 |
| 64 | 1; 3.064 s | resource cap | 180,000 |
| 128 | resource cap | not reached | 180,000 |
| 256 | resource cap | not reached | 179,999 |

Every recorded case passed the independent retained-payload and ownership
audit, including zero forbidden future payloads and zero accounting mismatch.
Those representation checks do not make the failed queries successful.
The full observations are in
the fixed-source profile (local artifact: `../../../results/diamond_fixed_513bit_noncycle_profile.json`).

An earlier decimal 196 candidate at N=16 also reached the same cap before
returning its first digit. Its actual retained inventory and work are preserved in
the pre-substitution profile (local artifact: `../../../results/diamond_reverse_before_fused_substitution_n16.json`).
The later largest-leading-power/fused-substitution candidate returned its first
digit in 4.817 seconds and its width in a further 1.313 seconds; those measurements
are preserved in
the leading-power profile (local artifact: `../../../results/diamond_reverse_leading_power_n16.json`).
These use the earlier runtime and are not measurements of the newer parametric
continuation evaluator.

Earlier 11-bit Collatz diagnostics are preserved separately:
baseline (local artifact: `../../../results/diamond_continuation_capped_profile.json`),
reset normalization (local artifact: `../../../results/diamond_continuation_reset_profile.json`), and
output pruning (local artifact: `../../../results/diamond_continuation_output_pruning_profile.json`).
They must not be mixed with the fixed 513-bit source to claim a scaling result.

## Remaining work

The dominant unresolved issue is repeated higher continuation/output work and
retention during exact substitution. The full H-stage output-complete transfer
quotient, source-independent higher macro reuse and both certified-family
production cutovers are not complete. The N=256 negative representation and
performance acceptance gates cannot be claimed for a query that does not
finish. Cold release measurements and final validation must be regenerated
after these blockers are fixed.

The earlier frozen tree passed 1,901 tests in 519.85 seconds, whole-tree Ruff,
strict mypy across 214 source files, and repository structural checks. The
validation record (local artifact: `../../../results/diamond_validation_v2.json`) includes the source
fingerprint. Earlier full-suite checkpoints passed 1,550, 1,610, 1,825, and
1,877 tests. These passing code-validation gates do not close the execution
and routing blockers documented above or mark the release complete.
