# Disconnected quotient and slow-test audit — 2026-09-09

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This is a read-only execution audit, not a completed optimization release. Three agents independently inspected reverse/add, Collatz/radix, and Fermat/Mersenne. The coordinator checked the key gates and ran two isolated measurements. No production source or test assertions were changed.

Audited authored-source fingerprint: `a978d72c867bbc2b55651017d29d560aba6c7173ed0f08a42d578e580a960d39` (source fingerprint schema 4). Environment: macOS, Python 3.14.7, repository virtual environment. Measurements used one guarded process group at a time, a 35-second deadline, and a 1 GiB aggregate measured physical-footprint limit. The special proof aggregate itself launches four workers; its resource measurement includes them.

## Findings

### 1. Active temporal behavior is missing from the live quotient

**High priority; reverse and Collatz.** Public powered queries now reach the shared tile stack. The remaining problem is inside its execution, not a public fallback to the old family codec.

[`FutureBehaviorProfile`](../../../src/number_compiler/hashlife/behavior/future_behavior.py:138) accepts only the quiescent observation contract. Its class is an inactive blank self-loop; [`quiescent_boundary`](../../../src/number_compiler/hashlife/execution/tile_causal_behavior.py:44) rejects active tiles. There is no active carry-consumer classification or successor transition for nonblank P4/P8 dependencies.

[`tile_causal.py`](../../../src/number_compiler/hashlife/execution/tile_causal.py:625) tries blank behavior, then a finite primitive-pair transfer, then requests exact producer boundary output. [`finite_pair_transfer`](../../../src/number_compiler/hashlife/execution/tile_causal_pair_transfer.py:29) admits exactly two primitive children. It does not turn an arbitrary balanced temporal child into a reusable active transfer.

**Missing connection:** closed local carry/interface behavior → active consumer-profile transition → fused temporal dependency discharge. Exact causal tiles remain the correct fallback, but can be repeatedly constructed under different temporal contracts. Tile interning does not eliminate the work performed before a late content alias.

Acceptance witness: active P4/P8 dependencies answered with exact construction for those dependencies poisoned; preserve exact fallback and equal-carry/different-output counterexamples. Measure classification cost as well as saved exact construction.

### 2. Decimal F5/F2 laws are live; Frobenius temporal discharge is not

The decimal primitive kernel calls the allocation-free F5×F2×F2 helper laws in [`block_kernel.py`](../../../src/number_compiler/arithmetic/contracts/block_kernel.py:34); it does not retain those coordinates as a separate semantic carrier. Production closed leaf functions retain exact successor-output distinctions, and spatial parent functions compose their carry and sector transfers. This is not a missing primitive carry law or missing growth bit.

The sector transfer computes bounded carry-derived forcing. Its production consumer currently helps decimal width. [`observe_reverse_sector_product`](../../../src/number_compiler/sequences/reverse_add/tile_sector_observation.py:143) first executes `application.interface()` and only afterward derives the sector product from initial and final-input summaries. It therefore summarizes work already performed rather than answering a pending temporal dependency first.

`ReverseFrobeniusPlan` is a branch-independent source-death bound, with no executed forcing or unit result. It is attached during kernel admission and composed in the temporal algebra, but scheduler causal tasks do not consume its annihilation information. The separate `ReverseFieldActionArena` and `ReversePoweredLocalCodec` have tested algebra/mirror logic but are not the public reverse executor.

**Missing connection:** carry-derived sector forcing and certified component annihilation → the active consumer transition in finding 1. Remove a source term only in the quotient where its death is established; exact digit output still needs its remaining exact dependency. Do not restore a second codec/store merely to access its algorithms.

### 3. Collatz algebra is a separate, incompletely executable island

[`PoweredCollatzTerm`](../../../src/number_compiler/sequences/collatz/block_power.py:478) compiles physical powers and builds `HashLifeBlockIndex`. It does not call [`build_collatz_runtime_action`](../../../src/number_compiler/sequences/collatz/runtime_action.py:34), the local transfer adapter, or the powered local codec.

Consequently, the separate 3-adic innovation, root/affine programs, character and frame/valuation program IDs do not accelerate those public temporal dependencies. The unused bundle itself constructs an empty character tuple and neutral residual class: wiring that bundle into a key alone would not implement the missing branch-dependent behavior.

Direct public character observations and explicit frame/germ APIs do use their own bounded laws. They must not be described as globally unused. The disconnect concerns powered point/width execution.

**Needed work:** extract executable bounded observations into the existing scheduler/interface owner, with exact physical/event/frame semantics. Avoid a second application backend or treating a finite 3-adic residue as an exact future tail.

### 4. A narrow Collatz admission gate forces avoidable spatial descent

[`_primitive_parent_payload`](../../../src/number_compiler/hashlife/execution/tile_causal_interface_step.py:40) admits reverse pair, digit normalization, and symbolic division effects, but excludes physical Collatz because its occurrence weight is not always zero.

The physical odd-event distinction is determined at the low-boundary leaf in the primitive law. Recovering it through general child descent misses a narrower opportunity: a certified low-edge/parity occurrence summary, or a bounded left-spine observation, composed with the existing parent transfer.

**Fix gate:** admit the physical parent only with correct event/tick metadata. Do not make the event zero or sum an entire future word to enable the shortcut. Test even starts, noninitial contracts, and partial/cycle events.

### 5. Closed division is gated off for the common small radices

[`_division_effect`](../../../src/number_compiler/projection/tile_radix.py:57) creates `FiniteBlockEffect` for radices 2–256 and `SymbolicBinaryDivisionEffect` above 256. Closed arithmetic leaf/parent composition is selected only for the symbolic effect. The primitive-parent shortcut in finding 4 likewise admits only that symbolic division type.

Thus radix 3/6/12 uses generic Boolean function compilation and misses the closed arithmetic route already implemented for the same division law at larger radices.

**Concrete integration fix:** issue a common immutable division certificate/semantic admission predicate for both representations, then use the closed remainder/activity functions. Never infer arithmetic identity from a kernel name or admit arbitrary finite effects. Compare exact output and operation counts at the 256/257 boundary and for 3/6/12.

### 6. Public radix observations miss completed-stage reuse and pay width first

[`TileRadixObservation`](../../../src/number_compiler/projection/tile_radix.py:323) builds an application for `source_action` followed by `D**(index+1)` and observes its interface. These applications deliberately have no complete root. They share action/interface subgraphs but cannot consume an earlier completed quotient tile.

`TileRadixProjection` implements completed quotient-stage consumption, but it is not the public scalar route. For isolated points, forcing all stages would be a regression. For adjacent/dense output, use completed stages where available or an executable division-consumer behavior transition through the same scheduler.

[`collatz_radix_digit`](../../../src/number_compiler/projection/lazy_radix.py:298) calls exact `term.width()` before most scalar radix observations; projection also checks width. This adds a complete width dependency even for a low requested digit. Use the existing conservative extent bound plus division activity to decide validity, preserving exact out-of-range behavior. Width itself remains exact when requested.

Current repeat-digit tests can succeed through a microblock hit. They are not evidence of core parent/stage reuse with acceleration disabled.

### 7. Certified symmetry is stored but not used to normalize complete requests

Kernel admission exposes `CertifiedLocalSymmetry`, but the public causal scheduler does not call the adapter's `local_symmetry` to canonicalize action, both contracts, boundary operands, direction and wiring together. Runtime mirroring instead builds/caches exact mirrored tile content.

**Missing connection:** complete certified request/result normalization, with inverse transformation of output and metadata. Distinct exact mirrored contents retain distinct TileIDs. The existing mirror/conjugacy subgroup must not be labeled full D4; additional transformations require complete certificates.

This is separate from hash collisions. No finding here demonstrates accidental TileID hash collision or inadequate integer fingerprint width.

### 8. Fermat/Mersenne digit paths are fast; theorem support extraction is incomplete

[`FermatTermPayload.digit`](../../../src/number_compiler/api/number_api.py:203) is a sparse-coordinate test; [`MersenneTermPayload.digit`](../../../src/number_compiler/api/number_api.py:222) returns one inside the validated extent. Source compilation uses sparse/run geometry. These paths should not be replaced with a temporal HashLife engine.

The separate theorem/primality path builds a germ plan with unconstrained support. [`special_frobenius_chunk_probe`](../../../src/number_compiler/sequences/power_numbers/frobenius_chunk.py:510) explicitly returns `UNKNOWN` because the candidate-derived zero-class extractor is unavailable. Terminal/certificate queries can therefore call [`classical_ceiling.py`](../../../src/number_compiler/sequences/power_numbers/classical_ceiling.py:65): Fermat performs `2**n - 1` modular squarings; Mersenne performs `p - 2` modular squarings. These are not ordinary digit queries.

This is an incomplete extractor/consumer obligation, not a ready proven optimization disabled by a flag. Existing tests reject nonclosed or injective cyclotomic, carry, Hensel and phase-history candidates. Keep that negative evidence; memoizing the unconstrained plan cannot decide its terminal defect.

Repeated identical theorem requests could reuse immutable certified artifacts where policy permits, while preserving explicit independent cold construction. That avoids repetition but does not change the cold classical algorithm.

### 9. Special proof aggregation repeats immutable construction across workers

[`special_successor_generators`](../../../devtools/experiments/power_numbers/special_successor_generators.py:247) launches four isolated workers. Hensel, temporal, and phase groups request overlapping carrier/square-field proof inputs. Their process-local caches cannot share those artifacts. The frozen aggregate is reused by later assertions in the test process only after the initial build.

**Optimization:** reuse the existing immutable artifact mechanism for complete recipe-keyed upstream carrier tables/DAGs; bind fresh analysis objects in each worker. Preserve explicitly cold builders, process-isolation assertions and all exhaustive comparisons. Sharing immutable inputs is different from caching the derived operation under test.

The normal serial pytest test order does not imply serial work inside this test: it explicitly launches four processes. This measurement stayed below the memory guard; it does not reproduce the earlier multi-GB incident.

`binary_jump`, `source_program`, and `power_monoid` in `sequences/power_numbers` have test/devtool consumers, not other production-package consumers. They are proof-ownership cleanup candidates after import/test migration, not dormant public accelerators. Do not delete their unique proof assertions.

## Measurements and evidence limits

| Run | Result | Pytest duration | Guard elapsed | Aggregate peak |
|---|---|---:|---:|---:|
| All `tests/sequences/power_numbers` | 57 passed | 1.22 s | 1.599 s | 77,021,736 bytes |
| Cold successor-generator aggregate | 1 passed | 11.16 s | 11.497 s | 466,536,896 bytes |

The aggregate's test-call phase was 10.6994 seconds. The slowest normal family test was the exhaustive cost-one source grammar at 0.37 seconds; compiler integration was 0.27 seconds. Logs, guard reports and complete phase traces are saved alongside this report. These are single-run diagnostic measurements, not five-trial scaling or release evidence.

Prior preserved cold reverse evidence in [the cleanup checkpoint](../carry-domain-cleanup-2026-09-09/README.md) shows N32→N64 causal frames 47,962→176,753 (3.69×), concatenation frames 19,808→87,853 (4.44×), and time 4.424→16.597 seconds. Those observations corroborate repeated causal work; they were not rerun in this audit and are not a universal asymptotic proof.

No full suite was rerun. The under-300-second release gate remains unpassed. Static disconnects above have exact call/admission evidence; their individual performance benefit still requires controlled before/after measurements.

## Focused next gates

1. Close the certified small-radix arithmetic admission gap and Collatz low-boundary occurrence summary; measure primitive-parent hits, descents and reduction work.
2. Make active reverse carry-consumer transitions executable before exact boundary construction; include sector forcing and component-specific Frobenius death in those transitions. Retain exact output distinctions.
3. Integrate complete certified symmetry normalization and persistent active/fused observations in the current stores.
4. Measure public Collatz/radix with microblocks and response registers disabled; distinguish interface hits, exact stage hits and width work.
5. Optimize immutable special proof inputs separately from theorem extraction. Keep ordinary Fermat/Mersenne output paths unchanged.

For every probe, separate compiler plan construction from successful dependency discharge. Report primitive decisions, causal/concat frames, exact boundary evaluations, behavioral discharge, parent hits, classification/reduction work, cumulative allocations and peaks. A high leaf alias rate or an attached Frobenius/3-adic record does not demonstrate avoided temporal work.
