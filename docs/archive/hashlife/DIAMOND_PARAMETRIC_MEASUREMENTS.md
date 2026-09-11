# Frozen direct parametric diamond measurements

The v1 candidate **does not pass the requested performance release gate**. Reverse/add fails to complete every temporal cold-point case at N=16..256 within the fixed limits. Collatz completes the N=16 cold point, but its subsequent width query times out; higher powers time out or exceed the cache budget. Passing audits of the retained objects after these attempts does not establish completed N=256 point or width acceptance.

The raw evidence is reverse v1 (local artifact: `../../../results/diamond_parametric_reverse_v1.json`) and Collatz v1 (local artifact: `../../../results/diamond_parametric_collatz_v1.json`). The separate merged analysis (local artifact: `../../../results/diamond_parametric_analysis_v1.json`) assesses each reported work counter, retained-resource unit, role inventory, and workspace peak. It preserves failed observations as unavailable and retains attempted work separately.

## Execution and measurement method

Each of the 22 cases runs in a fresh process with a fresh `ResourceLedger(max_cache_entries=180_000)`. The entry cap counts retained ledger slots; it is not a byte or node cap. Every measured phase has a fixed 35-second wall-clock watchdog. Each inventory audit receives its own 35-second watchdog after the query timer stops. The outer worker timeout is 500 seconds. Neither the cap nor watchdog increases for larger cases.

The temporal series uses N=16,32,64,128,256:

- Reverse/add starts from decimal 196. For positive N, `DiamondReverseApplication` constructs the immutable initial pair field from the original three seed digits, compiles the reverse-pair power and terminal digit normalization, and uses extent `3+N`. This is the opt-in candidate; these measurements do not assert a public-family routing change.
- Collatz starts from the fixed 513-bit integer `(1 << 513) - 1`. N counts physical steps: even values halve, odd values become `3*n+1`. Original bits enter `SourceGeometry`; the compiler uses the verified physical-four-step kernel and the actual temporal DAG. Extent is `513+N+8`, hence 537,553,585,649,777. The input width stays fixed while N changes.

The spatial series fixes N=4 and varies original source width over 16,32,64,128,256,512. Collatz uses `(1 << width)-1`, with extent `width+12`. Reverse uses the decimal string whose digit at index i is `1+(7*i)%9`, with extent `width+4`. These are specific source families, not a worst-case bound over every word of a given width.

Each case performs construction, cold point 0, immediate repeat of point 0, adjacent point 1, revisit of point 0, then active width. All queries call `parametric_point` or `parametric_width` directly. There is no point-response register, cycle shortcut, or sequential-generation adapter in this measured route. Later phases are skipped after the first execution failure. A scalar oracle runs only after all measured production phases and checks each completed observation; its values do not feed the candidate.

All 22 cases have the same source fingerprint, unchanged before and after each case:

```text
c068ef4dc00c29d91b73f0c208c501b821eaf580534b462eb3ec18d943fccd73
```

The fingerprint covers source Python files, kernel artifacts, and the profiler. It does not cover this report or the separately added postprocessor. The analysis records SHA-256 hashes of its raw JSON inputs. Families were profiled sequentially. Wall times are observations from this machine, not a hardware-independent performance claim; raw rows also record process CPU time.

## Temporal cold-point results

Seconds, retained slots, nodes, work, and RSS on a failed row describe the **attempt up to failure**, not a completed query. A failed result is unavailable. All construction phases completed. Their retained slots were 56,66,76,86,96 for reverse and 182,188,194,200,206 for Collatz; these small construction counts do not describe execution cost.

| Family | N | Cold point 0 | Seconds | Retained slots | Retained nodes | Scheduler transitions | Process peak MiB |
|---|---:|---|---:|---:|---:|---:|---:|
| Reverse | 16 | Timeout; result unavailable | 35.005 | 48,082 | 23,421 | 479,013 | 79.2 |
| Reverse | 32 | Timeout; result unavailable | 35.005 | 92,500 | 45,188 | 647,504 | 93.2 |
| Reverse | 64 | Budget rejection; result unavailable | 3.357 | 180,000 | 89,419 | 5,499 | 103.3 |
| Reverse | 128 | Budget rejection; result unavailable | 2.355 | 142,223 | 70,803 | 4,407 | 101.3 |
| Reverse | 256 | Budget rejection; result unavailable | 2.463 | 150,341 | 74,860 | 4,430 | 106.2 |
| Collatz | 16 | Completed, exact | 2.812 | 6,412 | 2,901 | 87,462 | 49.2 |
| Collatz | 32 | Timeout; result unavailable | 35.004 | 19,957 | 9,299 | 1,499,852 | 50.7 |
| Collatz | 64 | Timeout; result unavailable | 35.003 | 24,240 | 11,420 | 1,579,220 | 51.4 |
| Collatz | 128 | Timeout; result unavailable | 35.005 | 50,412 | 24,281 | 1,532,086 | 56.6 |
| Collatz | 256 | Budget rejection; result unavailable | 2.720 | 147,268 | 72,904 | 4,379 | 87.5 |

The rejected reservations would have raised slot totals to 180,002 / 185,498 / 196,814 for reverse N=64/128/256 and 193,741 for Collatz N=256. Rejection can therefore occur below 180,000 retained slots when an atomic pending publication is larger than the remaining budget. Lower attempted work at a larger N is not a speedup: these cases fail earlier in a different part of execution.

Collatz N=16 subsequently completes repeat, adjacent, and revisit observations, then times out during active width after 35.006 seconds. That failed width attempt leaves 41,321 slots and 19,202 nodes after 1,250,273 scheduler transitions. Its width result is unavailable. Every reverse temporal repeat, adjacent, revisit, and width observation is unavailable because the cold point failed first.

Across both raw profiles there are 82 successful phases, 10 timeouts, 4 budget rejections, and 36 skipped phases. Successful phases include 22 constructions; they are not 82 completed number observations. Eight cases complete all six phases: the six Collatz width cases and reverse width 16 and 32.

## Warm replay is measured separately from retained growth

Collatz N=16 retains no additional slots on an immediate point-0 repeat, yet repeats substantial work:

| Metric | Cold point 0 | Immediate repeat | Point-0 revisit |
|---|---:|---:|---:|
| Seconds | 2.812 | 2.518 | 2.530 |
| Scheduler transitions | 87,462 | 87,179 | 87,179 |
| Finite-port applications | 50,974 | 1,900 | 1,900 |
| Primitive transitions | 2,595 | 46 | 46 |
| Primitive outputs | 1,566 | 37 | 37 |
| Early finite-interface admission hits | 19,610 | 19,661 | 19,661 |
| Early continuation request hits | 2,084 | 2,082 | 2,082 |
| Late expression-interner duplicates | 8,025 | 7,889 | 7,889 |

The adjacent point expands retention from 6,412 to 8,876 slots and from 2,901 to 3,965 nodes. The subsequent revisit retains those totals. Early cache hits, late duplicate discoveries, actual primitive execution, and retained growth are different units: a large hit count or zero new slots does not establish that repeated execution was skipped.

For reverse at N=4, repeat work grows with original width despite zero added slots on that repeat:

| Original width | Repeat seconds | Repeat scheduler transitions | Repeat early interface hits | Cold slots | After adjacent/revisit slots | Active-width outcome |
|---:|---:|---:|---:|---:|---:|---|
| 16 | 0.045 | 773 | 127 | 14,643 | 15,183 | Exact, 4.583 s; 21,515 slots |
| 32 | 0.063 | 1,492 | 270 | 13,550 | 14,031 | Exact, 12.679 s; 27,037 slots |
| 64 | 0.116 | 2,915 | 556 | 13,943 | 14,402 | Timeout; result unavailable |
| 128 | 0.238 | 5,746 | 1,129 | 20,331 | 20,762 | Timeout; result unavailable |
| 256 | 0.389 | 11,393 | 2,279 | 22,651 | 23,063 | Timeout; result unavailable |
| 512 | 0.752 | 22,672 | 4,581 | 24,055 | 24,556 | Timeout; result unavailable |

Every reverse width cold/repeat/adjacent/revisit observation completed exactly. The repeat transition series approximately doubles with width and fails the sampled logarithmic envelope. Each reverse repeat still executes two primitive outputs; each Collatz N=4 repeat executes one. The existing strict zero-primitive-replay gate reports these explicitly as failures, separately from the sampled growth assessment; those scalar terminal emissions alone do not imply a retained output tape.

## Completed Collatz spatial series and source-construction cost

All six fixed-N4 Collatz cases complete. Cold point times are 0.018–0.021 seconds, active-width times 0.041–0.043 seconds, and repeat scheduler transitions are exactly 11 at each width.

| Original width | Cold slots | Final slots | Final nodes | Active-width scheduler transitions |
|---:|---:|---:|---:|---:|
| 16 | 740 | 2,140 | 1,094 | 166 |
| 32 | 741 | 2,144 | 1,096 | 169 |
| 64 | 742 | 2,148 | 1,098 | 172 |
| 128 | 743 | 2,152 | 1,100 | 175 |
| 256 | 744 | 2,156 | 1,102 | 178 |
| 512 | 745 | 2,160 | 1,104 | 181 |

All measured postconstruction counter/resource series for this sample pass the postprocessor's criteria. Original-source construction remains separate: source-leaf interner requests are 18,34,66,130,258,514, and source-parent requests are 20,36,68,132,260,516. Reading/building this supplied input has linear work even though canonical retained geometry is small. The report does not relabel that work as logarithmic.

The postprocessor preserves the original anchored `1.25` log-envelope diagnostic and adds an exact affine-log sample rule: integer cross-products must prove geometric axis spacing, and integer first differences must be identical. Thus the measured unary-composition-hit series 1,2,3,4,5,6 at widths 16..512 passes as `log2(width)-3`; its old anchored diagnostic remains visible as `BLOCKED`. No tolerance was enlarged. Tests retain rejection of linear and quadratic series. Passing finitely many sampled series is not an asymptotic proof.

## Retention, workspace, and materialization

Each phase snapshots the actual ownership inventory after its timer stops. Cache slots count retained mappings/list entries; unique nodes count actual owned records. Scoped references, program syntax, canonical finite functions, source geometry, and spatial request bindings are not interchangeable. Node subsets in the metrics must not be added again to the complete node partition.

For example, the failed reverse N=16 cold attempt retains 10,378 boundary-expression nodes, 11,610 canonical-transfer nodes, 214 closure programs, 55 higher-context records, and 104 higher-unary records. The completed Collatz N=16 cold point retains 1,277 boundary-expression nodes, 1,376 canonical-transfer nodes, 37 closure programs, 9 higher-context records, and 19 higher-unary records. These program records are not asserted to be fully reduced extensional equivalence classes.

Workspace fields report actual high-water counts in their own units. Reverse N=16 reaches scheduler workspace 169, expression rewrite-result slots 343, and substitution state-input slots 3,358 before timeout. Collatz N=16 cold point reaches scheduler workspace 128; its failed active-width phase reaches 2,703. These component peaks need not occur simultaneously and are not added into invented bytes. RSS is fresh-worker lifetime peak memory, including earlier audits and interpreter overhead. It is not a ledger-owned-byte count, and audit time is excluded from query times.

Every executed-phase audit completed with `representation_boundary_complete=1`. Across these snapshots, `forbidden_future_payloads`, `retained_unbounded_future_integers`, `retained_point_response_scalars`, `exact_endpoint_nodes`, `endpoint_lowering_requests`, and `explicitly_materialized_endpoints` are all zero. Original source storage is deliberately retained and charged. These independently checked retained-state observations support the representation boundary for inspected states; they neither supply missing timeout results nor alone prove the absence of every possible transient violation on an unexecuted path. The independent adversarial tests provide separate boundary evidence.

## Reproduction and historical scope

Run the families sequentially from the repository root. Use new output names to preserve the frozen v1 evidence:

```sh
PYTHONPATH=src /tmp/number-compiler-check-env/bin/python bench/diamond_parametric_profile.py --family collatz --series all --output /tmp/diamond_parametric_collatz_reproduction.json
PYTHONPATH=src /tmp/number-compiler-check-env/bin/python bench/diamond_parametric_profile.py --family reverse --series all --output /tmp/diamond_parametric_reverse_reproduction.json
PYTHONPATH=src /tmp/number-compiler-check-env/bin/python bench/parametric_profile_analysis.py /tmp/diamond_parametric_collatz_reproduction.json /tmp/diamond_parametric_reverse_reproduction.json --output /tmp/diamond_parametric_analysis_reproduction.json
```

`--series temporal` and `--series width` select the two matrices. A single independently timed case can be inspected with `--worker --family collatz --steps 16`, or `--worker --family reverse --steps 4 --width 64`. The fixed limits are defined by the [profiler](bench/diamond_parametric_profile.py); the [postprocessor](bench/parametric_profile_analysis.py) cannot convert failed phases into completed samples.

Historical evidence remains unchanged: v6 lazy-route measurements (local artifact: `../../../results/lazy_resource_audit_v6.json`), [early canonical lookup report](../repository-and-algebra/EARLY_CANONICAL_LOOKUP.md), earlier fixed-513-bit diamond probe (local artifact: `../../../results/diamond_fixed_513bit_noncycle_profile.json`), and pre-fused-substitution reverse probe (local artifact: `../../../results/diamond_reverse_before_fused_substitution_n16.json`). Those runs differ in route, implementation, instrumentation, or method; their numbers must not be silently substituted into this frozen matrix. Bimachine composition closure and this candidate's measured resource acceptance are separate claims. The available closure argument does not erase the execution failures reported here.
