# Source-bound skew scheduler evidence

**Release blocked.** The integration is partial. This directory distinguishes
actual production execution, arithmetic proofs, resource measurements and
unresolved constructors. No passing finite test establishes an arbitrary-size
construction bound or an all-time non-halting theorem.

The implementation report is
[the current scheduler ledger](../../../docs/skew-scheduler-unification-2026-09-13.md).
`final-freeze.json` pins the authored source; `final-wheel.json` pins its installed
wheel. Each final validation guard records the source before and after execution.
The JSON and logs are generated local evidence, in accordance with the repository
ignore policy; this summary and reproduction scripts are reviewable sources.

## Production paths covered

- Prime term queries enter `PrimePrefixRank.count_prime_interval`, then
  `PrimePartialSuccessorQuery` and the common source-image executor. Its primitive
  applies the fresh-prime parent-minus-deletion operation; interval descent
  consumes that admitted image. The CLI connectivity test disables the retired
  `count_leq` wrapper and checks actual fresh-prime filter applications.
- The complete-period prime descriptor has separately tested lazy phase ports,
  binary action composition and rank/select descent. It is not the ordinary
  prime CLI's finite-interval construction and does not implement a full paired
  Goldbach sieve.
- Antihydra spacetime requests use shared-core section images, then demand
  coefficients from their exact support. The detached fragment cache accepts
  an image handle, not submitted coefficient tuples. Cold demand still visits
  every return; warm reuse is scoped to the same run.
- No 196, Collatz or Fermat/Mersenne adapter is claimed to be migrated to the
  common source-image executor. Their existing production paths and P0 holds
  remain in force.

Prime CLI `--info metrics` now reports `prime_scheduler_work`,
`prime_scheduler_peak_entries` and a `prime_scheduler_counters` object. The scope
is `query_before_disposal`. The older `prime_retained_entries` and
`prime_request_allocations` still count only Phi/progression states and factor
stages; they must not be presented as complete source-image retention. The
scheduler work field is part of aggregate rank work, so summing both would
double-count it. Named core counters expose additional construction, validation
and projection work. This success snapshot does not claim final disposal or
failed-query reporting.

## Proof scope

The fresh build in `prime-isabelle-25.*` checked the new
`Prime_Wheel_Skew_Actions` theory in 16.249 seconds under 35 seconds / 4 GiB. The
final session check also validates that theory against the final source's
Isabelle dependencies. The arithmetic theorems cover progression counting,
fresh-prime half-open intervals, restoration of the known prime prefix,
chronological phase transport, full-cycle phase closure, and the seven-deletion /
eight-survivor implication. In-session assertions check oracle dependencies.

These are not proofs of the Python worklist, scheduler publication/leases,
full rank/select consumer refinement, macro contraction laws, all family
projections, Fermat/Mersenne terminal construction, or the source-7 barrier.
The archive's large symbolic powers and finite Goldbach controls retain their
reported, finite scope.

## Reproduction

Use the project's development Python environment from the repository root.
The baseline wheel paths and hashes, workloads, five-trial requirement and
unchanged budgets are pinned in `acceptance-inputs.json`.

```bash
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py focused
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py wheel
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py prime
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py proof
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py cli
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py unit
python results/current/skew-scheduler-unification-2026-09-13/performance_release_manifest.py NEW_OUTPUT_DIRECTORY
python results/current/skew-scheduler-unification-2026-09-13/run_final_validation.py antihydra-growth
```

Run one guarded process group at a time. Existing logs are intentionally not
overwritten; use a fresh evidence destination for a new run. The growth runner
attempts every unchanged manifest trial even after earlier timeouts. A benchmark
process returning zero does not mean its tolerance comparisons pass: inspect
the recorded comparisons. Missing samples are not assigned zero cost.

Files beginning `pre-` and the diagnostic measurements are superseded evidence,
not current passes. The interrupted growth collection was stopped to repair
missing CLI scheduler accounting; its partial samples do not close the manifest.
The earlier failed latency comparisons and initial incomplete cache admission
checks remain preserved rather than being replaced by passing samples.

## Final frozen validation

The authored source fingerprint is
`95353e85f969895d8c6cc2bc9ab08c9dc7ac48d892bd323e8b798038853d1b24`.
The installed `number_compiler-0.59.9-py3-none-any.whl` has SHA-256
`dc55553371b4dfe3d55a3d183056d81370c551be6dea0e3fabc22d553d52858e`.
Final guards retain matching source fingerprints before and after each check.

| Check | Result |
|---|---|
| Focused semantics, admission, ownership, laziness and CLI tests | 346 passed, 13 deselected; 7.46 seconds |
| Repository policy; typing and Ruff over `src tests devtools` | Pass |
| Wheel construction, isolated inventory and CLI checks | Pass |
| Full ordinary unit selection | 5,205 passed, 4 failed, 1,277 deselected; 229.82 seconds |
| Unchanged explicit P0 selection | 7 passed, 15 failed |
| Five final Isabelle session checks | Pass with cached dependencies; scope described above |
| Whole-tree typing | Blocked by duplicate archived `validation_driver` modules |
| Whole-tree Ruff | Three existing E701 errors in the September 10 measurement archive |

The full-unit process guard measured 230.582 seconds and 703,923,184 bytes,
within 300 seconds / 1 GiB. Its four failures remain the 196 warm-clock probe,
the special-number impossible-sheet resolution assertion, the reverse runtime
class accounting assertion, and the reverse source-publisher cutover assertion.
Their complete node IDs and tracebacks are in `final-full-unit.log`; assertions
and test selections were not relaxed.

The final Isabelle checks cover `Prime_Wheel_Bridge`, `Reverse_Residuals`,
`Temporal_Clock_Jumps`, `Etale_Primary_Carry` and `Antihydra`. Cached session
success does not erase the earlier dependency-inclusive Temporal build timeout
or supply the missing executable refinement theorems.

The cold Collatz comparison exceeded its 35-second guard and supplies no complete
paired latency result. The other general family CLI comparisons preserve their
semantic results. The special-family controls query Fermat index zero and
Mersenne exponent eleven; matching trivial or unresolved results does not
establish the required general classification or factor constructor.

| Fresh-process query | Prior frozen median ms | Candidate median ms | Tolerance result |
|---|---:|---:|---|
| 196, nth 8 | 207.982 | 213.859 | Pass |
| Antihydra, nth 512 with ledger and clock | 73.120 | 75.225 | Pass |
| Fermat, index 0 with primality only | 95.696 | 95.836 | Pass, limited control |
| Mersenne, exponent 11 with factor only | 97.774 | 97.762 | Pass, limited control |

These smaller query controls do not replace the growth manifest or the larger
Antihydra spacetime comparison below.

## Final prime comparisons

All values are paired medians in milliseconds; the unchanged tolerance is
`baseline + max(10% of baseline, 1 ms)`. Each comparison uses five trials.

| Baseline | Mode | Query | Baseline ms | Candidate ms | Tolerance result |
|---|---|---|---:|---:|---|
| current | same-process warm | prime | 16.219 | 2.339 | Pass |
| current | same-process warm | prime-start | 9.764 | 1.709 | Pass |
| current | fresh CLI process | prime | 73.716 | 85.512 | Fail |
| current | fresh CLI process | prime-start | 67.568 | 78.313 | Fail |
| historical | same-process warm | prime | 31.105 | 2.270 | Pass |
| historical | same-process warm | prime-start | 1.403 | 1.687 | Pass |
| historical | fresh CLI process | prime | 99.955 | 86.424 | Pass |
| historical | fresh CLI process | prime-start | 69.143 | 83.509 | Fail |
| last_frozen | same-process warm | prime | 1.153 | 2.323 | Fail |
| last_frozen | same-process warm | prime-start | 1.160 | 1.798 | Pass |
| last_frozen | fresh CLI process | prime | 78.344 | 86.209 | Fail |
| last_frozen | fresh CLI process | prime-start | 71.563 | 79.410 | Fail |

The arithmetic results match throughout. Candidate cache-bypassed samples are
also retained in each warm comparison report. A warm pass against an older
baseline does not close cold construction or the fastest-baseline regression.

## Final installed Antihydra spacetime comparison

The 2,048-return query matches all semantic lanes. Its five-trial paired median is 239.994 ms against 182.367 ms for the pinned prior wheel: **fail** under the same tolerance.
The trace records 256 common-core primitive fragments and 2,048 cold leaf-return
visits. Each CLI query creates a new run. Same-run API retention is a different
measurement and cannot be substituted for this cold CLI result.

## Final growth and retention evidence

`final-growth/report.json` records all **105 attempted fresh-process trials**,
five per unchanged manifest point, on the frozen source. Eighty completed and
25 exceeded the 35-second guard. The requested manifest is complete, but the
measurement collection and release acceptance are **incomplete / RED**.

| Manifest series | Completed trials | Timeouts | Series result |
|---|---:|---:|---|
| Fixed width 16, temporal horizons 16–1,024 | 30 | 5 at horizon 1,024 | RED: missing measurements |
| Fixed depth 16, spatial widths 16–1,024 | 35 | 0 | RED: work and retention growth envelopes fail |
| Growing 196, horizons 16–1,024 | 15 | 20 at horizons 128–1,024 | RED: missing measurements |

The completed spatial series still violates the existing logarithmic increment
envelopes, including causal frames, parent observations, validation visits and
retained entries. Completing a trial under its watchdog is not equivalent to
passing its work/retention gates. Incomplete series retain null envelope results;
null does not mean zero or pass. Per-trial setup, observation, diagnostics, work,
retention, process time and sampled memory are preserved in the report and guards.

The additional `final-antihydra-growth.log` has all **35 API control samples**,
five each at 16–1,024 returns. It completes in 3.787 seconds under its guard,
matches semantic lanes across cold/repeated/cache-bypassed evaluation, and
reconciles ledger retention. Medians below are milliseconds and separate source
construction from observation; they are not installed-CLI latency measurements.

| Returns | Construction | Cold observation | Same-run repeat | Bypassed observation | Retained nodes after cold demand |
|---|---:|---:|---:|---:|---:|
| 16 | 0.122 | 2.284 | 0.069 | 1.551 | 57 |
| 32 | 0.170 | 4.236 | 0.077 | 3.376 | 61 |
| 64 | 0.307 | 8.263 | 0.108 | 7.960 | 69 |
| 128 | 0.534 | 17.883 | 0.205 | 17.653 | 136 |
| 256 | 0.969 | 34.782 | 0.357 | 37.764 | 268 |
| 512 | 1.838 | 70.826 | 0.765 | 86.869 | 531 |
| 1,024 | 3.395 | 141.040 | 1.576 | 200.427 | 1,043 |

At every horizon the repeat constructs zero additional primitive fragments and
visits zero additional leaf returns. Cold evaluation visits exactly the requested
number of returns, with 128 primitive fragments at horizon 1,024. Retained nodes
include the run and support owners, not only detached coefficients. These data
establish bounded same-run reuse and expose linear cold work; they do not close
the required powered-construction or cold CLI gate.
