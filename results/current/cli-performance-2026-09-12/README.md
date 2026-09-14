# CLI performance evidence — September 12

Final validation completed September 13, continuing the September 12 audit.

The [performance report](../../../docs/cli-performance-release-audit-2026-09-12.md)
describes the repairs and remaining obligations. **Release remains blocked.**
No mathematical, performance or accounting assertion, discovery counter, budget
or proof obligation was relaxed.

## Installed CLI comparison

`benchmark-final-a.log/json` and `benchmark-final-b.log/json` compare isolated installed
wheels using three fresh processes per wheel and command. The `.log` files
contain timing samples and semantic comparisons; `.json` files contain the
process guard's time and memory measurements. Normal filesystem caches remain
enabled. These are measurements of the listed finite requests.

| Query | Baseline median | Candidate median |
| --- | ---: | ---: |
| Family list | 0.434 s | 0.075 s |
| 196 N=8, JSON value | 0.519 s | 0.234 s |
| Collatz seed 27, 64 physical iterations, JSON value | 3.874 s | 3.714 s |
| Antihydra 512 returns, value+ledger+clock, JSON | 0.490 s | 0.079 s |
| F0 primality information only, JSON | 0.449 s | 0.103 s |
| M11 factor information only, JSON | 0.453 s | 0.102 s |

Baseline wheel SHA256:
`d0d47c047302b41c397cc6fe52d7cc524e4e98453e9b50aadc024f54a7cd7774`.
Candidate wheel SHA256:
`e64d8f8b944fd1c8de869c853c77eb1093bd45fd2deab030f3bf4a69ece5320f`.

Reproduce with `python -m devtools.benchmarks.cli_startup BASELINE.whl
CANDIDATE.whl --samples 3 --case families --case 196 --case antihydra --case fermat
--case mersenne`, then a second invocation with `--case collatz`. Wrap
each invocation in `devtools/checks/process_guard.py --timeout 35 --memory-mib
1024 --output LOG --report REPORT -- ...`.

The initial six-case batch exceeded the unchanged 35-second guard. Its
`benchmark-timeout` report is retained. Splitting the same requests into two
final batches completed in 14.95 and 30.60 seconds, without raising the watchdog or
changing a query. Isolated environment creation is included in those batch
times but excluded from the per-query medians.

## Component and adversarial evidence

- `admission-final.log/json`: all 265 adversarial input, primitive-table,
  schema, package-contract and startup tests pass after the full-suite findings
  were repaired; 8.28 seconds, 111 MB sampled peak. In particular, rejecting a
  composed action from primitive tables no longer allocates a cache entry.
- `installed-final.log/json`: installed package/source equality, public exports,
  bundled kernels, family-first CLI contracts, UNKNOWN handling and checked M11
  factor output pass; 4.85 seconds, 115 MB sampled peak.
- `schema-startup.log/json`: 66 schema, publisher and startup tests pass;
  4.58 seconds, 110 MB sampled peak. Hostile IDs are rejected before cache
  access, read-only validation does not publish, and primitive/rejected inputs
  allocate nothing. Import poison tests cover actual subprocess CLI dispatch.
- `adversarial-schema-rejections.log/json`: the earlier cache implementation
  failed three allocation tests. The failures were repaired by eliminating
  mutable validation caching and declining to cache absent composition edges;
  the assertions remain unchanged.
- `typing-final.log/json`: strict mypy passes 1,296 files. Ruff and
  `git diff --check` also pass.
- `antihydra-tests.log/json`: 134 focused tests pass, 13 validation cases
  deselected; 1.39 seconds, 56 MB sampled peak. Repeated engine execution has
  distinct charged result owners. Retained section folding constructs at most
  two leaf roofs and releases its workspace, including after budget failures.
- `antihydra-projection.log/json`: N=512 and N=2048 cached/uncached projections
  agree exactly and reconcile accounting. Macro branch rediscovery is zero;
  retained support fold counts are 512 and 2048 respectively. This is an O(N)
  projection fold, not a cheap arbitrary-size source construction.
- `antihydra-projection-final.log/json`: the final N=2048 replay also agrees
  exactly and reconciles accounting. The benchmark field is now explicitly
  named `observer_macro_rediscovery_gate_closed`; it does not declare source
  construction complete. The initial source still discovers 1,280 kernel
  branches and the projection folds 2,048 retained steps.
- `antihydra-warm-final.log/json`: two executions on one engine agree with the
  canonical one-return reference. N=512 takes 2.04 ms cold and 0.49 ms warm;
  the reference using two preconstructed atoms takes 0.56 ms. Thus this finite
  cold construction is not faster than that reference. Warm execution performs
  zero branch discoveries or cylinder compositions, while its eight block
  applications, 512 physical roof terms and separate publication remain charged.
- `antihydra-fold.log/json`: isolated support folding improves 2.77× at N=512
  and 1.88× at N=2048. These ratios do not describe the full spacetime observer.
- `reverse-publisher-schema-profile-0912.txt`: before the final primitive-admission
  repair, the children-only cache reduces a preliminary N=64 point profile from 1.251 to 1.178 seconds CPU (5.8%). Counted
  higher continuations remain 2,851 and concrete operations remain 9,776.
  The faster discarded validation-cache profile is not accepted evidence.
- `collatz-profile.report`: the actual N=64 seed-27 JSON value query spends
  13.649 seconds of its instrumented 14.069-second run in the causal complete
  output engine. It makes 155,095 action-validation calls and 1,423,814 scoped
  handle validations. Duplicate endpoint leaf resolution is immaterial at
  this width. Instrumented time is not comparable to the unprofiled CLI median;
  required authority and liveness checks were not bypassed.

The public-package test's old syntactic ban on `__getattr__` was replaced by
checks that the literal deferred-export table equals the unchanged public
`__all__`, every name resolves to its canonical owner's exact object, and
private, obsolete and unknown names raise `AttributeError`. The resolver has
one fixed dispatch path and no compatibility-name synthesis. Old forwarding
module rejection and the package ownership rules remain unchanged. Poison
fixtures now patch canonical algorithm owners instead of removed eager-import
aliases, preserving their invalid-input and lazy-execution assertions.
Independent review caught the resolver helper itself being exposed on the
facades. Both facades now import it privately; cold-process and package tests
reject the public helper name. The auditor confirmed this repair. An in-flight
full suite was interrupted to freeze and validate that final change; its
`full-unit-interrupted` record is not treated as completion evidence.

The first rebuilt wheel retained a deleted generated helper under `build/lib`.
The installed inventory check rejected it (`installed-stale-build.log/json`).
Removing that generated file and rebuilding produced the verified final wheel.
`source-and-wheel.json` binds it to the final Python/theory hashes and records
the working tree as uncommitted integration, including earlier-turn changes.

## Final serialized release checks

- `full-unit-final.log/json`: **5,002 passed, four failed, 1,277 deselected**;
  265.64 seconds including the guard, peak 638 MB. The unchanged limit is
  300 seconds/1 GiB. The failures match the baseline: the 196 clock-work gate,
  two reverse/add cutover assertions and unresolved special-number output.
  The initial run's additional 31 import-fixture, ownership and allocation
  failures were repaired; they are retained in `full-unit-initial.log/json`.
  Repository structural policy passes in the final suite.
- `release-final.log/json`: **15 failed, seven passed**, 5.59 seconds including
  the guard, peak 92 MB under the unchanged 35-second/1-GiB limit. This selection
  preserves the previous 22 assertions. The Antihydra no-rediscovery assertion
  changes from failing to passing. The remaining failures are its absent
  source-7 certificate, nine special-number assertions and five reverse/add
  assertions. The broader Collatz construction and full projection obligations
  remain separately tracked in the release ledger; these 22 tests are not a
  proof of those missing constructions.

The release selection uses `pytest -q -m ''` on the complete
`test_antihydra_release.py`, `test_shadow_jet_primality_release.py` and
`test_temporal_cutover_reporting.py` files in `tests/validation/proofs`, plus
the existing F4 guarded-output assertion in `test_idempotent_output.py`,
source-publisher assertion in `test_dyadic_hashlife.py`, and cutover assertion
in `test_resource_metric_units.py`. None of these release assertions changed
during this performance audit.

Raw generated logs and source manifests remain local under repository policy.
No Isabelle theory changed in this performance patch; the earlier scoped
arithmetic proofs do not discharge the outstanding production constructor,
complete projection or source-7 non-halting obligations.
