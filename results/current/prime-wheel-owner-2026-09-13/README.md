# Recursive-wheel owner evidence — September 13

[Owner audit and production-path distinction](../../../docs/prime-clock-owner-audit-2026-09-13.md).

The canonical implementation is unchanged. This follow-up adds a regression
gate and corrects the current release description of the fixed-wheel result.

- `wheel-tests.log/json`: 10 focused wheel tests pass, including the new
  eleven-stage gate with parent-gap constructors poisoned; 2.02 s guard,
  38 MB sampled peak.
- `policy-tests.log/json`: 32 repository-policy tests pass; 7.62 s guard,
  486 MB peak.
- Strict mypy on the new test, Ruff and `git diff --check` pass.
- `owner-count.log/json`: the actual production count owner returns 152,840
  for the million-bound query, using 1,240 cold local DAG states and an empty
  stack at return. Direct coprimality checks every prefix through 10,000;
  six prefix rank/select comparisons also pass.
- `batch-count.log/json`: profiling that complete documented batch finds
  140,747 distinct `(depth,limit)` keys, 3,024,608 total state evaluations and
  10,027 retained whole-query answers. These are different quantities from
  the cold count's 1,240 states. The cited 120,146 is not reproduced without
  its original batch/caching schedule.

The `*-probe.py.txt` files preserve the exact measurement scripts. They inspect
the canonical function's local memo at return using `sys.setprofile`; they do
not implement another recurrence. Run either as a Python script through
`devtools/checks/process_guard.py --timeout 35 --memory-mib 1024` with separate
`--output` and `--report` paths. Profiling overhead is included in their times.
The probes have six prefix selects; the regression gate additionally tests
far selects and a periodic boundary, so their work counts are not interchangeable.

An independent audit traced `prime --nth` to `nth_prime_at_or_after` and the
finite divisor-lane compiler. A bounded poison probe confirmed that this CLI
path does not call the recursive wheel index. No CLI route, source-discovery
assumption, primality fallback, or existing release assertion was changed.
