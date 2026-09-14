# Development

Install the project and development dependencies with `python -m pip install -e '.[dev]'`.
Use the environment's tools from the repository root:

```bash
ruff format .
ruff format --check .
ruff check .
mypy
mypy --no-incremental
python -m devtools.checks.repository_policy
pytest
```

Strict mypy checks the configured maintained roots `src`, `tests`, and `devtools`.
Historical reproduction scripts under `results` are run artifacts, not one Python
package (several share module names); they remain included in repository-wide
Ruff checks. There are no mypy error exclusions or inline mypy/Ruff suppressions
in the maintained roots.

Development minimums are pytest 9.1.1, mypy 2.3.1, Ruff 0.16.7 and setuptools
84.0.0, checked against PyPI on September 14, 2026. Runtime installation remains
dependency-free and supports Python 3.11 and newer.

## Unit and exhaustive validation suites

The default `pytest` command runs the unit suite. Exhaustive proof construction,
research sweeps and end-to-end release workloads run separately:

```bash
pytest                         # unit suite; target below five minutes, serial
pytest -m validation           # exhaustive and release validation
pytest -m ''                   # both suites, including every release blocker
pytest -m validation tests/sequences/reverse_add  # focused validation
```

The validation directory contains independent proofs and research experiments.
Long integration workloads beside their subsystem tests carry the `validation`
marker. Small correctness, ownership, budget, identity and poison-route regressions
remain in the unit suite. Classification changes selection, not test assertions,
fixtures, parameter values, watchdogs or runtime budgets. New long workloads must
declare their validation role; a failing unit test is not moved merely to hide it.

JUnit evidence records `serial-unit`, `serial-validation`, `serial-selected` or
`serial-unfiltered` and the selected test manifest. A unit or validation pass cannot
satisfy the complete release-evidence validator. The full HashLife release remains
subject to its separate correctness, scaling and five-minute full-suite gates.

Mypy checks retained authored Python in production, tests and developer tools.
`src` is the explicit production import base; regular package initializers give
developer modules unique identities. No shell `MYPYPATH`, `PYTHONPATH` or runtime
`sys.path` modification is required. Invoke developer tools with `python -m` and
their canonical module name, not by executing a file path.

Only generated build products, external environments and tool caches are outside
authored-source checks. All authored Python shares the 1,000-line limit and the
prohibition on direct or mutual recursion. Formatting is not compressed to evade
that limit.

Historical evidence keeps its original fingerprint. New passing evidence uses
the versioned authored-source fingerprint and a fresh unfiltered serial run.
An interrupted run or one whose sources changed is diagnostic, not release evidence.

## Resource-controlled diagnostics

During the tile cutover, run expensive checks and probes through the shared
watchdog, one worker group at a time:

```bash
python -m devtools.checks.process_guard \
  --output /tmp/probe-001.log --report /tmp/probe-001.json \
  -- python -m pytest tests/repository/test_process_guard.py -q
```

Use fresh output paths. The defaults are a 35-second probe deadline, a 1 GiB
sampled group-footprint limit and an 8 MiB retained log. A full serial release
run uses `--timeout 300`; do not raise gates to accommodate slow execution.
Use `python -m pytest` for the unit gate and `python -m pytest -m ''` for the full
release gate. Explicit validation may be diagnosed in bounded subsystem runs;
those partial runs must not be reported as complete release evidence.
Memory sampling is not a hard allocation cap and can miss peaks between
samples. macOS measurement uses `proc_pid_rusage` physical footprint, because
RSS alone omits compressed/swapped memory. Linux uses RSS plus swap, with that
different measurement explicitly identified in the report.
Summing Linux RSS may count shared resident pages more than once. Missing memory
samples are reported as unavailable, never zero-byte peak evidence. Output is
drained through a bounded pipe and the log never exceeds its cap; reported
output bytes count bytes observed before the writer is stopped.

The guard owns and cleans up its process group, including surviving children
after the leader exits. Diagnostic children must not detach into new groups.
This is supervision of cooperative developer commands, not a sandbox capable
of preventing `setsid`/`setpgid` escapes. Detached or externally killed workers
require a separate process audit. A leader that leaves live group members is
reported as `descendants_retired`, not a successfully completed command.
No user-space watchdog can guarantee cleanup if the watchdog itself is killed
with SIGKILL or the machine stops; check for survivors in those cases. A tool
returning a running session is a yield, not a timeout. Keep tracking that
session to completion, or terminate the guard so its cleanup runs.

These controls contain the [recorded memory
incident](../results/current/memory-incident-2026-09-08.md); they do not make the
affected wide-port decision-DAG algorithm acceptable. Large failing probes stay
paused until the construction path is bounded. Guard failures are incomplete
evidence, and application allocation budgets remain independently enforced.

Remove generated `build/` and `src/*.egg-info` directories before building a wheel; otherwise setuptools can preserve deleted modules from a previous build. The installed-distribution check compares every package file and resource with the current source, then exercises the installed package outside the checkout.

Build a wheel with `python -m pip wheel --no-deps --wheel-dir /tmp/number-compiler-wheels .`, then run `python -m devtools.checks.installed_distribution /tmp/number-compiler-wheels/number_compiler-0.59.9-py3-none-any.whl`. This check installs into a disposable environment and exercises the CLI and kernel admission outside the checkout.

New evidence uses fingerprint version 4: project configuration plus authored files and assets under `src`, `tests`, and `devtools`, excluding tool caches and generated distribution metadata. Historical fingerprints are unchanged.

New benchmark narratives use `devtools.paths.report_output` under `results/current/`, grouped by canonical developer module. They do not overwrite archived checkpoints or create Markdown in source directories.

Generated run payloads under `results/` are local or CI artifacts and are ignored
by Git. Commit only reviewed Markdown summaries and reproduction scripts there;
keep console transcripts, JUnit XML, result JSON, profiles and caches out of
source control. Historical raw artifacts were removed during the September 11
cleanup. Paths in retained summaries describe local outputs, and their recorded
passes do not certify the current source. Generate and validate fresh evidence
before a release; the evidence requirements above remain unchanged. See the
[artifact retention policy](../results/README.md).

For an interrupted-suite diagnostic, add
`-p devtools.benchmarks.pytest_timing --timing-output /tmp/NEW-phases.jsonl`
to a guarded pytest command. The file is created exclusively and flushed after
each setup/call/teardown record, with a 32,768-record/8 MiB cap. A missing finish
record means the run was interrupted; a truncation record invalidates complete
coverage claims. Use this trace to locate expensive tests, then time the default
serial release command without the plugin. The plugin caches no test runtime or
proof result.
