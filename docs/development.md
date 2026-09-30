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
python -m devtools.checks.docs_index
python -m devtools.checks.isabelle_proof_index
pytest
```

Strict mypy checks the configured maintained roots `src`, `tests`, and `devtools`.
Executable reproductions live under `devtools`; `results` contains weekly summaries and ignored raw evidence, with no executable checkpoint launchers. Repository-wide Ruff checks include every remaining authored Python file. There are no mypy error exclusions or inline mypy/Ruff suppressions
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

## Shared audit and arithmetic owners

- Python architecture checks use the AST helpers in
  [`dependency_graph.py`](../devtools/checks/dependency_graph.py). Comments and
  incidental string literals are not evidence of imports or runtime dispatch.
  Literal lazy-export tables and import-loader calls are inspected explicitly;
  aliases retain their original targets, and an unknown dynamic router target
  cannot pass the executor boundary gate.
- The Isabelle inventory uses
  [`isabelle_syntax.py`](../devtools/checks/isabelle_syntax.py) for its supported
  source syntax. This is a conservative navigation reader, not Isabelle's
  elaborated AST or proof checker. Registered sessions come from `ROOT`; builds
  and oracle checks remain required.
- F2 and F5 transports share the radix-exponent decomposition in
  [`affine_transport.py`](../src/number_compiler/arithmetic/polynomials/affine_transport.py).
  Their annihilation, coefficient and coordinate laws remain distinct.
- Dyadic reuse resolves sealed scheduler publications before sharing complete
  effects. Equal integer indices, Boolean/numeric aliases and equal F5
  observations cannot substitute for source/action authority.
- Symbolic F5 result memos retain arena-bound handles and charge exponent
  metadata. Capacity growth evicts memo entries; it does not discard the shared
  expression DAG or authorize a source image.

The unused Collatz target-seam interner and the `RuntimeInputCellID` alias module
were removed. Independent clock-law coverage lives with the inverse-three clock
tests; higher summaries use the existing `SourceCellID` directly. Small shared
helpers with live consumers are retained when merging would introduce circular
imports or mix different semantic contracts.

## Resource-controlled diagnostics

Install the optional sampling profiler with `python -m pip install -e '.[profile]'`.
The development environment uses Pyinstrument 5.1.3; runtime installations
remain dependency-free. Use the standard-library `cProfile`/`pstats` for exact
call counts and `tracemalloc` for focused allocation investigations. Sampling
profiles are useful for hot paths; uninstrumented runs remain the latency
baseline.

```bash
python -m pyinstrument -r speedscope -o /tmp/collatz.speedscope.json \
  -m number_compiler collatz --seed 931386509544713451 --nth 2000
python -m cProfile -o /tmp/collatz.prof \
  -m number_compiler collatz --seed 931386509544713451 --nth 2000
python -m pstats /tmp/collatz.prof
```

Wrap expensive profiling invocations in the watchdog below. Capture successful
output and the unprofiled exit status as well as the profile: `cProfile`'s
module runner can swallow `SystemExit`, so its zero exit status does not prove
the CLI completed the request. The sampling CLI preserves that status in the
checked environment. A fast budget refusal is not a performance improvement.
Use the existing `devtools.benchmarks.pytest_timing` plugin for separate
collection/setup/call/teardown evidence. Never share warmed production caches
between independent tests to improve timings.

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

These controls contain the memory incident recorded in the [September 7–13 retrospective sprint](../results/history/2026-09-07--2026-09-13/README.md); they do not make the
affected wide-port decision-DAG algorithm acceptable. Large failing probes stay
paused until the construction path is bounded. Guard failures are incomplete
evidence, and application allocation budgets remain independently enforced.

Remove generated `build/` and `src/*.egg-info` directories before building a wheel; otherwise setuptools can preserve deleted modules from a previous build. The installed-distribution check compares every package file and resource with the current source, then exercises the installed package outside the checkout.

Build a wheel with `python -m pip wheel --no-deps --wheel-dir /tmp/number-compiler-wheels .`, then run `python -m devtools.checks.installed_distribution /tmp/number-compiler-wheels/number_compiler-0.59.9-py3-none-any.whl`. This check installs into a disposable environment and exercises the CLI and kernel admission outside the checkout.

New evidence uses fingerprint version 4: project configuration plus authored files and assets under `src`, `tests`, and `devtools`, excluding tool caches and generated distribution metadata. Historical fingerprints are unchanged.

Summarize new benchmark evidence in the appropriate topic file under
`results/current/week-of-YYYY-MM-DD/`, using the **Sunday** start date.
Canonical developer modules write raw evidence to fresh local paths; they do
not create another versioned microtask report.

### Documentation placement

- **Research papers:** definitions, propositions, assumptions, proof sketches,
  exact counterexample scope and open constructions. Keep a short production
  connection and a canonical reproduction command. Update the existing account
  when a result changes rather than appending another implementation milestone.
- **Weekly sprints:** dated changes, patch provenance, cache fixes, rejected
  implementations, benchmark tables, validation counts and source fingerprints.
  Weeks run Sunday–Saturday. Keep `README.md` as a short topic index; append
  records to the relevant family or shared-infrastructure file, not the index.
  Give each record its actual date or date range. File cross-week work once in
  its completion week and state the full range. Do not guess missing dates;
  retain undated aggregate history as explicitly labeled retrospectives.
  Preserve original fingerprints and evidence limits. Use the existing topic
  categories; register new categories in the catalog and the narrow Markdown
  allowlist in `.gitignore` when needed.
- **Architecture and API guides:** current module responsibilities, interfaces
  and user-visible behavior. Keep implementation history in the sprint.
- **Release ledger and proof index:** current gate disposition and formal
  statement/assumption/build references, respectively. Neither a historical
  pass nor a documentation edit closes a current construction obligation.

Link a research result to its dated evidence instead of copying the full run
report. A superseded status belongs in history; the maintained paper should
state the current scope once. Keep raw logs local or in CI and externally
supplied archived documents unchanged. Register maintained pages in
`docs/catalog.toml` and run `python -m devtools.checks.docs_index` after moving
sections so local links and heading references remain valid.

Generated run payloads under `results/` are local or CI artifacts and are ignored
by Git. Commit only reviewed weekly Markdown summaries there; keep executable reproductions under `devtools` and independent oracles under `tests/support`;
keep console transcripts, JUnit XML, result JSON, profiles and caches out of
source control. Historical raw artifacts were removed during the September 11
cleanup. Paths in retained summaries describe local outputs, and their recorded
passes do not certify the current source. Generate and validate fresh evidence
before a release; the evidence requirements above remain unchanged. See the
[artifact retention policy](../results/README.md).

For an interrupted-suite diagnostic, add
`-p devtools.benchmarks.pytest_timing --timing-output /tmp/NEW-phases.jsonl`
to a guarded pytest command. The file is created exclusively and flushed after
collection and each setup/call/teardown record, with a 32,768-record/8 MiB cap. A missing finish
record means the run was interrupted; a truncation record invalidates complete
coverage claims. Use this trace to locate expensive tests, then time the default
serial release command without the plugin. The plugin caches no test runtime or
proof result.
