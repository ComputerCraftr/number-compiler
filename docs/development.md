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
Maintained executable reproductions live under `devtools`; reviewed weekly records live under `docs/sprints`. New raw evidence goes to ignored `results/runs`; old local logs and scripts remain historical evidence, not maintained launchers. Repository-wide Ruff checks include every remaining authored Python file. There are no mypy error exclusions or inline mypy/Ruff suppressions
in the maintained roots.

Development minimums are pytest 9.1.1, mypy 2.3.1, Ruff 0.16.7 and setuptools
84.0.0, checked against PyPI on September 14, 2026. Runtime installation remains
dependency-free and supports Python 3.11 and newer.

## Executable source policy

The policy owner is [`repository_policy.py`](../devtools/checks/repository_policy.py),
with regression gates in [`test_repository_policy.py`](../tests/repository/test_repository_policy.py)
and [`test_python_clones.py`](../tests/repository/test_python_clones.py). Run
`python -m devtools.checks.repository_policy` for machine-readable violations;
`pytest tests/repository/test_repository_policy.py tests/repository/test_python_clones.py`
checks both the implementation and the actual repository. The quality release
suite runs the same owner and fails on any violation.

- Python implementations/stubs, Isabelle theories/ML and ROOT/ROOTS sources have
  a 1,000-physical-line cap. Generated results and external environments remain
  outside authored source; tests and developer tools are included. Names such as
  `build`, `dist` and `venv` inside authored packages do not exempt those modules.
- The static call graph rejects resolved direct/mutual recursion, including
  local/module/captured callable aliases, async functions, methods and lambdas.
  Comprehension, exception, match and enclosing scopes remain distinct. Calls in
  nested definition defaults/decorators belong to their executing outer function.
  Conditional aliases conservatively retain both branches; sequential assignment
  analysis is not flow-sensitive. This is not a proof about arbitrary dynamic
  dispatch, deep attribute chains, `super()` or generated Python.
- [`python_clones.py`](../devtools/checks/python_clones.py) rejects substantial
  alpha-equivalent bodies and statement blocks: at least 24 expression/statement
  nodes and either three executable statements or one statement containing at
  least three arithmetic, Boolean, comparison, conditional or comprehension
  operations. Large literal tables and thin forwarding calls alone do not qualify.
  It checks complete suites and contiguous three-statement windows, including
  distinct same-line fragments and substantial lambda bodies. Bound local names
  and captured closure bindings are
  normalized; argument positions, binding relationships, literals, operators,
  external names and attribute names remain significant. Comments and docstrings
  cannot conceal copies. Hash matches require exact canonical-token equality.

This is a structural clone policy, not an arbitrary algorithm-equivalence prover.
There is no duplicate-code baseline, path allowlist or suppression mechanism.
Independent oracle implementations must not be casually replaced by production
calls merely to clear a finding; preserve independent coverage when resolving
the reported duplication. The JSON report includes each location and the exact
thresholds. Existing violations keep the command and repository test red.

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

## Reproducible release commands

Use `python -m devtools.checks.release --suite SUITE --output-dir PATH`, choosing `quality`, `unit`, `proofs`, `p0` or `all`. Each run creates fresh guarded evidence with fingerprint version 5. For example:

```sh
python -m devtools.checks.release --suite quality --output-dir results/runs/quality-review
python -m devtools.checks.release --suite unit --output-dir results/runs/unit-review
```

The command preserves the existing unit, P0, proof and quality selections and their resource guards. Failure evidence remains a failure; a historical baseline comparison is separate from acceptance. Developer code uses `devtools.paths.isabelle_root()` to locate the canonical `proofs/isabelle/` tree.

Runtime release checks live with their actual family under `tests/sequences/`,
shared runtime checks under `tests/hashlife/` or `tests/validation/runtime/`,
and compiler-facing checks under `tests/api/`. Expensive runtime checks retain
`validation` membership. A runtime assertion is not a proof merely because it
was historically stored under `tests/validation/proofs/`.
[`release.P0`](../devtools/checks/release.py) is the canonical explicit selection;
moving a test requires preserving its selected instances and recording its old
and new node IDs. Shared publication/replay assertions live in
[`source_image_assertions.py`](../tests/support/source_image_assertions.py).

The cross-family source-image benchmark is
`python -m devtools.benchmarks.source_image_runtime_audit`. It checks exact
outputs, replay and accounting; its name does not claim a bisimulation proof.
The Collatz C4 reference executor is developer-only and remains forbidden on
production import paths.

Scaffold a Sunday-start topic with `python -m devtools.checks.sprint_scaffold --week-start YYYY-MM-DD --topic TOPIC --title TITLE`. The tool registers the topic and regenerates weekly topic links/counts without replacing authored topic content. Run it again with `--check` to verify generated navigation.

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

These controls contain the memory incident recorded in the [September 7–13 retrospective sprint](sprints/history/2026-09-07--2026-09-13/README.md); they do not make the
affected wide-port decision-DAG algorithm acceptable. Large failing probes stay
paused until the construction path is bounded. Guard failures are incomplete
evidence, and application allocation budgets remain independently enforced.

Use `python -m devtools.checks.package_release --output-dir results/runs/package-review` for a clean staged wheel build and installed-distribution verification. The tool stages current source in a fresh directory, builds the wheel in isolation, and exercises the installed CLI and kernel admission outside the checkout. Package identity comes from current project metadata; stale local build products cannot supply deleted modules.

Canonical probe entry points accept `--output-dir PATH`. Choose a fresh directory for every invocation; an existing directory is rejected. Without this option, a unique timestamp/UUID directory is allocated under `results/runs/`. Reports share the invocation's directory and `manifest.json`, which records command, tool versions, metrics schema, limits, source fingerprints before/after, and completion outcome. An unguarded probe records that limits were not enforced. Interrupted or source-changed work remains diagnostic. Raw JSON, logs and profiles stay local; summarize scoped conclusions in the reviewed sprint topic.

For configurable current public-route comparisons, use `python -m devtools.benchmarks.public_query_comparison --family collatz --horizons 16 32 64 --trials 5 --modes cold warm bypass --bases 2 10 --output-dir results/runs/public-query-review`. The report retains warm priming and all CLI/point samples; it measures route agreement and states its timing scope without introducing a release threshold.

New evidence uses fingerprint version 5: project configuration plus authored files and assets under `src`, `tests`, `devtools`, and `proofs`, excluding tool caches and generated distribution metadata. Historical fingerprints are unchanged.

Summarize new benchmark evidence in the appropriate topic file under
`docs/sprints/week-of-YYYY-MM-DD/`, using the **Sunday** start date.
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
  categories; register new categories in the catalog; `docs/sprints/` accepts new topic files
  without `.gitignore` exceptions.
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
by Git. Commit reviewed weekly Markdown summaries under `docs/sprints/`; keep executable reproductions under `devtools` and independent oracles under `tests/support`;
keep console transcripts, JUnit XML, result JSON, profiles and caches out of
source control. Historical raw artifacts were removed during the September 11
cleanup. Paths in retained summaries describe local outputs, and their recorded
passes do not certify the current source. Generate and validate fresh evidence
before a release; the evidence requirements above remain unchanged. See the artifact retention policy below.

For an interrupted-suite diagnostic, add
`-p devtools.benchmarks.pytest_timing --timing-output /tmp/NEW-phases.jsonl`
to a guarded pytest command. The file is created exclusively and flushed after
collection and each setup/call/teardown record, with a 32,768-record/8 MiB cap. A missing finish
record means the run was interrupted; a truncation record invalidates complete
coverage claims. Use this trace to locate expensive tests, then time the default
serial release command without the plugin. The plugin caches no test runtime or
proof result.

## Artifact retention policy

Generated test logs, JUnit XML, JSON measurements, guard reports, profiles,
databases and other run payloads are ignored here. They belong in local run
directories or CI artifact storage, not in Git. The September 11 cleanup removed
these files from the working tree; it did not rewrite existing Git history.

Reviewed Sunday-start `docs/sprints/week-of-YYYY-MM-DD/` indexes and topic files,
and cross-week retrospectives under `docs/sprints/history/`, are versioned.
All payloads beneath `results/` are local or CI artifacts. See the [sprint index](index.md#sprint-history-and-provenance).
Run-local Markdown reports and Python scripts are ignored
alongside JSON, logs and profiles; there are no extension-wide exceptions.
Already tracked artifacts must be explicitly untracked because `.gitignore`
does not remove them from Git's index. Reproduction tools live under `devtools`, and bounded independent test oracles under `tests/support`.
Historical summaries record what a particular run observed. Their raw artifact
paths describe local outputs and are not downloadable evidence in this checkout.
Historical fingerprints and reported passes do not certify a later source tree.

Generate fresh evidence with canonical `devtools` commands. Historical checkpoint launchers have been retired; their recorded commands describe those historical runs only. Comparisons may require a separately measured baseline. Use a fresh run directory and preserve it locally
while reviewing a result. Keep concise conclusions, commands, limitations and
source fingerprints in reviewed summaries; do not paste console transcripts.

This retention policy does not change release gates. Full release evidence must
still be generated and checked against the current source, using the existing
process guard and test-run evidence checks. A summary alone cannot satisfy those
checks. See [development guidance](development.md).

Fixtures and required kernel assets belong beside their source owners outside
this output directory. JSON and XML are not globally ignored: legitimate inputs
remain reviewable.
