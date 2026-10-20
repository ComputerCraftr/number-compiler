# Development

Create a virtual environment in `.venv` and install the exact development tools
from `pyproject.toml`. The reproducible validation environment targets CPython
3.14 on macOS arm64:

```bash
.venv/bin/python -m pip install -c devtools/typing/constraints-py314-macos.txt -e '.[dev,profile]'
npm ci --prefix devtools/typing --ignore-scripts
.venv/bin/python -m pip check
```

The constraints file includes transitive dependencies; it is generated from a
clean resolution of the declared extras. Other validation platforms need their
own clean resolution. The package still supports Python 3.11 and newer, checked
separately by installing the wheel with the minimum interpreter. The existing
installed-distribution checker accepts `--python-executable /path/to/python3.11`
for that smoke check; it remains subject to the normal command guard.

Use the environment's tools from the repository root:

```bash
ruff format .
python -m devtools.checks.release --suite quality
python -m devtools.checks.repository_policy
python -m devtools.checks.docs_index
python -m devtools.checks.isabelle_proof_index
python -m devtools.checks.release --suite unit
```

Strict mypy and strict Pyright check `src`, `tests`, and `devtools`.
The quality runner invokes the repository-private Pyright installation in
serial, deterministic batches of at most 25 authored files, including
nonignored untracked sources. Each batch has the standard command guard and a
2-GiB Node heap; incomplete output or a failed batch fails the gate. Imported
modules remain analyzed. Put Node on PATH or set `NUMBER_COMPILER_NODE` to its
executable. No global or ephemeral `npx` installation is used. The quality preflight checks
every locked Python package and runs `pip check`. Acceptance installs the private
npm lock before analysis; put npm on PATH or set `NUMBER_COMPILER_NPM` to its
JavaScript CLI entrypoint. Shell wrappers are not used by the runner.

VS Code uses `.venv`, strict Pylance and open-file background diagnostics to
limit editor memory. The workspace recommends the Python, Pylance and Ruff
extensions; Ruff uses the selected environment so its version matches the
project's pinned development dependency. After creating `.venv` and installing
the project in editable mode, select `.venv/bin/python` with **Python: Select
Interpreter** if VS Code retained another interpreter from an earlier session.
The default interpreter setting applies when VS Code first chooses an
interpreter; it does not replace a previously selected one. The editable
installation makes source changes available immediately without reinstalling.
Pylance resolves the source tree through `src` and checks open files strictly.
The guarded sweep supplies whole-repository coverage. Evidence records the
Pylance extension version separately; a CLI Pyright pass does not certify
editor diagnostics. Ruff enables `E4`, `E7`, `E9`, `F`, `I`, `UP`, `B`, `ANN`
and `RUF100`, with preview disabled.
Maintained executable reproductions live under `devtools`; reviewed weekly records live under `docs/sprints`. New raw evidence goes to ignored `results/runs`; old local logs and scripts remain historical evidence, not maintained launchers. Repository-wide Ruff checks include every remaining authored Python file. There are no mypy error exclusions or inline mypy/Ruff suppressions
in the maintained roots.

Use the development dependency versions declared in `pyproject.toml`; validation
records the effective toolchain. The timeout plugin is explicitly pinned and
loaded by the shared runner. Runtime installation remains dependency-free and
supports Python 3.11 and newer.

## Executable source policy

The policy owner is [`repository_policy.py`](../devtools/checks/repository_policy.py),
with regression gates in [`test_repository_policy.py`](../tests/repository/test_repository_policy.py)
and [`test_python_clones.py`](../tests/repository/test_python_clones.py). Run
`python -m devtools.checks.repository_policy` for machine-readable violations;
`python -m devtools.checks.release --suite unit --select tests/repository/test_repository_policy.py --select tests/repository/test_python_clones.py`
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

Repository pytest execution must use the shared runner. Direct invocations fail
before collection with the equivalent guarded command. The unit selection excludes
`validation`; `all` includes the complete serial Python suite and other release gates.
Repeated `--select` arguments execute the exact requested paths or node IDs,
including their validation-marked cases; they report `serial-selected`, not a
complete unit or full-suite result:

```bash
python -m devtools.checks.release --suite unit
python -m devtools.checks.release --suite all
python -m devtools.checks.release --suite unit --select tests/repository/test_process_guard.py
```

Add `--unit-only` to a selected unit run to exclude validation-marked cases,
matching the default unit suite's marker filter. Use this without `--profile`
when measuring whether a subset fits the unit timing budget.

To locate expensive functions in a failing performance selection, add `--profile`.
The runner writes `unit.pstats` (or `p0.pstats`) beside the phase timing log. Read
it with Python's `pstats` module. Profiling includes collection and fixture work,
retains the same execution limits, and is development-only; its overhead must not
be confused with an unprofiled acceptance measurement.

The validation directory contains independent proofs and research experiments.
Long integration workloads and complete repository AST/Isabelle dependency scans
beside their subsystem tests carry the `validation` marker. Small correctness,
ownership, budget, identity, poison-route and checker-fixture regressions remain
in the unit suite. Classification changes selection, not test assertions,
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

Historical evidence keeps its original source attribution and limits. It cannot
certify the current commit.

## Reproducible release commands

Use `python -m devtools.checks.release --suite SUITE`, choosing `quality`, `unit`,
`proofs`, `p0` or `all`. Optional `--output-dir PATH` must be a fresh directory.
The authoritative limits live in
[`validation_policy.py`](../devtools/checks/validation_policy.py).

| Run | Wall-clock ceiling | Aggregate process-tree memory |
| --- | --- | --- |
| Individual Python test, including fixtures and teardown | 60 seconds | 4 GiB |
| Python selection or full suite | 300 seconds; each test still 60 seconds | 4 GiB |
| Standalone Python validation or probe command | 60 seconds | 4 GiB |
| Each Isabelle session | 300 seconds | 6 GiB across the build tree |
| Isabelle version or session-inventory probe | 300 seconds | 6 GiB across the build tree |

A single explicit test-node invocation also has a 60-second outer deadline.
Collection and initialization count toward invocation limits. Python runs serially.
The pinned `pytest-timeout` plugin uses thread termination with debugger suppression
disabled; an interrupted report is incomplete evidence. Nested commands inherit the
remaining deadline. Timeout markers, environment overrides and competing settings
are rejected. Short watchdog-test inputs do not alter this policy. Existing
workload latency assertions remain measured assertions; they do not install
separate signal alarms or reset the test deadline.

Isabelle uses four prover threads, `parallel_proofs=1`, `timeout_scale=1`, and one
building session (`-j 1`). Java has a 1-GiB maximum; Poly/ML has a 4-GiB maximum.
One dependency-aware build applies the native 300-second timeout to each session.
The process guard also times each inventory-admitted session from its build-start
event, so delayed native cancellation cannot use the orchestration allowance.
Repeated start events do not reset that clock. Timeout evidence names the session
and records descendant cleanup; interrupted or incomplete builds are failures.
The outer orchestration fail-safe is `300 × (dependency-session count + 1)`,
using Isabelle’s native graph including installed session dependencies; it never extends a session deadline. Select sessions with repeated
`--session SESSION`, or omit them for the aggregate build. Reused heaps are reported
separately from rebuilt sessions and do not demonstrate cold-build performance.

For the pending comma semantic cutover, select `Comma_Semantic_B1_Instance`
first, then `Comma_Semantic_Future_Instance` through this runner. The latter
owns the semantic global theorem and its dependency closure. The differently
named `Comma_Global_Future_Safety` selects the legacy native chain. An aggregate
build includes registered legacy/audit sessions too; their presence in its log
does not establish that the semantic release theorem depends on them. Neither
target selection nor a local theorem pass admits the runtime provider artifact.

Development runs allow dirty work and record Git HEAD, tree object, object format
and dirty status. They cannot certify a commit or supply reusable release evidence.
`--acceptance` requires clean committed source and uses one isolated detached Git
worktree for the selected run, checking Git cleanliness before and after execution.
The runner never stages, commits or discards user work. Generated output stays
ignored and separate. Changed acceptance sources invalidate the evidence.
No recursive source fingerprint, inode snapshot or filesystem watcher substitutes
for Git. Artifact integrity checksums and Isabelle dependency checking remain valid.
Developer code locates proofs through `devtools.paths.isabelle_root()`.
Registration discovery follows `ROOTS` through the shared Isabelle registry;
session paths are relative to the common proof root. Moving a session does not
change its deadline or reset the enclosing process budget. Nested registrations
are subject to the same option checks as the former single `ROOT` file.

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
  elaborated AST or proof checker. The
  [`registration reader`](../devtools/checks/isabelle_registry.py) discovers all
  `ROOT` files through `ROOTS`, checks the combined session graph and rejects
  hidden registrations and path escapes. Builds and oracle checks remain required.
- [`isabelle_source_analysis.py`](../devtools/checks/isabelle_source_analysis.py)
  inventories supported declarations and reports nontrivial structural duplicate
  candidates and declarations without observed incoming references. Argument
  order, literals, operators and external names remain significant. These are
  review findings: exported facts, automation attributes, ML antiquotations and
  dynamic extensions prevent a lexical reader from proving a theorem unused.
  Unsupported syntax is reported explicitly. The adversarial parser tests cover
  scope, shadowing, quoted fake commands and cross-file references; a shared
  `by simp` proof script alone is not duplicate mathematical logic.
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

## Execution and proof ownership

Production `arithmetic` owns parameterized mathematical laws, `hashlife` owns
generic scheduler/application machinery, and `resources` owns accounting and
lifetimes. Those layers must not import `sequences`, including through local or
type-only imports. Family adapters supply recurrence parameters, source admission
and family observations to the shared contracts. There is one `TileScheduler`;
moving a family adapter does not introduce an executor or alter semantic IDs.

Isabelle sources are grouped under `shared/<domain>/<session>`,
`families/<family>/<session>` and `integration/<contract>/<session>`. Each session
has one directory and keeps its declared name and native timeout. Shared theories
do not import families; family-to-family bridges belong to integration owners.
Generic carry/borrow equations are shared only when their hypotheses and transported
phase conventions agree. Family safety, recurrence and source-admission statements
remain with their family.

Tests follow the mathematical or runtime owner. Migration records must map moved
assertions and proof claims to their retained owner. Directory relocation cannot
turn an existing failed constructor gate into a pass or make an audit theorem a
production refinement. Lexical duplicate and unused-theorem findings require
review of exports, automation attributes and dynamic ML references before deletion.
Audit sessions live under their owner's `audit/` directory. Release theories,
sessions and ML resources cannot depend on those audit-only implementations.
The shared inventory checks those edges across all registrations discovered by
the top-level `ROOTS`.

## Resource-controlled diagnostics

Install the optional sampling profiler with `python -m pip install -e '.[profile]'`.
The development environment uses Pyinstrument 5.1.3; runtime installations
remain dependency-free. Use the standard-library `cProfile`/`pstats` for exact
call counts and `tracemalloc` for focused allocation investigations. Sampling
profiles are useful for hot paths; uninstrumented runs remain the latency
baseline.

```bash
python -m devtools.checks.release --suite unit \
  --select tests/sequences/collatz/test_source_image_runtime.py --profile
```

The runner writes the profile beside its guarded timing and outcome records.
Sampling or CLI profiling must likewise run inside an existing guarded probe;
direct profiler commands are not an alternative validation launcher. Capture
successful output and the unprofiled exit status as well as the profile: `cProfile`'s
module runner can swallow `SystemExit`, so its zero exit status does not prove
the CLI completed the request. The sampling CLI preserves that status in the
checked environment. A fast budget refusal is not a performance improvement.
Use the existing `devtools.benchmarks.pytest_timing` plugin for separate
collection/setup/call/teardown evidence. Never share warmed production caches
between independent tests to improve timings.

Run checks serially through the shared release runner. Standalone probes use the
same process guard and fixed 60-second / 4-GiB policy; no custom timeout flags are
needed. Partial selections remain diagnostic and cannot establish a full-suite pass.
The guard retains at most 8 MiB of command output.
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

Canonical probe entry points accept `--output-dir PATH`. Choose a fresh directory for every invocation; an existing directory is rejected. Without this option, a unique timestamp/UUID directory is allocated under `results/runs/`. Reports share the invocation's directory and `manifest.json`, which records command, tool versions, metrics schema, limits, Git provenance, effective limits, and completion outcome. Interrupted work remains diagnostic; dirty development runs never certify a commit. Raw JSON, logs and profiles stay local; summarize scoped conclusions in the reviewed sprint topic.

For configurable current public-route comparisons, use `python -m devtools.benchmarks.public_query_comparison --family collatz --horizons 16 32 64 --trials 5 --modes cold warm bypass --bases 2 10 --position 0 --output-dir results/runs/public-query-review`. The report retains warm priming and all CLI/point samples; it measures route agreement and states its timing scope without introducing a release threshold. Point positions must be valid at every requested horizon, including cycle values.

New evidence uses Git object identities and an explicit development/acceptance mode. Historical fingerprint evidence remains unchanged and cannot be upgraded to current acceptance evidence.

Summarize new benchmark evidence in the appropriate topic file under
`docs/sprints/week-of-YYYY-MM-DD/`, using the **Sunday** start date.
Canonical developer modules write raw evidence to fresh local paths; they do
not create another versioned microtask report.

### Documentation placement

- **Release status:** one current disposition per gate, a short remaining
  requirement and a link to its evidence owner. Do not copy run counts, timing
  tables, receipt lists or previous dispositions into this page.
- **Weekly sprints:** the owning topic records changes and the evidence needed
  to assess them. Keep one scoped result and receipt per check; replace
  superseded checkpoints in an active topic instead of appending every failed
  attempt and successful rerun. Retain a baseline only when it supports a real
  before/after comparison, and a failure only while it explains an unresolved
  obligation or a useful rejected approach. Do not repeat receipt details in
  multiple sections. Completed dated records remain historical, not current gates.
- **Research papers:** definitions, propositions, assumptions, proof sketches,
  counterexamples and open mathematical constructions. Link to sprint evidence
  and release status. Do not duplicate test tallies, operational failure logs or
  patch-by-patch implementation histories. A theorem's hypothesis or a genuine
  counterexample remains relevant even after an implementation bug is fixed.
- **Architecture and API guides:** current responsibilities and user-visible
  behavior. The proof index owns formal statements, assumptions and build
  references; the validation guide owns commands and execution limits.

Weeks run Sunday–Saturday. File a topic once in its completion week and state
its actual date range; keep the weekly index short. Use Git for prior versions
and ignored run artifacts for detailed diagnostics. Removing a superseded
summary does not require creating another history page or deleting raw evidence.
Externally supplied archived documents retain their original text.

Register maintained pages in `docs/catalog.toml`. Check links and headings with
`devtools.checks.docs_index` through the guarded validation runner after edits.
A documentation change cannot close a failing execution or proof gate.

Generated run payloads under `results/` are local or CI artifacts and are ignored
by Git. Commit reviewed weekly Markdown summaries under `docs/sprints/`; keep executable reproductions under `devtools` and independent oracles under `tests/support`;
keep console transcripts, JUnit XML, result JSON, profiles and caches out of
source control. Historical raw artifacts were removed during the September 11
cleanup. Paths in retained summaries describe local outputs, and their recorded
passes do not certify the current source. Generate and validate fresh evidence
before a release; the evidence requirements above remain unchanged. See the artifact retention policy below.

The shared runner writes `unit.phases.jsonl` with collection timing and each
test's setup, call and teardown timing, including after an interrupted run.
The file is created exclusively and flushed after each record. Its record allowance
scales with the selected item count, up to 65,536 records, with an 8 MiB byte cap.
A missing finish record means the run was interrupted; a truncation record
invalidates complete coverage claims. Use this trace to locate expensive tests,
then measure the default serial release command without `--profile`. The timing
plugin caches no test runtime or proof result.

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
source provenance in reviewed summaries; do not paste console transcripts.

This retention policy does not change release gates. Full release evidence must
still be generated and checked against the current source, using the existing
process guard and test-run evidence checks. A summary alone cannot satisfy those
checks. See [development guidance](development.md).

Fixtures and required kernel assets belong beside their source owners outside
this output directory. JSON and XML are not globally ignored: legitimate inputs
remain reviewable.
