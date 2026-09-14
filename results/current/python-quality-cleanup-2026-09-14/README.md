# Python quality and slow-test cleanup — September 14, 2026

This checkpoint upgrades the Python development tools and removes obsolete typing
and lint suppressions. It preserves existing CLI indices, release-gate workloads,
resource limits and mathematical release assertions. Runtime remains dependency-free.

## Dependencies and configuration

PyPI metadata was checked for [pytest](https://pypi.org/project/pytest/),
[mypy](https://pypi.org/project/mypy/), [Ruff](https://pypi.org/project/ruff/), and
[setuptools](https://pypi.org/project/setuptools/). The latest stable versions at
this checkpoint are pytest 9.1.1, mypy 2.3.1, Ruff 0.16.7 and setuptools 84.0.0.
The environment also uses pip 26.2.1 and wheel 0.48.0. See
`dependency-versions.json` and `installed-dependencies.json`; `pip check` passes.
Python >=3.11 remains the package support declaration; tests here use Python 3.14.

`mypy` uses strict mode over the maintained `src`, `tests`, and `devtools` roots.
The old explicit error exclusion was removed. `mypy .` is not the supported
command: historical reproduction directories contain duplicate unpackageable
module names, such as `validation_driver`. Those scripts remain in `ruff check .`.
The old narrow Ruff rule selection was removed in favor of current defaults plus
unused-suppression checking. No `type: ignore` or `noqa` remains in the maintained
roots. No `cast(Any, ...)` remains there either; this is not a claim that Python
reflection or every use of the `Any` type has been eliminated.

Historical scripts needed lint and formatting fixes. Exact original bytes are
preserved beside each changed script as `.py.original.txt`; their SHA-256 hashes
are in `historical-script-migration.json`. Old timing logs and outcome JSON were
not regenerated or relabeled as results of the edited scripts.

## Repairs and independent review

- Higher local interfaces no longer inherit the incompatible finite quotient
  arena. Their own source authority, registered stores and validation remain;
  construction no longer allocates unused finite-function/quotient stores.
- Aggregate repository policy reports parse a fresh AST snapshot once and share
  it with their component checks. Standalone calls still read fresh source;
  there is no persistent cache that can accept stale file contents.
- The bounded reverse publisher oracle builds its own admitted reference geometry.
  Its 1–16 digit checks compare its output to the literal reference directly,
  avoiding a separate production traversal just to exercise the old oracle.
  Production digit/cutover checks remain separate and unchanged in workload.
- Unreachable partition-lift code was removed from the development proof evaluator.
  Live boundary quotient behavior remains intact. Tests were not moved to the
  validation partition to conceal slow execution.
- Sort hashing now validates and computes hashes in one postorder traversal.
  Signature admission consumes that result instead of validating the same DAG
  again. An adversarial shared-node test checks one visit and exact hash formulas;
  forged cycles are still rejected. Constructor-wide validation is unchanged.
- Frozen defaults, closure captures, validation property reads, private hook types,
  tuple variants, exports and negative fixtures were repaired for the new toolchain.
  Explicit validation still runs; intentional invalid setters retain descriptor
  and frozen-object failures. Broad benchmark catches retain their result schemas
  and log debug tracebacks.

Workers owned disjoint source/test areas. Independent adversarial review caught
and repaired an omitted Antihydra `observe_run` export, hidden scheduler hook Any
casts, and two proposed lint evasions (an Exception alias and a false feature flag).
Further narrow casts are justified by checked runtime domains or the existing
adapter protocol, rather than making malformed test inputs statically valid.

## Validation

Commands run under the existing serialized process guard: ordinary checks and
probes use 35 seconds/1 GiB; the full unit suite uses 300 seconds/1 GiB.
The final source fingerprint and per-command watchdog reports are stored here.
The interrupted full-unit run preceded the final sort/protocol edits and lacks
completed JUnit fingerprint evidence; it is diagnostic evidence only.
Preliminary runs are retained and are not presented as final-source evidence.

- Initial runtime/ownership/oracle/policy group: 133 passed in 18.00 seconds.
- CLI, rendering, lazy requests and negative fixtures: 263 passed in 14.61 seconds.
- Final strict nonincremental mypy: 1,318 files pass (`verified-mypy.log`).
- Diagnostic full-unit run: 4,730 passed calls and one failed call before the
  unchanged 300-second watchdog expired (708,740,056 peak sampled bytes).
  There is no finish record, so this is not a complete unit pass. The unfinished
  call was the reverse-32 case in `test_higher_primitive_table_cache.py`.
- That late reverse/cache/fused group passes separately: 29 passed, two existing
  validation tests deselected, in 16.49 seconds. This isolates the outer suite
  timeout from an unsupported claim that the last test independently hung.
- The known F4 control still fails at `test_idempotent_output.py:232`: explicitly
  demanding classification returns `GUARDED`, while the assertion requires
  `RESOLVED`. Its assertion was preserved (`known-f4-control.log`).
- Final sort/fused group: 83 passed in 5.08 seconds (`sort-fused-final.log`).
- Final strict mypy: 1,318 files; Ruff check and format check: pass across the
  repository; structural policy: no line-cap, recursion or package violations.
- Isolated wheel inventory/public API/CLI check: pass, including ten family-first
  contracts (`wheel-check.log`). Independent nonzero digit checks: 14 plain/JSON
  cases across seven family names pass (`installed-digits.log`).
- Independent final read-only review found no defect in the fused structural
  contract or combined sort validation/hash pass. No hook-presence reflection
  was added to each traversal and no hash collision replaces exact equality.

## Remaining performance work

The phase log attributes nearly all time to test bodies, not pytest fixture
setup/teardown. It does not establish a dependency-version slowdown without an
A/B baseline. The suite timeout is still a release blocker.

Independent audit found quadratic deep-sort construction: every nested sort
constructor validates the existing child graph. Only duplicate hashing/signature
passes were removed here. Avoiding constructor-wide validation needs an integrity
and authority design because tests deliberately forge cycles in frozen objects.

Cold reverse-32 construction and cache eviction/requery are required production
workloads. They were not changed to shared warm fixtures. Full-tree source audits
also have measurable parsing/traversal cost; aggregate reports now share a fresh
AST snapshot, but independent test invocations still perform their own audits.
Fine latency thresholds, cold-path workloads, validation markers and mathematical
P0 assertions remain unchanged.

This cleanup does not supply the missing arbitrary-depth constructor refinements,
Fermat/Mersenne shadow classification coverage or Antihydra non-halting certificate.
Those existing release holds are neither weakened nor closed by passing lint.
