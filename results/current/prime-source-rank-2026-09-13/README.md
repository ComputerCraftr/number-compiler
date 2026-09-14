# Prime source rank/select evidence — September 13

Release remains **BLOCKED**. This packet records a production owner integration,
component proofs and measured performance; it does not assert end-to-end formal
CLI refinement or closure of the existing cross-family P0s.

## Scope

Production uses one iterative Legendre DAG for source-derived factor-stage
construction and exact rank/select, with query-owned retained storage and explicit
state/work/stage budgets. Both source and installed CLI checks exercise it.
Compatibility wheel queries reuse the evaluator with local per-call memoization.
No parent wheel gaps or leaf bitmap are constructed.

## Checked evidence

- `prime-source-checks.log/json`: 165 tests pass, 13 deselected; 12.62 seconds,
  527 MB. Covers prime modules, CLI/API migration/context, cold import boundaries,
  and unchanged repository policy. This run preceded the final smaller-window
  tuning and four additional source-owner/input tests; the full-unit result below
  is the final Python check.
- `prime-source-p0.log/json`: unchanged selected release gate, **15 failed,
  7 passed**, 3.16 seconds, 91 MB. The failures remain 196/source-image cutover,
  Fermat/Mersenne compact terminal recovery and Antihydra source-7 certification.
- `prime-wheel-isabelle-v26.log/json`: **PASS**, 9.46 seconds, 952 MB under
  the unchanged 35-second/4-GiB guard. Source-prefix growth, discovery stop,
  least-survivor and finite count lemmas are checked. Exported theorem oracle
  dependencies are empty. No new axioms or skipped proofs.
- Ruff and mypy pass for the changed Python owners, CLI wiring, tests and probes.

Still missing formally: numerical division-recurrence transport, executable
postorder memo and binary-selector refinement, overcovered smaller-bound
transport, and the resource bound. These are written explicitly in the theory;
the source-admission loop is not certified merely by assuming a complete prefix.

## Installed performance

The optimized wheel is `/tmp/prime-source-wheels-owned/number_compiler-0.59.9-py3-none-any.whl`.
SHA256: `481a8f1d32e44145c7c051cbd25484dca2e075f10d7b7f690f31e8281a22c478`.
The baseline is the previously verified wheel with SHA256
`8ccf371071621efa99c73a26e7ba8540845a8eb55b6c5765b404541c1260cd31`.

`prime-source-timing-owned.log/json` includes three fresh process runs per
case and wheel, including imports, discovery, construction and exact output.
Filesystem caches remain enabled. Values agree exactly.

| Query | Previous median | Candidate median |
| --- | ---: | ---: |
| `prime --nth 1000 --format json` | 123.81 ms | 93.10 ms |
| `prime --nth 0 --start 10000 --format json` | 92.32 ms | 86.22 ms |

`prime-source-warm-owned.log/json` runs four real `main()` CLI calls in each
installed interpreter after importing the dispatcher. Each new call creates its
own query. The median of calls 2–4 is:

| Query | Previous median | Candidate median |
| --- | ---: | ---: |
| `prime --nth 1000 --format json --info metrics` | 32.14 ms | 16.38 ms |
| `prime --nth 0 --start 10000 --format json --info metrics` | 1.26 ms | 28.23 ms |

**The warm high-start regression remains open.** The old lane path retains global
compiled results; the candidate disposes query state and repeats charged discovery.
The final workload counters are 6,530 work steps / 3,361 memo states for nth1000
and 3,885 / 1,955 for start10000. These counts do not establish a bound for arbitrary
prime indices and are not wall-clock or CPU bit-operation units.

Earlier timing logs are retained to show the optimization sequence rather than
select only favorable samples. The initial retained-memo treatment of local wheel
calls took 16.33 seconds for 46 focused tests; restoring local compatibility memo
reduced that to 4.25 seconds. The first wheel build without isolation failed because
this interpreter lacked `setuptools.build_meta`; isolated builds succeeded.

## Ownership regression and final validation

`prime-source-full-unit.log/json` found one new failure alongside the previous
four: the compatibility local map was assigned to an owner attribute, violating
the existing factory policy. That run had 5,064 passes, five failures and 1,277
deselections in 239.28 guarded seconds (639 MB). It is preserved, not presented
as passing.

The repair keeps `self.memo` factory-owned in every mode and creates a genuinely
local map only inside `count()` for compatibility queries. It clears that map
and frames in `finally`; closed workspaces reject reuse. No factory-policy
exception was added. Independent re-audit found no retained local memo or helper
closure. `prime-source-ownership-fix.log/json` passes 140 tests, including all
prime tests, API/CLI, lifecycle/ownership and repository policy, in 13.81 seconds.

`prime-source-installed-owned.log/json` passes source-byte inventory, public API,
resource and ten installed family-first CLI checks, including actual prime-DAG
metrics and budget refusal. It takes 6.16 seconds / 114 MB. The final wheel above
includes the ownership repair; final cold/warm timings were rerun against it.
Timing variance across the preserved runs is visible; the warm high-start
regression persists and is not represented as closed.

`prime-source-full-unit-final.log/json` completes the final rerun in **250.87
seconds**, peak **637,846,440 bytes**, under the unchanged 300-second/1-GiB limit:
**5,067 passed, four failed, 1,277 deselected**. There are no new unit failures.
The four remaining failures are exactly the previously recorded 196/source-image
and runtime-cutover failures:

- `test_clock_audit_keeps_live_context_and_measures_warm_cache[196]`
- `test_source_compiler_is_theorem_free_and_cheap_shapes_resolve_impossible_sheets_first`
- `test_reverse_diamond_does_not_report_proof_states_as_runtime_classes`
- `test_certified_reverse_uses_source_publisher_and_reports_concrete_work`

The factory-ownership regression is fixed without changing its assertion. No
release assertion or time/memory limit has been weakened. The selected P0 suite
still reports 15 failures / seven passes; formal executable refinement and the
warm high-start prime regression remain explicitly open.
