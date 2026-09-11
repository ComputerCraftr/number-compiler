# Unit-suite cleanup: September 9, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The default serial suite passes **4,032 tests in 293.67 seconds**. The 918
exhaustive, research and release-validation cases remain available separately.
Both partitions contain all 4,950 collected cases, with no overlap, skipped
cases or expected failures in the passing unit run.

This is a unit-suite result, not completion of the HashLife performance release.

## Commands and evidence

```bash
pytest                         # default unit suite
pytest -m validation           # exhaustive/research/release validation
pytest -m ''                   # complete collection
```

The frozen source fingerprint is
`22e75ce3c728ec1cea293600cd5df5c6a63e82a74ea03dda21f0f7e6ca9bb7d2`
using `number-compiler-authored-source-v4`.

| Gate | Observed result |
| --- | --- |
| Default serial pytest | 4,032 passed; 918 deselected; 293.67 s |
| JUnit suite duration | 293.785 s, including reporting overhead |
| Guarded command duration | 294.521 s; unchanged 300 s deadline |
| Sampled aggregate process footprint | 578,929,504 bytes, approximately 552 MiB |
| Ruff format/check | Passed; 1,188 files formatted |
| Whole-tree strict mypy, incremental cache disabled | Passed; 1,064 source files |
| Recursive structural checks | No line-count, recursion or package violations |
| Exact collection partition | 4,032 unit + 918 validation = 4,950 |

The run used ordinary garbage collection and serial execution on a Mac14,15,
8 GiB RAM, 8 logical CPUs, macOS 26.6.2, Python 3.14.7. It is one timing trial
with approximately six seconds of pytest timing headroom, not a guarantee under
different machine load. Memory is sampled Darwin process-group physical footprint;
the 1 GiB watchdog is supervision, not a hard allocation cap.

The machine-readable evidence (local artifact: `evidence.json`) includes the twenty slowest cases.
Their combined testcase time is 104.941 seconds. The slowest case is the
public reverse tile-runtime work check at 21.506 seconds. Future tuning can
target these costs without changing their assertions.

The JUnit result (local artifact: `unit-final.xml`) records the exact selected manifest and
matching before/after fingerprints. The collection audit (local artifact: `final-collection.json`)
verifies complementary selections. Logs and guard reports are in [final/](final/).
The release-evidence validator rejects this `serial-unit` result as full-release
evidence; only a complete, passing `serial-unfiltered` manifest can satisfy it.

## What changed

- Proof and research tests now live in regular `tests.validation` packages.
  Long end-to-end orbit, exhaustive matrix and release-performance workloads
  retain their subsystem placement and carry an explicit `validation` marker.
  The ten absorption gates remain runnable. Classification preserves test
  bodies, parameters, fixtures, assertions, budgets, tracing and watchdogs.
- Fast correctness, authority, numeric-ID, ownership, budget and poisoned-route
  checks remain in the default suite. Added small reverse point/width/lowering
  differentials for bases 2–5 and decimal, and collection/evidence regressions.
- Repeated immutable operator construction was removed from a proof matrix:
  99 operators instead of 792, with all 792 independent applications retained.
  The radix matrix shares its intended application across radix views while
  keeping all 48 cases; cold/isolation tests still create fresh runtimes.
- The existing capped point microblock cache now includes the source scope and
  validates symbols against the output alphabet. A cached point can survive
  query-memo eviction without replaying its temporal computation. This adds no
  unbounded output cache or shared execution engine.
- Prepared reverse-width queries consume their existing certified interface
  before reconstructing sibling interfaces. Kernel admission gives separately
  owned bounded containers to equal immutable domains; mutable multi-owner
  rejection remains enforced. Fresh codec budget failure occurs before opening
  workspace when even its mandatory root cannot fit.
- Accounting fixes distinguish charged DAG nodes from interface-record counts,
  forward unambiguous ledger roles, and compare shared memo totals with actual
  retained entries. The independent runtime audit now validates threshold
  summary records instead of incorrectly treating them as action requests.
  Standalone geometry records are no longer bypassed by the live-runtime audit.
- Obsolete private-carrier reporting assertions were migrated to exact owner
  inventories or the current fail-closed carrier result. The threshold-summary
  optimization test now checks the actual arithmetic shortcut; the independent
  Boolean-mask optimizer regression remains. These are explicit instrumentation
  corrections, separate from moving validation tests unchanged.

## Preserved incomplete evidence and remaining work

The initial unsplit diagnostic hit the 300-second guard at 300.078 seconds; its
total suite time is unknown. An early split attempt also timed out at 300.056
seconds. A later attempt reached 96% but timed out at 300.069 seconds with twelve
failing checks. All twelve subsequently passed in focused verification and in
the final unit run. Their logs remain under [baseline/](baseline/) and
[diagnostics/](diagnostics/); interrupted or truncated profiles are not complete
coverage evidence. The earlier `collection.json` describes an intermediate tree,
while `final-collection.json` describes the passing fingerprint.

Exhaustive validation was not completed in this pass. A focused exhaustive block
matrix still exceeded its unchanged 35-second diagnostic guard after the setup
consolidation. Earlier diagnostics also exposed the reverse cold-work doubling
failure and a Collatz source-morphism metric expectation that the binary route
does not satisfy. Those tests remain validation gates; no counters or limits
were changed to manufacture a pass.

The suite split does not prove sublinear cold execution, complete N=16…1024
scaling evidence, the five-process radix medians, or a complete passing HashLife
release. Production algorithm and exhaustive-validation performance work remain
visible and separate from this completed unit-suite milestone.
