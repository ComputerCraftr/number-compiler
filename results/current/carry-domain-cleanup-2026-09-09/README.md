# Closed reverse carry interfaces and obsolete-runtime deletion

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This checkpoint is an implementation and cleanup record, not a completed
sublinear-runtime release. The first measured source fingerprint (algorithm v4) is
`0d94790cb1a1feee9a02939965feebdff36d7a28d1363a1c625ac935082a656e`.
Validation uses Python 3.14.7 on the existing macOS host. Each Python check runs
alone under the process-group guard: 1 GiB physical-footprint limit, 35 seconds
for focused probes, and 300 seconds for the serial release attempt.

## Implemented execution and ownership changes

- Decimal primitive and parent interfaces use closed carry/output functions,
  preserving the exact 43-left/5-right primitive semantics without temporal
  product-domain enumeration or Boolean substitution for every parent.
- Fixed mod-32 sector summaries compose spatially with the three-element carry
  monoid. Growth and forcing are derived from those summaries. The authenticated
  tile application can observe the full bounded affine sector product without
  an endpoint or generation itinerary. Decimal width consumes the carry/extent
  interface; this is actual execution, unlike compiler-only source-death bounds.
- Primitive parent interfaces and cached temporal midpoint interfaces are probed
  before descendants. Midpoint misses retain fused evaluation; they do not force
  completion. Cached/fused tests compare the entire payload, including noninitial
  boundary inputs and cocycle deltas.
- Interface preparation pins completed causal subresults in the application
  ownership scope. Repeated observations can reuse them after temporary tasks end.
- Quotient and spatial binding publication share one aggregate reservation and
  rollback journal. Sparse monotonic quotient IDs are not recycled after failure.
- Reporting forwards actual execution counters. Independent accounting separates
  per-record charged arithmetic slots from unique live backing objects, including
  deliberately shared functions. Neither inventory evaluates semantic functions.

The affine product observation still obtains the final input interface through
the causal executor. Deriving that product is not counted as avoided causal
construction. General source-dependency elimination and the deep work envelope
remain distinct obligations.

## Deleted execution islands

Removed the reverse concrete adapter, radix observation/image input and higher
radix interface adapters, and Collatz field observer, recursive image runtime and
temporal emission modules. Optional image inputs were removed from higher values,
summaries and dependency tasks together with their audit branches and dead roles.
No production callers of the deleted modules remain.

Current tile tests preserve the large Collatz source 598926 at steps 4 and 64,
sparse source geometry, numeric aliases, budget rejection, leases, eviction and
absence of the retired routes. Live proof/semantic compilation still uses parts
of the continuation package. Those dependencies have not been mislabeled dead.

## Validation and measurements

| Check | Result |
| --- | --- |
| Ruff format/check | Pass; 1,167 files already formatted |
| Strict mypy, empty incremental state | Pass; 1,047 source files, 9.63 s guarded |
| Recursive structural policy | Pass; no source-size, recursion or package violations |
| Sector, atomic accounting, midpoint tests | 72 passed in 7.49 s |
| Preserved large-source radix and alias fixtures | 6 passed in 10.62 s |
| Reverse N=64 width absorption, unchanged poison gate | 1 passed in 17.04 s; 109 MB sampled peak |

The earlier N=64 width attempt exceeded 35 seconds. The current passing test
includes interface preparation and does not create a final endpoint to prepare
the parent. These are individual trials, not a five-trial scaling series.

The earlier focused midpoint run has 71 passes and one accounting-fixture
failure: its source did not happen to share function objects between records.
The final accounting test deliberately creates shared records and independently
checks unique backing versus conservative charges; all 72 tests then pass.
Both logs are retained rather than hiding the failed intermediate run.

## Subsequent cleanup and reuse corrections

The closed finite-port laws now cover the exact primitive kernels for bases
2–15, with exhaustive comparisons over their finite states and symbols. Base 16
and unsupported custom laws retain ordinary finite-interface admission. The
decimal Frobenius sector formulas are still restricted to their certified base.

Exact causal-boundary concatenations now have bindings in the existing result
memo, with reverse indexes, application leases, atomic reservation and eviction.
An adjacent view of the same backing tile uses its constant-time view law before
construction. Relative origins that do not affect a directed transfer normalize
before task lookup; forged numeric aliases still reject before that lookup.
These are exact reuse optimizations, not a claim that all causal prefixes alias.

Fixed proof C⁴ projection lowers to the existing balanced primitive physical
Collatz action DAG. Its 50/90 proof-state domains do not enter production tile
interfaces. The unchanged full-halo comparison and an added poisoned-proof-law
test exercise that translation. Resource tests also now inspect the actual tile
application and lease graph instead of removed callback carriers.

Canonical parent counts come from actual nonleaf tile records. Canonical
interface counts exclude inline coefficient storage charges while preserving
separately owned higher-interface records. Existing proof geometry and cycle
certificates report their observed populations; they are not forced to zero.

## Execution evidence and unmet gates

The first frozen serial run was stopped by the unchanged **300-second** guard
at approximately 30% of the suite: elapsed 300.0559 seconds, sampled process-group
peak 594,445,176 bytes. It had collected 4,788 tests. No completed JUnit result
was produced. This is an interrupted run, not a passing suite, a count of tests
passed, or a measured complete-suite duration.

An N=128 width probe also exceeded 35 seconds. Larger depths were not launched
after this failure. A later grouped absorption probe completed its first three
cases, then exceeded 35 seconds; the ten-test gate remains incomplete.

After boundary-concatenation reuse, individual cold point observations with
acceleration disabled produced:

| Quantity | N=32 | N=64 | Doubling ratio |
| --- | ---: | ---: | ---: |
| Time (seconds) | 4.4650 | 16.7762 | 3.757 |
| Causal scheduler frames | 47,962 | 176,753 | 3.685 |
| Task evaluations | 8,609 | 31,390 | 3.646 |
| Boundary concatenation frames | 19,808 | 87,853 | 4.435 |
| Concatenation evaluations / early hits | 1,124 / 141 | 4,514 / 326 | — |
| Retained entry charges | 30,468 | 112,924 | 3.706 |
| Node quota units, including inline arithmetic | 38,272 | 112,500 | 2.940 |

The scheduler-frame effective exponent is approximately **1.88**. These two
individual trials are insufficient for asymptotic claims, but their executed
work is visibly superlinear. Resource quota units are not unique DAG nodes.
Growing causal construction and low prefix reuse remain real blockers; bounded
innovation, compiler size and a smaller live graph cannot hide that work.

A separate N=32 CPU diagnostic found approximately 231,000 action validations
and 50 million total Python calls. Its instrumented duration is not comparable
to ordinary timing. This motivated removing duplicate same-call validation,
while keeping public warm identity, liveness and publication checks.

Directed transfers subsequently gained a transient admission for one scan:
immutable action/kernel metadata is checked once, while every node retains
exact-type, admissibility, tile-liveness, alphabet and publication validation.
No unchecked application-wide action cache was introduced. Consuming one
completed result also reuses its already validated output reference within that
call instead of reopening the same lease repeatedly.

The five-process fixed radix-3 gate passed on the first fingerprint: cold median
0.000181125 seconds, repeat median 0.000076208 seconds. That narrow original-source
law is not evidence of general deep HashLife performance. The complete
N=16…1024 work/retention series and a serial run under 300 seconds remain required.

## Frozen production validation and follow-up poison repair

The production-validation source fingerprint is
`655b2e5ef544b867b5da4e6bedd8c468546ffab6e85fe3e9eb08663cadbefb3d`
(algorithm v4). The final focused gate passed **132 tests in 8.43 seconds**.
It includes noninitial two-sided transfers, exact boundary reuse, numeric-alias
rejection, mixed-role accounting, and fixed-C⁴ compatibility. An earlier run
had 110 passes and one new-test exception-message mismatch; the validation itself
rejected correctly before ledger mutation, and the test now checks the certificate
error without depending on which validating layer reports it.

An isolated wheel built from this tree passes installed public-API, CLI, typing
marker, resource-content and developer-package-exclusion checks. It exposes the
37 intentional public exports. Generated build directories were removed afterward.

The fixed radix gate passed across five fresh processes on this fingerprint:
cold median **0.000174750 seconds**, repeat median **0.000076333 seconds**.
Its report confirms identical before/after source fingerprints and explicitly
limits the result to the original-source regression.

The serial run collected **4,816 tests** and was stopped at **300.079 seconds**,
with **2,026 completed passes and one completed failure** in the verbose log,
at approximately 42% completion. Sampled group footprint peaked at
647,056,072 bytes, below the 1 GiB guard. No complete JUnit result exists.
A one-second native stack sample was taken during the run; this is a diagnostic
attempt and cannot establish a pristine passing timing gate.

The failure was an obsolete failure-injection hook in
`test_leaf_product_failed_construction_rolls_back_binding_reservation`: the test
patched `_leaf_components`, which closed base-3 compilation now bypasses. The
test now also injects failure into the actual `reverse_leaf_components`
constructor, preserving its source, budget and all rollback assertions. Related
warm-leaf poison tests also cover that live constructor, so they cannot pass
merely by poisoning an unused path. All **33 tests** in the corrected kernel
test module pass in **2.34 seconds**. This repair does not convert the interrupted
serial run into a passing result.

A read-only collection audit found no substantial module-level proof build to
remove: generated parameter samples are small, and immutable T² loading is
already cached. Buffered diagnostic output explained the apparent collection
pause. Exhaustive compiler operations under test remain uncached.

The broader follow-up poison and inventory gate passes **90 tests in 7.00
seconds**. It covers the live closed constructor in the warm causal-parent and
independent-inventory tests as well. The original radix test intentionally
poisons generic compilation to prove use of the numeric division law, and the
digit-normalization test still reaches its generic constructor; those assertions
were preserved.

Final cold rechecks take 4.4241 seconds at N=32 and 16.5971 seconds at N=64.
Their scheduler frames, task evaluations, concatenation frames and retained
charges are identical to the earlier table. These small timing differences are
not a scaling improvement. The bounded sector product still needs to discharge
consumer dependencies earlier; merely deriving it after causal evaluation does
not remove the measured repeated work.

After the test-hook repairs, the final authored-tree fingerprint is
`a978d72c867bbc2b55651017d29d560aba6c7173ed0f08a42d578e580a960d39`
(v4). Production package bytes are unchanged from the wheel/radix checkpoint.
Final validation passes Ruff formatting/checks, **strict nonincremental mypy over
1,049 files**, and recursive structural checks with no recursion, package or
1,000-line violations. The complete serial suite has not passed on this tree.
Every Python process group has exited; none remains running in the background.
