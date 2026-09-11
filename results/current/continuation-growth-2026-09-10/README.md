# Continuation growth: final evidence

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Final authored-source fingerprint:
`fc2190a8495b9f34a8562215adad0609829bb35b8df256b2a660feb5a6f29ca1`.
All 431 selected tests passed with matching before/after fingerprints and
validated JUnit manifests. This is selected validation, not a full-suite run.

The summary (local artifact: `final2/validation-summary.json`) records 123.643 aggregate pytest
seconds. The identical 44-partition, 209,960-source mod9 sweep took 38.375
seconds, compared with 73.122 in the preceding
checkpoint (local artifact: `../future-consumer-cleanup-2026-09-10/final/validation-summary.json`):
about 48% less measured time. The branch-demand evaluator preserves coverage
while skipping unchosen widths and growth branches. This comparison does not
establish an end-to-end production speedup.

Validation also covers all 32,768 odd 16-bit Collatz sources with eight further
successors from each exact two-step Hensel image; the existing 1,016 small-ring
square controls; conditional pullback and composition; failed-publication
rollback; free Collatz carry/shift selection; complete bounded multiplication
refinement; and repository structural/proof-boundary policies.

Strict mypy passes 1,177 source files (log (local artifact: `final2/mypy.log`)). Ruff passes
across `src`, `devtools`, and `tests`; changed files were formatted before the
freeze. The local Isabelle theories are unchanged; their earlier checked
factorization proofs are not extended to a general continuation theorem here.

All heavy runs used the unchanged 35-second/1-GiB guard. The largest selected
test subprocess used about 478 MB. No test or audit was credited after a guard
failure. Earlier failed Collatz test/probe iterations outside `final2/` are
superseded by the passing frozen manifests and measured final probe.

## Production integrations and public-path checks

The frozen selection now includes public 196/Collatz future-tile execution,
resource inventories, and poison tests. The 196 right consumer composes only
carry-domain actions from the shared skew law, without exact intermediate pair
binding. Physical Collatz compiles branch-selected unary value views through
the actual tile interface dispatcher. Its scalar effect owns the law, with an
independent exhaustive 54-context regression. The shared Fermat/Mersenne
square kernel uses triangular products and three subsquares while keeping
exact coefficient arithmetic.

The public scheduler report (local artifact: `final2/public-production.json`) uses fresh public
terms at 8/16/32 steps and exposes retained-key dimensions. At 32 steps,
196/Collatz retain 2,305/1,024 completed results, of which 2,035/991 carry
boundary operands. Omitting only finite ports from the diagnostic grouping
still leaves 2,056/994 contexts. These are the remaining spatial occurrence
and boundary-discovery hotspots; this grouping is not a quotient certificate.
The report retains the actual finite leaf work and checks zero sequential or
retired interpreter execution. Both families remain RED on measured result
retention, without a false retired-image-publication blocker.

The square-only audit (local artifact: `final2/square-consumers.json`) separately tests complete
small-ring unary closure, sign cancellation and terminal pullback. Its work
rows report dense triangular square costs. An eight-digit schoolbook leaf now
uses 36 scalar products instead of 64; this is a work reduction in the shared
digit backend, not a speed claim for the native bigint fallback. General
multiplication/addition counterexamples remain negative controls for those
stronger consumers, rather than a rejection of unary squaring.

The actual tile width probe (local artifact: `final2/square-width-growth.json`) measures the
remaining fold/normalization hotspot: on its fixed bit pattern, maximum
folded coefficients grow from 3 to 86 over widths 8→256, with observed
width-256 carry intervals −49…49 (Fermat) and 12…49 (Mersenne). No fixed
carry alphabet is established. The full-ring unary partitions stabilize at
9/129/16/64 for F2/F3/M5/M7, exactly their sign-class counts; the demanded
observers find no further stable merging beyond that symmetry.

CLI smoke checks (local artifact: `final2/cli-smoke.json`) compare complete output numbers for
196, Collatz, Fermat and Mersenne with independent formulas/recurrences.
Fermat/Mersenne `nth` computes the numbers, not their primality bits. No new
unbounded temporal or prime-bit scheduler certificate is claimed.

The earlier 346-test checkpoint (local artifact: `final/validation-summary.json`) is preserved
as historical evidence. The final source and all report regeneration checks
are in `final2/`; failed exploratory invocations are not counted as successes.

## Exact final audits

All five research JSON audits below were regenerated against the final source
fingerprint, each with its adjacent `.guard.json` resource record:

- 196 free-action growth (local artifact: `final2/reverse-growth.json`): A32 retains 28,690
  nodes, of which 28,629 expressions are reachable; just two expressions are
  unreachable. Source ports stay 17, midpoint ports stay zero, and schemas
  plateau at 58. The A64 attempt fails at the same 30,000-node limit and rolls
  back to the valid 28,690-node arena.
- Cold demanded projections (local artifact: `final2/reverse-projections.json`): A32 admission
  alone retains 28,131 nodes; admission plus the first domain retains 28,179.
  The shared future-admission/value dependency explains why endpoint
  projection saves only a constant number of nodes.
- Small complete response interfaces (local artifact: `final2/reverse-consumer-residuals.json`):
  branch-masked response functions are canonicalized without expression IDs.
  At capacities 3/4, initial concrete context partitions 25/49 refine to 71/226.
  Initial successor conflicts are 42/189; independently verified refined
  conflicts are zero. These finite context partitions include an explicit
  overflow sink and are not general free-action residual classes.
- Multiplication and addition congruence (local artifact: `final2/power-congruence.json`):
  F3 refines 13→17 and M7 refines 52→64, reconstructing their carriers. Addition
  already fails on the sign/orbit carrier. F4/M11/M13 refinement is rejected
  before exceeding the fixed 4,096-cell table budget. No noninjective quotient
  table or scheduler certificate is published.
- Instrumented Collatz pipeline (local artifact: `final2/collatz-growth.json`): actual seed 27
  runs use 1/2/4/8/16/32 stages and 1/2/4/12/28/60 feed calls. Targets and
  valuations match the shared independent scalar owner. The primitive free
  consumer contains 76 factored and 1,963 Boolean nodes with three ports;
  all-context leaf rows distinguish 64/64 digits and are rejected as a
  compressing identity.

The fixed-point refinement algorithms have one owner:
`minimize_finite_observer` and its unary adapter. Requested primitive
Collatz rows are transient; the rejected permanent 1,152-pair table is absent.
Research evaluator counters charge actual demanded observations. Failed
construction restores identity storage while preserving attempted work and
discarded-allocation accounting.

See [the detailed cross-family audit](../../../docs/continuation-growth-audit.md)
for the operation counts, branch/admission distinctions, exact call sites,
and remaining theorem obligations.
