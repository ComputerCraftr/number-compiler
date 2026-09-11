# Adversarial production quotient and dead-code audit — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Three read-only explorer agents audited reverse/add, Collatz, and shared
execution. The parent checked their claims against current call paths and ran
bounded reproductions. Production, tests, devtools, and configuration were not
changed. This is an audit, not a claim that the remaining quotients are solved.

## Confirmed findings

### 1. Repeated action validation is a measured production hotspot (P2)

`tile_kernel.py:393` validates every `_action()` access. The cold public
`ReverseAddPoweredTerm(196, 32).digit(0)` profile records **166,896 action
validations**, **166,674 decimal growth certificate validations**, and
**1,567,721 scoped-handle validations**, against **11 action publications**.
Action validation is the largest individual Python self-time entry: 1.221s
self / 2.719s cumulative in the instrumented run. These times overlap callers;
they must not be added together or treated as an achievable speedup.

There is a concrete local duplicate in `tile_scheduler.py:363`: `_children()`
validates the action and then calls `action_children()`, which validates it
again through `_action()`. The analogous causal-engine helper has already
been fixed (`tile_causal.py:103`); this audit does not attribute all validation
calls to the remaining scheduler duplicate.

Next action: reuse a checked record within a well-defined operation and remove
provable duplicate boundary checks. A persistent cache keyed only by action ID
or record identity is unsafe: `test_reverse_frobenius_actions.py:74` deliberately
mutates an already-used sector in place and requires rejection. Preserve those
adversarial guards. The `validated_signature_for()` docstring means one check
for that combined operation; it is not a promise of persistent memoization.

### 2. Active reverse morphism computes unused fallback metadata (P2)

In `tile_causal_pair_transfer.py:115`, multi-chunk decimal execution fetches
two wirings and initial ports before entering the loop. When `morphism` is
present, every iteration takes the morphism branch and continues at line 128;
all three values are used only by the fallback below it. The eligibility
predicate at line 71 also fetches each primitive law twice, triggering repeated
validation.

The three-cell probe exercises both directions, poisons the fallback, and
agrees with the independent scan oracle. In each direction it observes two
morphism applications **plus two unused wiring calls and one unused initial
ports call**. See `findings-probe-final.json`.

Next action: construct fallback metadata only when that branch is selected,
and fetch each checked primitive law once. This is avoidable work in a live
quotient path; it does not depend on solving the full temporal quotient.

### 3. Power-of-two radix projection rejects valid partial limbs (P1 correctness)

`projection/lazy_radix.py:298-316` uses `maximum_width` for lazy admission, then
reads every binary position in that upper-bound limb. `PoweredCollatzTerm.digit`
correctly rejects positions beyond the actual value. Therefore valid radix-64
digits raise during padding reads:

| Seed, zero steps | Radix-64 coordinate | Expected | Actual |
| --- | ---: | ---: | --- |
| 1 | 0 | 1 | `IndexError: 1` |
| 2 | 0 | 2 | `IndexError: 2` |
| 64 | 1 | 1 | `IndexError: 7` |
| 82 | 1 | 1 | `IndexError: 7` |

Reproduction: `PoweredCollatzTermPayload(PoweredCollatzTerm(1, 0), 64).digit(0)`.
The bounded matrix also checks exact full limbs and exterior coordinates.
This is reachable through the payload/lazy-radix API; the high-level Collatz
specification has a narrower radix policy. Next action: distinguish blank high
bits within a valid limb from an entirely exterior limb, without restoring an
eager exact-width query or swallowing unrelated errors.

### 4. Unreferenced Collatz boundary-proof module (P3)

`sequences/collatz/boundary_proofs.py` defines a boundary-proof collector and
validator. Searches for its module name and all three exported names find only
the module itself in `src`, `tests`, and `devtools`. It is a repository-internal
dead-code candidate, unlike the tested local-codec libraries below. No external
consumer compatibility claim is made. Next action: remove it if it is not a
supported external import, or explicitly integrate and test its intended owner.

### 5. Write-only eviction state (P3)

`hashlife/tiles/tile_results.py:285` initializes `_eviction_occurred`; line 933
sets it. There is no read or accessor in `src`, `tests`, or `devtools`. This is
dead retained state, not a material explanation for multi-second queries.

### 6. Legacy completion branch cannot handle canonical composite execution (P3)

`tile_scheduler.py:617-624` calls `causal_complete()` before the older temporal
and midpoint completion branches at lines 625 onward. For an exact
`PrimitiveTileKernelAdapter` and composite action, `causal_complete()` either
returns a result or raises; it does not decline. Thus the later composite
branches cannot execute for that canonical adapter. They remain relevant to
other/fake adapters and direct helper tests. This is duplicated maintenance
surface, not measured hot-path execution time. Separate that contract before
considering removal; do not delete the whole generic scheduler path blindly.

## Important quotient gaps that remain, rather than newly discovered fixes

The reverse primitive output morphism is connected, but
`reverse_active_transfer.py:18` declines composed consumers. A complete
successor-closed 196 context graph is still absent. The existing finite
context minimizer and conditional Isabelle theorem cannot generate that graph
or establish its total transition law by themselves. Current public point
execution still constructs substantial exact causal work:

| Fresh query, seed 196 | Unprofiled seconds | Causal frames | Exact causal fallbacks | Action publications |
| --- | ---: | ---: | ---: | ---: |
| `digit(0)`, 16 steps | 1.136 | 15,912 | 376 | 9 |
| `digit(0)`, 32 steps | 3.700 | 53,396 | 1,362 | 11 |

These are single trials with construction outside timing and exact arithmetic
verification afterward. They establish current work amplification in this
range, not an asymptotic lower bound. The prior
[uniform-run audit](../reverse-run-controls-2026-09-10/README.md) also records
the million-cell, four-event live query exceeding the unchanged 35-second
guard. Its symbolic arbitrary-width control proof is not a production speedup.

Collatz's radix-64 carry/output pipeline and powered local codec are tested
but do not replace `PoweredCollatzTerm`'s binary physical kernel. The architecture
explicitly says its streaming pipeline uses one stage per event and lacks
whole-event phase/extent admissibility for powering. The new finite Hensel
refinement is not a successor-complete quotient: 129/385 still alias and 524
sampled refined classes have conflicting successors. These candidates should
not be wired into semantic identity merely because they are disconnected.

The slow reverse unit test at
`tests/sequences/reverse_add/test_dyadic_hashlife.py:67` executes a real 64-step
point query and multiple diagnostics. The new 16/32-step measurements expose
work in that same production path. Do not weaken its accounting assertions to
hide the cost. No new full-suite runtime is claimed by this read-only audit.

## Candidates not established as production defects

- Scalar radix observations build a per-coordinate division application
  (`tile_radix.py:376`), while materialized tile projection has completed-stage
  reuse (`:192`). Their observation contracts differ, and the scheduler already
  shares action/results. Adjacent-digit reuse is a profiling candidate, not a
  proven missing safe quotient; forcing completion could worsen sparse queries.
- Diagnostic Collatz compilation builds the requested orbit and a sentinel
  orbit. This is opt-in extra work. Their tick semantics and products differ;
  the comment's single accelerated traversal refers to auxiliary channels.
  Duplicate equivalent execution has not been established here.
- Reverse morphism bindings are cleared with workspace leases. Tests require
  stale source rejection. Retaining those bindings without lifetime changes is
  unsafe; no cache-persistence bug is established by that clear operation alone.
- Width-sector observations cannot answer arbitrary digit queries. Local mirror
  symmetry also does not establish conjugacy of complete 43/5-port contexts.
  Neither is a ready point-cache quotient.
- Reverse `domain.py`, `local_interface.py`, `tile_sector_observation.py`, and
  the field-action/local-codec cluster have test/research users. Collatz's
  runtime-action/output-morphism/local-codec cluster does too. Inventory these
  as dormant on the public powered path, not wholly dead or safe to delete.
  In particular, Frobenius source-elision metadata is consumed by the explicit
  sector observer; a claim that it has no consumer would be false.
- Historical small-radix division admission, Collatz primitive-parent metadata,
  and width-first scalar observation have already been addressed. The partial
  limb bug above is a distinct defect in the current lazy path. Old `.pyc`
  files are not evidence of authored dead code.

## Evidence and limits

`public32-profile.json` and `public32.pstats` contain the instrumented query:
42,624,691 calls, 13.661s. Its separate 1.442s metrics measurement includes
`dataclasses.asdict(term.metrics())`, not just metrics collection. Use
`cold-public16.json` and `cold-public32.json` for unprofiled point timings.
All query results checked here agree with independent arithmetic/scan oracles;
the four radix failures above are intentionally retained audit findings.

`probe_findings.py` supplies the radix and dead-setup reproductions. Its first
invocation failed because the repository root was absent from `PYTHONPATH`;
the successful invocation used `PYTHONPATH=.`. The first profile-script type
check failed on untyped `pstats.Stats` attributes; those accesses were corrected.
All three final scripts pass mypy and Ruff. Initial failed logs are retained.
Heavy work ran serially under the unchanged 35-second/1 GiB process guard.
No full unit suite or Isabelle rebuild was needed for this read-only audit.

`manifest.json` records the unchanged authored-source fingerprint and evidence
hashes. Prior proof/test results remain prior evidence, not new validation of
an implemented optimization.
