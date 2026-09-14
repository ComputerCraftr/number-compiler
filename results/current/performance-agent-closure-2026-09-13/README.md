# Frozen performance validation — September 13

**Release status: BLOCKED.** The implementation and remaining construction/proof
obligations are described in the [coordinator report](../../../docs/performance-agent-closure-2026-09-13.md).

Source fingerprint: `fd5228627fe13896b662c7ec617bc4993917d26dcefd0c3ce755594d28d019a6`.
Wheel SHA-256: `01c4924341f5b2f0c2140b0320fe6112151376a28c29f2a1b888894f9f83f585`.
[Source inventory](source-freeze.json), [installed wheel/source comparison](wheel-source-match.json),
[independent audit](independent-review.json), [machine-readable summary](summary.json).
All 501 packaged Python files match the frozen tree. No release sign-off is granted.

## Validation result

- [Full unit suite](full-unit.log): **5,127 passed, four unchanged failures, 1,277 deselected**;
  [guard](full-unit.guard.json): 268.49 seconds, 696,959,960 sampled peak bytes, within 300 seconds/1 GiB.
- [Explicit unchanged P0 selection](explicit-p0.log): **15 failed, seven passed**.
- [Installed wheel](installed-wheel.log): family-first syntax, checked M11 factor,
  output, budget and migration contracts pass.
- [Authored-source typing](authored-mypy.log), [Ruff](authored-ruff.log), and
  [structural/ownership policy](policy.log) pass.
- Whole-directory [mypy](whole-tree-mypy.log) and [Ruff](whole-tree-ruff-final.log) are
  blocked by older result-artifact module duplication and formatting, separately
  from the passing `src tests devtools` checks. No exclusion or assertion was weakened.
- [Prime Isabelle](isabelle-prime.log), [reverse/add](isabelle-Reverse_Residuals.log),
  [étale](isabelle-Etale_Primary_Carry.log), and [Antihydra](isabelle-Antihydra.log)
  build within their 35-second/4-GiB guards. The first [temporal build](isabelle-Temporal_Clock_Jumps.log)
  timed out while constructing its reverse/add parent heap. Subsequent explicitly
  guarded heap/build attempts, if present, are recorded separately.

## Paired prime latency

Five samples per condition; units are milliseconds. Acceptance is at most the
baseline median plus `max(10%, 1 ms)`. Warm probes also execute cache-bypassed
candidate controls and compare exact results. They retain an initial cold query
separately from five warm queries.

| Condition | Baseline median | Candidate median | Tolerance gate |
|---|---:|---:|---|
| cold-current / prime | 83.237 | 86.615 | PASS |
| cold-current / prime-start | 76.774 | 79.980 | PASS |
| cold-historical / prime | 146.756 | 119.420 | PASS |
| cold-historical / prime-start | 116.192 | 96.523 | PASS |
| warm-current / prime | 16.947 | 1.365 | PASS |
| warm-current / prime-start | 9.884 | 1.272 | PASS |
| warm-historical / prime | 34.959 | 1.183 | PASS |
| warm-historical / prime-start | 1.407 | 1.042 | PASS |

Covered warm queries report zero repeated factor discovery. This is bounded
process reuse; it is not an arbitrary-size source construction or full executable
refinement theorem. The supplied wheel paths and commands are retained in the
corresponding `.guard.json` files and frozen acceptance manifest.

## Cross-family and growth evidence

[196](cold-196.log), [Antihydra](cold-antihydra.log), and
[Fermat/Mersenne](cold-special.log) have five-sample fresh installed comparisons.
The original combined [family batch](cold-families.guard.json) and five-pair
[Collatz batch](cold-collatz.guard.json) timed out at 35 seconds. Five separately
guarded Collatz pairs are summarized [here](cold-collatz-pairs.json); their full
measurements do not erase the original batch failures.

The [unchanged growth manifest](growth-manifest/report.json) attempted all
**105 trials**, covering horizons 16–1024 with five trials per request.
Guard outcomes: **{'completed': 80, 'timeout': 25}**. Final status: **RED**;
`collection_complete=False`. Missing metric rows remain
missing, not zero. Every worker was capped at 35 seconds/1 GiB; the controller
only serialized and aggregated them.

The manifest measures setup, observation, diagnostics, physical-action counts,
concrete construction counters and retained state. It does not furnish every
requested independent discovery/rendering phase or a complete all-family powered
bound. Unavailable instrumentation and uncovered constructor obligations remain red.

The new prime theories establish numerical Phi, local postorder existence,
prefix restriction and rank/select component laws. The full Python shortcuts,
lease lifecycle, budget/cleanup simulation and unbounded construction bounds are
not certified. Passing these sessions does not discharge the 196, Collatz,
Antihydra or Fermat/Mersenne production refinement gates.

## Final Antihydra and heap follow-ups

The [installed spacetime comparison](antihydra-installed-spacetime-summary.json)
performs five actual CLI calls per wheel at 2,048 returns, with one demanded
projection per call and identical semantic output. Median time is 224.25 ms for
the current baseline and 235.46 ms for this candidate. Batching saves 720 charged
projection terms (470,539 → 469,819) but adds 32 peak workspace nodes; it does not
show a latency improvement here. Both versions visit 2,048 retained support
sections. No powered-observation closure is credited to this optimization.

An explicit [reverse/add heap build](isabelle-reverse-heap.guard.json) also reached
the 35-second timeout. The temporal session therefore remains without a completed
current build under the unchanged guard. The passing component sessions are not
used to infer that it passed.

The saved reproduction scripts also pass Ruff and the final repository structural
policy rerun: [32 passes](final-artifact-policy.log). The [final source check](final-source-check.json)
confirms that the measured production/test/tool fingerprint is unchanged.
