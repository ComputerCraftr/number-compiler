# Current release gates

Version **0.60.0 is prepared; release remains blocked**. The gate and cache repairs are validated, but the full reverse/add HashLife cutover is incomplete. No release was tagged or published.

Current authored-source fingerprint v5:
`622418f8010524e0e2297719e36e32b50d02969886379202dd901fea4eb068f2`
(abbreviated `622418f8`). The [September 30 integration record](sprints/week-of-2026-09-27/shared.md#september-30--runtime-gates-applied-reuse-and-provider-contexts) contains assertion dispositions, review scope, measurements and local evidence references. Earlier snapshots remain historical evidence with their own fingerprints.

| Scope | Result | Source | Evidence | Remaining obligation |
| --- | --- | --- | --- | --- |
| Strict mypy, Ruff 0.16.9 and formatting | PASS: zero findings | `622418f8` | Frozen quality run; 1,609 typed sources | No suppressions, exclusions or thresholds changed. |
| Source policy, documentation and proof inventory | PASS | `622418f8` | Policy: 28.124 s / 798,114,872 sampled bytes; final documentation recheck | Inventory status is not checked production refinement. |
| Clean installed wheel | PASS | `622418f8` | 27 CLI contracts, installed Collatz cross-seed and Mahler parent-reuse checks; 31.746 s | Separate CLI processes remain cold. |
| Focused runtime, cache and reporting checks | PASS: 292 tests | `622418f8` | Exact outputs, issuer/context authority, poison tests, accounting and laziness | General reverse construction is covered by separate positive failing gates. |
| Collatz runtime and occurrence reuse | PASS for measured cases | `622418f8` | Five former flag-only cases and shared runtime checks pass; at N=1,024, same receiving seed uses 71 run actions warm versus 86 bypassed | At most one shared occurrence is consumed on this route. Complete constructor/lifecycle refinement and cold-construction bounds remain open. |
| Mahler complete-root and observer reuse | PASS for measured cases | `622418f8` | Warm parent skips cold construction; outer cached coefficients checked against admitted transfer; refused publications counted | Child-action reuse and complete source-constructor refinement remain open. A private producer capability does not prove a fabricated source record correct. |
| Ordinary Antihydra digit construction | Existing route preserved | `622418f8` | Exact bounded references and stress checks pass | No new structural work reduction was measured for digit-only queries. |
| Applicable Isabelle refinements | PASS: two focused sessions | `622418f8` | `Source_Cache_Integration` and `Antihydra_Mahler_Integration`; 5.751 s / 1,262,816,208 sampled bytes | Cached source transport assumes constructor admission. Checked Mahler composition/cap induction is not a complete Python constructor or non-halting proof. |
| Full unit suite | BLOCKED: 7,728 pass / 42 fail | `622418f8` | 287.536 s / 1,014,383,888 sampled bytes; per-test comparison finds no new failing obligations | Same 41 reverse construction/consumer failures and one F4 recovery failure; all migration regressions fixed. |
| Revised explicit P0 selection | BLOCKED: 17 pass / 43 fail | `622418f8` | Same seven module roles; obsolete declarations replaced by behavioral checks | 34 reverse, eight shadow-recovery and one Antihydra non-halting failure. No Collatz failure. |
| Five-trial 16–1024 queries | PARTIAL: 315 successes / 105 reverse failures | `622418f8` | All 420 cold/warm/bypassed samples retained; exact references checked | Reverse output remains unavailable. Whole-query timings do not supply separately timed construction, observation and conversion phases. |
| Compact indices and budgeted stress | PARTIAL | `622418f8` | K=0..3 equivalence; Collatz K=6/12 cycles; Antihydra/Mahler 10,000-return checks with 20,000-bit budgets | Reverse K=1..3 and stress requests still fail construction. Fermat K=2/3 exceed the unchanged output budget. Matching refusals are not construction acceptance. |
| Aggregate Isabelle | BLOCKED: 60.196-second timeout | `622418f8` | 3,822,442,616 sampled bytes; reached `Comma_Decade_Residual_Core` | Complete aggregate validation under unchanged limits. This was an incremental build, not a cold-build bound. |
| Decimal reverse completed occurrence and emission | INCOMPLETE | `622418f8` | Archive/live-owner audit; active D2/D4/D8 and later positive construction tests | Parent joins must consume completed provider images, publish output/extent/successor admission and support one spatial output traversal. Original-source recompilation is not that constructor. |
| Other mathematical and production gates | OPEN | `622418f8` | Active tests and proof inventory | Special-number recovery, comma forest/fuel cutover and global Antihydra/Mahler/Goldbach obligations remain separate. |

Runtime metrics no longer expose the removed completion/blocker declarations. Applied hits count actual admitted use; exact/transported retrieval and local/process location are separate. CLI reporting remains snapshot-only, while detailed Python resource audits remain explicit. Positive construction assertions remain active; none was converted to a skip, expected failure or success-on-refusal test. Raw run paths in the sprint record are local provenance, not portable downloads.
