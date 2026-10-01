# Current release gates

Version **0.60.0 is prepared; release remains blocked**. Current cleanup gives family and shared-runtime tests their correct owners,
centralizes support assertions/oracles, and repairs stale audit selectors.
Production arithmetic is unchanged; the private Collatz source-word comparator
and developer reference names now state their scope. The requested general 196 production cutover remains
**incomplete**; no release was tagged or published.

Current authored-source fingerprint (v5):
`f37500e1f794b43bc7d6ba7f7bb534fe385f1dd17854715dcbf6e80ec063aeca`.
Commands, assertion dispositions, independent review and evidence are in the
[October 1 test-ownership record](sprints/week-of-2026-09-27/repository.md#october-1--test-ownership-and-runtime-naming-audit).
The earlier [shared growth record](sprints/week-of-2026-09-27/shared.md#october-1--audited-homogeneous-growth-and-exact-gain-reuse)
retains its original fingerprint; those measurements do not certify this source.

| Scope | Result | Source | Evidence | Remaining obligation |
| --- | --- | --- | --- | --- |
| Strict mypy, pinned Ruff, formatting, source policy | PASS | `f37500e1` | Zero findings; 1,657 typed sources; Ruff 0.16.9 | No suppressions or policy thresholds changed. |
| Documentation, proof inventory, installed wheel | PASS | `f37500e1` | 96 sessions / 237 theories; wheel check 33.815 s | Inventory is not executable refinement. |
| Focused reverse, field-image and resource tests | 742 PASS / 1 FAIL | Prior `192b1d9b` | 45.87 pytest seconds; admission, forged bindings, deferred streaming, eviction and cleanup covered | Cold point query still opens higher temporal continuations. |
| Test ownership and audit selection | PASS | `f37500e1` | All 8,296 unit and 60 P0 instances preserved under explicit mappings; all 597 adversarial selectors resolve | Runtime validation is distinct from proof; existing failing assertions remain active. |
| Ownership/rename affected tests | 182 PASS / 1 existing FAIL; 63 reference-poison PASS | `f37500e1` | 2.27 and 0.63 pytest seconds; the failure is the relocated special-number compiler assertion | No new affected-test outcome; does not substitute for full units. |
| Full units | BLOCKED: 300-second timeout | `f37500e1` | 8,296 selected / 1,993 deselected; exact old-to-new collection equivalence; timeout after 98% progress, 1,032,521,024 sampled bytes | No completed full-suite result on this fingerprint; prior run had five failures. |
| Explicit P0 | 33 PASS / 27 FAIL | `f37500e1` | Same 60 instances in nine owner modules; exact relocation map and unchanged outcomes; 14.55 pytest seconds | Eighteen reverse, eight special-number, one global Antihydra non-halting failure. |
| Bounded completed-provider integration | Runtime PASS; concrete proof OPEN | Prior `192b1d9b` | D4→D8→D16→D20 with seed reconstruction poisoned; chronological right-child consumption; warm parent reuse after eviction | Prove the implemented publication, application and lifetime contract. This does not supply cold EXIT closure. |
| Reverse mirror/palindrome consumers | Runtime PASS | Prior `192b1d9b` | One completed output stream; reserved scratch, failure cleanup, no per-digit temporal point calls; partial traversal defers undemanded right boundaries | Shared spatial/output proofs do not prove the remaining temporal constructor. |
| Focused reverse Isabelle | Scoped PASS | Prior `192b1d9b` | Reverse_Digit_Terminal and Reverse_Growth_Admission; cached confirmation 5.726 s | Existing carry/growth/output lemmas do not refine the new complete source-selected constructor, which remains absent. |
| Aggregate Isabelle | Prior BLOCKED; not rerun | Prior `61ff4816` | Comma_Source_Entry_Witness completed; timed out while building Comma_Future_Source; 2,855,474,600 sampled bytes | Complete aggregate build under unchanged limits. |
| Reverse public output and performance | Bounded through 128; full cutover BLOCKED | Prior `192b1d9b` | D20 = `70446464506`; 120 literal-reference value checks; five trials per cold/warm/bypassed mode at 16/32/64/128; higher work 1,082/4,359/17,172/67,296 | Replace generic zero-growth descriptor and higher first-demand evaluator. Existing 256–1024 gates remain unavailable/failing. |
| Reverse reuse scope | Measured point reuse; no cold speedup established | Prior `192b1d9b` | D128 median CLI cold 1,955.437 ms, warm 1,788.158 ms, bypassed 1,798.196 ms; warm point 0.215 ms vs bypassed 1,780.409 ms | Repeated point reuse cannot certify a cold powered bound or eliminate construction per CLI process. |
| Reverse G161/P7 growth projection | Finite audit retained; producer OPEN | Prior `cd25708b` | Bounded 3,610-row audit; EXIT/ABSENT/duration/growth distinct | Authenticate P7 continuation and construct active EXIT successor/output; finite supplied-word tables are insufficient. |
| Shared homogeneous growth and Mahler readout | Runtime checks retained; executable proof OPEN | Prior `cd25708b` | Exact bounded ratios, rational enclosures and budgeted mechanical readout | Prove concrete enclosure/equality/CF loops; scaling cannot discover nonlinear branches. |
| Antihydra/Mahler and Collatz performance | Prior measured evidence retained | Prior `cd25708b` | Five-trial shared-growth sprint evidence; this reverse-only change does not establish new family speedups | Reuse and public-route attribution remain scoped to those measurements. |
| Other mathematical and production gates | OPEN | Separate historical evidence | Active assertions and proof inventory | Comma forest/fuel cutover, special-number recovery and global non-halting remain separate holds. |

Local frozen evidence:
`results/runs/20261001T205338Z-64257e7f879c4b48b63a40cd6c50e278`;
affected-test evidence:
`results/runs/20261001T210124Z-424fb43101be44f2a2d2df53afcdbe91`.
The relocation manifest verifies identical unit/P0 membership and unchanged P0
outcomes. Current full units timed out; no partial run is counted as a pass.
Prior reverse measurements and scoped proof confirmation retain source `192b1d9b`
at `results/runs/20261001T110639Z-7c1665dfe9ce4a139b1b67fdc5a206fe`.
The earlier aggregate proof timeout remains at
`results/runs/20261001T102022Z-25ac165db3be4e128ae85b0036cda621/aggregate-proof`.
Historical evidence does not certify the current source.

Execution metrics remain schema 8 and snapshot-only. Exact growth is observation
metadata, not a repeated work charge. Occurrence, semantic and projection reuse
remain distinct. No positive constructor or performance assertion was skipped,
weakened or converted into a passing refusal test. Probes retain 35 seconds/1 GiB,
proofs 60 seconds/4 GiB, and units 300 seconds/1 GiB.
