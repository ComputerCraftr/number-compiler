# Current release gates

Updated 2026-09-20. Last aggregate-validation authored-source fingerprint:
`664702034548ee7ebd8964c65e0f8de127e8090aa8ccab9b5e3d8fd57651a61e`
(abbreviated below). It covers configuration, `src`, `tests` and `devtools`;
documentation is checked separately. **Release remains blocked.**

The subsequent Mahler safety integration has separate focused evidence in the
[research synthesis](research/antihydra-mahler.md#original-mahler-fractional-safety).
It reuses the Antihydra source orbit and checks finite fractional-safety
certificates; it does not close the source-seven barrier. The aggregate
results below retain their earlier fingerprint and have not been rerun for
that addition.

Evidence stems below refer to local files under
`results/current/repository-hygiene-2026-09-20/checks/`. They are not portable
download links. Exact historical scope and commands are retained in the
[weekly record](../results/current/2026-W38/README.md) and
[test-by-test disposition](hygiene-disposition.md).

| Scope | Result | Source fingerprint | Evidence | Remaining obligation |
| --- | --- | --- | --- | --- |
| Direct cylinder forcing/reset recovery | 217 focused checks PASS; 14 unchanged reverse/add cutover FAILURES; focused spatial Isabelle and whole-tree quality PASS | `605e76066c6f` | `results/current/future-grammars-agents-2026-09-20/`: `direct-events-frozen-tests`, `direct-events-proofs-v8`, `direct-events-frozen-measurements`, `direct-events-frozen-quality` | Carry-SLP round trip removed from research consumer; temporal boundary discovery, complete source refinement and production cutover remain open |
| 757/179 retirement and package boundary | PASS | `664702034548` | `final-installed-wheel`, `final-repository`; retired modules and all three assets absent | None for the retired implementation; removal does not construct its replacement |
| Strict typing, lint, formatting, policy | PASS | `664702034548` | `final-quality`; 1,429 typed files, 1,552 formatted files | No new suppressions or exclusions |
| Documentation and history | Navigation/checks PASS; historical provenance LIMITED | `664702034548`; docs checked separately | `final-quality`, six syntheses, weekly records, provenance and disposition | Some ignored authored summaries have no recoverable baseline copy; absent metadata remains labeled |
| Default unit selection | BLOCKED: 6,086 passed, 42 failed | `664702034548` | `final-unit-3`; 229.28 s, 300-second/1-GiB guard | 41 reverse/add temporal-return or sector-pullback obligations; one F4 concrete-resolution obligation |
| Architectural and primality P0 selection | BLOCKED: 44 failed, 6 passed | `664702034548` | `final-p0-2`; unchanged positive assertions | 36 reverse cutover failures and eight candidate-shadow primality failures; four other-family digit cutover cases pass |
| Focused and temporal aggregate Isabelle | PASS | `664702034548` | `final-isabelle-focused`, `final-isabelle-aggregate`; aggregate 29.57 s under 35 seconds/4 GiB | Scoped theorem statements retain their assumptions; this is not generic temporal construction |
| All registered Isabelle sessions | BLOCKED: TIMEOUT | `664702034548` | `final-isabelle-all`; 35.12 s under unchanged guard | Complete all-session acceptance remains unverified within the deadline |
| Five-trial 16–1024 growth manifest | BLOCKED: 80 measured, 25 timed out | `664702034548` | `final-growth`; all 105 requested trials attempted under 35 seconds/1 GiB per worker | Fixed-width depth 1,024 and growing-196 depths 128–1,024 lack measurements; the fully measured spatial series violates 24 logarithmic-increment envelopes |
| General family construction and global mathematics | OPEN | `664702034548`; prior experiments retain their own scope | Maintained research papers and active release tests | Generic 196 grammar and bounds; compact F/M terminal extraction; larger Antihydra retention and literal refinement; source-global Antihydra, Mahler and Goldbach obligations |
| Original Mahler fractional-safety integration | Focused Isabelle, certificate/API checks and quality PASS | `c46c9dc834fe` | `results/current/mahler-safety-integration-2026-09-20/`: `final-build`, `final-tests`, `quality` | Finite 46/64 exclusions and necessary all-time residue conditions only; broader selected tests retain one existing reverse/add construction failure; no source-seven non-halting certificate |
| Joint Mahler source/guard transport | Focused mathematical proofs and bounded constructor/observer checks PASS; non-halting P0 FAILS | `e499946ef765` | `results/current/mahler-joint-transport-2026-09-20/`: `final-proof`, `validated-tests`, `final-quality`, `validated-refinement` | Full runtime/worklist refinement, a safety-preserving global prime/carry abstraction, and an all-time certificate remain open; this research integration is not a production cutover |
| Reachable Mahler event grammar and repetition obstruction | Focused theorem/grammar/quality checks PASS; selected release checks retain two FAILURES | `18d66988222d` | `results/current/mahler-future-grammar-2026-09-20/`: `validated-proof`, `validated-tests`, `validated-quality`, `validated-grammar` | General parameter-changing pumps, all-time source realizability and construction bounds remain open; no production cutover or non-halting verdict |
| 196 and Mahler future/spatial grammar research | 286 focused checks PASS; 15 selected P0 checks FAIL; three focused Isabelle sessions PASS | `e4267e386d6e` | `results/current/future-grammars-agents-2026-09-20/`: `final-focused`, `final-proofs`, `final-mypy`, `domain-before/after`, spatial probes; weekly scope below | 196 spatial compression still has roughly quadratic temporal construction; Mahler domain pruning reduces finite search but does not prove general temporal closure, complete worklist refinement or non-halting; no CLI cutover |
| Centered production-algebra bridge and reverse/add re-entry measurement | 362 focused checks PASS; same 15 P0 FAILURES; focused Isabelle and whole-tree quality PASS; 70 research trials complete | `42862bb0f8c9` | Same evidence directory: `geometry-final-tests`, `geometry-final-proofs`, `geometry-final-quality`, `geometry-pair-final-measurements.json`; independent reviews on this source | Finite Mahler construction now uses production skew composition and the checked Antihydra centered chart. Reverse/add remains roughly quadratic in temporal horizon; research results do not authorize CLI re-entry or close full scheduler/worklist refinement and non-halting obligations |

Of the 206 baseline failing cases, **79 retained cases now pass, 42 remain
failing and 85 were retired or rewritten**. Retired cases are not counted as
fixed. No skip, expected failure or successful-refusal substitute closes a
construction gate. Cleanup and focused proof success do not authorize release.
