# Current release gates

Updated 2026-09-20. Authored-source fingerprint:
`664702034548ee7ebd8964c65e0f8de127e8090aa8ccab9b5e3d8fd57651a61e`
(abbreviated below). It covers configuration, `src`, `tests` and `devtools`;
documentation is checked separately. **Release remains blocked.**

Evidence stems below refer to local files under
`results/current/repository-hygiene-2026-09-20/checks/`. They are not portable
download links. Exact historical scope and commands are retained in the
[weekly record](../results/current/2026-W38/README.md) and
[test-by-test disposition](hygiene-disposition.md).

| Scope | Result | Source fingerprint | Evidence | Remaining obligation |
| --- | --- | --- | --- | --- |
| 757/179 retirement and package boundary | PASS | `664702034548` | `final-installed-wheel`, `final-repository`; retired modules and all three assets absent | None for the retired implementation; removal does not construct its replacement |
| Strict typing, lint, formatting, policy | PASS | `664702034548` | `final-quality`; 1,429 typed files, 1,552 formatted files | No new suppressions or exclusions |
| Documentation and history | Navigation/checks PASS; historical provenance LIMITED | `664702034548`; docs checked separately | `final-quality`, six syntheses, weekly records, provenance and disposition | Some ignored authored summaries have no recoverable baseline copy; absent metadata remains labeled |
| Default unit selection | BLOCKED: 6,086 passed, 42 failed | `664702034548` | `final-unit-3`; 229.28 s, 300-second/1-GiB guard | 41 reverse/add temporal-return or sector-pullback obligations; one F4 concrete-resolution obligation |
| Architectural and primality P0 selection | BLOCKED: 44 failed, 6 passed | `664702034548` | `final-p0-2`; unchanged positive assertions | 36 reverse cutover failures and eight candidate-shadow primality failures; four other-family digit cutover cases pass |
| Focused and temporal aggregate Isabelle | PASS | `664702034548` | `final-isabelle-focused`, `final-isabelle-aggregate`; aggregate 29.57 s under 35 seconds/4 GiB | Scoped theorem statements retain their assumptions; this is not generic temporal construction |
| All registered Isabelle sessions | BLOCKED: TIMEOUT | `664702034548` | `final-isabelle-all`; 35.12 s under unchanged guard | Complete all-session acceptance remains unverified within the deadline |
| Five-trial 16–1024 growth manifest | BLOCKED: 80 measured, 25 timed out | `664702034548` | `final-growth`; all 105 requested trials attempted under 35 seconds/1 GiB per worker | Fixed-width depth 1,024 and growing-196 depths 128–1,024 lack measurements; the fully measured spatial series violates 24 logarithmic-increment envelopes |
| General family construction and global mathematics | OPEN | `664702034548`; prior experiments retain their own scope | Maintained research papers and active release tests | Generic 196 grammar and bounds; compact F/M terminal extraction; larger Antihydra retention and literal refinement; source-global Antihydra, Mahler and Goldbach obligations |

Of the 206 baseline failing cases, **79 retained cases now pass, 42 remain
failing and 85 were retired or rewritten**. Retired cases are not counted as
fixed. No skip, expected failure or successful-refusal substitute closes a
construction gate. Cleanup and focused proof success do not authorize release.
