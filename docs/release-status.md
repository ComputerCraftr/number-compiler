# Current release gates

Version **0.60.0 is prepared; release remains blocked**. The hygiene migration does not close construction, mathematical or performance obligations. No release was tagged or published.

Current code evidence uses authored-source fingerprint version 5:
`795bca0f2d26d766644b1514c02923c4310e8b06edc7589fef55eed994cbe9c1`
(abbreviated `795bca0f` below). The [source-policy cleanup](sprints/week-of-2026-09-27/repository.md#september-29--source-policy-cleanup-and-regression-review) records consolidation of all 710 structural duplicate groups, independent review and final validation. The [original enforcement](sprints/week-of-2026-09-27/repository.md#september-29--executable-source-policy-enforcement) and [adversarial audit](sprints/week-of-2026-09-27/repository.md#september-29--adversarial-policy-and-memo-audit) retain their historical outcomes. Earlier P0/proof measurements remain scoped to `f64b7e72…dc68c1a9` in the [September 29 validation](sprints/week-of-2026-09-27/repository.md#frozen-validation-results); they do not certify this later tree. Historical results retain their original fingerprints in the [previous ledger](sprints/history/release-status-through-2026-09-27.md).

| Scope | Result | Source | Evidence | Remaining obligation |
| --- | --- | --- | --- | --- |
| Compact index and hygiene implementation | IMPLEMENTED | `f64b7e72` | Current unit run and independent migration review | Integer APIs remain bounded; no symbolic-scheduler or arbitrary-horizon performance claim. |
| Strict typing, lint, formatting, docs/proof indexes | PASS | `795bca0f` | Current `quality` suite | Maintain current ownership and schema checks. |
| Executable source policy | PASS: zero findings | `795bca0f` | Current policy JSON and active repository tests | Keep the unchanged line, recursion, clone and package-boundary assertions active. |
| Clean 0.60.0 installed wheel | PASS | `795bca0f` | 27 cold CLI contracts; developer/formal-source leakage checks | No publication authorized while other gates fail. |
| Full unit suite | BLOCKED: 7,652 pass / 42 fail | `795bca0f` | Every failure mapped to the existing baseline; no removed unit cases | 41 reverse/add construction failures and one special-number concrete-resolution failure remain. |
| Last architectural/primality P0 selection | BLOCKED: 13 pass / 50 fail | prior `f64b7e72` | Seven unchanged module selections; explicit diagnostic-identity migration | 35 reverse/add, six Collatz refinement, eight shadow recovery, one Antihydra non-halting obligation. |
| Focused Isabelle migration checks | PASS | prior `f64b7e72` | Prefix_Effect_Core and Shared_S_Arithmetic | Local checked results retain their assumptions and scope. |
| Aggregate Isabelle acceptance | BLOCKED: 60-second timeout | prior `f64b7e72` | Comma_Cylinder completed; Comma_Chart_Bridge started | Complete the aggregate build under 60 s / 4 GiB; no assumptions or proofs were weakened. |
| Collatz / Antihydra / Mahler production refinement | OPEN | `f64b7e72` | Active P0 assertions and proof inventory | Executable worklist, source/consumer binding and cold-construction bounds remain distinct from finite algebra and warm reuse. |
| A367620 / comma forest/fuel cutover | BLOCKED | `f64b7e72` | Registered proof chain and production admission | Complete residual classification, losing/winning instance, source entry and infinite weighted branch refinement. Existing admission remains required. |
| Global mathematics | OPEN | `f64b7e72` | No new global theorem claimed | Antihydra/Mahler all-time safety and Goldbach obligations remain. |
| Unfiltered runtime / growth acceptance | NOT CERTIFIED | `f64b7e72` | Unit/P0 evidence is not unfiltered acceptance | Complete the unchanged five-trial growth manifest and full serial release gate. |

The source-policy repository tests pass. The current full unit run and prior P0 run still fail on the listed production obligations. There are no new skips, expected failures or relaxed thresholds. Raw run paths are local evidence, not portable download links.
