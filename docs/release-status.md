# Current release gates

Version **0.60.0 is prepared; release remains blocked**.
Reviewed 2026-10-26. This is the current disposition, not a run log.
Evidence below is scoped development evidence from a dirty checkout based on
Git `f33a96c0a34491d33361ad5b6e92781a82850a72`; it does not certify a release commit.

| Gate | Current disposition | Evidence owner / next requirement |
| --- | --- | --- |
| Strict mypy, Ruff, Pyright and formatting | PASS with zero findings across the complete maintained Python tree | [Current whole-tree quality evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#current-status--2026-10-26) |
| Repository source policy | PASS, including duplicate bodies, dependency direction and guarded launch paths | [Current audit evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26) |
| Pylance | Editor-specific review remains separate from the guarded Pyright batch | [October 25 evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#current-status--2026-10-26) |
| Installed wheel and minimum Python | Fresh wheel passes; the prior Python 3.11 smoke check remains separately recorded | [Current wheel evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26) and [minimum-version evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#runtime-and-diagnostic-evidence) |
| Complete default Python suite | PASS: native and Colima full selections complete within the 300-second limit | [Current full-suite evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26) |
| P0 release assertions | Reverse/add and Collatz pass; source-7 non-halting and candidate prime-bit holds remain | [Current P0 evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#runtime-and-diagnostic-evidence) |
| Shared carry, reverse and double-reverse refinements | Shared carry-period/sparse-row and finite double-reverse consumer sessions pass; remaining source-selection and signed-cut refinements stay open | [Scoped proof obligations](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#remaining-consumer-and-proof-gates) |
| Antihydra/Mahler cold integration | Shared balanced root publication and exact even-run guards pass runtime and kernel checks. Integer bypass work is reduced; a reliable Mahler/matrix cold-process speedup is not established | [October 26 evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#antihydra-and-mahler-cold-integration--2026-10-26) |
| Powered CLI integration and performance | No comma speedup established: cold/bypass workload exceeds 60 seconds; a warm repeat alone is insufficient. Other family refinements remain scoped | [October 25 evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#current-status--2026-10-26) |
| 2rev10 bounded temporal carry square | Runtime, scoped typing and concrete kernel refinements pass; seed-196 index-1,024 CLI median improves 1.77× cold / 2.19× warm. Unrestricted future closure remains open | [October 26 four-port evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#2rev10-four-port-and-outer-port-integration--2026-10-26) |
| Standalone 2rev10 macro summary | Open: no term-owned published occurrence cursor; explicit matrix traces are available | [Demand-laziness boundary](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#remaining-work) |
| Comma B1/B32/global and forest/fuel retirement | Graph instance and native reuse fixtures pass. Concrete B1 advances farther but exhausts its unchanged action/proof arena before completion. B32/global remain unaccepted; the cutover patch is unapplied and the artifact registry empty | [Current proof and retention evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#comma-near-reuse-and-crt-retention-repair--2026-10-26) and [pending patch](../devtools/cutovers/README.md) |
| Unrestricted constructors, primality and global non-halting | Open mathematical/production obligations | [Research scope](index.md#research-syntheses) and [formal proof index](proofs.md) |

Validation uses the [shared execution policy](development.md#reproducible-release-commands).
Release acceptance requires a clean committed source, the isolated acceptance
worktree, complete required selections and their applicable kernel builds.

Run counts, timings and run identifiers belong only in the linked sprint record.
Superseded dispositions are recoverable through Git; they are not active gates.
