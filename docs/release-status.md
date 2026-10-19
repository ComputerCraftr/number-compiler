# Current release gates

Version **0.60.0 is prepared; release remains blocked**.
Reviewed 2026-10-18. This is the current disposition, not a run log.
Evidence below is scoped development evidence from a dirty checkout based on
Git `068827840bf80120b5bb6e8bd55cc202323466b8`; it does not certify a release commit.

| Gate | Current disposition | Evidence owner / next requirement |
| --- | --- | --- |
| Strict mypy, Ruff, formatting, source policy and documentation | Passing whole-tree checkpoint | [Current quality evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#validation-provenance) |
| Strict Pyright / Pylance | Under-10,000 tranche target reached; strict gate remains red and editor review remains open | [Toolchain work](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#remaining-work) |
| Installed wheel and minimum Python | Fresh wheel and Python 3.11 checks pass | [Packaging evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#validation-provenance) |
| Complete default Python suite | Completes within the deadline; sole failing assertion is the existing F4 concrete-resolution hold | [Latest full-suite evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#validation-provenance) |
| P0 release assertions | Current selection passes reverse/add and Collatz; existing non-halting and candidate prime-bit holds remain | [Current P0 evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#validation-provenance) |
| Shared carry, reverse and double-reverse refinements | Affected sessions pass; no aggregate proof acceptance claimed | [Scoped kernel evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#validation-provenance) |
| Powered CLI integration and performance | Partial: bounded projection improvements are measured; Fermat/Mersenne live adjacent-summary consumers and their CLI evidence remain missing | [Integration evidence and remaining consumers](sprints/week-of-2026-10-11/nc17-source-rings.md#october-18--bounded-default-coverage-and-packed-consumer-follow-up) |
| Standalone 2rev10 macro summary | Open: no term-owned published occurrence cursor; explicit matrix traces are available | [Demand-laziness boundary](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#remaining-work) |
| Comma B1/B32/global and forest/fuel retirement | Blocked: concrete B1 acceptance is incomplete; forest admission remains active. The rebased cutover patch remains unapplied | [Comma proof evidence](sprints/week-of-2026-10-11/comma.md) and [pending patch](../devtools/cutovers/README.md). Passing generic/C1 bridges do not close concrete publication. |
| Unrestricted constructors, primality and global non-halting | Open mathematical/production obligations | [Research scope](index.md#research-syntheses) and [formal proof index](proofs.md) |

Validation uses the [shared execution policy](development.md#reproducible-release-commands).
Release acceptance requires a clean committed source, the isolated acceptance
worktree, complete required selections and their applicable kernel builds.

Run counts, timings and run identifiers belong only in the linked sprint record.
Superseded dispositions are recoverable through Git; they are not active gates.
