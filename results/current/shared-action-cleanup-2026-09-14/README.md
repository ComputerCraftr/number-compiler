# Shared-action cleanup checkpoint

This checkpoint records the first applied changes from the
[assigned cleanup](../../../docs/shared-action-cleanup-2026-09-14.md).
It does not close the multi-family release hold.

Authored-source fingerprint:
`6e8b8a5403ed367165a722d9d9451f2951a3bcfaf99a07648db8d5c7b1f74064`.
Wheel SHA-256:
`897cd5197c5d63ab192456f1c69c37ca63a1b6ed164cb6ff77486f2f40d8d2bb`.

Implemented:

- One-query reuse of identical Antihydra tape/twisted and Hensel/Mahler demands,
  preserving requested labels and recording `query_observer_reuses`. This is
  observation reuse, not a source/action identity substitution.
- A canonical `Shared_S_Arithmetic.S_Arithmetic_Skew` theory, with compatibility
  wrappers for existing étale observers and explicit identity/composition maps
  for Antihydra's linear fields and Collatz's clock/cylinder-prefix fields.
- Independent proof-agent review of the actual applied maps and their scope.

Validation on the implementation checkpoint:

| Check | Outcome | Guard elapsed seconds |
|---|---|---:|
| CLI query-context tests | 41 passed | 1.854 |
| Shared_S_Arithmetic build | Pass | 9.158 |
| Temporal_Clock_Jumps build | Pass | 15.186 |
| Etale_Primary_Carry build | Pass | 28.588 |
| Antihydra build | Pass | 20.894 |
| Typing over src/tests/devtools | Pass, 1,316 files | 0.989 |
| Ruff over src/tests/devtools | Pass | 0.111 |
| Repository policy | Pass | 10.286 |
| Wheel build | Pass | 2.610 |
| Installed-wheel inventory and CLI checks | Pass | 6.137 |

Every listed build uses 35 seconds / 4 GiB. The other listed checks use
35 seconds / 1 GiB. Logs and process guards are retained locally under the
repository's generated-evidence ignore policy. `source-wheel.json` identifies
the source and installed wheel for the packaging checks.

The full unit suite, whole-tree result archives, growth manifest and performance
comparisons were not rerun for this initial cleanup checkpoint. Their preceding
red results remain in force; no fresh all-family pass is claimed.

The prime prefix interner and Antihydra arithmetic-publication proposals were
not applied: review found incomplete authority/eviction/accounting contracts.
Those agents own revision and independent review. The next family constructor
and proof waves remain assigned in the cleanup ledger. No conditional theorem,
unsupported cache authority or unimplemented constructor was marked complete.
