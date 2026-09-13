# Recurrence removal component checkpoint

Release remains BLOCKED. These are selected checks from the recurrence-removal
checkpoint before subsequent certificate-admission and Isabelle work. They do
not attest the later working tree, a full-suite run, or a frozen-source release.
The two pytest selections overlap. No source fingerprint was captured for this
checkpoint; none is inferred retroactively.

- Classification/layout selection: 84 passed, guard 4.38 seconds.
- Compiler/quotient/cache/policy selection: 135 passed, guard 14.01 seconds.
- Candidate shadow-jet P0 gate: four failures, guard 1.26 seconds.
- Strict mypy: 1,254 source files, guard 1.33 seconds.

The accompanying logs and process-guard JSON preserve these outcomes and the
resource limits. The four failures are unresolved default classification of
F4, F5, M11 and M13. Failure-handling tests are not extraction evidence.
