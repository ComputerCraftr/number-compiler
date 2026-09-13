# P0 cylinder release evidence

Release remains **BLOCKED**. See the [acceptance ledger](../../../docs/cylinder-p0-release-gates-2026-09-12.md)
for the required production and Isabelle integrations.

- `validation.json` records the status, source fingerprint, static checks and open gates.
- `selected.*` records 86 passing selected tests; this is not the full release suite.
- `isabelle.*` records the complete `Etale_Primary_Carry` build, including exact
  coefficient-vector refinement and terminal zero/palindrome equivalence.
- `mirror-comparison.*` compares fresh finite 196 mirror demands through scalar
  points and the shared output-DAG consumer. These are single samples.
- `policy.*` records the passing line-count, recursion and package checks.
- `unit.*` records the frozen ordinary-unit timeout at the unchanged 300-second
  limit, near 98%, without a completed JUnit report.
- `optin.*` records the selected Collatz gate timeout at the unchanged 35-second
  diagnostic limit after two captured failure markers.
- `source-gates.*` records a complete rerun of those first two Collatz gates:
  both fail, with seven finite leaf applications and no production source-morphism
  compilation counter respectively.

Conditional checked factor output is accepted. These finite consumer improvements
do not certify cheap source-derived powered construction or a green release.
