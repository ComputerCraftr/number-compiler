# Antihydra integration evidence — September 12

Release **BLOCKED**. These records distinguish component execution from the
unresolved literal macro bridge and source-7 non-halting certificate.

- `components.log/json`: 312 selected tests passed in 14.03 seconds; the guard
  measured 14.57 seconds and 509 MB process-tree peak.
- `benchmark.log/json`: Python 32,768-return cold/warm execution exactly matches
  canonical one-return physical actions. Timings include cold kernel construction.
- `full-unit.log/json`: unchanged 300-second gate timed out near 97%, with one
  captured failure marker and no completed failure summary. This is not a pass.
- `final-components.log/json`: 332 passed, one validation case deselected,
  18.79 seconds. `factor-gate.log/json` separately passes the final stronger
  assertion requiring the actual factor 3, rather than accepting no factor.
- `isabelle.log/json`: Antihydra v65 passes in 15.35 seconds at 461 MB. Covers
  component semantics and actual admitted-replay physical counts; not universal
  literal section admission or the source-7 all-time barrier.
- `mypy.log/json`: 1,277 source files pass strict typing.
- `wheel-build-final`, `wheel-check`, `installed-cli`: fresh-wheel build,
  inventory and isolated installed commands pass. The smoke runner's exact
  source is preserved as `installed-smoke.py.txt`.
- `release-gates.log/json`: twelve explicit failures remain: three Antihydra
  obligations and nine unchanged Fermat/Mersenne assertions.
- `payload-audit.json`: actual shared retained-payload audit at 64 returns
  reports 16 forbidden, 8 unbounded-integer and 15 unknown payloads.
- `refinement.json`: all three reconstructed abstract failure paths exclude
  source h=8. These are not full-system counterexamples.
- `source-and-wheel.json`: final relevant source hashes and wheel SHA256.

The current branch adds explicit opt-in release failures for the missing
source-7 certificate, remaining macro rediscovery by the spacetime observer,
and shared retained-payload admission.
Existing Fermat/Mersenne and 196/Collatz gates remain unchanged.

See `docs/antihydra-production-and-proof-2026-09-12.md` for machine/archive
fingerprints, source/index semantics, certificate schema and precise proof scope.
