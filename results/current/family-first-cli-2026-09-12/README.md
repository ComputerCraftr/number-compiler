# Family-first CLI migration evidence

The breaking CLI migration is implemented. Mathematical release status remains
**BLOCKED**. The [migration guide](../../../docs/family-first-cli.md) specifies
selectors, index units, output routing, budgets and proof scope.

## Component evidence

- `api-final.log/json`: 522 API and repository-layout tests pass, nine validation
  cases deselected; 20.22 seconds including the guard, peak 129 MB. This includes
  output-base boundaries, lazy observations, shared query ownership and changed
  physical-result rejection.
- `static-final.log/json`: strict mypy passes 1,291 files, including the new CLI
  benchmark. Ruff and `git diff --check` also pass.
- `isabelle-family-iteration.log/json`: the complete Antihydra session passes in
  16.75 seconds, peak 455 MB, under the unchanged 35-second/4-GiB limits. The new
  arithmetic theory checks oracle dependencies and proves generated parity-word
  skew application, composition, centered transport, ledger/minimum projections
  and exact prefix admission. Its guarded option is an arithmetic guard; it does
  not identify every Python constructor or physical roof with the literal TM.
- `physical-seal.log/json`: 133 focused Antihydra tests pass, ten CLI cases
  deselected. Both Python and CLI execution now use the same term owner. Tests
  reject changed physical fields and compare total arithmetic with guarded
  first-failure execution on a synthetic unsafe section.

## Audit conclusions

The arithmetic block retains a bounded chronological parity word, and demanded
physical roofs consume that word. Poisoning branch discovery after construction
does not prevent physical observation. Result-validation work is separately
charged. Partial arithmetic publication rolls back retained segments while
preserving work already spent.

Physical outputs have a charged issuance record and a source owner. Independent
payload auditing reconstructs their arithmetic and physical semantics. These
checks prevent the previously demonstrated cached-result mutation; they do not
replace the outstanding executable refinement theorem.

The bounded node ledger is not a measurement of allocated integer bytes.
Source discovery, roof arithmetic and operand-bit counters remain visible.
The Antihydra spacetime observer still has its separate no-rediscovery P0 gate.

## Final serialized validation

- `full-unit-final.log/json`: **4,987 passed, four failed, 1,277 deselected**;
  248.29 seconds including the guard, peak 627 MB. The unchanged limit is
  300 seconds/1 GiB. The four failures match the previous baseline: the 196 clock
  work gate, two reverse/add cutover assertions and unresolved special-number
  output. The migrated layout assertion and all new CLI/Antihydra tests pass.
  Repository policy runs as part of this suite.
- `release-gates-final.log/json`: **16 failed, six passed**, 4.00 seconds,
  peak 94 MB. These are the preserved two Antihydra, nine special-number and
  five reverse/add obligations. No assertion or watchdog limit was weakened.
- `installed-final.log/json`: a fresh isolated wheel passes package/source
  byte equality, resource admission, public API checks, all family-first term
  examples in the checker, Antihydra ledger/clock, checked M11 factor output,
  UNKNOWN exit status and old-command rejection. 8.68 seconds, peak 115 MB.
- `wheel-build-final.log/json`: wheel SHA256
  `d0d47c047302b41c397cc6fe52d7cc524e4e98453e9b50aadc024f54a7cd7774`.
  `source-and-wheel.json` binds it to the final source and theory hashes.
- `benchmark-final.log/json`: the included `benchmark_cli.py` measures a real
  512-return Antihydra value+ledger+clock+metrics query. Cold subprocess time is
  0.636 seconds; three runs with warm imports and fresh query owners take
  6.48, 2.77 and 2.53 ms. The query reports eight retained source blocks,
  456 kernel branch steps, 512 physical roof terms, 16 arithmetic validation
  block applications, 123 retained nodes and 136 peak nodes. Repeating
  information on the same query adds no work. These finite measurements do
  not establish cheap arbitrary-size source discovery.

The first wheel attempt without build isolation lacked setuptools in the test
environment. The normal isolated build succeeded; installation checks used
`--no-deps --no-index` with the resulting local wheel.

Generated logs remain local under the repository evidence policy. Passing
migration checks do not turn the failing unit or P0 gates green.
