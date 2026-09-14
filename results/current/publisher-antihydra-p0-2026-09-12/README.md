# Publisher and Antihydra follow-up evidence

Release **BLOCKED**. The reverse/add CLI now consumes the source-bound higher
publisher. Its higher continuation work remains an explicit release failure.
Antihydra cache admission passes; retained event support and the source-7
certificate remain separate obligations.

- `final-components.log/json`: 336 selected CLI, package, Antihydra, cache and
  repository-policy tests pass; 13.45 seconds including the process guard.
- `publisher-components.log/json`: 94 pass, one deselected, two preserved
  cutover assertions fail because higher continuations still execute.
- `antihydra-components.log/json`: 190 Antihydra, shared payload and policy
  tests pass, including forged-record and repeated-query checks.
- `certificate-components.log/json`: after the final admission repair, all
  28 publisher tests pass. Invalid certificates leave allocation unchanged;
  post-publication certificate substitution is rejected.
- `fixture-components.log/json`: 47 component tests pass after explicitly
  constructing the tile backend for tile-only audits and inspecting the actual
  publisher in production-route tests. Semantic and budget assertions remain.
- `mirror-components.log/json`: 12 tests pass, two validation workloads
  deselected. Fault injection checks empty fold workspaces and exact successful
  reuse after failure; synthetic accounting checks retain the replay poison gate.
- `antihydra-projection-benchmark.log/json`: cached and direct typed images
  agree at 2,048 returns. Total measured time is 0.194 versus 0.429 seconds;
  both charge 2,048 source-discovery steps. Peak nodes are 2,080 versus 448,
  with 384 retained in both cases.
- `payload-audit.json`: shared admission reports zero forbidden, oversized or
  unknown Antihydra payloads. Bounded record reconstruction is charged.
- `mypy.log/json`: 1,284 files pass strict typing.
- `isabelle-publisher.log/json`: the complete `Reverse_Residuals` session passes
  in 20.65 seconds at 456 MB. The new theorem proves one-step whole-list
  two-port refinement for every valid decimal pair word, with an all-196-iterates
  corollary and oracle-dependency checks. Python powered refinement remains open.
- `installed-cli.log/json`: a fresh isolated wheel passes finite Antihydra,
  196 publisher, Collatz, factor and forged-certificate checks. Fermat 4's
  UNKNOWN result is recorded as a blocker, not prime-bit coverage.
- `wheel-build.log/json`: wheel SHA256
  `e40b6d22642b6decf98058d31fd1153125c7dbad208e30662b55996e61431d38`.
  `source-and-wheel.json` records source hashes and exact wheel/source comparison.
- `release-gates.log/json`: 16 failures and six passes under the 35-second guard.
  Failures are two Antihydra obligations, nine Fermat/Mersenne assertions and
  five reverse/add continuation/cutover assertions. Payload admission now passes.
- `full-unit.log/json`: final frozen-code suite completes in 243.18 seconds,
  peak 632 MB, within the unchanged 300-second/1-GiB budget. It reports
  **4,929 passed, four failed, 1,277 deselected**. The four failures are the
  actual 196 clock work gate, two cutover-complete assertions, and unresolved
  special-number output. Earlier stale-backend fixture failures are repaired.
  This remains a failed unit gate despite meeting the watchdog budget.

Generated logs remain local under the repository's evidence policy. The
checked-in report describes their scope; passing components do not establish
powered executable refinement, compact Fermat/Mersenne recovery, complete
projection proofs or Antihydra non-halting.
