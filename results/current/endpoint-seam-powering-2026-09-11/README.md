# Endpoint-seam powering evidence — September 11

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

One frozen authored-source fingerprint and exact theory hashes cover every accepted
run in the manifest (local artifact: `final/manifest.json`). The unchanged process guard is
35 seconds / 1 GiB per command. All jobs execute serially.

Fingerprint: `2c0f77c2644b0aa07a3825bb8a3d2f95b247daa4772f6b90f395ffe5fe57fd5d`.

## Accepted validation

| Job | Tests | Seconds | Peak MiB |
|---|---:|---:|---:|
| mypy | — | 0.51 | 61.2 |
| isabelle | — | 9.17 | 427.5 |
| focused | 97 | 9.21 | 108.3 |
| decimal-widths-audit | — | 1.13 | 71.7 |
| decimal-width8-audit | — | 5.16 | 76.7 |
| decimal-neighborhood-audit | — | 0.97 | 47.3 |
| decimal-orbit-audit | — | 1.74 | 99.5 |
| decimal-power-audit | — | 0.51 | 48.5 |
| collatz-audit | — | 0.64 | 49.2 |
| power-audit | — | 2.30 | 57.6 |
| public-cache | — | 15.48 | 82.7 |
| policy-structural | 32 | 5.81 | 441.7 |
| policy-boundary-static | 10 | 2.10 | 76.3 |
| policy-boundary-runtime | 1 | 22.13 | 193.1 |
| ruff | — | 0.10 | 4.4 |

All five theories pass a clean `Temporal_Clock_Jumps` child-session build, with
no oracle dependencies. The source contains no `sorry`, `oops`, or added axiom
admissions. The focused 97 tests include exact endpoint image controls, cold
and warm dyadic memoization, poisoned primitive execution after a complete
bounded A1 table, all-port decimal identities, inverse-root/curvature poisons,
Collatz occurrence/budget controls, F/M Moore and readout-germ tests, and existing
jump/event-memory dependencies. The 43 policy tests pass in disjoint complete
selectors. Strict mypy checks 1,205 files; Ruff and diff whitespace checks pass.
This is not a full-suite result.

## Audits

- Reachable source widths (local artifact: `final/decimal-widths-audit.json`): the five supplied
  leading-nonzero source and A1 image counts match exactly.
- Width-8 endpoints (local artifact: `final/decimal-width8-audit.json`): A1…A32 counts
  70,659 / 48,266 / 36,511 / 34,063 / 33,448 / 33,429. At A32 there are
  90,033 cumulative equal-key publication hits, but 1,227,529 primitive
  transitions and materialized intermediate endpoints remain.
- 196 neighborhood (local artifact: `final/decimal-neighborhood-audit.json`): 2,269 distinct
  source pairs reduce to 2,259 at A1 and 2,231 at A8…A32.
- 196 single orbit (local artifact: `final/decimal-orbit-audit.json`): 4,095 distinct sources
  have 4,095 distinct A1 endpoints. No single-orbit alias is claimed.
- 196 dyadic memo (local artifact: `final/decimal-power-audit.json`): first-use primitives=N
  at N16…N1024; each identical warm power adds zero. Retained endpoint
  values=N and result keys=2N-1. Child endpoint reuse is not a new orbit alias.
- Collatz endpoint frontier (local artifact: `final/collatz-audit.json`): odd16 endpoint counts
  24,576 / 19,968 / 14,352 / 9,029 / 4,474 at A1…A16. A16 frontier construction
  still costs 195,658 primitive transitions. Exact accelerated ticks and odd
  targets are kept; physical tick semantics are not discarded.
- F/M depth/readout germ (local artifact: `final/power-audit.json`): the full admitted prime
  carriers retain Moore counts 5/9/17 and 5/7/13 with no extra germ classes.
  Supplied local-depth examples are not independently extracted candidate
  certificates. M11 retains its observer/admission negative controls.
- Public cache (local artifact: `final/public-cache.json`): all counters equal the prior frozen
  report. At N32, decimal and physical Collatz retain 2,305 and 1,024 results.
  No production CLI speedup is inferred from the research frontier merges.

The measurement checks (local artifact: `final/measurement-checks.json`) compare the reported
counts and public baseline explicitly. Future congruence of equal exact
endpoints is certified by the generic deterministic-kernel theorem; the
frontier reports do not invent a sampled zero-conflict counter.

## Reproduction and limits

The [driver](validation_driver.py) records exact commands, guard outputs,
JUnit counts, source hashes and theory hashes, and verifies the fingerprint
after each command. Resuming skips accepted jobs only on the same fingerprint
and theory hashes. Isabelle uses the installed application with the existing
`ISABELLE_IDENTIFIER=number-compiler-ports-proof` low-memory profile.

Development failures and intermediate runs outside `final` are retained but
are not credited. The final run needed no timeout or memory-budget relaxation.
It establishes semantic endpoint closure and the listed bounded executions;
it does not certify sublinear first-use HashLife work, global germ equivalence
for stronger observers, or candidate-to-clock extraction.

See [the research summary](../../../docs/endpoint-seam-powering-audit.md) for
implementation ownership, carrier distinctions and remaining production growth.
