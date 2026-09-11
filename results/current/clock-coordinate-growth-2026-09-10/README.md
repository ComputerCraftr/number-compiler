# Clock-coordinate growth evidence — September 10

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The final manifest records one frozen source tree and explicit theory hashes. All
accepted commands use the unchanged 35-second / 1-GiB process guard. This is a
focused validation checkpoint, not a full-suite result.

Frozen source fingerprint: `fd69557f326c36225d5e89ec2f2704df0c896d2d6bbc4febd95100cdda418471`.

## Accepted runs

| Job | Passed tests | Elapsed seconds | Peak MiB |
|---|---:|---:|---:|
| mypy | — | 3.53 | 220.5 |
| isabelle | — | 8.51 | 430.8 |
| focused | 72 | 7.57 | 77.3 |
| decimal-audit | — | 24.87 | 47.7 |
| collatz-audit | — | 0.63 | 47.2 |
| power-audit | — | 2.37 | 56.6 |
| public-cache | — | 17.72 | 83.2 |
| policy-structural | 32 | 8.83 | 439.7 |
| policy-boundary | 11 | 33.53 | 183.3 |
| ruff | — | 0.11 | 4.1 |

All five theories in `Temporal_Clock_Jumps` pass a clean child-session build.
Theorem groups reject all oracle dependencies. The source contains no `sorry`,
`oops`, or axiomatization admissions. The 72 focused tests include the new
clock/phase consumers, high-precision root poison, signed tangent payloads,
decimal growth rebase and successor conflicts, previous jump gates, and shared
event-memory dependencies. The 43 repository tests also pass. Strict mypy covers
1,198 source files; Ruff and `git diff --check` pass.

## Measurements and scope

- Decimal audit (local artifact: `final/decimal-audit.json`): 6,859 symmetric six-cell pair fields,
  13,718 successful checks for each algebraic identity, 1,665 alias fibers, and
  1,647 next-signature conflict fibers. Seed 196 at N16…N1024 retains N tangent
  IDs with zero hits and N charged primitive successors.
- Collatz audit (local artifact: `final/collatz-audit.json`): 16 phase keys, seven local skeletons,
  1,017/1,024 hits in the first sweep and 65,529/65,536 at extent 1,024. These are
  context sweeps, not accelerated trajectories. Exact suffix payload survives.
- Power audit (local artifact: `final/power-audit.json`): full Fermat rings have 5/9/17 depth
  actions; M5/M7/M13 generated trace carriers have 5/7/13. Independent Moore
  partitions agree exactly. Direct jumps through 1,024 and 10^12 use zero
  primitive successors after explicitly charged bounded enumeration. Each
  admitted clock has one actual hit on its second lookup. M11 order 990 fails
  pure-clock admission; trace zero is absent and terminal Moore has one class.
- Public cache (local artifact: `final/public-cache.json`): N32 retains 2,305 decimal and 1,024
  physical Collatz completed results. All counters equal the pre-change
  diagnostic baseline (comparison (local artifact: `final/public-comparison.json`)). These
  measurements provide no evidence of a public CLI speedup.

## Reproduction and development failures

The [validation driver](validation_driver.py) runs jobs serially, records the
guard reports and JUnit counts, and checks the frozen source after every job.
It can resume already accepted jobs only when source and theory hashes match.
The manifest (local artifact: `final/manifest.json`) records exact commands. The low-memory
Isabelle profile is `ISABELLE_IDENTIFIER=number-compiler-ports-proof` for the
installed `/Applications/Isabelle2025-2.app/bin/isabelle`.

Development logs are retained outside `final` and are not credited. Two
development proof searches timed out; explicit algebra replaced the expensive
searches. The final combined policy invocation also timed out after 40 dots;
its two complete test files were subsequently run separately under the same
unchanged guard. The timed-out `final/policy.*` is excluded from the accepted
manifest; `policy-structural` and `policy-boundary` are the accepted results.

See [the research report](../../../docs/clock-coordinate-growth-audit.md) for
carrier/observer distinctions, production admission limits and remaining growth
hotspots.
