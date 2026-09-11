# Clock quotient and growth evidence

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

See the [research and production report](../../../docs/clock-quotient-growth-audit.md).

The `final/` directory contains the formatted, frozen-source run. Its
source manifest (local artifact: `final/source-freeze.json`) records the authored-source SHA-256
and hashes of the supplied workbook and five text attachments. The workbook
was not changed. Earlier files outside `final/` record development iterations,
including the corrected initial assumption that a warm public query reaches
the microblock cache: it actually hits the preceding point-response cache.

## Reproduced results

* Public cold/warm caches and key ablations (local artifact: `final/final-public-cache.json`):
  N8/16/32 public 196 and physical Collatz indexed outputs agree with scalar
  oracles. N32 retains 2,305/1,024 completed-result entries, unchanged from the
  previous checkpoint. Each repeated point hits the point-response cache once
  with zero additional scheduler leaf work and result entries.
* Collatz phase identities (local artifact: `final/final-collatz-phase.json`): 32 zero-run
  occurrence extents reduce to eight cell-threshold actions or four bit-output
  actions. Counts are potential action reuse, not production cache gains.
* Square forcing lifetime (local artifact: `final/final-power-forcing.json`): old zero-birth
  mod-32 tangent actions collapse after five transports; live births and
  four-phase mod-5 clocks remain. The population experiment uses scalar
  constant-germ controls, not a full cyclic/negacyclic digit-field quotient.

The public probe is reproducible with
`python -m devtools.benchmarks.clock_key_growth_probe`. The phase report uses
`python -m devtools.proofs.collatz_harmonic_probe phase-normalization`.
The final manifest (local artifact: `final/final-manifest.json`) records every exact command and
guard result, with source fingerprint verification after each command.

## Validation scope

The final selected run passes **80 tests**: 35 focused owner/cache/admission
checks, two spatial/death validations, and 43 repository/proof-boundary checks.
JUnit manifests accompany each group. This includes all 64² Collatz two-cell
inputs under three carry ports, complete length-1…8 spatial response exploration,
all 6⁵ homogeneous phase sequences, and the four small-ring tangent controls.
The pre-existing 16-partition odd-source harmonic sweep was not rerun because
its temporal arithmetic was unchanged; it is not credited as fresh validation.

Every heavy process uses the unchanged 35-second/1-GiB guard. No failed guard
or earlier failed test run is counted. Strict mypy covers all 1,181 authored
Python files; Ruff covers `src`, `devtools` and `tests`. The causal fused-consumer
wiring correction is covered by its full 18-test neighboring module.

No new Isabelle theory or universal nonlinear successor theorem is claimed.
Workbook `WorkingGate`/`AblationV2` totals are supplied research evidence, not
an executable quotient gate reproduced by these tests.
