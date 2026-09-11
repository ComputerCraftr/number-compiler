# CLI and clock-cylinder validation checkpoint

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The [cross-family report](../../../docs/cli-clock-cylinder-cleanup.md) describes
the production changes, bounded research results and remaining growth.

Accepted frozen evidence lives in `final2/`. The initial `final/` pass reached
a CLI optional-radix typing error after its tests passed; it is not the accepted
final checkpoint. The corrected source is tested again under the same limits.

* **277 selected tests passed** on source
  `ba979a6662d83d1336a78b9250d3b5584ccb8b4e280e462ef35a9ce0ec59788d`.
  Manifest (local artifact: `final2/manifest.json`) records the source fingerprint, each command,
  JUnit count and process guard. Selected test groups cover CLI rendering and
  adversarial input, API regressions, shared owners, new decimal and power
  research, and repository/proof boundaries. This is not a full-suite run.
* Strict mypy (local artifact: `final2/mypy.log`) checks 1,188 source files. Ruff is clean across
  `src`, `devtools` and `tests`.
* Measurement (local artifact: `final2/measurement.json`) checks exact 128-phase lookup against
  per-width powering, instruments actual CLI render paths, and records the
  complete bounded terminal deck audits. [Measurement script](measurement.py)
  is retained for reproducibility; timings are one local lookup probe, not an
  end-to-end performance claim. The process guard excludes neither runtime
  imports nor fixed table construction, but the internal lookup timer does.
* Public cache probe (local artifact: `final2/public-cache.json`) reruns N8/16/32 exact indexed
  outputs, warm reuse and key-ablation controls on the frozen source.
* The previous Isabelle session (local artifact: `../port-valued-mealy-2026-09-10/isabelle-third.log`)
  proves the unchanged spatial Mealy theory. Its SHA-256 is rechecked by the
  final driver: `ec03d370c780df87560726d2dcfece458a5fecfeb53f65da294894d21c71c0d8`.
  No new temporal or full-germ Isabelle theorem is claimed in this checkpoint.

All heavy jobs run serially through the unchanged 35-second/1-GiB guard.
The driver checks the authored-source fingerprint after every job. The
previous full odd-16-bit Collatz occurrence validation is linked from the
[shared-owner checkpoint](../port-valued-mealy-2026-09-10/README.md); it is not
counted again as fresh testing here.
