# Production P0 evidence — September 11

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The historical checkpoint used `release-audit/manifest.json`, now removed with
the generated artifacts. This summary records 368 passing selected tests, strict mypy, Ruff, all five Isabelle
theories, and serial guarded production measurements. Per-command limits remain
35 seconds and 1 GiB. `release_ready` is **false**.

Source fingerprint:
`afd0fb5d5c3b01ff0b66ce72187eacaed7d3e1efeb8f084752a6a89bcae4c8e0`.

- Results and independent CLI oracle checks (local artifact: `release-audit/comparison.json`)
- [Report and remaining hotspots](../../../docs/production-p0-integration.md)
- [Validation driver](validation_driver.py)
- [Comparison driver](comparison_driver.py)

The driver runs the unchanged process guard separately for each heavy job.
From the repository root, its Python imports require `PYTHONPATH=.` when invoked
by pathname. Choose a fresh output directory before reproducing a run; frozen
evidence must not be overwritten.

Earlier files and `final/` are development runs, including a corrected test
metric-name failure and a corrected mypy extent-union failure.
`final-verified/` is the successful intermediate checkpoint before primitive
emission-proof hoisting; its CLI output provides the before-work counters.
These intermediate results are not counted again in the final 368 tests.

Point queries use N=8,16,32. Full CLI and independent oracle checks use N=32,64.
Warm request reuse is deliberately separate from cold construction. Larger
unmeasured horizons and the complete test suite are not claimed green.
