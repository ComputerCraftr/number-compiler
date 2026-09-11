# Continuation and growth evidence

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This directory records the guarded focused checks for the Collatz free
directional consumer, its growth edge, the seven workbook witnesses, and the
neighboring reverse/add and power-number continuation work.

The Collatz implementation and its limits are documented in
[`docs/collatz-free-consumer-growth.md`](../../../docs/collatz-free-consumer-growth.md).
The deterministic growth report (local artifact: `collatz-free-consumer-growth.json`) records
the fixed-context fibers, the 64/64 all-context obstruction, growth support,
the seven workbook witnesses, and the linear A1..A32 streaming inventory.
It instruments a real seed-27 pipeline: stage counts and peak live pending
quotients grow `1,2,4,8,16,32`; feed calls grow `1,2,4,12,28,60`; every target
and valuation matches the scalar oracle. The compiled free primitive has 76
factored nodes, 1,963 Boolean nodes, and external port arity three.

Final guarded checks:

- `collatz-focused-final.log`: 40 passed, 10 validation cases deselected;
- `collatz-focused-final.guard.json`: completed in 3.91 seconds with a
  78,414,376-byte sampled peak;
- `collatz-mypy-final2.log`: strict mypy passed all eight selected source/test
  files;
- `collatz-mypy-final2.guard.json`: completed in 0.49 seconds with a
  53,821,920-byte sampled peak;
- `collatz-probe-final.guard.json`: the instrumented growth report completed in
  0.71 seconds with a 48,497,120-byte sampled peak.

The earlier `collatz-focused.log` is superseded. Its single failure showed the
test had declared the occurrence digit as an input to the growth-only query.
The corrected test constructs the intended carry/shift-only interface and
proves that the digit port is absent.
