# Current validation and release status

Latest checkpoint: [two-sided tile execution](../hashlife/HASHLIFE_TWO_SIDED_CHECKPOINT.md),
source `994fa53f9182`: **4,348 passed, ten unchanged absorption failures, 380.09 s**.
Ruff, strict mypy and structural checks pass. Deep absorption, production cutover
and the serial 300-second release gate remain incomplete. Earlier checkpoints
below are historical evidence.


Final frozen source `64244f87626f`: **4,324 passed, 10 failed** in **386.08s**
(serial, unfiltered). Ruff, strict mypy and recursive structural checks pass.
The failures are the ten unchanged powered-output absorption gates. The
five-minute release ceiling and production cutover remain unmet.
See [the complete checkpoint](../hashlife/HASHLIFE_BOUNDARY_QUOTIENT_CHECKPOINT.md).

## Previous frozen full-suite checkpoint

The earlier frozen tree passed **1,901 tests in 519.85 seconds**, including repository
recursion and global 1,000-line source-file checks. Whole-tree Ruff passed;
strict mypy passed all 214 source files. The largest source file has 905 lines.
The validation record (local artifact: `../../../results/diamond_validation_v2.json`) contains the exact
commands and source fingerprint.

This run includes the final reset-key canonicalization, singleton-port erasure,
foreign/wrong-sort publication rejection, exhausted-budget preflight, and
reservation rollback regressions, as well as the earlier future-tape probes.

Passing correctness tests does not close the missing certified-family diamond
routing or the cold N=256 performance gates. The targeted 135-test report below
is historical evidence for an earlier carrier, not current release validation.

## Historical v0.59.9 validation results

## Bounded temporal HashLife cutover

The current production release path was validated with:

```text
135 passed in 17.89s
```

The targeted command covers:

- temporal quotient integrity;
- reverse H=20 carry-cut quotient;
- HashLife behavior-growth metrics;
- block and Collatz block powering;
- dyadic HashLife;
- reverse powered-term exactness;
- reverse temporal release probe;
- spacetime cache/identity integrity;
- carry-action and live-carry itinerary regressions;
- reverse and Collatz forcing morphisms;
- causal spacetime exactness;
- repository policy and layout.

No targeted test failed.

## Production invariants exercised

```text
unquotiented recursive application nodes       0
raw temporal scalar length fields              0
raw temporal span fields                       0
raw SpacetimeBoundary carrier                  deleted
generic macro/residual production entries      0
source-index duplicate action entries          0
node-ID semantic dependency adversary          PASS
identical warm query creates new cold work     false
```

The adversarial ID regression gives different sibling dyadic tiles the same diagnostic `node_id` and verifies that directed action traversal still produces the correct distinct result.

## Release probes

```text
bench/reverse_temporal_power_probe.py   PASS; global logarithmic closure false
bench/collatz_temporal_power_probe.py   PASS; seed-27 tail sublinear; arbitrary-source closure false
```

Reverse/add remains open only on cold **spatial forcing-action composition**: its bounded temporal state is constant but primitive forcing evaluations are 15,31,63,127,255 for N=16..256.

Collatz seed 27 primitive evaluations are 8,17,32,43,42 over the same range.

## Machine-readable evidence

- `results/hashlife_state_action_growth_reverse_196.json`
- `results/hashlife_state_action_growth_collatz_27.json`
- `results/hashlife_cache_audit_reverse_196_n256.json`
- `results/hashlife_cache_audit_collatz_27_n256.json`
- `results/reverse_temporal_power_metrics.json`
- `results/collatz_temporal_power_metrics.json`
