# v0.54.1 eager space/time cleanup results

## Removed accidental eager work

- Public Fermat nth-term projection no longer materializes `2**n` merely for width metadata or direct digit projection.
- `ProjectionMetrics.width` is extent-aware; CLI metrics serialize `DyadicExtent` exactly instead of lowering it.
- `SpecialSourceShape` keeps Fermat bit length/top bit symbolic.
- Formula-to-integer materialization consumes a digit iterator rather than allocating an intermediate full digit tuple.
- Native base-2 Fermat/Mersenne rendering bypasses whole-integer construction.
- Mersenne theorem resolution uses deterministic u64 primality for the exponent Boolean gate before requesting a factor witness.
- Mersenne square-root threshold search no longer allocates the full Mersenne candidate for a magnitude comparison.
- Fermat modular factor witnesses keep `2**n` as `DyadicExtent` and test factor stride using `v2(q-1)`.
- Candidate-derived special-modulus validation no longer builds a duplicate `2**n`.
- Bench/JSON metrics were updated to retain symbolic extents rather than calling `int(extent)`.

## Smoke checks

- `F_1,000,000` public projection retains width `2**1000000+1` with a 20-bit source descriptor and can answer low digit projections without dyadic materialization.
- Native binary `F_4`/`M_13` output tests forbid special-number integer materialization and still produce exact output.
- The exact u64 exponent gate classifies `2,147,483,647` without entering `smallest_factor`.
- `bench/nth_projection_probe.py`: PASS.
- `bench/special_constraint_pullback_probe.py`: PASS.

## Validation

- 711 tests PASS across 90 isolated test modules.
- The remaining module timeout is inherited: the same `test_successor_generator_probe_locks_constraints_and_negative_middle_result` timeout reproduces on the untouched v0.54.0 tree.
- Python bytecode compilation: PASS.

No temporal jump, nth-prime stage-collapse, or special-number theorem-injector claim was changed in this patch release.
