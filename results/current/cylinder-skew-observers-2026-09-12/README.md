# Cylinder skew observer integration — September 12

The production and theorem scope is recorded in
[the research integration document](../../../docs/cylinder-skew-observers.md).
The previous carry-jet and factor work remains documented in the neighboring
[cylinder-ray restoration record](../cylinder-ray-restoration-2026-09-12/README.md).

## Formal checks

`Etale_Primary_Carry` builds successfully with Isabelle2025-2,
`quick_and_dirty=false`, and explicit rejection of oracle dependencies.
The new theories are `Skew_Cylinder_Observers` and `Twisted_Support_Observers`.
They prove the common skew algebra and its commuting observers, S-arithmetic
product formula, compatible twisted evaluation, modular affine demand invariance,
saturated-gcd multiplication, and current-target mirror obstruction implication.
No universal factor-separation, future valuation-discovery, or 196 avoidance
theorem is asserted.

## Measured shared-action observer work

Run `python -m devtools.proofs.cylinder_skew_probe` to reproduce the complete
A1..A1024 table. The program is the supplied repeated valuation-2 Collatz action;
its offset satisfies `P(3,2)=4^N-3^N`, checked independently modulo 257.

| Supplied events | Observed shared nodes | Skew compositions | Ring-power compositions |
| ---: | ---: | ---: | ---: |
| 1 | 1 | 0 | 2 |
| 2 | 2 | 1 | 2 |
| 16 | 5 | 4 | 2 |
| 256 | 9 | 8 | 2 |
| 1024 | 11 | 10 | 2 |

Every row adds zero action nodes and materializes zero exact affine cocycles.
Tests additionally poison exact event execution and offset lowering, check an
exponent `10^100+17`, and verify the precision guard for oversized Hensel demands.
These are observations of a supplied action, not a cold Collatz itinerary search.

## Python validation

- Final affected-path selection: **138 passed**, including the opt-in tropical
  research controls, decimal skew, existing Hensel transport, event powering,
  carry-jet and tile regressions, root factor output, new observer tests and
  repository policy.
- Ruff: passed on `src tests devtools`.
- Mypy: **1,241 source files passed**.
- `git diff --check`: passed.
- Mixed CRT-root controls return **641 from F5** and **23 from M11** using the
  same family square field, with the Mersenne constant corrected by +2.
- The 196 ladder uses powered target digit queries and passes with integer
  materialization and full digit iteration poisoned.

A separate broader opt-in run had **32 passes and 3 failures** in existing
`test_collatz_block_power.py` release assertions. All three failures were
reproduced from an archive of unchanged HEAD
`92afb957c54689fc004982a1a0f4bb132a18697a`:

1. N=256 reports seven temporal leaf applications where the test expects zero.
2. N=64 lacks the expected radix-4 source-morphism compilation counter.
3. The release probe reports a completed-result scaling blocker rather than the
   higher-interface blocker required by that assertion.

Their assertions and production admission gates were not changed. The endpoint
successor theorem does not resolve these implementation/scaling failures.
