# Antihydra arithmetic, literal machine, and Mahler action

Status: **finite arithmetic and demanded-cylinder laws are checked; the
source-7 all-time barrier and complete literal/macro refinement remain open**.

Antihydra has three related semantics that must remain distinct: the total
arithmetic family, the guarded ledger computation, and the literal six-state
machine. Mahler/Hensel outputs are projections of authenticated arithmetic
source data; they are not alternate evidence that the literal machine never
halts.

## Reading guide

- **Definitions:** total arithmetic starts at `a=8` and applies `a <- a + floor(a/2)`. The ledger starts at zero and changes by `+2` for even `a`, `-1` for odd `a`; centered state is `D=a-1`.
- **Checked theorem:** finite arithmetic composition and minimum-prefix guards preserve their stated semantics.
- **Implemented construction:** arithmetic images and demanded support fragments retain source authority; guarded physical execution remains a separate consumer.
- **Open obligation:** source-7 non-halting, complete literal/macro refinement and arbitrary-horizon retention bounds remain unresolved.

## Checked arithmetic and cylinders

[`Antihydra_Family_Iteration.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Family_Iteration.thy)
proves the total skew equation, centered orbit, block composition, exact minimum
prefix guard, and guarded agreement before the first failed block. The latter is
conditional on remaining before failure and does not prove all-time safety.

[`Antihydra_Arithmetic_Cylinder_Lift.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Arithmetic_Cylinder_Lift.thy)
identifies family bits with a dyadic source word and proves exact demanded
cylinder composition, split, bit, and ledger projections. These results assume
the admitted arithmetic source; they do not generate a literal macro word.

[`Antihydra_Mahler_Skew.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Mahler_Skew.thy)
proves centered return, numerator and minimum-prefix composition, and the
one-return kernel coefficients. The associated-action refinement
[`Antihydra_Mahler_Associated_Action.thy`](../../devtools/proofs/isabelle/integration_mahler/Antihydra_Mahler_Associated_Action.thy)
proves source coefficients determine the defined Mahler action. It also proves
that the centered word `11` has distinct Mahler and ledger outcomes, so a Mahler
failure must not be reported as Antihydra halting.

## Literal and barrier boundary

[`Antihydra_Literal_TM.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Literal_TM.thy)
checks startup and the exact halt boundary.
[`Antihydra_Macro_Grammar.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Macro_Grammar.thy)
proves length, shift, directional clock, and admitted terminal cases for supplied
macro words. The missing bridge is a source-generated macro word with reads,
overwrites, startup invariant, powered image, and first-failure refinement.

[`Antihydra_Source_Barrier.thy`](../../devtools/proofs/isabelle/antihydra/Antihydra_Source_Barrier.thy)
proves `source_bound_barrier_soundness` for a supplied valid barrier.
`source_seven_all_time_barrier_exactly` is an equivalence: it does not construct
the barrier. No accepted source-7 all-time certificate or source-reachable
counterexample is currently present.

## Production boundary

Finite `--nth` arithmetic and selected projections are available with bounded
ownership. Reusing retained parity avoids rediscovery, but folding every
retained step is still linear in the represented source. Batch aliases share
one authenticated discovery result; Hensel and Mahler packets remain distinct.

Finite bounded barrier searches and observed nonhalting prefixes are evidence
only. They neither prove all-time nonhalting nor refute a future source-global
certificate.

## Production and reproduction

- **Implemented owner:** [sequences/antihydra/arithmetic_images.py](../../src/number_compiler/sequences/antihydra/arithmetic_images.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Composed arithmetic and retained projection fragments do not prove cheap all-time source discovery or non-halting.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/api/test_antihydra_support_cache.py tests/api/test_antihydra_projection_occurrences.py
```
