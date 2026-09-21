# Shared actions, cylinders, and resource ownership

Status: **the shared algebra and ownership rules are in production; no one
shared action proves every family-specific publisher**.

Number Compiler represents long computations by associative actions, typed
ports, source-bound cylinders, and demand-specific projections. The common rule
is that a quotient is valid only after its observer and composition law are
proved for the exact source domain. Equal endpoints, residues, or phase are not
enough to merge states whose future support differs.

## Reading guide

- **Definitions:** a skew action combines an arithmetic map with transported boundary data; a source occurrence also carries admission authority.
- **Checked theorem:** chronological composition and pullback laws apply to admitted actions and consumers.
- **Implemented construction:** the scheduler and ledger own publication and reuse; the associated scalar consumer has the form `F(x) = min(C, A*x+B)` with positive `A`.
- **Open obligation:** shared algebra does not establish each family's source construction or its cost bound.

## Checked shared algebra

[`S_Arithmetic_Skew.thy`](../../devtools/proofs/isabelle/shared/S_Arithmetic_Skew.thy)
proves associativity, identities, and transport for the shared skew record.
[`Skew_Cylinder_Observers.thy`](../../devtools/proofs/isabelle/etale/Skew_Cylinder_Observers.thy)
proves observer/composition, clock-offset, S-arithmetic product, physical tick,
and demand-pullback laws. These theorems assume the supplied actions and
observers satisfy their definitions; they do not construct a family source.

[`Dyadic_Source_Lift.thy`](../../devtools/proofs/isabelle/shared/Dyadic_Source_Lift.thy)
proves source lifting with extra precision under the positive-precision label
and step premises. Exact-precision lifting is a corollary for an already
admitted source word.

The production resource ledger owns retained nodes, tables, metadata, and
temporary work. Constructors preflight degree, length, and integer-bit growth;
interrupted work may retain only complete canonical objects with charged
ownership. Foreign, stale, or mutated handles are rejected before reuse.

## Composition versus construction

Append, repeat, and binary powering laws prove how supplied summaries compose.
They do not bound discovery of the source word being summarized. This
distinction applies to reverse/add pair residues, Collatz branch words,
Antihydra parity words, prime windows, and special-number terminal products.

The shared scheduler can reuse authenticated source fragments and publish
selected observations. Each family still owes its own source constructor,
coverage theorem, and successful resource bound. An unavailable family
certificate must return `unknown` or an explicit refusal; it may not call an
unbudgeted classical fallback.

## Counterexample scope

- Different support offsets with the same endpoint and weight disprove that
  particular quotient, not all source cylinders.
- Phase-neutral actions can still differ on later observations; phase equality
  alone is not admission.
- A supplied-word monoid may be exact while source discovery remains linear.
- Cleanup, dead-owner removal, and faster imports improve implementation health
  without satisfying a mathematical release gate.

The family papers below state the additional premises and open constructors.

## Production and reproduction

- **Implemented owner:** [hashlife/execution/tile_scheduler.py](../../src/number_compiler/hashlife/execution/tile_scheduler.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** The scheduler authenticates construction and reuse; it does not supply a universal family construction bound.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/hashlife/execution/test_source_bound_images.py tests/arithmetic/fields/test_consumer_pullback.py
```
