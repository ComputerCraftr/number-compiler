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

## Memo authority and accounting audit

The September 22 adversarial audit found implementation defects, not new
mathematical quotients:

- Scheduler origin, application, relative-input and projection keys compared
  Boolean and integer components using Python equality. `True` and `1` could
  select the same cached result even when the adapter distinguished them.
  The scheduler now compares typed structures, including nested frozen
  descriptors. Hashing traverses shared descriptor DAGs with an explicit
  postorder stack and per-node memo, rather than expanding repeated subgraphs.
  Origin publication seals retain the actual source, avoiding a redundant seal
  of its cache-key wrapper while checking that both identify the same source.
- The process cache now rejects Boolean components in source/local authority
  keys; its prime consumers use exact integers and strings. Boolean payloads
  remain supported. Lease validation uses exact scalar types and the issued
  partition identity. Failed close attempts preserve the ability to correct
  and release a lease. Active-lease counts increase only after successful
  resource reservation and publication; refused admission cannot leave a phantom
  lease. A mutated generation cannot impersonate an actual reset
  and leave a live partition permanently pinned. Issued leases remain strongly
  held until close/reset, preventing object-ID reuse from overwriting authority
  records. Their retention is charged to the bounded store.
- Higher temporal image node and blank memos now include the complete
  consumer declaration. Its independent seal snapshots types, values and
  scoped-handle fields, so mutating the composer and its memo key together
  does not authorize a warm hit. Workspace probes and memo hits are counted
  separately from newly visited image nodes.
- Spatial and temporal constructors share one sealed consumer declaration.
  Provider registration now authenticates the output/source/action relation,
  including warm alias requests, and pins the runtime and callbacks. Individually
  valid handles are not sufficient evidence of that relation. Already issued
  provider bindings survive clearing the construction workspace.

The temporal-image reproduction warmed a private blank-macro workspace and
then changed its consumer. The public `step()` in the audited checkout already
clears that workspace in `finally` and rejects composite consumers. Its
independent 16-step output/work regression does not reproduce free D8/D16
construction. No zero-work observation from a different experimental harness
certifies temporal compression without that harness's source and binding
trace. The retained positive release gates remain unchanged.

Final source fingerprint: `de9d18c1c6f587015138c049cded52cbd70d43d9cfb1791d18f26964da4614e1`.
The frozen run passed 213 focused checks, strict typing/lint/formatting, repository
policy, proof inventory and installed-wheel checks. Full unit validation reports
6,279 passes and the same 42 failing cases as its baseline; the explicit cutover
selection retains 14 failures and six passes. No Isabelle theorem changed in
this memo audit, and no new mathematical refinement is claimed.

Local evidence is under `results/current/temporal-memo-audit-2026-09-22/`.
The implementation regression tests are
[source-bound scheduler tests](../../tests/hashlife/execution/test_source_bound_images.py),
[process-cache tests](../../tests/resources/test_process_cache.py),
[macro authority tests](../../tests/hashlife/execution/test_higher_macro_authority.py), and
[higher temporal image tests](../../tests/hashlife/execution/test_higher_temporal_image.py).

## Production and reproduction

- **Implemented owner:** [hashlife/execution/tile_scheduler.py](../../src/number_compiler/hashlife/execution/tile_scheduler.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** The scheduler authenticates construction and reuse; it does not supply a universal family construction bound.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/hashlife/execution/test_source_bound_images.py tests/arithmetic/fields/test_consumer_pullback.py
```
