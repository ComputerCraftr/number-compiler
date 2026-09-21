# Collatz physical time, events, and Hensel cylinders

Status: **finite physical/event refinements and source lifts are checked; the
remaining compact publication and growth gates are not implied by them**.

The CLI's `--nth` counts ordinary Collatz iterations. Accelerated events are a
separate coordinate. A valid cylinder therefore records both physical tick
count and event count rather than identifying them.

## Reading guide

- **Definitions:** physical iteration applies `T(x)=x/2` for even `x` and `T(x)=3*x+1` for odd `x`; an accelerated event groups a different number of those ticks.
- **Checked theorem:** finite source cylinders, Hensel transport and physical/event refinements use the specified source, precision and action.
- **Implemented construction:** physical terms and event observations consume authenticated source images.
- **Open obligation:** exact finite output does not establish convergence or cheap construction at arbitrary horizons.

## Exact source and clock laws

[`Collatz_Cylinder_Constructor.thy`](../../devtools/proofs/isabelle/temporal_collatz/Collatz_Cylinder_Constructor.thy)
proves exact dyadic source splitting, block composition, physical-tick
composition, and embedding of events in physical time. The constructor
evaluation theorem applies to the defined finite cylinder; the explicit
`phase_neutrality_does_not_fix_cylinder_action` lemma records why phase alone is
not a quotient.

[`Collatz_Physical_Cylinder_Lift.thy`](../../devtools/proofs/isabelle/temporal_collatz/Collatz_Physical_Cylinder_Lift.thy)
proves branch words are dyadic source words and gives exact-precision affine and
low-residue lifts. Its selector split and affine-leaf division assume the
admitted branch/source construction.

[`Collatz_Clock_Jumps.thy`](../../devtools/proofs/isabelle/temporal_collatz/Collatz_Clock_Jumps.thy)
proves block composition, inverse-three conjugacy, Hensel prefix skips, mismatch
death, one-hot radix-64 curvature, and normalized jet composition. A matching
prefix permits the stated skip; a mismatch kills that forcing branch. Neither
claim proves all future branches absent.

The physical bound consumer in
[`Physical_Collatz_Bound_Consumer.thy`](../../devtools/proofs/isabelle/etale/Physical_Collatz_Bound_Consumer.thy)
assigns odd-event ownership to the low boundary under its finite state cases and
proves the compiled publisher/pullback refines that emission. The support theory
[`Physical_Collatz_Support.thy`](../../devtools/proofs/isabelle/etale/Physical_Collatz_Support.thy)
exhibits sources with equal normalization but different offsets, proving that
endpoint and weight do not determine support.

## Production and resource boundary

The installed implementation shares directional carry actions, source Hensel
anchors, physical/event clocks, and demanded output buffers. Terminal output
allocation is charged before materialization. Cached support belongs to the
source occurrence and cannot be reused after provenance changes.

The remaining release work is to keep construction and demanded projection
within the public resource contract for arbitrary admitted queries. A local
free-selection theorem or curvature view does not remove the source event
pipeline. The three-cycle identities for source one describe that admitted
cycle; low-residue equality alone is explicitly not cycle admission.

## Counterexample scope

Equal endpoint/weight examples refute that compressed key only. They do not
refute a cylinder carrying support offsets. Event-clock and ordinary-time
comparisons must use the same counting convention. Bounded orbit comparisons
validate implementation but do not establish the Collatz conjecture.

## Production and reproduction

- **Implemented owner:** [sequences/collatz/physical_images.py](../../src/number_compiler/sequences/collatz/physical_images.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Admitted cycle compression bounds repeated-cycle work. General source discovery, event projections and output-sensitive rendering have separate costs.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/hashlife/execution/test_collatz_tile_cycle.py tests/projection/test_collatz_binary_radix_limbs.py
```
