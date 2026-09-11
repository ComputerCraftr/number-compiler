# Geometry-first etale tile applicability

The geometry-first/value-view split applies partially to Fermat and Mersenne
terminal quotients.  Their exact binary source geometry determines the spatial
closure before any theorem coordinate is introduced:

| family | closure | boundary sign |
|---|---|---:|
| Fermat | negacyclic | -1 |
| Mersenne | cyclic | +1 |

The value-side transport is owned by `SquareTileAction` (the former
`SpecialGermTransfer` name is only a compatibility alias). It represents
an entire terminal dyadic span by binary composition and retains neither exact
source digits nor one state per consumed lift level.  The old
`SpecialFrobeniusSectionState` controller duplicated this temporal coordinate;
it was not called by the production terminal path and has been removed.

The analogous scheduler boundary is therefore

```text
SpecialSourceShape -> cyclic/negacyclic geometry
                   -> powered angular germ action
                   -> demanded etale selector output port
```

The etale selector must remain outside the action identity.  It asks whether
the terminal root or torus phase exists in every candidate-ring component.
That Boolean is not determined by the formal Frobenius action: split and
nonsplit quadratic fibres obey the same universal polynomial relation, and
composite candidates can have Frobenius pseudoprime behaviour.  A zero
Frobenius defect is consequently not a primality proof.

The bounded digit projections now share one canonical square/carry tile.  The
native integer classical ceiling stays separate because it is the scalable
fallback and a Python coefficient carrier would regress it; see
[`arithmetic-square-tiles.md`](../../architecture/arithmetic-square-tiles.md).
This removes the duplicate family-specific digit projection paths without
claiming that the nonlinear temporal action can already be powered by the tile
scheduler.

Production tile admission is not yet sound for these families.  The shared
runtime currently certifies only reverse-add and Collatz.  Small structural
cases already have a selector value, but lack a power-family tile certificate;
the general candidate-derived etale selector extractor remains unavailable.
Registering a Fermat/Mersenne tile adapter now would either leave the same
`UNKNOWN` output or smuggle an unproved prime bit into the action key.  The
research audit therefore emits separate geometry, angular-action, and
selector-port keys while reporting `scheduler_promotion_safe = False`.

The same caution applies one layer lower to the proposed future-consumer
quotient.  `RadixCarryAction` already is the extensional action on an admitted
carry port, and `CarryCyclotomicTransducer` adds a demanded harmonic emission.
The bounded power-number audit now derives both from the actual shared square
tile.  Its exact-output control retains
`(outgoing carry, normalized payload)` for each port and is necessarily
injective in the raw folded product: one response reconstructs that product.
Dropping the payload gives real compression, while the existing bounded
Fermat/Mersenne tables still measure successor conflicts; adding low-order
harmonics can refine those actions without establishing temporal closure.

Accordingly there is no production `CyclotomicActionID` or BSG admission from
these tables.  The source occurrence remains the canonical digit block, while
`ArithmeticTileStep.boundary_action` exposes a demanded, nonpersistent carry
consumer action.  The internal carry interval is likewise computed only by
`step_with_carry_interval`; ordinary tile steps neither retain interval fields
nor scan the internal carry history.  Promotion requires a noninjective
successor congruence and an independently verified composition law, not just
an exact finite table.

The next valid integration step needs both:

1. a candidate-derived extractor whose zero/unit defect has proved all-local
   semantics over composite moduli; and
2. a `TemporalFamilyCertificate` validating the power-number tile kernel and
   its cyclic or negacyclic boundary interface.

Only then can the selector be published as a demanded result port beside the
powered angular action.  It must never become the action's semantic identity.

Executable evidence lives in
[`terminal_etale_square.py`](../../../devtools/experiments/power_numbers/terminal_etale_square.py)
and
[`test_terminal_etale_square.py`](../../../tests/validation/research/power_numbers/test_terminal_etale_square.py).
