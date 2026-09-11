from number_compiler.arithmetic.fields.radix import symbol_runs
from number_compiler.sequences.collatz.pair import (
    collatz_valuation_itinerary,
    valuation_itinerary_slab,
    valuation_projection_from_runs,
)


def test_collatz_valuation_projection_monoid_matches_exact_itinerary_slab() -> None:
    vals = collatz_valuation_itinerary(27, max_odd_steps=1000)
    block = valuation_projection_from_runs(symbol_runs(vals))
    exact = valuation_itinerary_slab(vals)
    assert block.slab == exact
    assert block.odd_steps == len(vals)
    assert block.valuation_sum == sum(vals)


def test_collatz_repeated_valuation_symbol_powers_logarithmically_but_keeps_payload() -> (
    None
):
    block = valuation_projection_from_runs(((1, 1_000_000),))
    assert block.odd_steps == 1_000_000
    assert block.valuation_sum == 1_000_000
    assert block.compositions < 64
    # The exact affine offset/domain payload is not claimed to be logarithmic.
    assert block.slab.description_bits > 100_000
