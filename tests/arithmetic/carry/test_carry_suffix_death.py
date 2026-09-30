"""Different fixed histories collapse to the same live carry occurrence."""

from devtools.verification import exact_oracle
from devtools.verification.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)
from number_compiler.arithmetic.carry.carry_itinerary import LiveCarryItinerary


def test_95_104_drop_twelve_dead_rows_and_remain_equal() -> None:
    with exact_oracle():
        engine = ReverseAddCausalSpacetimeEngine(base=10)
        histories = [
            engine.bootstrap_slab(ReverseAddPairField.from_value(seed, base=10))[
                0
            ].row_values()
            for seed in (95, 104)
        ]
        assert histories[0] != histories[1]
        left, right = (LiveCarryItinerary.seed(rows, base=10) for rows in histories)
        assert left == right
        assert left.row_count == 8 and left.dropped_rows == 12
        for _ in range(12):
            left, right = left.advance(), right.advance()
            assert left == right
        assert left.dropped_rows == 23
