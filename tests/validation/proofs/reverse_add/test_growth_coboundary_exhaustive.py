"""Growth's many-to-one quotient, independently checked on complete fields."""

from collections import Counter
from itertools import product

import pytest

from devtools.verification.growth_coboundary import (
    GROWTH_SYMBOLS,
    GrowthCoboundaryHalf,
    growth_symbol_value,
)
from number_compiler.arithmetic.carry.event_memory import carry_field, pair_step


@pytest.mark.parametrize(
    ("width", "sources", "images", "largest"),
    (
        (4, 180, 99, 2),
        (5, 1805, 1040, 2),
        (6, 3429, 1080, 4),
        (7, 34295, 11705, 4),
        (8, 65160, 12429, 8),
    ),
)
def test_complete_growth_quotient(
    width: int, sources: int, images: int, largest: int
) -> None:
    fibers: Counter[GrowthCoboundaryHalf] = Counter()
    outputs: dict[tuple[int, ...], GrowthCoboundaryHalf] = {}
    alphabets = [range(19)] * (width // 2) + ([range(0, 19, 2)] if width % 2 else [])
    for half in product(*alphabets):
        source = half + (half[:-1] if width % 2 else half)[::-1]
        carry = carry_field(source)
        if not carry[-1]:
            continue
        symbols = tuple(
            growth_symbol_value(v % 10, carry[i + 1], carry[width - i])
            for i, v in enumerate(half)
        )
        for i, symbol in enumerate(symbols):
            q, delta = GROWTH_SYMBOLS[symbol]
            assert q == source[i] - 9 * carry[i + 1]
            assert delta == carry[width - i] - carry[i + 1]
        occurrence = GrowthCoboundaryHalf(width, symbols)
        actual = occurrence.output_half()
        expected, growth = pair_step(source, 10)
        assert growth == 1 and actual == expected[: len(actual)]
        fibers[occurrence] += 1
        assert outputs.setdefault(expected, occurrence) == occurrence
    assert sum(fibers.values()) == sources
    assert len(outputs) == len(fibers) == images
    assert max(fibers.values()) == largest
