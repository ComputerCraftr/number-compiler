"""All 209,960 symmetric decimal fields through width eight, explicitly sharded."""

from itertools import product

import pytest

from devtools.verification.reverse_geometry_context import ReverseGeometryContext
from number_compiler.arithmetic.carry.event_memory import pair_step


@pytest.mark.parametrize(
    ("width", "first"),
    [(width, None) for width in range(1, 7)]
    + [(width, first) for width in (7, 8) for first in range(19)],
)
@pytest.mark.parametrize(
    ("growth_quotient", "value_quotient"),
    ((False, "crt"), (True, "crt"), (False, "mod9")),
)
def test_geometry_all_symmetric_fields(
    width: int, first: int | None, growth_quotient: bool, value_quotient: str
) -> None:
    context = ReverseGeometryContext(
        width + 1, growth_quotient=growth_quotient, value_quotient=value_quotient
    )
    action = context.primitive()
    alphabets = [range(19)] * (width // 2) + ([range(0, 19, 2)] if width % 2 else [])
    if first is not None:
        alphabets[0] = range(first, first + 1)
    count = 0
    for half in product(*alphabets):
        source = half + (half[:-1] if width % 2 else half)[::-1]
        expected = pair_step(source, 10)[0]
        assert context.observe(action, context.binding(source)) == expected
        count += 1
    assert count == 19 ** (width // 2) * (10 if width % 2 else 1) // (
        19 if first is not None else 1
    )
