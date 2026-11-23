"""Accounting checks for retained integer words."""

from __future__ import annotations

import pytest

from number_compiler.resources.payload_cost import aggregate_integer_limb_units


@pytest.mark.parametrize(
    ("values", "expected"),
    [
        ((), 1),
        ((0,), 1),
        ((0, 0, 0), 1),
        ((2**63,), 1),
        ((2**64,), 2),
        ((-(2**64),), 2),
        ((2**62, 0), 1),
        ((2**63, 0), 2),
    ],
)
def test_aggregate_integer_limb_units_preserves_field_bits(
    values: tuple[int, ...], expected: int
) -> None:
    assert aggregate_integer_limb_units(*values) == expected
