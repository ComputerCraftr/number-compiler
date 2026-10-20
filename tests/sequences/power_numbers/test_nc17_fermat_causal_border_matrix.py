from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from tests.support.exact_integer_power import exact_integer_power


@pytest.mark.parametrize("base,position", ((2, 6), (5, 3), (7, 1), (10, 2)))
def test_causal_matrix_selects_actual_source_row_and_keeps_conditional_rows(
    base: int, position: int
) -> None:
    level = 2
    physical_steps = 9
    source = 3 ** (1 << level)
    modulus = exact_integer_power(base, position + 1)
    low_modulus = exact_integer_power(base, position)
    actual_residue = source % modulus

    matrix = FermatNumberSpec(3).demand_three_power_causal_border_matrix(
        level,
        physical_steps,
        base=base,
        position=position,
    )

    assert matrix.producer_verified
    assert matrix.source_residue == actual_residue
    assert matrix.selected_digit == (actual_residue // low_modulus) % base
    assert len(matrix.rows) == base
    selected = matrix.selected_row
    assert selected.source_residue == actual_residue
    for tick, digit in enumerate(selected.digits):
        physical_residue = source * pow(3, tick, modulus) % modulus
        assert digit == physical_residue // low_modulus
    assert (
        selected.endpoint_residue == source * pow(3, physical_steps, modulus) % modulus
    )
    assert matrix.work_units == base * physical_steps * (position + 1)
    assert matrix.row_cells == base * physical_steps
    assert matrix.construction_peak_cells == base * (3 * physical_steps + 1)

    for digit, row in enumerate(matrix.rows):
        expected = (actual_residue % low_modulus) + digit * low_modulus
        assert row.source_digit == digit
        for tick, (incoming, outgoing) in enumerate(
            zip(row.carries_in, row.carries_out, strict=True)
        ):
            state = expected * pow(3, tick, modulus) % modulus
            low = state % low_modulus
            current_digit = state // low_modulus
            expected_in = 0 if position == 0 else (3 * low) // low_modulus
            expected_out, _next_digit = divmod(3 * current_digit + expected_in, base)
            assert incoming == expected_in
            assert outgoing == expected_out


def test_causal_matrix_issuer_rejects_structural_copy() -> None:
    matrix = FermatNumberSpec(3).demand_three_power_causal_border_matrix(
        2, 4, base=10, position=2
    )
    copied = replace(matrix, selected_digit=matrix.selected_digit)
    assert matrix.producer_verified
    assert not copied.producer_verified
    with pytest.raises(ValueError, match="unissued"):
        copied.packet()


def test_causal_matrix_validates_dimensions_before_source_compilation() -> None:
    spec = FermatNumberSpec(3)
    with pytest.raises(ValueError, match="physical span"):
        spec.demand_three_power_causal_border_matrix(2, 4097)
    with pytest.raises(ValueError, match="digit position"):
        spec.demand_three_power_causal_border_matrix(2, 1, position=257)


def test_causal_work_budget_is_checked_before_source_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec = FermatNumberSpec(3)

    def forbidden_source(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("rejected row work reached source compilation")

    monkeypatch.setattr(
        FermatNumberSpec,
        "demand_three_power_signed_border_action",
        forbidden_source,
    )
    with pytest.raises(BlockContextBudgetExceeded, match="work budget"):
        spec.demand_three_power_causal_border_matrix(
            2, 1, base=10, position=0, max_work_units=1
        )
