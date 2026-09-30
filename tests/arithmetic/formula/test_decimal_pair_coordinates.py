"""Independent finite checks for the supplied mixed-radix research laws."""

from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_add_normalized,
    decimal_normalized_coordinates,
    decimal_normalized_pair_sum,
    decimal_pair_carry_action,
    decimal_pair_coordinates,
    decimal_pair_value,
)


def _coordinates(symbol: int) -> tuple[int, int, int]:
    return symbol % 5, (symbol % 10) // 5, symbol // 10


def _normalize(symbol: int, incoming: int) -> tuple[int, int]:
    alpha, beta, _nu = _coordinates(symbol)
    return (alpha + incoming) % 5, beta ^ int(alpha == 4 and incoming == 1)


def _combine(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int, int]:
    phase_sum = left[0] + right[0]
    binary_sum = left[1] + right[1] + int(phase_sum >= 5)
    return phase_sum % 5, binary_sum % 2, int(binary_sum >= 2)


def _value(coordinates: tuple[int, int, int]) -> int:
    alpha, beta, nu = coordinates
    return alpha + 5 * beta + 10 * nu


@pytest.mark.algebra
def test_decimal_factorization_is_bijective_but_carry_projection_is_not() -> None:
    states = {_coordinates(symbol) for symbol in range(19)}
    assert states == set(product(range(5), range(2), range(2))) - {(4, 1, 1)}
    for symbol in range(19):
        alpha, beta, nu = coordinates = _coordinates(symbol)
        assert decimal_pair_coordinates(symbol) == coordinates
        assert decimal_pair_value(coordinates) == symbol
        assert _value(coordinates) == symbol
        wire = alpha == 4 and beta == 1
        function = CarryFn.ID if wire else CarryFn.CONST1 if nu else CarryFn.CONST0
        assert decimal_pair_carry_action(symbol) is function
        assert function is value_carry_fn(symbol, 10)
        for carry in (0, 1):
            assert apply_carry_fn(function, carry) == int(symbol + carry >= 10)
            digit_alpha, digit_beta = _normalize(symbol, carry)
            assert decimal_normalized_coordinates(symbol, carry) == (
                digit_alpha,
                digit_beta,
            )
            assert digit_alpha + 5 * digit_beta == (symbol + carry) % 10
    assert value_carry_fn(2, 10) is value_carry_fn(4, 10)
    assert _normalize(2, 0) != _normalize(4, 0)


@pytest.mark.algebra
def test_decimal_full_adder_and_exceptional_phase_are_exhaustive() -> None:
    for left, right in product(range(10), repeat=2):
        coordinates = _combine(divmod(left, 5)[::-1], divmod(right, 5)[::-1])
        assert (
            decimal_add_normalized(divmod(left, 5)[::-1], divmod(right, 5)[::-1])
            == coordinates
        )
        assert coordinates != (4, 1, 1)
        assert _value(coordinates) == left + right
    for symbol, left, right in product(range(19), range(2), range(2)):
        alpha, beta, _nu = _coordinates(symbol)
        actual = _combine(_normalize(symbol, left), _normalize(symbol, right))
        assert decimal_normalized_pair_sum(symbol, left, symbol, right) == _value(
            actual
        )
        carry_sum = left + right
        assert _value(actual) == (symbol + left) % 10 + (symbol + right) % 10
        assert actual[0] == (2 * alpha + carry_sum) % 5
        if alpha != 4:
            assert actual[1:] == (int(2 * alpha + carry_sum >= 5), beta)
        else:
            assert actual[1:] == ((1, beta), (1, 0), (0, 1 - beta))[carry_sum]


@pytest.mark.algebra
def test_decimal_growth_rewiring_matches_existing_pair_recurrence() -> None:
    # Exhaust the small symmetric pair domain, including repeated EQ interiors.
    # These are proof-only rows; production is never called to emit a carry row.
    for width in range(1, 5):
        for half in product(range(19), repeat=(width + 1) // 2):
            source = half + half[: width // 2][::-1]
            carry = [0]
            for symbol in source:
                carry.append(int(symbol + carry[-1] >= 10))
            reflected = carry[::-1]
            if carry[-1]:
                edge = _value(_combine(_normalize(source[0], 0), (1, 0)))
                interior = tuple(
                    _value(
                        _combine(
                            _normalize(source[i], carry[i]),
                            _normalize(source[i - 1], reflected[i]),
                        )
                    )
                    for i in range(1, width)
                )
                output = (edge, *interior, edge)
            else:
                output = tuple(
                    _value(
                        _combine(
                            _normalize(symbol, carry[i]),
                            _normalize(symbol, reflected[i + 1]),
                        )
                    )
                    for i, symbol in enumerate(source)
                )
            assert (output, carry[-1]) == pair_step(source, 10)


@pytest.mark.algebra
def test_decimal_pair_conjugacy_and_reset_composition() -> None:
    def conjugate(function: CarryFn) -> CarryFn:
        return {
            CarryFn.CONST0: CarryFn.CONST1,
            CarryFn.ID: CarryFn.ID,
            CarryFn.CONST1: CarryFn.CONST0,
        }[function]

    for symbol in range(19):
        assert (18 - symbol - 9) % 20 == (-(symbol - 9)) % 20
        assert value_carry_fn(18 - symbol, 10) is conjugate(value_carry_fn(symbol, 10))
    for before, after in product(CarryFn, repeat=2):
        assert conjugate(compose_carry_fn(after, before)) is compose_carry_fn(
            conjugate(after), conjugate(before)
        )
        for carry in (0, 1):
            assert apply_carry_fn(conjugate(before), 1 - carry) == 1 - apply_carry_fn(
                before, carry
            )


@pytest.mark.algebra
def test_decimal_factoring_rejects_numeric_aliases_and_invalid_coordinates() -> None:
    for value in (True, 1.0, -1, 19):
        with pytest.raises((TypeError, ValueError)):
            decimal_pair_coordinates(cast(int, value))
    for carry in (True, 0.0, -1, 2):
        with pytest.raises((TypeError, ValueError)):
            decimal_normalized_coordinates(9, cast(int, carry))
    bad_coordinates: tuple[tuple[int, int, int], ...] = (
        (4, 1, 1),
        (5, 0, 0),
        (0, 2, 0),
    )
    for coordinates in bad_coordinates:
        with pytest.raises(ValueError):
            decimal_pair_value(coordinates)


@pytest.mark.algebra
def test_decimal_base_kernel_uses_factored_carry_and_output_laws(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts import block_kernel
    from number_compiler.arithmetic.contracts.block_effect import BoundarySide
    from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
        _decimal_kernel_carry_action,
        _decimal_kernel_pair_sum,
    )

    carry_law = _decimal_kernel_carry_action
    output_law = _decimal_kernel_pair_sum
    calls = {"carry": 0, "output": 0}

    def carry(symbol: int) -> CarryFn:
        calls["carry"] += 1
        return carry_law(symbol)

    def output(
        left_symbol: int,
        left_carry: int,
        right_symbol: int,
        right_carry: int,
    ) -> int:
        calls["output"] += 1
        return output_law(left_symbol, left_carry, right_symbol, right_carry)

    monkeypatch.setattr(block_kernel, "_decimal_kernel_carry_action", carry)
    monkeypatch.setattr(block_kernel, "_decimal_kernel_pair_sum", output)
    effect = BaseBlockEffect(10)
    left_states = effect.boundary_universe(BoundarySide.LEFT)
    right_states = effect.boundary_universe(BoundarySide.RIGHT)
    assert left_states is not None and right_states is not None
    for left in left_states:
        for right in right_states:
            for symbol in range(19):
                effect.emit(left, symbol, right)
    assert calls["carry"] > 0
    assert calls["output"] > 0


def test_threshold_residue_saturation_requires_the_admitted_pair_range() -> None:
    # The proposed (F5, parity, final threshold) chart is an exact recoding
    # of physical pair coefficients, not arbitrary accumulated forcing sums.
    for symbol in range(19):
        alpha, epsilon, nu = symbol % 5, symbol % 2, int(symbol > 9)
        beta = epsilon ^ (alpha % 2)
        assert decimal_pair_value((alpha, beta, nu)) == symbol
    collision = [(value % 5, value % 2, int(value > 9)) for value in (10, 20)]
    assert collision[0] == collision[1]
    with pytest.raises(ValueError):
        decimal_pair_coordinates(20)


def test_a_local_chamber_does_not_replace_the_full_spatial_cylinder() -> None:
    # Same width, same low pair coefficient and zero exterior incoming carry,
    # but another internal domain changes the next reflected pair. This only
    # rules out a context-free 19->19 successor on one coordinate.
    seeds = (111, 191)
    old_pairs = []
    new_pairs = []
    for seed in seeds:
        digits = tuple(map(int, str(seed)))
        old_pairs.append(tuple(a + b for a, b in zip(digits, reversed(digits))))
        target = seed + int(str(seed)[::-1])
        digits = tuple(map(int, str(target)))
        new_pairs.append(tuple(a + b for a, b in zip(digits, reversed(digits))))
    assert old_pairs == [(2, 2, 2), (2, 18, 2)]
    assert old_pairs[0][0] == old_pairs[1][0]
    assert new_pairs == [(4, 4, 4), (5, 16, 5)]
    assert new_pairs[0][0] != new_pairs[1][0]
