"""Exact input contracts and algebra laws for the carry-transfer monoid."""

from __future__ import annotations

from itertools import product
from typing import Never, cast

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    CarryScanAutomatonResult,
    apply_carry_fn,
    centered_carry_fn,
    compose_carry_fn,
    scan_carry_automaton,
    value_carry_fn,
)


def test_centered_ports_are_the_same_canonical_monoid() -> None:
    for base in (2, 3, 10, 64):
        for symbol, incoming in product(range(2 * base - 1), (0, 1)):
            centered = centered_carry_fn(symbol - (base - 1))
            assert centered is value_carry_fn(symbol, base)
            assert apply_carry_fn(centered, incoming) == (symbol + incoming) // base
    assert centered_carry_fn(0) is CarryFn.ID
    assert apply_carry_fn(centered_carry_fn(0), 1) == 1


@pytest.mark.parametrize("alias", (True, False, 0.0, "0", None))
def test_centered_port_rejects_noninteger_aliases(alias: object) -> None:
    with pytest.raises(TypeError):
        centered_carry_fn(cast(int, alias))


def test_raw_pair_classifier_calls_the_centered_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.carry.carry_monoid as monoid

    observed: list[int] = []
    original = monoid.centered_carry_fn

    def record(delta: int) -> CarryFn:
        observed.append(delta)
        return original(delta)

    monkeypatch.setattr(monoid, "centered_carry_fn", record)
    assert monoid.value_carry_fn(9, 10) is CarryFn.ID
    assert monoid.value_carry_fn(18, 10) is CarryFn.CONST1
    assert observed == [0, 9]


def test_carry_composition_has_the_documented_before_after_order() -> None:
    # The reset applied last wins; reversing these operands changes the result.
    assert compose_carry_fn(CarryFn.CONST1, CarryFn.CONST0) is CarryFn.CONST1
    assert compose_carry_fn(CarryFn.CONST0, CarryFn.CONST1) is CarryFn.CONST0
    for after, before, bit in product(CarryFn, CarryFn, (0, 1)):
        composed = compose_carry_fn(after, before)
        assert apply_carry_fn(composed, bit) == apply_carry_fn(
            after,
            apply_carry_fn(before, bit),
        )


def test_carry_composition_is_associative_with_shared_identity() -> None:
    for first, second, third in product(CarryFn, repeat=3):
        assert compose_carry_fn(
            third,
            compose_carry_fn(second, first),
        ) is compose_carry_fn(
            compose_carry_fn(third, second),
            first,
        )
        assert compose_carry_fn(first, CarryFn.ID) is first
        assert compose_carry_fn(CarryFn.ID, first) is first


def test_carry_composition_uses_reset_law_without_observing_inputs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.carry.carry_monoid as monoid

    def forbidden(*_args: object) -> Never:
        raise AssertionError("composition evaluated a Boolean input")

    monkeypatch.setattr(monoid, "apply_carry_fn", forbidden)
    for before in CarryFn:
        assert monoid.compose_carry_fn(CarryFn.ID, before) is before
        assert monoid.compose_carry_fn(CarryFn.CONST0, before) is CarryFn.CONST0
        assert monoid.compose_carry_fn(CarryFn.CONST1, before) is CarryFn.CONST1


@pytest.mark.parametrize("alias", ("id", 1, True, None))
def test_composition_rejects_non_carry_function_aliases(alias: object) -> None:
    with pytest.raises(TypeError, match="CarryFn"):
        compose_carry_fn(cast(CarryFn, alias), CarryFn.ID)
    with pytest.raises(TypeError, match="CarryFn"):
        compose_carry_fn(CarryFn.ID, cast(CarryFn, alias))


@pytest.mark.parametrize("alias", (False, True, 0.0, 1.0, "1", None))
def test_apply_rejects_numeric_alias_carry_bits(alias: object) -> None:
    with pytest.raises(TypeError, match="exact integer"):
        apply_carry_fn(CarryFn.ID, cast(int, alias))


@pytest.mark.parametrize("alias", (False, True, 3.0, "3", None))
def test_value_classification_rejects_numeric_aliases(alias: object) -> None:
    with pytest.raises(TypeError, match="exact integer"):
        value_carry_fn(cast(int, alias), 10)
    with pytest.raises(TypeError, match="exact integer"):
        value_carry_fn(3, cast(int, alias))


@pytest.mark.parametrize("alias", (False, True, 0.0, 1.0, "0", None))
def test_scan_rejects_aliased_input_carry_and_symbols(alias: object) -> None:
    with pytest.raises(TypeError, match="exact integer"):
        scan_carry_automaton((0, 1), incoming=cast(int, alias))
    with pytest.raises(TypeError, match="exact integer"):
        scan_carry_automaton((0, cast(int, alias)))


@pytest.mark.parametrize("alias", (False, True, 10.0, "10", None))
def test_scan_rejects_aliased_radices(alias: object) -> None:
    with pytest.raises(TypeError, match="exact integer"):
        scan_carry_automaton((0, 1), base=cast(int, alias))


def test_scan_composes_the_same_extensional_functions() -> None:
    values = (0, 9, 18, 9)
    result = scan_carry_automaton(values, base=10, incoming=1)
    functions = tuple(value_carry_fn(value, 10) for value in values)
    expected = CarryFn.ID
    carry = 1
    boundaries = [carry]
    for function in functions:
        expected = compose_carry_fn(function, expected)
        carry = apply_carry_fn(function, carry)
        boundaries.append(carry)
    assert result == CarryScanAutomatonResult(
        tuple(boundaries),
        expected,
        len(set(functions)),
    )
