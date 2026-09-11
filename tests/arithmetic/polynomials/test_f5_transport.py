"""Exact checks for compact source-independent F5 spatial transport."""

from math import comb

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)


def _shift(values: tuple[int, ...], distance: int) -> tuple[int, ...]:
    return (0,) * distance + values


def _add(first: tuple[int, ...], second: tuple[int, ...]) -> tuple[int, ...]:
    width = max(len(first), len(second))
    return tuple(
        ((first[i] if i < len(first) else 0) + (second[i] if i < len(second) else 0))
        % 5
        for i in range(width)
    )


def _scale(values: tuple[int, ...], scalar: int) -> tuple[int, ...]:
    return tuple(scalar * value % 5 for value in values)


def test_coefficients_and_callback_application_match_binomial_transport() -> None:
    source: tuple[int, ...] = (1, 4, 2)
    for q in range(5):
        for r in range(21):
            transport = F5SpatialTransport(q, r)
            expected_terms = tuple(
                (k, pow(2, q, 5) * comb(r, k) % 5)
                for k in range(r + 1)
                if comb(r, k) % 5
            )
            assert transport.shifts() == expected_terms
            assert tuple(transport.coefficient(k) for k in range(r + 1)) == tuple(
                pow(2, q, 5) * comb(r, k) % 5 for k in range(r + 1)
            )
            expected: tuple[int, ...] = (0,)
            for k, coefficient in expected_terms:
                expected = _add(expected, _scale(_shift(source, k), coefficient))
            assert (
                transport.apply(source, shift=_shift, add=_add, scale=_scale)
                == expected
            )


def test_frobenius_power_applies_without_expanding_terms() -> None:
    distance = 5**40
    transport = F5SpatialTransport(0, distance)
    calls: list[int] = []

    def symbolic_shift(value: object, shift: int) -> object:
        calls.append(shift)
        return ("shift", value, shift)

    def symbolic_add(first: object, second: object) -> object:
        return ("add", first, second)

    def symbolic_scale(value: object, scalar: int) -> object:
        return ("scale", value, scalar)

    source: object = "source"
    result = transport.apply(
        source, shift=symbolic_shift, add=symbolic_add, scale=symbolic_scale
    )
    assert calls == [distance]
    assert result == (
        "scale",
        ("add", "source", ("shift", "source", distance)),
        1,
    )
    assert transport.shifts(max_terms=2) == ((0, 1), (distance, 1))
    with pytest.raises(BlockContextBudgetExceeded):
        F5SpatialTransport(0, distance - 1).shifts(max_terms=4096)


def test_composition_and_output_forcing_are_explicit() -> None:
    first = F5SpatialTransport(3, 7)
    second = F5SpatialTransport(2, 18)
    assert first.then(second) == F5SpatialTransport(1, 25)
    assert first.then(second) == second.then(first)

    source: tuple[int, ...] = (2, 1)
    forcing: tuple[int, ...] = (4, 3, 2)
    homogeneous = first.apply(source, shift=_shift, add=_add, scale=_scale)
    assert first.apply_with_output_forcing(
        source,
        forcing,
        shift=_shift,
        add=_add,
        scale=_scale,
    ) == _add(homogeneous, forcing)


def test_affine_composition_transports_earlier_output_forcing() -> None:
    source: tuple[int, ...] = (3, 1, 4, 2)
    before = F5AffineTransport[tuple[int, ...]](F5SpatialTransport(1, 0), (1, 0, 3, 2))
    after = F5AffineTransport[tuple[int, ...]](F5SpatialTransport(0, 1), (4, 1, 0, 2))
    intermediate = before.apply(source, shift=_shift, add=_add, scale=_scale)
    sequential = after.apply(intermediate, shift=_shift, add=_add, scale=_scale)
    composed = before.then(after, shift=_shift, add=_add, scale=_scale)
    assert composed.linear == F5SpatialTransport(1, 1)
    assert composed.forcing == _add(
        after.linear.apply(
            before.forcing,
            shift=_shift,
            add=_add,
            scale=_scale,
        ),
        after.forcing,
    )
    assert composed.apply(source, shift=_shift, add=_add, scale=_scale) == sequential


def test_affine_transport_rejects_another_linear_sort() -> None:
    with pytest.raises(TypeError):
        F5AffineTransport(object(), (0,))  # type: ignore[arg-type]
    valid = F5AffineTransport[tuple[int, ...]](F5SpatialTransport(), (0,))
    with pytest.raises(TypeError):
        valid.then(
            object(),  # type: ignore[arg-type]
            shift=_shift,
            add=_add,
            scale=_scale,
        )


def test_exact_input_contracts_fail_closed() -> None:
    for bad in (True, -1, 1.0):
        with pytest.raises(ValueError):
            F5SpatialTransport(bad, 0)  # type: ignore[arg-type]
    bad_shift: object = True
    with pytest.raises(TypeError):
        F5SpatialTransport().coefficient(bad_shift)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        F5SpatialTransport().then(object())  # type: ignore[arg-type]
