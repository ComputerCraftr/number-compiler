"""Exact checks for compact source-independent F2 spatial transport."""

from math import comb

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.f2_transport import (
    F2AffineTransport,
    F2SpatialTransport,
)


def _shift(values: tuple[int, ...], distance: int) -> tuple[int, ...]:
    return (0,) * distance + values


def _add(first: tuple[int, ...], second: tuple[int, ...]) -> tuple[int, ...]:
    width = max(len(first), len(second))
    return tuple(
        (first[i] if i < len(first) else 0) ^ (second[i] if i < len(second) else 0)
        for i in range(width)
    )


def test_coefficients_and_callback_application_match_binomial_transport() -> None:
    source: tuple[int, ...] = (1, 0, 1)
    for q in range(3):
        for r in range(25):
            transport = F2SpatialTransport(q, r)
            expected_terms = (
                () if q else tuple((k, 1) for k in range(r + 1) if comb(r, k) % 2)
            )
            assert transport.shifts() == expected_terms
            assert tuple(transport.coefficient(k) for k in range(r + 1)) == tuple(
                0 if q else comb(r, k) % 2 for k in range(r + 1)
            )
            expected: tuple[int, ...] = (0,) * len(source)
            for k, _coefficient in expected_terms:
                expected = _add(expected, _shift(source, k))
            assert transport.apply(source, shift=_shift, add=_add) == expected


def test_large_frobenius_power_remains_one_shift() -> None:
    distance = 1 << 80
    transport = F2SpatialTransport(0, distance)
    calls: list[int] = []

    def symbolic_shift(value: object, shift: int) -> object:
        calls.append(shift)
        return ("shift", value, shift)

    def symbolic_add(first: object, second: object) -> object:
        return ("xor", first, second)

    source: object = "source"
    result = transport.apply(source, shift=symbolic_shift, add=symbolic_add)
    assert calls == [distance]
    assert result == ("xor", "source", ("shift", "source", distance))
    assert transport.shifts(max_terms=2) == ((0, 1), (distance, 1))
    with pytest.raises(BlockContextBudgetExceeded):
        F2SpatialTransport(0, distance - 1).shifts(max_terms=4096)


def test_positive_doubling_is_canonical_source_annihilation() -> None:
    assert F2SpatialTransport(1, 17) == F2SpatialTransport(10**100, 5**100)
    assert F2SpatialTransport(1, 17).frobenius_factors() == ()
    assert F2SpatialTransport(1, 17).shifts() == ()
    source: tuple[int, ...] = (1, 0, 1)
    assert F2SpatialTransport(1, 17).apply(source, shift=_shift, add=_add) == (0, 0, 0)


def test_affine_composition_transports_earlier_output_forcing() -> None:
    source: tuple[int, ...] = (1, 1, 0, 1)
    before: F2AffineTransport[tuple[int, ...]] = F2AffineTransport(
        F2SpatialTransport(0, 1), (1, 0, 1, 0, 0)
    )
    after: F2AffineTransport[tuple[int, ...]] = F2AffineTransport(
        F2SpatialTransport(0, 2), (0, 1, 0, 1, 0, 0, 0)
    )
    intermediate = before.apply(source, shift=_shift, add=_add)
    sequential = after.apply(intermediate, shift=_shift, add=_add)
    composed = before.then(after, shift=_shift, add=_add)
    assert composed.linear == F2SpatialTransport(0, 3)
    assert composed.forcing == _add(
        after.linear.apply(before.forcing, shift=_shift, add=_add), after.forcing
    )
    assert composed.apply(source, shift=_shift, add=_add) == sequential


def test_annihilating_after_action_leaves_only_its_forcing() -> None:
    source: tuple[int, ...] = (1, 0, 1)
    before: F2AffineTransport[tuple[int, ...]] = F2AffineTransport(
        F2SpatialTransport(), (1, 1, 0)
    )
    after: F2AffineTransport[tuple[int, ...]] = F2AffineTransport(
        F2SpatialTransport(1, 9), (0, 1, 1)
    )
    combined = before.then(after, shift=_shift, add=_add)
    assert combined.linear.annihilated
    assert combined.forcing == after.forcing
    assert combined.apply(source, shift=_shift, add=_add) == after.forcing
    assert combined.apply(source, shift=_shift, add=_add) == after.apply(
        before.apply(source, shift=_shift, add=_add), shift=_shift, add=_add
    )


def test_exact_input_contracts_fail_closed() -> None:
    for bad in (True, -1, 1.0):
        with pytest.raises(ValueError):
            F2SpatialTransport(bad, 0)  # type: ignore[arg-type]
    bad_shift: object = True
    with pytest.raises(TypeError):
        F2SpatialTransport().coefficient(bad_shift)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        F2SpatialTransport().then(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        F2AffineTransport(object(), (0,))  # type: ignore[arg-type]
