"""Independent source semantics for the formal decimal growth potential."""

from itertools import product

import pytest

from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
)


def _step(pair: tuple[int, ...]) -> tuple[tuple[int, ...], bool]:
    carry = 0
    digits = []
    for value in pair:
        carry, digit = divmod(value + carry, 10)
        digits.append(digit)
    if carry:
        digits.append(1)
    return tuple(a + b for a, b in zip(digits, reversed(digits), strict=True)), bool(
        carry
    )


def _rank(edge: int) -> int:
    if edge == 18:
        return 3
    if edge == 9:
        return 2
    return int(edge >= 10)


@pytest.mark.parametrize("width", (1, 2, 3, 4, 5))
def test_actual_symmetric_carry_refines_certificate_edge_graph(width: int) -> None:
    graph = dict(DECIMAL_REVERSE_GROWTH_CERTIFICATE.outer_successors)
    for half in product(range(19), repeat=(width + 1) // 2):
        tail = half[:-1] if width % 2 else half
        pair = half + tuple(reversed(tail))
        target, growth = _step(pair)
        assert target == target[::-1]
        assert all(0 <= value <= 18 for value in target)
        if growth:
            assert 9 <= pair[0] <= 18
            assert target[0] == 1 + pair[0] % 10 == graph[pair[0]]
            assert _rank(target[0]) + 1 == _rank(pair[0])
        else:
            assert _rank(target[0]) <= _rank(pair[0]) + 3


def test_neutral_lsd_can_coexist_with_terminal_growth() -> None:
    target, growth = _step((9, 18, 9))
    assert growth
    assert target == (10, 8, 8, 10)
    assert _rank(target[0]) + 1 == _rank(9)


@pytest.mark.parametrize("seed", (0, 1, 18, 196, 999, 909, 1041, 1051, 1593))
def test_source_growth_potential_bounds_live_radial_age(seed: int) -> None:
    digits = tuple(map(int, reversed(str(seed))))
    state = tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
    initial_rank = _rank(state[0])
    q = r = run = 0
    trace = []
    for _ in range(256):
        state, growth = _step(state)
        trace.append(growth)
        if growth:
            r += 1
            run += 1
        else:
            q += 1
            run = 0
        assert run <= DECIMAL_REVERSE_GROWTH_CERTIFICATE.maximum_consecutive_growth
        assert r + _rank(state[0]) <= 3 * q + initial_rank
        # Every 20-step live segment has already accumulated five doublings.
        if len(trace) >= 20:
            assert trace[-20:].count(False) >= 5
    if seed == 999:
        assert trace[:4] == [True, True, True, False]
