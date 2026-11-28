"""Finite conditional periods with independent physical boundary controls."""

from __future__ import annotations

from itertools import product

import pytest

pytestmark = pytest.mark.validation


def _pair_gate(m: int, a: int, b: int, c: int) -> int:
    base = 10 // m
    left = m * (b % base) + a // base
    right = m * (c % base) + b // base
    return m * (left % base) + right // base


@pytest.mark.parametrize(
    ("m", "moving", "size"),
    [(2, False, 31), (2, True, 31), (5, False, 31), (5, True, 21)],
)
def test_complete_extreme_drive_monoid(m: int, moving: bool, size: int) -> None:
    identity = tuple(range(10))
    generators = {
        tuple(
            _pair_gate(m, x, a, b) if moving else _pair_gate(m, a, b, x)
            for x in identity
        )
        for a, b in product(identity, repeat=2)
    }
    work = [identity]
    reached = {identity}
    while work:
        response = work.pop()
        for g in generators:
            composed = tuple(g[x] for x in response)
            assert len(set(composed)) <= 2
            assert all(
                composed[composed[composed[composed[x]]]] == composed[composed[x]]
                for x in identity
            )
            if composed not in reached:
                work.append(composed)
                reached.add(composed)
    assert len(reached) == size


@pytest.mark.parametrize(("m", "states"), [(2, (1, 4, 7, 1)), (5, (1, 7, 4, 1))])
def test_closed_two_cell_ring_needs_both_ports(m: int, states: tuple[int, ...]) -> None:
    ring = (states[0], states[0])
    for expected in states[1:]:
        a, b = ring
        ring = (_pair_gate(m, b, a, b), _pair_gate(m, a, b, a))
        assert ring == (expected, expected)


def test_q19_raw_factors_for_every_reachable_guarded_response() -> None:
    # Retain complete responses, so a congruent residue cannot merge unequal raw sums.
    identity = tuple(range(19))
    generators = {
        tuple((s + a) % 10 + (v if birth else (s + v) % 10) for s in identity)
        for birth in (False, True)
        for a in range(2)
        for v in range(10 if birth else 2)
    }
    work = [identity]
    reached = {identity}
    periods: set[int] = set()
    while work:
        f = work.pop()
        for g in generators:
            h = tuple(g[x] for x in f)
            if h not in reached:
                reached.add(h)
                work.append(h)
        if f != identity:
            for x in identity:
                # One whole block fixes the parity for nonunit slopes; the
                # last physical port recovers the raw sum on the following block.
                y = f[f[x]]
                z = f[y]
                for k in range(1, 11):
                    if z == y:
                        periods.add(k)
                        break
                    z = f[z]
                else:
                    pytest.fail("uncovered guarded return")
    assert periods == {1, 2, 4, 5, 10}


@pytest.mark.parametrize("k", [1, 2, 7, 64, 256])
def test_q19_equal_outer_sums_do_not_determine_birth(k: int) -> None:
    for middle, growth in (("00", 0), ("55", 1)):
        digits = "1" * k + middle + "8" * k
        assert all(int(digits[i]) + int(digits[-1 - i]) == 9 for i in range(k))
        assert len(str(int(digits) + int(digits[::-1]))) == len(digits) + growth
