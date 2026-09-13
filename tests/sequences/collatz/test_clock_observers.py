from math import comb

import pytest

from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers
from number_compiler.sequences.collatz.power import CollatzEventArena
from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselCylinder,
    HenselAffineBlock,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded


def test_all_views_are_specializations_of_one_clock_polynomial() -> None:
    depths = (1, 4, 2, 3, 1)
    arena = CollatzEventArena()
    node = arena.from_valuations(depths)
    observer = CollatzClockObservers(arena)
    points = []
    ksum = 0
    for j, k in enumerate(depths):
        points.append((len(depths) - 1 - j, ksum))
        ksum += k
    nodes_before = arena.node_count
    offset = sum(3**a * 2**b for a, b in points)
    for modulus in (16, 27, 35, 257):
        m = observer.modular(node, modulus)
        assert (m.upper, m.offset, m.lower) == (
            3 ** len(depths) % modulus,
            offset % modulus,
            2**ksum % modulus,
        )
        assert observer.hasse(node, degree=4, modulus=modulus) == tuple(
            sum(3**a * comb(b, j) for a, b in points) % modulus for j in range(4)
        )
        for width in (1, 3, 5):
            for sign in (-1, 1):
                expected = [0] * width
                for a, b in points:
                    expected[b % width] += 3**a * sign ** (b // width)
                assert observer.twisted(
                    node, width=width, sign=sign, modulus=modulus
                ) == tuple(x % modulus for x in expected)
    for alpha, beta in ((1, 1), (-3, 2), (4, -1), (0, 0)):
        assert observer.tropical(node, s_weight=alpha, z_weight=beta) == min(
            alpha * a + beta * b for a, b in points
        )
    clock = observer.clock(node)
    assert clock.physical_ticks == len(depths) + ksum
    assert tuple(
        a + b
        for a, b in zip(
            clock.real_prime_exponents,
            (clock.two_adic_exponent, clock.three_adic_exponent),
        )
    ) == (0, 0)
    assert arena.node_count == nodes_before
    assert arena.cocycle_materializations == 0


def test_hensel_projection_commutes_with_transport_and_preserves_guards() -> None:
    arena = CollatzEventArena()
    node = arena.from_valuations((1, 2, 3))
    views = CollatzClockObservers(arena)
    exact = arena.materialize_cocycle(node)
    for target in (HenselCylinder(0, 0), HenselCylinder(1, 1), HenselCylinder(4, 7)):
        observed = views.hensel_pullback(node, target)
        assert observed == target.pullback(HenselAffineBlock(3, 6, exact.addend))
        for x in range(512):
            numerator = 27 * x + exact.addend
            assert observed.contains(x) == (
                numerator % 64 == 0 and target.contains(numerator // 64)
            )
    # Exact event valuations need the odd target, not just divisibility by 2**K.
    cylinder = views.hensel_pullback(node, HenselCylinder(1, 1))
    for x in range(cylinder.residue, cylinder.residue + 512, 1 << cylinder.bits):
        assert arena.apply_exact(node, x) & 1


def test_powered_observers_never_lower_or_walk_temporal_midpoints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = CollatzEventArena()

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("exact lowering or event execution")

    monkeypatch.setattr(CollatzEventArena, "materialize_cocycle", forbidden)
    monkeypatch.setattr(CollatzEventArena, "apply_exact", forbidden)
    for level in range(11):
        node = arena.power(arena.event(2), 1 << level)
        views = CollatzClockObservers(arena)
        transfer = views.modular(node, 257)
        # P for repeated k=2 is 4**n-3**n; no division or expanded itinerary.
        n = 1 << level
        assert transfer.offset == (pow(4, n, 257) - pow(3, n, 257)) % 257
        assert views.node_evaluations <= level + 1
        assert views.compositions <= level
    huge = arena.power(arena.event(2), 10**100 + 17)
    views = CollatzClockObservers(arena)
    assert (
        views.modular(huge, 257).offset
        == (pow(4, 10**100 + 17, 257) - pow(3, 10**100 + 17, 257)) % 257
    )
    assert views.node_evaluations < 700
    with pytest.raises(BlockContextBudgetExceeded):
        views.hensel_pullback(huge, HenselCylinder(1, 1))
    assert arena.cocycle_materializations == 0


def test_factor_output_is_conditional_and_nodes_remain_scoped() -> None:
    arena = CollatzEventArena()
    node = arena.from_valuations((1, 1))
    views = CollatzClockObservers(arena)
    assert views.factor_observation(node, 15).proper_factor == 5
    assert views.factor_observation(node, 7).proper_factor is None
    other = CollatzEventArena()
    with pytest.raises(ValueError, match="another arena"):
        views.modular(other.event(1), 15)
    with pytest.raises(ValueError, match="another arena"):
        arena.concat(node, other.event(1))
