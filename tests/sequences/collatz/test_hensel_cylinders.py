"""Exact dying forcing projection, including finite-precision boundary cases."""

from collections import Counter
from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.carry.collatz_output_quotient import radix64_domain
from number_compiler.arithmetic.fields.two_adic import v2_nonzero
from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselAffineBlock,
    HenselCylinder,
    three_dyadic_phase,
    three_unit_phase,
)
from number_compiler.sequences.collatz.root_germs import RationalPadicRootGerm


def test_radix64_root_cylinder_quotients_clock_and_constant() -> None:
    fibers = Counter(
        HenselCylinder.from_root(6, h, c) for h, c in product(range(16), range(64))
    )
    assert len(fibers) == 64
    assert set(fibers.values()) == {16}
    domains = Counter(radix64_domain(c.residue) for c in fibers)
    assert tuple(domains[i] for i in range(5)) == (21, 1, 20, 1, 21)


@pytest.mark.parametrize("bits", (6, 12, 18, 24, 30))
def test_raw_representatives_have_same_all_symbol_successors(bits: int) -> None:
    order = 1 << (bits - 2)
    for h, c in ((2, 3), (17, -1001), ((1 << 256) + 19, (1 << 96) + 77)):
        image = HenselCylinder.from_root(bits, h, c)
        other = HenselCylinder.from_root(bits, h + 3 * order, c + 7 * (1 << bits))
        assert image == other
        assert image.residue == -c * pow(pow(3, h, 1 << bits), -1, 1 << bits) % (
            1 << bits
        )
        for d in range(64):
            event = image.consume(d)
            assert event == other.consume(d)
            if d != image.residue % 64:
                assert event.status == "mismatch" and event.target is None
                assert event.valuation_bits == v2_nonzero(d - image.residue % 64)
            else:
                assert event.valuation_bits == 6
                assert event.target == (
                    HenselCylinder(bits - 6, image.residue >> 6) if bits > 6 else None
                )
                assert event.status == ("match" if bits > 6 else "exhausted")


def test_phase_powering_including_small_precision_and_lte_exception() -> None:
    for bits in range(33):
        for j in range(36):
            phase = three_dyadic_phase(j, bits)
            assert phase == pow(3, 1 << j, 1 << bits)
            assert three_dyadic_phase(j + 1, bits) == phase * phase % (1 << bits)
        for h in range(32):
            assert three_unit_phase(h, bits) == pow(3, h, 1 << bits)
    assert [three_dyadic_phase(j, 6) for j in range(5)] == [3, 9, 17, 33, 1]
    assert three_dyadic_phase(0, 2) == 3
    assert three_dyadic_phase(1, 2) == 1
    assert three_dyadic_phase(10**100, 30) == 1
    assert v2_nonzero(3 - 1) == 1  # LTE j+2 only holds from j=1.


def test_exhaustion_retains_unknown_higher_valuation() -> None:
    universal = HenselCylinder(0, 0).consume(63)
    assert universal.status == "exhausted" and universal.valuation_bits == 0
    for bits in range(1, 6):
        c = HenselCylinder(bits, 3)
        for symbol in range(64):
            event = c.consume(symbol)
            if c.contains(symbol):
                assert event.status == "exhausted" and event.valuation_bits == bits
            else:
                assert event.status == "mismatch" and event.valuation_bits < bits
    assert HenselCylinder(12, 99) != HenselCylinder(6, 99)


def test_germ_projection_uses_finite_clock_without_full_denominator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = RationalPadicRootGerm(40, 313)

    def forbidden(_self: object) -> int:
        raise AssertionError("finite root projection constructed full denominator")

    monkeypatch.setattr(RationalPadicRootGerm, "denominator", property(forbidden))
    assert root.root_residue(30) == HenselCylinder.from_root(30, 40, 313).residue


def test_pullback_composes_and_keeps_integrality_for_universal_target() -> None:
    first, second = HenselAffineBlock(2, 3, 5), HenselAffineBlock(3, 4, 7)
    for q, r in product(range(9), range(9)):
        target = HenselCylinder(q, r)
        assert target.pullback(second).pullback(first) == target.pullback(
            first.then(second)
        )
    target = HenselCylinder(0, 0).pullback(first)
    assert target.bits == 3
    for x in range(-64, 64):
        assert target.contains(x) == ((9 * x + 5) % 8 == 0)
    for bad in (True, -1, 1.5):
        with pytest.raises((ValueError, TypeError)):
            three_unit_phase(cast(int, bad), 6)
