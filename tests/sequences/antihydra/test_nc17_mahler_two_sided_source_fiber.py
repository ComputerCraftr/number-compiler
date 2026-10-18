"""Exact Mahler integer, fractional and Antihydra-ledger source products."""

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import HalfOpenInterval
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as antihydra_keys
from number_compiler.sequences.antihydra.mahler_odd_macro import (
    MahlerOddToOddAction,
)
from number_compiler.sequences.antihydra.mahler_two_sided_cylinder import (
    MahlerFractionalGuardEmpty,
    MahlerGuardedSourceFiber,
    MahlerLedgerUnsafe,
    MahlerTwoSidedCylinder,
)


def _pointed(source: int) -> MahlerGuardedSourceFiber:
    cylinder = MahlerTwoSidedCylinder.from_pointed_source(
        source,
        binary_bits=8,
        five_places=1,
        leading_bits=min(8, source.bit_length()),
    )
    return MahlerGuardedSourceFiber(cylinder, HalfOpenInterval(), 0)


def test_integer_admission_does_not_replace_fractional_guard() -> None:
    source = 7
    two_odd_bits = MahlerOddToOddAction.from_bits((1, 1))
    assert two_odd_bits.integer_admits(source)
    assert two_odd_bits.joint.guard.empty

    with pytest.raises(MahlerFractionalGuardEmpty):
        _pointed(source).advance(two_odd_bits)


def test_forced_future_stops_at_first_empty_fractional_guard() -> None:
    action, fiber, accepted, reason = _pointed(7).forced_future(
        max_events=16, max_extent=128
    )

    assert accepted == 1
    assert action.extent == 1
    assert fiber.integers.first == fiber.integers.last == 11
    assert reason == "fractional_guard"
    assert not fiber.fractional_guard.empty
    assert fiber.ledger_balance == 2


def test_integer_cylinder_transport_keeps_the_full_affine_stride() -> None:
    source = MahlerTwoSidedCylinder(
        lower=7,
        upper=255,
        residue=7,
        modulus=16,
    )
    action = MahlerOddToOddAction.run(1)
    admitted = source.admitted_by(action)
    assert admitted is not None
    assert admitted.count == source.count

    target = source.transport(action)
    assert target.count == source.count
    assert target.modulus == 24
    assert target.first == (3 * source.first + 1) // 2
    assert target.last == (3 * source.last + 1) // 2


def test_forced_singleton_cylinder_carries_newly_implied_action_guard() -> None:
    # The initial 341 mod 1280 cylinder is a singleton, but its ambient stride
    # does not imply the exponent-10 parity guard modulo 2048.  Restricting to
    # the action's exact source guard preserves that singleton and supplies an
    # integral affine stride for transport.
    ledger = ResourceLedger()
    source = MahlerTwoSidedCylinder.from_pointed_source(
        341,
        binary_bits=8,
        five_places=1,
        leading_bits=8,
        ledger=ledger,
    )
    assert (source.first, source.last, source.count) == (341, 341, 1)
    assert source.modulus == 1280
    assert source.forced_next_odd_exponent == 10
    construction_work = ledger.counters[
        antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS
    ]
    source.summary(upper_bits=8, low_bits=8, five_places=1, ledger=ledger)
    assert (
        ledger.counters[antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS]
        > construction_work
    )

    event = source.next_forced_event()
    assert event is not None
    action, target = event

    assert action.extent == 10
    assert target.count == source.count
    assert (
        target.first == target.last == (3**10 * 341 + action.joint.innovation) // 2**10
    )


def test_identity_transport_checks_and_retains_the_odd_source_guard() -> None:
    identity = MahlerOddToOddAction.identity()

    with pytest.raises(ValueError, match="complete action guard"):
        MahlerTwoSidedCylinder(2, 2, 0, 1).transport(identity)

    # The singleton is odd even though its ambient modulus does not imply
    # parity. Guard intersection authenticates the exact finite set and
    # returns a strengthened cylinder rather than skipping the guard.
    odd_singleton = MahlerTwoSidedCylinder(7, 7, 0, 1)
    transported = odd_singleton.transport(identity)
    assert transported.count == 1
    assert transported.first == transported.last == 7
    assert transported.modulus == 2
    assert transported.residue == 1


def test_summary_rejects_unbounded_precision_before_ledger_charge() -> None:
    cylinder = MahlerTwoSidedCylinder.from_pointed_source(
        341, binary_bits=8, five_places=1, leading_bits=8
    )
    ledger = ResourceLedger()
    before = dict(ledger.counters)

    assert cylinder.low_ports(0, 10**8) is None
    with pytest.raises(ValueError, match="precision"):
        cylinder.summary(five_places=10**8, ledger=ledger)
    with pytest.raises(ValueError, match="precision"):
        cylinder.summary(low_bits=-1, ledger=ledger)

    assert dict(ledger.counters) == before


def test_ledger_safety_is_separate_from_fractional_safety() -> None:
    action = MahlerOddToOddAction.run(5)
    integers = MahlerTwoSidedCylinder.from_pointed_source(
        53, binary_bits=8, five_places=1, leading_bits=6
    )
    assert integers.admitted_by(action) is not None
    assert not action.joint.guard.empty
    unsafe = MahlerGuardedSourceFiber(integers, HalfOpenInterval(), -action.minimum - 1)

    with pytest.raises(MahlerLedgerUnsafe):
        unsafe.advance(action)
