"""Exact packet-clock experiments; none of these assertions admits CLI returns."""

from __future__ import annotations

from math import comb
from random import Random

import pytest

from devtools.experiments.reverse_add.radial_event_clock import (
    ClockLimits,
    ClockWitness,
    ClockWork,
    RadialEventPacket,
    expression_packets,
    extract_radial_clock,
)
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.centered_events import clock_event_tail
from number_compiler.arithmetic.fields.event_innovation import event_difference
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.arithmetic.fields.test_centered_carry import _evaluate, _polynomial


def _literal(packets: tuple[RadialEventPacket, ...]) -> ClockWitness | None:
    values: dict[int, int] = {}
    for packet in packets:
        for k in range(packet.growth + 1):
            i = packet.shift + k
            values[i] = values.get(i, 0) + (
                packet.coefficient * (1 << packet.no_growth) * comb(packet.growth, k)
            )
    nonzero = sorted((i, c) for i, c in values.items() if c)
    return ClockWitness(*nonzero[0]) if nonzero else None


def test_packet_clock_matches_independent_bounded_polynomial_oracle() -> None:
    random = Random(196)
    for _ in range(1500):
        packets = tuple(
            RadialEventPacket(
                random.randrange(-10, 11),
                random.randrange(-4, 16),
                random.randrange(16),
                random.randrange(4),
            )
            for _ in range(random.randrange(1, 9))
        )
        assert extract_radial_clock(packets, work=ClockWork()) == _literal(packets)


def test_cross_radial_identity_has_an_exact_sparse_zero_certificate() -> None:
    packets = (
        RadialEventPacket(1, 0, 1),
        RadialEventPacket(-1, 0, 0),
        RadialEventPacket(-1, 1, 0),
    )
    work = ClockWork()
    assert extract_radial_clock(packets, work=work) is None
    assert work.zero_blocks == 1
    assert work.jet_coefficients == 4


def test_new_packet_can_cancel_the_first_nonzero_jet_of_earlier_packets() -> None:
    # Looking only at the packets that start at zero would incorrectly emit -1
    # at position one. The later-starting packet cancels it exactly.
    packets = (
        RadialEventPacket(1, 0, 0),
        RadialEventPacket(-1, 0, 1),
        RadialEventPacket(1, 1, 0),
        RadialEventPacket(7, 10**200, 0),
    )
    work = ClockWork()
    assert extract_radial_clock(packets, work=work) == ClockWitness(10**200, 7)
    assert work.jet_coefficients == 5
    assert work.zero_blocks == 1


def test_jet_order_can_exceed_packet_count_minus_one() -> None:
    packets = (
        RadialEventPacket(-1, 0, 0),
        RadialEventPacket(1, 0, 3),
        RadialEventPacket(-3, 1, 1),
    )
    assert extract_radial_clock(packets, work=ClockWork()) == ClockWitness(3, 1)


def test_enormous_radial_powers_need_only_two_exact_jets() -> None:
    exponent = 10**200
    packets = (
        RadialEventPacket(1, 17, exponent + 1),
        RadialEventPacket(-1, 17, exponent),
    )
    work = ClockWork()
    assert extract_radial_clock(packets, work=work) == ClockWitness(18, 1)
    assert work.jet_coefficients == 2


def test_incorrect_jet_bound_cannot_certify_zero(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.experiments.reverse_add.radial_event_clock as clock

    monkeypatch.setattr(clock, "_bound", lambda packets: packets[0].shift)
    with pytest.raises(ArithmeticError, match="zero certificate"):
        extract_radial_clock(
            (RadialEventPacket(1, 0, 2), RadialEventPacket(-1, 0, 1)),
            work=ClockWork(),
        )


@pytest.mark.parametrize("slope", [-1, 1])
def test_extractor_consumes_existing_event_normalizer_and_reflected_radials(
    slope: int,
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    expression = arena.chart(
        arena.radial(arena.interval(3), RadialMultiplier(2, 4)),
        CylinderChart(slope, -3),
    )
    events = event_difference(arena, expression)
    packets = expression_packets(arena, events, limits=ClockLimits())
    literal = min(_evaluate(arena, events).items())
    assert extract_radial_clock(packets, work=ClockWork()) == ClockWitness(*literal)


def test_clock_tail_compensation_remains_required_after_extraction() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    events = event_difference(arena, _polynomial(arena, [0, 2, 1]))
    witness = extract_radial_clock(
        expression_packets(arena, events, limits=ClockLimits()), work=ClockWork()
    )
    assert witness is not None
    assert witness == ClockWitness(1, 2)
    tail = clock_event_tail(
        arena, events, extent=3, prefix=witness.prefix, leading=witness.leading
    )
    assert extract_radial_clock(
        expression_packets(arena, tail, limits=ClockLimits()), work=ClockWork()
    ) == ClockWitness(0, 1)


def test_unresolved_source_atoms_are_not_implicitly_evaluated() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    source = arena.atom(SemanticIdentity("clock-test", (1,)))
    with pytest.raises(ValueError, match="resolved scalar"):
        expression_packets(arena, source, limits=ClockLimits())


def test_jet_and_integer_limits_refuse_without_a_zero_claim() -> None:
    packets = (RadialEventPacket(1, 0, 2), RadialEventPacket(-1, 0, 1))
    with pytest.raises(ValueError, match="jet budget"):
        extract_radial_clock(
            packets, work=ClockWork(), limits=ClockLimits(max_jet_coefficients=1)
        )
    with pytest.raises(ValueError, match="integer budget"):
        extract_radial_clock((RadialEventPacket(1, 0, 0, 10**200),), work=ClockWork())


def test_repeated_small_integer_work_has_a_separate_aggregate_limit() -> None:
    packets = tuple(RadialEventPacket(1, i, 0) for i in range(8))
    work = ClockWork()
    with pytest.raises(ValueError, match="integer work budget"):
        extract_radial_clock(
            packets,
            work=work,
            limits=ClockLimits(max_integer_bits=10, max_integer_work_bits=10),
        )
    assert work.integer_work_bits > 10
    assert work.jet_coefficients == 0
