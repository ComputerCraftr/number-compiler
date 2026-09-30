"""Concrete constructor laws and rejected shortcuts, not cold-work certificates."""

from fractions import Fraction

import pytest

from devtools.verification.decimal_endpoint_seam import decimal_step
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.inverse_three_clock import InverseThreeClock
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.reverse_add.active_output import PAIR
from number_compiler.sequences.reverse_add.contextual_residual import (
    ReverseContextualResidualArena,
)

pytestmark = pytest.mark.validation


def _source_prefix(clock: int, source: int, events: int) -> tuple[Fraction, int, int]:
    """Scalar proof oracle: deliberately charges one ordinary step per event."""
    beta = Fraction(0)
    valuation_sum = 0
    target = source
    for event in range(events):
        beta -= Fraction(1 << valuation_sum, 3 ** (clock + event + 1))
        step = accelerated_odd_collatz(target)
        valuation_sum += step.valuation
        target = step.target
    return beta, valuation_sum, target


@pytest.mark.parametrize("clock", (0, 1, 17))
@pytest.mark.parametrize("source", (1, 27, 65, 129, 58723))
def test_source_derived_cylinder_identity_and_prefix_composition(
    clock: int, source: int
) -> None:
    for events, more in ((0, 0), (0, 4), (1, 1), (2, 2), (4, 4), (8, 8)):
        beta, consumed, midpoint = _source_prefix(clock, source, events)
        tail, tail_bits, target = _source_prefix(clock + events, midpoint, more)
        whole, total_bits, final = _source_prefix(clock, source, events + more)
        assert final == target
        assert total_bits == consumed + tail_bits
        assert whole == beta + (1 << consumed) * tail
        normalized_source = Fraction(source, 3**clock)
        normalized_target = Fraction(target, 3 ** (clock + events + more))
        assert normalized_source - whole == (1 << total_bits) * normalized_target
        if total_bits:
            modulus = 1 << total_bits
            prefix = whole.numerator * pow(whole.denominator, -1, modulus) % modulus
            assert prefix == source * pow(3**clock, -1, modulus) % modulus


def test_phase_death_does_not_identify_endpoint_or_physical_weight() -> None:
    clock = InverseThreeClock(6, 0)
    assert clock.advance(16) == clock
    assert clock.normalized_prefix(1) == clock.normalized_prefix(129) == 1
    _, first_bits, first = _source_prefix(0, 1, 16)
    _, second_bits, second = _source_prefix(0, 129, 16)
    assert (first, first_bits, 16 + first_bits) == (1, 32, 48)
    assert (second, second_bits, 16 + second_bits) == (175, 25, 41)


def test_inverse_three_phase_death_needs_the_low_precision_side_condition() -> None:
    # v2(3**(2**p)-1)=p+2 requires p>=1. At p=0 the valuation is one.
    assert (3 ** (2**0) - 1) == 2
    assert pow(3, -(2**0), 4) != 1
    for precision in range(3, 19):
        level = precision - 2
        assert pow(3, -(1 << level), 1 << precision) == 1


def test_shared_decimal_action_pulls_future_threshold_back_to_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A fixed no-growth chamber. The action is shared; source values are
    # occurrence bindings, never part of the consumer-transformer identity.
    arena = ReverseContextualResidualArena(BitFunctionArena(ResourceLedger()))
    source = FinitePort(PortVariable(0, 0, "pullback-source", 0), 9)
    target = FinitePort(PortVariable(0, 1, "pullback-target", 0), 19)
    s = arena.bits.variable((source,), source, AtomSort("lt-pair", 9))
    t = arena.bits.variable((target,), target, PAIR)
    double = arena.bits.map_atoms(s, PAIR, tuple(2 * i for i in range(9)))
    future_gt = arena.bits.map_atoms(t, BOOL, tuple(int(i >= 10) for i in range(19)))
    threshold_five = arena.bits.map_atoms(s, BOOL, tuple(int(i >= 5) for i in range(9)))
    evaluate = arena.bits.evaluate

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("consumer pullback evaluated a concrete occurrence")

    monkeypatch.setattr(arena.bits, "evaluate", forbidden)
    pulled = arena.pullback(future_gt, {target.variable: double})
    assert pulled == threshold_five
    # One canonical pulled consumer handles both current LT occurrences.
    assert evaluate(pulled, {source.variable: 2}) == 0
    assert evaluate(pulled, {source.variable: 8}) == 1
    for value in range(9):
        assert evaluate(pulled, {source.variable: value}) == int(2 * value >= 10)
    assert decimal_step((2,)) == (4,)
    assert decimal_step((8,)) == (16,)


def test_endpoint_is_not_an_idempotent_canonical_representation() -> None:
    source = (2,)
    assert decimal_step(decimal_step(source)) == (8,)
    assert decimal_step(source) == (4,)
    # If NF were the endpoint step, the proposed NF(T(NF(O)))=NF(T(O))
    # seam equation would fail on this reachable one-cell occurrence.
    assert decimal_step(decimal_step(decimal_step(source))) == (16,)
    assert decimal_step(decimal_step(source)) != (16,)
