"""Bounded audit tests for the abstract comma temporal observer.

These tests are finite differential evidence.  They do not assert that one
abstract observer tick is a native decade, nor do they enable a production
temporal quotient.
"""

from __future__ import annotations

import pytest

from devtools.verification.comma_temporal_observers import (
    ABSTRACT_PERIOD,
    ABSTRACT_TRANSIENT,
    DYADIC_PERIOD,
    MAX_TRACE_LENGTH,
    JointObserverState,
    Radix9Word,
    dyadic_duration_representative,
    joint_observer_trace,
    q21_port_bytes,
    radix9_port_bytes,
    reset_germ_code,
)

pytestmark = pytest.mark.validation


@pytest.fixture(scope="module")
def _states() -> tuple[JointObserverState, ...]:
    """One read-only finite oracle shared by all audit assertions."""

    return joint_observer_trace(ABSTRACT_PERIOD + ABSTRACT_TRANSIENT + 1)


def test_joint_observer_has_exact_bytes_and_bounded_13863_classes(
    _states: tuple[JointObserverState, ...],
) -> None:
    states = _states
    signatures = [state.signature for state in states]

    assert all(type(signature) is bytes for signature in signatures)
    # The 3 transient states and one 13,860-state cycle account for the
    # duplicate at 3+13,860; signatures are compared as complete bytes.
    assert len(set(signatures)) == ABSTRACT_PERIOD + ABSTRACT_TRANSIENT
    assert states[ABSTRACT_TRANSIENT] == states[ABSTRACT_TRANSIENT + ABSTRACT_PERIOD]


def test_q21_and_reset_witnesses_separate_the_first_two_periodic_copies(
    _states: tuple[JointObserverState, ...],
) -> None:
    states = _states

    # At (f,d)=(1,0), n=1 and n=13861 have the same endpoint and harmonic
    # phase; Q21 remains a complete declared output and separates them.
    assert states[1].port_vector == states[1 + ABSTRACT_PERIOD].port_vector
    assert states[1].harmonic_phase == states[1 + ABSTRACT_PERIOD].harmonic_phase
    assert q21_port_bytes(states[1], 1, 0) != q21_port_bytes(
        states[1 + ABSTRACT_PERIOD], 1, 0
    )

    # At (f,d)=(7,0), the Q21, first-defect, endpoint and harmonic fields
    # already agree at n=2 and n=13862.  The last non-neutral reset germ is
    # the concrete separating field: R(4) versus R(3), encoded 5 versus 4.
    assert states[2].port_vector == states[2 + ABSTRACT_PERIOD].port_vector
    assert states[2].harmonic_phase == states[2 + ABSTRACT_PERIOD].harmonic_phase
    assert states[2].q21 == states[2 + ABSTRACT_PERIOD].q21
    assert states[2].first_defect == states[2 + ABSTRACT_PERIOD].first_defect
    assert reset_germ_code(states[2], 7, 0) == 5
    assert reset_germ_code(states[2 + ABSTRACT_PERIOD], 7, 0) == 4


def test_dyadic_audit_has_two_transients_and_a_60_cycle(
    _states: tuple[JointObserverState, ...],
) -> None:
    dyadic = tuple(
        _states[dyadic_duration_representative(level)]
        for level in range(DYADIC_PERIOD + 2)
    )

    assert len({state.signature for state in dyadic}) == DYADIC_PERIOD + 2
    assert dyadic_duration_representative(62) == dyadic_duration_representative(2)
    assert _states[dyadic_duration_representative(62)] == dyadic[2]


def test_radix9_word_append_law_uses_length_modulo_six() -> None:
    for left_sum in range(19):
        for right_sum in range(19):
            left = Radix9Word.atom(left_sum)
            right = Radix9Word.atom(right_sum)
            expected = ((left_sum % 9) + 2 * (right_sum % 9)) % 9
            assert left.then(right) == Radix9Word(2, expected)
    assert Radix9Word.identity().then(Radix9Word.atom(7)) == Radix9Word.atom(7)


def test_radix9_vector_has_one_transient_and_period_180(
    _states: tuple[JointObserverState, ...],
) -> None:
    assert len({state.radix9 for state in _states[:181]}) == 181
    assert _states[0].radix9 != _states[180].radix9
    assert _states[1].port_vector == _states[181].port_vector
    assert _states[1].radix9 == _states[181].radix9
    assert all(
        before.radix9 == after.radix9
        for before, after in zip(_states[1:-180], _states[181:], strict=True)
    )
    assert radix9_port_bytes(_states[1], 1, 0) == _states[1].radix9[:2]


@pytest.mark.parametrize("limit", (-1, True, MAX_TRACE_LENGTH + 1, 10**100))
def test_joint_audit_rejects_unbounded_traces(limit: int) -> None:
    with pytest.raises(ValueError):
        joint_observer_trace(limit)
