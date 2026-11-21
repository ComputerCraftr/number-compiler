"""C0 low-column signals retain physical clocks and same-time events."""

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.periodic_slp import periodic_word
from number_compiler.arithmetic.carry.temporal_signal import TemporalSignalBank
from number_compiler.sequences.double_reverse import c0_signal_session
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _mixed_low_pair(value: int) -> int:
    low, high = value % 10, value // 10 % 10

    def mix(digit: int) -> int:
        return int(digit >= 5) + (5 - digit if digit < 5 else 0)

    return mix(low) + 6 * mix(high)


def test_c0_signal_same_time_and_warm_parent(monkeypatch: pytest.MonkeyPatch) -> None:
    # Event 1 holds throughout C0; event 2 holds only on mixed mask 7.
    transitions = tuple(((0, 3 if symbol == 7 else 1),) for symbol in range(10))
    value = 196
    mixed: list[int] = []
    for generation in range(65):
        if generation >= 16:
            mixed.append(_mixed_low_pair(value))
        value = 2 * int(str(value)[::-1])
    expected = next(16 + i for i, symbol in enumerate(mixed[:20]) if symbol == 7)
    with DoubleReverseTerm(196, 64) as term:
        with term.c0_signal_session(transitions, 3) as signal:
            assert signal.first(16, 20) == expected

            def no_recompile(*_args: object) -> None:
                raise AssertionError("warm signal parent was recomposed")

            monkeypatch.setattr(TemporalSignalBank, "_then", no_recompile)
            monkeypatch.setattr(c0_signal_session, "_mixed_period", no_recompile)
            monkeypatch.setattr(c0_signal_session, "periodic_word", no_recompile)
            assert signal.first(16, 20) == expected
        with pytest.raises(ValueError, match="closed"):
            signal.first(16, 20)
        with term.c0_signal_session(transitions, 2) as signal:
            with pytest.raises(ValueError, match="before its admitted source"):
                signal.first(0, 2)


def test_c0_signal_reports_same_time_intersection() -> None:
    # 7 and 9 occur at different times, so their events never intersect.
    transitions = tuple(
        ((0, 1 if symbol == 7 else 2 if symbol == 9 else 0),) for symbol in range(10)
    )
    with DoubleReverseTerm(196, 64) as term:
        with term.c0_signal_session(transitions, 3) as signal:
            assert signal.first(16, 20) is None


def test_c0_palindrome_intersection_does_not_build_a_signal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    transitions = tuple(((0, 1),) for _ in range(10))
    with DoubleReverseTerm(196, 64) as term:
        with term.c0_signal_session(transitions, 1) as signal:

            def forbidden(*_args: object, **_kwargs: object) -> None:
                pytest.fail("a closed C0 palindrome event built its signal")

            monkeypatch.setattr(c0_signal_session, "periodic_word", forbidden)
            assert signal.first(16, 20, require_palindrome=True) is None
            with pytest.raises(ValueError, match="state alphabet"):
                signal.first(16, 20, inlet=1, require_palindrome=True)


def test_c0_signal_consumes_an_already_issued_late_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    transitions = tuple(((0, 1),) for _ in range(10))
    with DoubleReverseTerm(903939, 80, max_steps=80) as term:
        engine = term.temporal_engine
        engine.admit_extended_prefix(80)
        entry = engine.advance_source_prefix()
        while entry.certified_phase is None:
            entry = engine.advance_source_prefix()
        assert entry.physical_steps == 72
        with term.c0_signal_session(transitions, 1) as signal:

            def forbid() -> None:
                pytest.fail("the signal restarted C0 entry discovery")

            monkeypatch.setattr(signal, "_prefix", forbid)
            assert signal.first(72, 1) == 72
            with pytest.raises(ValueError, match="before its admitted source"):
                signal.first(71, 1)


def test_palindrome_demand_issues_late_c0_signal_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    transitions = tuple(((0, 1),) for _ in range(10))
    with DoubleReverseTerm(903939, 128, max_steps=128, max_state_bits=3000) as term:
        term.endpoint_root()
        assert term.first_palindrome_within(128) is None
        entry = term.temporal_engine.source_prefix()
        assert entry is not None and entry.physical_steps == 72
        assert entry.palindrome_covered and entry.certified_phase is not None
        with term.c0_signal_session(transitions, 1) as signal:

            def forbidden() -> None:
                pytest.fail("late C0 entry was discovered again")

            monkeypatch.setattr(signal, "_prefix", forbidden)
            assert signal.first(72, 32) == 72
            assert signal.first(72, 32, require_palindrome=True) is None


def test_seed196_low_digit_signal_covers_transient_and_stride_two(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    value = 196
    low_digits: list[int] = []
    for generation in range(65):
        if generation >= 16 and generation % 2 == 0:
            low_digits.append((value // 100) % 10)
        value = 2 * int(str(value)[::-1])
    target = low_digits[2]
    transitions = tuple(((0, 3 if digit == target else 0),) for digit in range(10))
    expected = 16 + 2 * low_digits.index(target)
    with DoubleReverseTerm(196, 64) as term:
        with term.c0_signal_session(transitions, 3) as signal:
            assert signal.first_seed196_low_digit(16, 20, 2) == expected

            def poisoned(*_args: object, **_kwargs: object) -> None:
                raise AssertionError("warm seed-196 signal reconstructed digits")

            monkeypatch.setattr(
                c0_signal_session,
                "seed196_low_four_digits_at_even_generation",
                poisoned,
            )
            monkeypatch.setattr(c0_signal_session, "periodic_word", poisoned)
            monkeypatch.setattr(TemporalSignalBank, "_then", poisoned)
            assert signal.first_seed196_low_digit(16, 20, 2) == expected
            with pytest.raises(ValueError, match="even origin"):
                signal.first_seed196_low_digit(17, 3, 2)


def test_failed_signal_publication_retires_session(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    transitions = tuple(((0, 1),) for _ in range(10))
    with DoubleReverseTerm(196, 64) as term:
        with term.c0_signal_session(transitions, 1) as signal:
            original = periodic_word

            def failed_after_construction(
                arena: LedgerSLPArena,
                period: tuple[int, ...],
                count: int,
                *,
                phase: int = 0,
            ) -> int:
                original(arena, period, count, phase=phase)
                raise RuntimeError("injected signal publication failure")

            monkeypatch.setattr(
                c0_signal_session, "periodic_word", failed_after_construction
            )
            with pytest.raises(RuntimeError, match="injected signal publication"):
                signal.first(16, 20)
            monkeypatch.setattr(c0_signal_session, "periodic_word", original)
            with pytest.raises(ValueError, match="failed"):
                signal.first(16, 20)
