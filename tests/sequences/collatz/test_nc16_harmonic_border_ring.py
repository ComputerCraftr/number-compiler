"""Exact source-guarded 6305 ring cutover and future-prime quotient tests."""

from __future__ import annotations

import pytest

from number_compiler.sequences.collatz.border_carry_cylinder import (
    Border6305CarryCylinder,
)
from number_compiler.sequences.collatz.border_harmonic_ring import (
    ConstantTail6305Ring,
    ZeroTailFreeBorderRing,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    select_border_return_macro,
    validate_border_return_macro,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.position_cycle_harmonics import (
    minimize_fixed_word_odd_position,
)


def _source(repetitions: int) -> int:
    return (1 << (2 * repetitions + 1)) * (2 if repetitions % 2 == 0 else 3) - 1


def _scalar_odd(source: int, repetitions: int) -> int:
    current = source
    for _ in range(2 * repetitions):
        assert current & 1
        current = (3 * current + 1) // 2
    return current


def test_closed_ring_is_exact_and_source_admitted() -> None:
    for repetitions in (1, 2, 3, 8, 16, 32, 64, 256):
        source = _source(repetitions)
        ring = ZeroTailFreeBorderRing.from_source(source)
        assert ring.return_capacity == repetitions
        assert (
            ring.admissible_count(ticks=4 * repetitions, returns=10_000) == repetitions
        )
        for count in (0, 1, repetitions // 2, repetitions):
            expected = _scalar_odd(source, count)
            assert ring.endpoint(count) == expected
            assert ring.scale(count).growths == 2 * count
            assert ring.scale(count).halvings == 2 * count
            for radix in (2, 3, 5, 6, 10, 27, 64):
                for places in (1, 2, 3):
                    assert ring.radix_residue(radix, places, count) == (
                        expected % radix**places
                    )
            for bits in (0, 1, 7, 65):
                assert ring.binary_residue(bits, count) == expected % (1 << bits)
            for radix in (3, 5, 7, 9, 11):
                assert ring.odd_prime_residue(radix, 3, count) == expected % radix**3
        assert not ring.admits(repetitions + 1)
        with pytest.raises(ValueError, match="source admitted"):
            ring.endpoint(repetitions + 1)


def test_odd_prime_ports_bound_the_full_modulus_before_powering() -> None:
    oversized_odd_base = (1 << 64) + 1
    zero_tail = ZeroTailFreeBorderRing.from_source(_source(2))
    constant_tail = ConstantTail6305Ring.from_source(_constant_tail_source(1, 2))
    with pytest.raises(ValueError, match="4096-bit"):
        zero_tail.odd_prime_residue(oversized_odd_base, 64, 0)
    with pytest.raises(ValueError, match="4096-bit"):
        constant_tail.odd_prime_residue(oversized_odd_base, 64, 0)


def test_bulk_border_producer_preserves_ports_and_width() -> None:
    for returns in (2, 4, 8, 16, 32, 64):
        source = _source(returns)
        macro = select_border_return_macro(source, 4 * returns)
        assert macro is not None
        assert macro.zero_tails == (0,) * returns
        assert macro.returns == returns
        assert macro.endpoint == _scalar_odd(source, returns)
        assert macro.fields.endpoint(source) == macro.endpoint
        assert macro.fields.steps == 2 * returns
        assert macro.physical_ticks == 4 * returns
        assert (
            macro.width_blank.delta == macro.endpoint.bit_length() - source.bit_length()
        )
        validate_border_return_macro(macro)


def test_6305_horizon_and_cap_are_source_guards() -> None:
    source = _source(100)
    ring = ZeroTailFreeBorderRing.from_source(source)
    assert ring.admissible_count(ticks=8, returns=64) == 2
    assert ring.admissible_count(ticks=400, returns=64) == 64
    for ticks in (8, 16, 36, 256):
        macro = select_border_return_macro(source, ticks)
        assert macro is not None
        assert macro.physical_ticks == ticks
        assert macro.zero_tails == (0,) * (ticks // 4)
    macro = select_border_return_macro(source, 400)
    assert macro is not None and macro.physical_ticks == 256
    assert macro.zero_tails == (0,) * 64


def test_nonadmitted_or_wrong_phase_refused() -> None:
    for source in (0, 1, 12, 44, 70):
        with pytest.raises(ValueError):
            ZeroTailFreeBorderRing.from_source(source)
    for source in (3, 23, 53, 73, 153, 333):
        ring = ZeroTailFreeBorderRing.from_source(source)
        assert ring.source == source
        assert ring.endpoint(0) == source


def test_prime_moore_quotient_is_on_exact_modular_action() -> None:
    word = DyadicTerminalFieldAction.one_run(2)
    first = minimize_fixed_word_odd_position(word, 3, 2)
    second = minimize_fixed_word_odd_position(word, 3, 2)
    # The quotient is deterministic but query-local; no unowned process cache
    # retains an observer object between family demands.
    assert first == second
    assert first.classes == 9
    for source in range(1, 81):
        state = first.class_for_source(source)
        modulus = 27
        next_residue = (
            (word.gain * source + word.offset) * pow(2, -2, modulus)
        ) % modulus
        assert first.transitions[state] == (first.class_ids[next_residue],)


def _constant_tail_source(tail: int, repetitions: int) -> int:
    residue, modulus = ConstantTail6305Ring.guard_residue(tail, repetitions)
    # CRT: both source congruences hold, including the decimal digit 3.
    return residue + modulus * ((3 - residue) * pow(modulus, -1, 5) % 5)


@pytest.mark.parametrize("tail", tuple(range(10)))
@pytest.mark.parametrize("repetitions", (3, 4, 8, 12))
def test_constant_tail_ring_proves_all_source_bound_repetitions(
    tail: int, repetitions: int
) -> None:
    source = _constant_tail_source(tail, repetitions)
    ring = ConstantTail6305Ring.from_source(source)
    assert ring.tail == tail
    assert ring.return_capacity >= repetitions
    assert (
        ring.admitted_count(ticks=repetitions * (tail + 4), returns=64) == repetitions
    )
    assert ring.scale(repetitions).growths == 2 * repetitions
    assert ring.scale(repetitions).halvings == (tail + 2) * repetitions
    scalar = source
    for index in range(repetitions):
        assert scalar % 10 == 3
        upper = 3 * ((scalar - 3) // 10) + 1
        assert (upper & -upper).bit_length() - 1 == tail
        scalar = (15 * (upper >> tail) + 1) // 2
        assert scalar == ring.endpoint(index + 1)
    word = (
        DyadicTerminalFieldAction.one_run(1)
        .then(DyadicTerminalFieldAction.zero_run(tail))
        .then(DyadicTerminalFieldAction.one_run(1))
    )
    powered = word.power(repetitions)
    assert powered.certifies(source)
    assert powered.endpoint(source) == scalar
    for position_base in (3, 5, 6, 10, 27, 64):
        for places in (1, 2, 3):
            assert ring.radix_residue(position_base, places, repetitions) == (
                scalar % position_base**places
            )
    macro = select_border_return_macro(source, repetitions * (tail + 4))
    assert macro is not None
    assert macro.zero_tails == (tail,) * repetitions
    assert macro.endpoint == scalar
    assert macro.fields.coefficient_snapshot() == powered.coefficient_snapshot()
    validate_border_return_macro(macro)
    spectrum = macro.demanded_position_harmonics(6, 1)
    expected_counts = [0] * 6
    start = source
    for _ in range(repetitions):
        expected_counts[start // 6 % 6] += 1
        numerator = 3 * ((start - 3) // 10) + 1
        start = (15 * (numerator >> tail) + 1) // 2
    assert spectrum.counts == tuple(expected_counts)
    assert spectrum.radial_scale.growths == 2 * repetitions


def test_constant_tail_guard_preserves_future_exit_distinctions() -> None:
    # Exact future capacity differs even for equal decimal source digits.
    first = ConstantTail6305Ring.from_source(33)
    second = ConstantTail6305Ring.from_source(633)
    assert first.tail == second.tail == 1
    assert first.return_capacity == 0
    assert second.return_capacity == 2
    assert not first.admits(1)
    assert second.admits(2)
    assert second.endpoint(2) % 10 == 3


def test_nonconstant_tails_stay_on_exact_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    macro = select_border_return_macro(23, 13)
    assert macro is not None and macro.zero_tails == (0, 4)
    assert macro.endpoint == 4
    calls = 0
    next_return = Border6305CarryCylinder.next_return

    def guarded_next_return(
        cursor: Border6305CarryCylinder,
    ) -> Border6305CarryCylinder | None:
        nonlocal calls
        calls += 1
        if calls > 1:
            raise AssertionError("harmonic observer advanced beyond its macro")
        return next_return(cursor)

    monkeypatch.setattr(Border6305CarryCylinder, "next_return", guarded_next_return)
    spectrum = macro.demanded_position_harmonics(6, 1)
    assert spectrum.repetitions == 2
    assert calls == 1


def test_walsh64_matches_constant_tail_position_transition() -> None:
    from number_compiler.arithmetic.fields.walsh import walsh64_mod5

    for tail in (0, 1, 2, 4):
        source = _constant_tail_source(tail, 64)
        ring = ConstantTail6305Ring.from_source(source)
        macro = select_border_return_macro(source, 64 * (tail + 4))
        assert macro is not None
        assert macro.zero_tails == (tail,) * 64
        spectrum = macro.demanded_position_harmonics(6, 1, walsh64=True)
        mask = 0
        for tick in range(64):
            before = ring.endpoint(tick) // 6 % 6
            after = ring.endpoint(tick + 1) // 6 % 6
            if before != after:
                mask |= 1 << tick
        assert spectrum.walsh64_change_mod5 == walsh64_mod5(mask)


def test_moore_quotients_equivalent_prime_actions_from_distinct_words() -> None:
    # Once q>=2, the 3-adic multiplier of a complete all-odd block is
    # zero modulo 9 and the centered affine endpoint is -1 modulo 9.
    first = minimize_fixed_word_odd_position(DyadicTerminalFieldAction.one_run(4), 3, 1)
    second = minimize_fixed_word_odd_position(
        DyadicTerminalFieldAction.one_run(5), 3, 1
    )
    assert first == second
    assert all(first.outputs[row[0]] == 2 for row in first.transitions)
