"""Exact two-orientation mod-18 temporal quotient, not a full-word period fit."""

from __future__ import annotations

import pytest

from number_compiler.api.json_output import is_string_object_mapping
from number_compiler.sequences.double_reverse.temporal_hashlife_borders import (
    edge_phase_of_integer,
)
from number_compiler.sequences.double_reverse.temporal_laurent_return import (
    physical_carry_field_borrow_projection,
)
from number_compiler.sequences.double_reverse.two_rev10_digit_field import (
    TwoReverseDualDigitField18,
    universal_forward_field_mod18,
)


def _field(x: int, *, low_first: bool = True) -> str:
    digits = str(x)
    if low_first:
        digits = digits[::-1]
    return "".join(str(2 * int(d)) for d in digits)


def _step(x: int) -> int:
    return 2 * int(str(x)[::-1])


def _observations(x: int) -> tuple[int, int]:
    word = _field(x)
    return int(word) % 18, int(word[::-1]) % 18


def test_universal_mod18_factor_both_directions_and_reflected_low_carry() -> None:
    for x in range(1, 15001):
        forward, reversed_chars = _observations(x)
        assert forward == 2 * x % 18
        assert universal_forward_field_mod18(x, 0) == forward
        assert int(_field(x, low_first=False)) % 18 == forward
        assert reversed_chars == (forward + 9 * (x % 10 >= 5)) % 18
        # High-first character reversal observes the opposite multiplication
        # carry, not the low port: this needs the leading source digit.
        high = _field(x, low_first=False)
        assert int(high[::-1]) % 18 == (forward + 9 * (int(str(x)[0]) >= 5)) % 18
        assert _observations(_step(x))[0] == 2 * forward % 18
        # Universal spatial CRT, before applying any temporal border guard.
        r9 = forward % 9

        def crt(last: int, field_residue: int = r9) -> int:
            return (last + 10 * ((field_residue - last) % 9)) % 90

        assert int(_field(x)) % 90 == crt(2 * int(str(x)[0]) % 10)
        assert int(_field(x, low_first=False)) % 90 == crt(2 * x % 10)
        assert int(_field(x)[::-1]) % 90 == crt(int(str(2 * (x % 10))[0]))
        assert int(high[::-1]) % 90 == crt(int(str(2 * int(str(x)[0]))[0]))


def test_seed196_samples_and_exact_border_transports_512_generations() -> None:
    x = 196
    physical: list[tuple[int, int, int]] = []
    for n in range(512):
        forward, rev = _observations(x)
        physical.append((x, forward, rev))
        assert forward == universal_forward_field_mod18(196, n)
        if n in range(40, 45):
            assert (forward, rev) == ((8, 17), (16, 16), (14, 14), (10, 1), (2, 11))[
                n - 40
            ]
        phase = edge_phase_of_integer(x)
        if n >= 16:
            assert phase is not None and phase == n % 4
            state = TwoReverseDualDigitField18.from_border(
                physical_mod198=x % 198, phase=phase
            )
            assert state.residue == forward
            assert state.reversed_characters_mod18 == rev
            assert state.incoming_carry == int(x % 10 >= 5)
            assert state.incoming_carry == int(len(str(_step(x))) > len(str(x)))
            assert state.centered_harmonic == 2 * int(x % 10 >= 5) - 1
            assert state.successor().residue == 2 * forward % 18
            packet = physical_carry_field_borrow_projection(
                target_phase=phase, physical_mod198=x % 198, seed_mod9=196 % 9
            )
            dual = packet["dual_digit_field18_temporal_quotient"]
            assert is_string_object_mapping(dual)
            assert dual["low_first_digit_field_mod18"] == forward
            assert dual["reversed_characters_of_low_first_mod18"] == rev
            assert dual["decoded_low_multiply_carry"] == int(x % 10 >= 5)
            assert dual["harmonic_annihilator"] == "S^2+1"
            o = dual["four_field_orientations_mod90"]
            assert is_string_object_mapping(o)
            assert o["high_first_mod90"] == int(_field(x, low_first=False)) % 90
            assert o["low_first_mod90"] == int(_field(x)) % 90
            assert (
                o["reverse_characters_of_high_first_mod90"]
                == int(_field(x, low_first=False)[::-1]) % 90
            )
            assert (
                o["reverse_characters_of_low_first_mod90"] == int(_field(x)[::-1]) % 90
            )
            assert o["high_first_mod90"] == packet["carry_field_mod90"]
            assert o["reverse_characters_of_high_first_mod90"] == o["low_first_mod90"]
        x = _step(x)
    # After the authenticated entry, all 12 physical phases repeat in this
    # projection, and not just the printed residues from the user's sample.
    assert all(physical[n][1:] == physical[n + 12][1:] for n in range(16, 500))
    for n in range(16, 509):
        assert (2 * int(physical[n][0] % 10 >= 5) - 1) == -(
            2 * int(physical[n + 2][0] % 10 >= 5) - 1
        )


def test_exact_temporal_power_and_no_occurrence_ids() -> None:
    x = 196
    for _ in range(16):
        x = _step(x)
    state = TwoReverseDualDigitField18.from_border(physical_mod198=x % 198, phase=0)
    assert state.primitive_period == 12
    assert state.power(12) == state
    big_steps = 10**21
    assert state.power(big_steps) == state.power(big_steps % 12)
    for delta in range(150):
        s = state.power(delta)
        assert _observations(x) == (s.residue, s.reversed_characters_mod18)
        assert s.power(2).centered_harmonic == -s.centered_harmonic
        x = _step(x)


def test_reverse_field_alone_is_not_autonomous_even_on_early_seed196_orbit() -> None:
    x = 196
    records = {}
    for n in range(9):
        records[n] = _observations(x)
        x = _step(x)
    assert records[1] == records[7] == (10, 10)
    assert records[2] == (2, 2)
    assert records[8] == (2, 11)
    assert records[2] != records[8]


def test_laurent_observation_builds_each_orientation_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0

    def crt(field_mod9: int, last_digit: int) -> int:
        nonlocal calls
        calls += 1
        return next(r for r in range(last_digit, 90, 10) if r % 9 == field_mod9)

    monkeypatch.setattr(TwoReverseDualDigitField18, "_crt90", staticmethod(crt))
    x = 196
    for _ in range(16):
        x = _step(x)
    packet = physical_carry_field_borrow_projection(
        target_phase=0, physical_mod198=x % 198, seed_mod9=196 % 9
    )
    assert calls == 4
    assert packet["carry_field_mod90"] == int(_field(x, low_first=False)) % 90
    dual = packet["dual_digit_field18_temporal_quotient"]
    assert is_string_object_mapping(dual)
    assert dual["low_first_digit_field_mod18"] == int(_field(x)) % 18


@pytest.mark.parametrize("bad_phase", [-1, 4, 7, 1.0, True])
def test_guard_malformed_phase_is_rejected(bad_phase: int) -> None:
    with pytest.raises(ValueError):
        TwoReverseDualDigitField18.from_border(physical_mod198=16, phase=bad_phase)
