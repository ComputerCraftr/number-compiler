"""Bounded independent checks for the proposed temporal Q95 boundary germ."""

from __future__ import annotations

import pytest
from typing import cast

from devtools.experiments.reverse_add.powered_f5f2_carrier import (
    cocycle_word,
    powered_block,
    reverse_add_pair_orbit,
)
from devtools.experiments.reverse_add.temporal_boundary_germ import (
    BLANK,
    BoundaryGerm3,
    audit_supplied_orbit,
    boundary_germ,
    local_carry_digit,
    reflected_pair_symbol,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn


def test_all_q95_local_carry_and_digit_rules() -> None:
    for symbol in range(19):
        for forcing in range(5):
            q95 = 5 * symbol + forcing
            for incoming in (0, 1):
                digit, outgoing, action = local_carry_digit(q95, incoming)
                assert digit == (symbol + incoming) % 10
                expected = incoming if symbol == 9 else int(symbol > 9)
                assert outgoing == expected
                assert action is (
                    CarryFn.ID
                    if symbol == 9
                    else CarryFn.CONST1
                    if symbol > 9
                    else CarryFn.CONST0
                )


def test_blank_is_not_a_twentieth_pair_symbol() -> None:
    germ = boundary_germ((5,))
    assert germ.low == (5, BLANK, BLANK)
    assert germ.high == (5, BLANK, BLANK)
    with pytest.raises(ValueError):
        local_carry_digit(BLANK, 0)
    with pytest.raises(ValueError):
        boundary_germ((BLANK,))
    with pytest.raises(ValueError):
        BoundaryGerm3(cast(tuple[int, int, int], (0, 1)), (0, 1, BLANK))
    with pytest.raises(ValueError):
        BoundaryGerm3((0, BLANK, 1), (0, 1, BLANK))
    with pytest.raises(ValueError):
        BoundaryGerm3((0, BLANK, BLANK), (0, 1, BLANK))


def test_reflection_is_chart_exchange_and_symbol_complement_is_distinct() -> None:
    word = (1, 8, 43, 94)
    germ = boundary_germ(word)
    assert germ.reflected() == boundary_germ(tuple(reversed(word)))
    assert germ.reflected().reflected() == germ
    for symbol in range(19):
        reflected = reflected_pair_symbol(symbol)
        assert reflected_pair_symbol(reflected) == symbol
        original_action = local_carry_digit(5 * symbol, 0)[2]
        reflected_action = local_carry_digit(5 * reflected, 0)[2]
        assert (
            reflected_action
            is {
                CarryFn.CONST0: CarryFn.CONST1,
                CarryFn.ID: CarryFn.ID,
                CarryFn.CONST1: CarryFn.CONST0,
            }[original_action]
        )


def test_measured_196_q95_halves_are_reflected_without_identifying_charts() -> None:
    orbit = reverse_add_pair_orbit(196, 96)
    for half_steps in (4, 8, 16):
        for start in range(97 - half_steps):
            block = powered_block(orbit, start, half_steps)
            if block.no_growths < 1:
                continue
            germ = boundary_germ(cocycle_word(block))
            assert germ.low == germ.high


def test_real_d4_three_cell_key_alone_does_not_predict_full_d8_germ() -> None:
    orbit = reverse_add_pair_orbit(196, 94)

    def literal_term(index: int) -> int:
        value = 196
        for _ in range(index):
            value += int(str(value)[::-1])
        return value

    assert orbit[77].value == literal_term(77)
    assert orbit[86].value == literal_term(86)
    assert orbit[77].value == 1797953072701241777777132207161449896
    assert orbit[86].value == 17893315300422394267788614031240046132996
    audit = audit_supplied_orbit(orbit, 4, range(77, 87))
    assert not audit.clock_conflicts
    witness = next(
        w for w in audit.germ_conflicts if (w.first_start, w.second_start) == (77, 86)
    )
    assert witness.key[0:2] == (2, 2)
    assert witness.key[2].low == (21, 25, 26)
    assert witness.first_successor[0:2] == witness.second_successor[0:2] == (1, 3)
    assert witness.first_successor[2].low == (82, 94, 41)
    assert witness.second_successor[2].low == (82, 94, 34)


def test_real_d8_three_cell_key_alone_does_not_predict_full_d16_germ() -> None:
    orbit = reverse_add_pair_orbit(196, 97)
    audit = audit_supplied_orbit(orbit, 8, range(70, 82))
    assert not audit.clock_conflicts
    assert {(w.first_start, w.second_start) for w in audit.germ_conflicts} >= {
        (70, 79),
        (71, 80),
    }


def test_larger_measured_keys_are_singletons_not_closure_evidence() -> None:
    orbit = reverse_add_pair_orbit(196, 256)
    for half_steps, checked in ((16, 225), (32, 193), (64, 129)):
        audit = audit_supplied_orbit(orbit, half_steps, range(257 - 2 * half_steps))
        assert audit.checked == checked
        assert audit.repeated_keys == 0
        assert audit.singleton_keys == checked
