"""Iterative SLP traversal for retained parity and weighted-carry prefixes."""

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.named_border_carry_matrix import (
    UnitsCarryMatrix,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape


def test_nested_concat_repeat_prefixes_match_the_literal_letters() -> None:
    parts = ((1, 0, 0), (1, 1), (0, 1, 0, 1))
    tape = ParityCarryTape.sequence(
        (
            ParityCarryTape.repeated(ParityCarryTape.letters(parts[0]), 3),
            ParityCarryTape.sequence(
                (
                    ParityCarryTape.letters(parts[1]),
                    ParityCarryTape.repeated(ParityCarryTape.letters(parts[2]), 2),
                )
            ),
        )
    )
    letters = parts[0] * 3 + parts[1] + parts[2] * 2

    for time in range(len(letters) + 1):
        expected = DyadicTerminalFieldAction.identity()
        for bit in letters[:time]:
            expected = expected.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        assert tape.prefix_action(time) == expected
        assert tape.prefix_odds(time) == sum(letters[:time])
        assert tape.prefix_units(time) == UnitsCarryMatrix.word(letters[:time])


def test_deep_concat_prefixes_use_an_iterative_worklist() -> None:
    tape = ParityCarryTape.letters((1,))
    letters = [1]
    for _ in range(1_100):
        tape = ParityCarryTape.sequence((tape, ParityCarryTape.letters((0,))))
        letters.append(0)

    expected = DyadicTerminalFieldAction.identity()
    for bit in letters[:-1]:
        expected = expected.then(
            DyadicTerminalFieldAction.one_run(1)
            if bit
            else DyadicTerminalFieldAction.zero_run(1)
        )
    assert tape.prefix_action(tape.steps - 1) == expected
    assert tape.prefix_odds(tape.steps - 1) == 1
    assert tape.prefix_units(tape.steps - 1) == UnitsCarryMatrix.word(
        tuple(letters[:-1])
    )
