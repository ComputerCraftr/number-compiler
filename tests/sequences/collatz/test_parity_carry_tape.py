"""Iterative SLP traversal for retained parity and weighted-carry prefixes."""

import pytest

from number_compiler.sequences.collatz.boundary_macros import select_boundary_macro
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
        assert tape.prefix_letters(time) == letters[:time]
        assert tape.prefix_units(time) == UnitsCarryMatrix.word(letters[:time])


def test_tuple_backing_preserves_exact_class_equality() -> None:
    tape = ParityCarryTape.letters((1, 0))
    equivalent = ParityCarryTape.letters((1, 0))
    payload_tuple = (tape[0],)

    assert tape == equivalent
    assert hash(tape) == hash(equivalent)
    assert tape != payload_tuple
    assert payload_tuple != tape
    with pytest.raises(AttributeError):
        object.__setattr__(tape, "word", (0, 1))


def _deep_concat_fixture() -> tuple[ParityCarryTape, tuple[int, ...]]:
    tape = ParityCarryTape.letters((1,))
    letters = [1]
    for _ in range(1_100):
        tape = ParityCarryTape.sequence((tape, ParityCarryTape.letters((0,))))
        letters.append(0)
    return tape, tuple(letters)


def test_deep_concat_prefixes_use_an_iterative_worklist() -> None:
    tape, letters = _deep_concat_fixture()

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


def test_prefix_letters_visits_the_compressed_path_once_per_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tape, letters = _deep_concat_fixture()

    original_getattribute = ParityCarryTape.__getattribute__
    kind_reads = 0

    def count_kind_reads(node: ParityCarryTape, name: str) -> object:
        nonlocal kind_reads
        if name == "kind":
            kind_reads += 1
        return original_getattribute(node, name)

    monkeypatch.setattr(ParityCarryTape, "__getattribute__", count_kind_reads)
    assert tape.prefix_letters(tape.steps) == tuple(letters)
    # The grammar has 2 * steps - 1 nodes. A linear bound allows repeated
    # kind checks within one frame while rejecting a root walk per output bit.
    assert kind_reads <= 6 * tape.steps


def test_named_macro_parity_grammar_folds_its_issued_action_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    macro = select_boundary_macro(159, 300, minimum_repetitions=1)
    assert macro is not None

    original_action = ParityCarryTape.action
    calls = 0

    def poison_second_fold(tape: ParityCarryTape) -> DyadicTerminalFieldAction:
        nonlocal calls
        calls += 1
        if calls > 1:
            raise AssertionError("named macro parity action was recomputed")
        return original_action(tape)

    monkeypatch.setattr(ParityCarryTape, "action", poison_second_fold)
    tape = ParityCarryTape.from_named_macro(macro)
    assert tape.steps == macro.fields.steps
    assert calls == 1


def test_failed_action_fold_clears_traceback_retained_worklists(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tape = ParityCarryTape.sequence(
        (ParityCarryTape.letters((1, 0)), ParityCarryTape.letters((0, 1)))
    )
    original_then = DyadicTerminalFieldAction.then
    calls = 0

    def fail_during_fold(
        action: DyadicTerminalFieldAction,
        later: DyadicTerminalFieldAction,
    ) -> DyadicTerminalFieldAction:
        nonlocal calls
        calls += 1
        if calls == 5:
            raise RuntimeError("injected parity fold failure")
        return original_then(action, later)

    monkeypatch.setattr(DyadicTerminalFieldAction, "then", fail_during_fold)
    with pytest.raises(RuntimeError, match="injected parity fold failure") as raised:
        tape.action()

    frame = raised.value.__traceback__
    while frame is not None and frame.tb_frame.f_code.co_name != "_full_effect":
        frame = frame.tb_next
    assert frame is not None
    assert frame.tb_frame.f_locals["pending"] == []
    assert frame.tb_frame.f_locals["values"] == {}
    assert frame.tb_frame.f_locals["child"] is None


def test_prefix_fold_reuses_shared_nodes_across_chunks_only_within_request(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    shared = ParityCarryTape.letters((1, 0))
    tape = ParityCarryTape.sequence(
        (
            ParityCarryTape.repeated(shared, 3),
            ParityCarryTape.repeated(shared, 5),
            ParityCarryTape.letters((0, 0)),
        )
    )
    expected = shared.action().power(8)
    original_one_run = DyadicTerminalFieldAction.one_run
    calls = 0

    def counted_one_run(length: int) -> DyadicTerminalFieldAction:
        nonlocal calls
        calls += 1
        return original_one_run(length)

    monkeypatch.setattr(
        DyadicTerminalFieldAction, "one_run", staticmethod(counted_one_run)
    )
    assert tape.prefix_action(16) == expected
    assert calls == 1
    assert tape.prefix_action(16) == expected
    assert calls == 2


def test_failed_prefix_fold_clears_its_shared_memo(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    shared = ParityCarryTape.letters((1, 0))
    tape = ParityCarryTape.sequence((shared, shared, ParityCarryTape.letters((0, 0))))
    original_then = DyadicTerminalFieldAction.then
    calls = 0

    def fail_second_chunk(
        action: DyadicTerminalFieldAction, later: DyadicTerminalFieldAction
    ) -> DyadicTerminalFieldAction:
        nonlocal calls
        calls += 1
        if calls == 4:
            raise RuntimeError("injected shared prefix fold failure")
        return original_then(action, later)

    monkeypatch.setattr(DyadicTerminalFieldAction, "then", fail_second_chunk)
    with pytest.raises(RuntimeError, match="shared prefix fold failure") as raised:
        tape.prefix_action(4)
    frame = raised.value.__traceback__
    while frame is not None and frame.tb_frame.f_code.co_name != "_prefix_effect":
        frame = frame.tb_next
    assert frame is not None
    assert frame.tb_frame.f_locals["values"] == {}
    assert frame.tb_frame.f_locals["chunks"] == ()
