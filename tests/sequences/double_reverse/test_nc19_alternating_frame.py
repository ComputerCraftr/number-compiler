"""Regression coverage for the exact four-port spatial ``2rev10`` square."""

from __future__ import annotations

from itertools import product
from typing import NoReturn

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.sequences.double_reverse import (
    source_adapter as source_adapter_module,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_alternating_carry import (
    FourPortCarryAction,
    FourPortCarryRow,
    FourPortSLPProjection,
    TwoStepCarryCell,
    TwoStepCarryPorts,
    fold_two_step_slp,
)


def _literal_ports(
    digits: tuple[int, ...], forward_in: int, reverse_in: int
) -> tuple[int, int, tuple[int, ...]]:
    first_pass: list[int] = []
    forward = forward_in
    for digit in digits:
        value = 2 * digit + forward
        emitted, forward = value % 10, value // 10
        first_pass.append(emitted)

    output = [0] * len(digits)
    reverse = reverse_in
    for index in range(len(digits) - 1, -1, -1):
        value = 2 * first_pass[index] + reverse
        output[index], reverse = value % 10, value // 10
    return forward, reverse, tuple(output)


def _literal_t2(seed: int) -> int:
    first = 2 * int(str(seed)[::-1])
    return 2 * int(str(first)[::-1])


def _function_locals(error: BaseException, function_name: str) -> dict[str, object]:
    frame = error.__traceback__
    while frame is not None:
        if frame.tb_frame.f_code.co_name == function_name:
            return frame.tb_frame.f_locals
        frame = frame.tb_next
    raise AssertionError(f"{function_name} missing from retained traceback")


def _traceback_names(error: BaseException) -> tuple[str, ...]:
    names: list[str] = []
    frame = error.__traceback__
    while frame is not None:
        names.append(frame.tb_frame.f_code.co_name)
        frame = frame.tb_next
    return tuple(names)


def test_four_port_digit_cells_match_both_ordered_doublings() -> None:
    for digit, forward_in, reverse_in in product(range(10), (0, 1), (0, 1)):
        first_value = 2 * digit + forward_in
        first, forward_out = first_value % 10, first_value // 10
        second_value = 2 * first + reverse_in
        output, reverse_out = second_value % 10, second_value // 10
        cell = TwoStepCarryCell.apply(digit, forward_in, reverse_in)
        assert (cell.digit, cell.forward_out, cell.reverse_out) == (
            output,
            forward_out,
            reverse_out,
        )


def test_four_port_slp_fold_matches_literal_words_and_all_inlets() -> None:
    arena = SLPArena()
    try:
        for width in range(1, 4):
            for digits in product(range(10), repeat=width):
                source = arena.word(digits)
                projection = fold_two_step_slp(arena, source)
                projection.validate_for(arena, source)
                assert projection.action.input_width == width
                for forward_in, reverse_in in product((0, 1), repeat=2):
                    row = projection.action.row(forward_in, reverse_in)
                    expected = _literal_ports(digits, forward_in, reverse_in)
                    assert (row.forward_out, row.reverse_out) == expected[:2]
                    assert arena.materialize(row.output_in(arena)) == expected[2]
    finally:
        arena.clear()


def test_four_port_projection_rejects_foreign_and_recycled_source_roots() -> None:
    arena = SLPArena()
    try:
        source = arena.word((1, 2, 3, 4))
        projection = fold_two_step_slp(arena, source)
        projection.validate_for(arena, source)

        other_source = arena.word((4, 3, 2, 1))
        assert arena.nodes[other_source].length == arena.nodes[source].length
        with pytest.raises(ValueError, match="another or stale source"):
            projection.validate_for(arena, other_source)

        arena.clear()
        SLPArena.__init__(arena)
        recycled_source = arena.word((4, 3, 2, 1))
        assert recycled_source == source
        with pytest.raises(ValueError, match="another or stale source"):
            projection.validate_for(arena, recycled_source)
    finally:
        arena.clear()


def test_four_port_projection_rejects_action_and_row_substitution() -> None:
    arena = SLPArena()
    try:
        source = arena.word((1, 2, 3, 4))
        projection = fold_two_step_slp(arena, source)
        issued_action = projection.action
        other_source = arena.word((8, 7, 6, 5))
        other_action = fold_two_step_slp(arena, other_source).action

        object.__setattr__(projection, "action", other_action)
        with pytest.raises(ValueError, match="another or stale source"):
            projection.validate_for(arena, source)
        object.__setattr__(projection, "action", issued_action)

        original_rows = issued_action.rows
        replacement_rows = (other_action.rows[0], *original_rows[1:])
        object.__setattr__(issued_action, "rows", replacement_rows)
        with pytest.raises(ValueError, match="action was changed after issue"):
            projection.validate_for(arena, source)
        object.__setattr__(issued_action, "rows", original_rows)
        projection.validate_for(arena, source)
    finally:
        arena.clear()


def test_four_port_source_adapter_checks_projection_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 3, max_state_bits=512) as term:
        arena = term.source_arena
        source_root = term.source_root
        source_width = arena.nodes[source_root].length
        foreign_root = arena.word(
            tuple((digit + 1) % 10 for digit in term.source_digits)
        )
        assert arena.nodes[foreign_root].length == source_width
        foreign_projection = fold_two_step_slp(arena, foreign_root)

        def return_foreign_projection(
            _arena: SLPArena,
            _root: int,
            **_kwargs: object,
        ) -> FourPortSLPProjection:
            return foreign_projection

        monkeypatch.setattr(
            source_adapter_module,
            "fold_two_step_slp",
            return_foreign_projection,
        )
        with pytest.raises(ValueError, match="another or stale source") as captured:
            term.materialize(max_bits=512)
        frame_locals = _function_locals(captured.value, "_general_two_step")
        assert frame_locals["projection"] is None
        assert frame_locals["row"] is None


def test_projection_snapshot_budget_refusal_clears_fold_traceback() -> None:
    arena = SLPArena()
    root = arena.word((1, 2, 3, 4))
    reservations: list[tuple[int, int]] = []

    def refuse_snapshot(entries: int, nodes: int) -> None:
        reservations.append((entries, nodes))
        if (entries, nodes) == (6, 6):
            raise MemoryError("projection snapshot refused")

    with pytest.raises(MemoryError, match="projection snapshot refused") as captured:
        fold_two_step_slp(arena, root, reserve_scratch=refuse_snapshot)
    assert (6, 6) in reservations
    frame_locals = _function_locals(captured.value, "fold_two_step_slp")
    assert frame_locals["values"] == {}
    assert frame_locals["action"] is None
    assert "__init__" not in _traceback_names(captured.value)


def test_repeat_node_uses_binary_action_composition() -> None:
    arena = SLPArena()
    try:
        pattern = arena.word((1, 6, 8, 0))
        source = arena.repeat(pattern, 7)
        assert arena.nodes[source].kind == "REPEAT"
        projection = fold_two_step_slp(arena, source)
        assert projection.action.input_width == 28
        for forward_in, reverse_in in product((0, 1), repeat=2):
            row = projection.action.row(forward_in, reverse_in)
            expected = _literal_ports((1, 6, 8, 0) * 7, forward_in, reverse_in)
            assert (row.forward_out, row.reverse_out) == expected[:2]
            assert arena.materialize(row.output_in(arena)) == expected[2]

        identity = FourPortCarryAction.identity(arena)
        assert identity.then(projection.action) is projection.action
        assert projection.action.then(identity) is projection.action
    finally:
        arena.clear()


def test_empty_four_port_action_is_carry_identity_and_composes_neutrally() -> None:
    arena = SLPArena()
    try:
        empty = fold_two_step_slp(arena, arena.empty_id).action
        assert empty.input_width == 0
        for forward_in, reverse_in in product((0, 1), repeat=2):
            row = empty.row(forward_in, reverse_in)
            assert (row.forward_out, row.reverse_out) == (forward_in, reverse_in)
            assert arena.materialize(row.output_in(arena)) == ()

        action = fold_two_step_slp(arena, arena.terminal(6)).action
        assert empty.then(action) is action
        assert action.then(empty) is action
    finally:
        arena.clear()


def test_empty_four_port_action_rejects_nonidentity_carry_map() -> None:
    arena = SLPArena()
    try:
        empty_node = arena.nodes[arena.empty_id]
        invalid_row = FourPortCarryRow(0, 0, arena, arena.empty_id, empty_node)
        rows: tuple[
            FourPortCarryRow,
            FourPortCarryRow,
            FourPortCarryRow,
            FourPortCarryRow,
        ] = (
            invalid_row,
            invalid_row,
            invalid_row,
            invalid_row,
        )
        with pytest.raises(ValueError, match="empty four-port action"):
            FourPortCarryAction(arena, 0, rows)
    finally:
        arena.clear()


def test_huge_repeat_projection_stays_in_the_shared_slp_arena(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SLPArena()

    def forbid_materialize(_arena: SLPArena, _root: int) -> NoReturn:
        raise AssertionError("four-port powered projection materialized its word")

    monkeypatch.setattr(SLPArena, "materialize", forbid_materialize)
    try:
        block = arena.word((2, 8, 0, 5))
        repetitions = 10**14
        source = arena.repeat(block, repetitions)
        projection = fold_two_step_slp(arena, source)
        assert projection.action.input_width == 4 * repetitions
        for forward_in, reverse_in in product((0, 1), repeat=2):
            row = projection.action.row(forward_in, reverse_in)
            output_root = row.output_in(arena)
            assert arena.nodes[output_root].length == 4 * repetitions
            assert arena.metrics(output_root).reachable_nodes < 512
    finally:
        arena.clear()


def test_four_port_rows_reject_foreign_and_reused_arena_ids() -> None:
    arena = SLPArena()
    other = SLPArena()
    try:
        source = arena.word((1, 6, 8))
        action = fold_two_step_slp(arena, source).action
        stale_row = action.row(0, 0)
        stale_root = stale_row.output_in(arena)

        other_action = fold_two_step_slp(other, other.word((1, 6, 8))).action
        with pytest.raises(ValueError, match="another SLP arena"):
            stale_row.output_in(other)
        with pytest.raises(ValueError, match="different SLP arenas"):
            action.then(other_action)

        arena.clear()
        SLPArena.__init__(arena)
        new_action = fold_two_step_slp(arena, arena.word((1, 6, 8))).action
        assert stale_root == new_action.row(0, 0).output_in(arena)
        with pytest.raises(ValueError, match="stale"):
            stale_row.output_in(arena)
        with pytest.raises(ValueError, match="stale"):
            action.then(new_action)
    finally:
        arena.clear()
        other.clear()


@pytest.mark.parametrize("seed", (5, 9, 10, 50, 168, 100, 176330))
def test_production_square_keeps_birth_and_zero_contraction_seams(seed: int) -> None:
    with DoubleReverseTerm(seed, 2, max_state_bits=512) as term:
        assert term.materialize(max_bits=512) == _literal_t2(seed)
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_square_applications"] == 1
        assert metrics.get("double_reverse_temporal_square_normalizations", 0) >= int(
            seed in (5, 10, 50, 100)
        )


def test_failed_four_port_fold_rolls_back_its_unpublished_suffix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(12, 2, max_state_bits=512) as term:
        arena = term.source_arena
        checkpoint = len(arena.nodes)
        scratch_usage = term.resource_ledger.account_usage(term.scratch_owner)
        original_apply = TwoStepCarryCell.apply
        calls = 0

        def fail_cell(
            _digit: int, _forward_in: int, _reverse_in: int
        ) -> TwoStepCarryPorts:
            nonlocal calls
            calls += 1
            if calls == 2:
                raise RuntimeError("injected four-port cell failure")
            return original_apply(_digit, _forward_in, _reverse_in)

        monkeypatch.setattr(TwoStepCarryCell, "apply", staticmethod(fail_cell))
        with pytest.raises(RuntimeError, match="injected four-port cell failure"):
            term.materialize(max_bits=512)
        assert len(arena.nodes) == checkpoint
        assert term.resource_ledger.account_usage(term.scratch_owner) == scratch_usage
        assert term.metrics()["double_reverse_temporal_square_region_visits"] > 0
        monkeypatch.setattr(TwoStepCarryCell, "apply", staticmethod(original_apply))
        assert term.materialize(max_bits=512) == _literal_t2(12)
