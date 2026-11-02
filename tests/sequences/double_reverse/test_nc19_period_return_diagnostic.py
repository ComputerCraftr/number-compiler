"""Regression coverage for finite and conditional 2rev10 period evidence."""

from __future__ import annotations

from random import Random

import pytest

from devtools.verification.double_reverse_period_action import (
    ConditionalActionRefused,
    SourceActionObservation,
    check_source_action_block,
    close_effective_program,
)
from devtools.verification.double_reverse_period_return import analyze_source_returns
from devtools.verification.double_reverse_period_source import (
    SourceEvidenceRefused,
    effective_gate,
    return_capacity,
    reverse_double_word,
    spatial_borrow_fold,
    spatial_return_row,
)
from number_compiler.sequences.double_reverse.temporal_birth_ring import (
    BirthRingPorts,
    BirthRingState,
)
from number_compiler.sequences.double_reverse.temporal_diagonal_induction import (
    SeamGate,
    certified_closed_outer_pair_return,
    seam_gate,
)


def _literal_borrow_words(
    source: str, target: str, depth: int
) -> tuple[str, str, str, str]:
    width = max(len(source), len(target))
    left, right = source.zfill(width), target.zfill(width)
    borrows = [0] * width
    transfers = ["I"] * width
    borrow = 0
    for index in range(width - 1, -1, -1):
        source_digit, target_digit = left[index], right[index]
        transfer = (
            "1"
            if target_digit < source_digit
            else "0"
            if target_digit > source_digit
            else "I"
        )
        borrow = int(transfer == "1" or (transfer == "I" and borrow == 1))
        borrows[index] = borrow
        transfers[index] = transfer
    span = depth + 1
    return (
        "".join(str(value) for value in borrows[:span]),
        "".join(
            str(borrows[index]) for index in range(width - 1, width - span - 1, -1)
        ),
        "".join(transfers[:span]),
        "".join(transfers[index] for index in range(width - 1, width - span - 1, -1)),
    )


def test_spatial_borrow_fold_matches_full_positional_oracle() -> None:
    random = Random(20261102)
    cases = [("481688", "376512", 2), ("100000", "99999", 2)]
    for _ in range(80):
        width = random.randrange(8, 40)
        source = str(random.randrange(10 ** (width - 1), 10**width))
        target_width = random.choice((width - 1, width, width + 1))
        target = str(random.randrange(10 ** (target_width - 1), 10**target_width))
        depth = random.randrange(2, min(6, (width - 2) // 2) + 1)
        cases.append((source, target, depth))

    for source, target, depth in cases:
        folded = spatial_borrow_fold(source, target, depth)
        assert (
            folded.upper_borrow,
            folded.lower_borrow,
            folded.upper_transfer,
            folded.lower_transfer,
        ) == _literal_borrow_words(source, target, depth)
        assert folded.edge_digit_updates == 2 * (depth + 1)


def test_return_capacity_gate_boundary_holds_at_every_claimed_depth() -> None:
    source = "17456789012342"
    target = reverse_double_word(source)
    first = spatial_return_row(0, source, target, depth=6)
    shifted = spatial_return_row(4, source, target, depth=6)

    for claimed_depth in range(1, 7):
        capacity, _ = return_capacity(first, shifted, claimed_depth)
        assert capacity == claimed_depth
        for depth in range(1, capacity + 1):
            assert effective_gate(first, depth) == effective_gate(shifted, depth)


def test_string_2rev10_transition_matches_small_integer_oracle() -> None:
    for source in range(1, 20_000):
        word = str(source)
        expected = str(2 * int(word[::-1]))
        assert reverse_double_word(word) == expected


def test_source_checkpoints_are_replayed_and_forgery_is_rejected() -> None:
    crosscheck = "196"
    for _ in range(4):
        crosscheck = reverse_double_word(crosscheck)

    def replay(checkpoint: str, later: str) -> None:
        analyze_source_returns(
            196,
            0,
            checkpoint,
            4,
            later,
            anchors=(64,),
            base_period=4,
            max_multiplier=1,
            first_depth=2,
            max_depth=2,
            window=4,
        )

    with pytest.raises(SourceEvidenceRefused, match="checkpoint"):
        replay("197", crosscheck)
    with pytest.raises(SourceEvidenceRefused, match="crosscheck"):
        replay("196", "671")


def test_effective_gate_action_preserves_the_complete_next_bank() -> None:
    state, program, source_inlet = _closed_gate_program()
    model = close_effective_program(state, program, max_states=1_000)
    gate = program[0]
    expected = state.advance(source_inlet)[0]
    assert model.at(1) == expected
    for left in range(10):
        for right in range(10):
            inlet = BirthRingPorts(left, right)
            if seam_gate(state, inlet) == gate:
                assert model.at(1) == state.advance(inlet)[0]


def test_sampled_rows_consume_the_already_computed_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    crosscheck = "196"
    for _ in range(4):
        crosscheck = reverse_double_word(crosscheck)
    calls = 0

    def counted(word: str) -> str:
        nonlocal calls
        calls += 1
        return reverse_double_word(word)

    monkeypatch.setattr(
        "devtools.verification.double_reverse_period_source.reverse_double_word",
        counted,
    )
    report = analyze_source_returns(
        196,
        0,
        "196",
        4,
        crosscheck,
        anchors=(64,),
        base_period=4,
        max_multiplier=1,
        first_depth=2,
        max_depth=2,
        window=4,
    )
    assert report.work.source_rows_retained == 8
    assert report.work.physical_generations_replayed == 71
    assert report.work.successor_evaluations == calls == 72


def _closed_gate_program() -> tuple[
    BirthRingState, tuple[SeamGate, ...], BirthRingPorts
]:
    inlet = BirthRingPorts(3, 7)
    state = BirthRingState((4,), (2,), 0)
    states: list[BirthRingState] = []
    gates: list[SeamGate] = []
    first_seen: dict[BirthRingState, int] = {}
    while state not in first_seen:
        first_seen[state] = len(states)
        states.append(state)
        gates.append(seam_gate(state, inlet))
        state = state.advance(inlet)[0]
    cycle_start = first_seen[state]
    return states[cycle_start], tuple(gates[cycle_start:]), inlet


def test_declared_gate_lasso_powers_only_its_exact_conditional_model() -> None:
    first, program, inlet = _closed_gate_program()
    model = close_effective_program(first, program, max_states=1_000)
    assert model.lasso.gate_program_fsteps == len(program)
    assert model.lasso.state_period_fsteps > 0
    assert type(model.lasso.bank_output_period_fsteps) is int
    assert model.lasso.bank_output_period_fsteps > 0
    assert type(model.lasso.period_comparisons) is int
    assert model.lasso.period_comparisons >= 0
    actual = first
    for fstep in range(len(program)):
        assert model.at(fstep) == actual
        actual = actual.advance(inlet)[0]
    assert actual == first
    assert model.at(len(program)) == first
    assert model.at(10**12) == model.at(
        model.lasso.preperiod_fsteps
        + (10**12 - model.lasso.preperiod_fsteps) % model.lasso.state_period_fsteps
    )


def test_second_source_block_is_checked_against_the_declared_gate_action() -> None:
    first = BirthRingState((4,), (2,), 0)
    second = BirthRingState((4,), (2,), 2)
    ports = BirthRingPorts(3, 7)
    program = (seam_gate(first, ports), seam_gate(second, ports))
    with pytest.raises(ConditionalActionRefused, match="no decimal inlet witness"):
        close_effective_program(first, program, max_states=1_000)

    valid_initial, valid_program, _inlet = _closed_gate_program()
    model = close_effective_program(valid_initial, valid_program, max_states=1_000)
    observations = tuple(
        SourceActionObservation(
            100 + 2 * index,
            model.at(len(valid_program) + index),
            valid_program[index % len(valid_program)],
        )
        for index in range(3)
    )
    check = check_source_action_block(
        observations,
        program=valid_program,
        model=model,
        model_offset=len(valid_program),
    )
    assert check.status == "matched_requested_rows"
    wrong_gate = SeamGate(0, 9, 9)
    tampered = (
        *observations[:2],
        SourceActionObservation(104, observations[2].state, wrong_gate),
    )
    failed = check_source_action_block(
        tampered, program=valid_program, model=model, model_offset=len(valid_program)
    )
    assert failed.status == "first_mismatch"
    assert failed.first_mismatch_fstep == 2
    assert failed.mismatch_kind == "effective_gate"
    assert failed.mismatch_generation == 104


def test_source_block_transports_the_program_phase_with_its_offset() -> None:
    initial, program, _inlet = _closed_gate_program()
    model = close_effective_program(initial, program, max_states=1_000)
    offset = len(program) + 1
    observations = tuple(
        SourceActionObservation(
            100 + 2 * index,
            model.at(offset + index),
            program[(offset + index) % len(program)],
        )
        for index in range(3)
    )
    check = check_source_action_block(
        observations, program=program, model=model, model_offset=offset
    )
    assert check.status == "matched_requested_rows"
    assert check.checked_fsteps == 3


def test_phase_spoof_is_refused_and_outer_return_scope_is_only_the_pair() -> None:
    state = BirthRingState((1, 7), (4, 2), 1)
    gate = seam_gate(state, BirthRingPorts(0, 0))
    with pytest.raises(ConditionalActionRefused, match="phase"):
        close_effective_program(
            state,
            (SeamGate((gate.phase + 1) % 4, gate.left_output, gate.right_output),),
            max_states=32,
        )

    outer = certified_closed_outer_pair_return((1, 7, 4, 2))
    assert outer.outer_pair_return_steps == 4
    assert outer.closed_component_edges == 9
    assert outer.all_binary_carry_words_covered
    with pytest.raises(ValueError, match="outside"):
        certified_closed_outer_pair_return((1, 7, 4, 3))
