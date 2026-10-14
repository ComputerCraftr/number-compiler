from __future__ import annotations

from collections import Counter

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    CollatzInnovationCocycle,
)
from number_compiler.sequences.collatz.innovation_input_tape import (
    ParityProgramBuilder,
    _D8ParityTransition,
)
from number_compiler.sequences.collatz.innovation_port_moore import (
    SIGNED_SYMBOLS,
    InnovationTapeObservation,
    global_innovation_port_moore,
    observe_parity_program,
)
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    InnovationObserverMemo,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)

_MINIMA = {
    3: {"signed": 6, "borrow": 4, "carry": 3},
    5: {"signed": 10, "borrow": 7, "carry": 8},
    9: {"signed": 16, "borrow": 13, "carry": 11},
    49: {"signed": 98, "borrow": 81, "carry": 83},
    77: {"signed": 154, "borrow": 127, "carry": 131},
    257: {"signed": 514, "borrow": 427, "carry": 437},
}


def test_huge_cycle_observation_keeps_the_parity_word_powered() -> None:
    repetitions = 10**12
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        1,
        3 * repetitions,
        ledger=ledger,
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    observation = result.innovation_observation
    assert observation is not None and observation.producer_issued
    assert result.endpoint == 1
    assert observation.normalized_steps == 2 * repetitions
    assert observation.one_symbols == repetitions
    assert observation.symbol_counts == (0, 0, repetitions, 0, repetitions, 0)
    assert observation.borrow_f5 == observation.carry_f5 == (0,) * 6
    assert ledger.counters["collatz_innovation_moore_input_symbols"] < 100
    assert (
        ledger.counters["collatz_innovation_moore_cycle_skipped_motif_repetitions"]
        > repetitions - 100
    )


def _crt_source(residue: int, modulus: int, modulo_four: int) -> int:
    lift = ((modulo_four - residue) * pow(modulus, -1, 4)) % 4
    source = residue + modulus * lift
    return source if source else 4 * modulus


def _signed_innovation(source: int, modulus: int) -> str:
    cocycle = CollatzInnovationCocycle(source % (4 * modulus), 4 * modulus)
    operation, sign = cocycle.operation()
    family = "B" if operation == "sub" else "N" if sign < 0 else "A"
    return f"{family}{cocycle.kappa(modulus)}"


def _project(port: str, symbol: str) -> str:
    if port == "signed":
        return symbol
    if port == "borrow":
        return symbol if symbol == "B1" else "_"
    return symbol if symbol in ("A1", "N1") else "_"


@pytest.mark.parametrize("modulus", tuple(_MINIMA))
def test_global_port_moore_covers_both_crt_inputs_and_each_punctured_port(
    modulus: int,
) -> None:
    ledger = ResourceLedger()
    with InnovationObserverMemo(ledger) as memo:
        for port, expected_classes in _MINIMA[modulus].items():
            machine = global_innovation_port_moore(modulus, port, memo=memo)
            assert machine.producer_issued
            assert len(machine.class_ids) == 2 * modulus
            assert machine.class_count == expected_classes

            inverse_two = pow(2, -1, modulus)
            for residue in range(modulus):
                for parity in (0, 1):
                    source = _crt_source(residue, modulus, parity)
                    state = 2 * residue + parity
                    control = machine.control(source)
                    assert control == machine.class_ids[state]

                    for next_parity in (0, 1):
                        branch4 = parity + 2 * next_parity
                        lifted = _crt_source(residue, modulus, branch4)
                        assert lifted % modulus == residue
                        assert lifted % 4 == branch4
                        assert lifted & 1 == parity

                        expected = _project(port, _signed_innovation(lifted, modulus))
                        assert machine.outputs[control][next_parity] == expected

                        target_residue = (
                            ((3 * residue + 1) * inverse_two)
                            if parity
                            else residue * inverse_two
                        ) % modulus
                        actual_target = (3 * lifted + 1) // 2 if parity else lifted // 2
                        assert actual_target % modulus == target_residue
                        assert actual_target & 1 == next_parity
                        assert (
                            machine.successors[control][next_parity]
                            == (machine.class_ids[2 * target_residue + next_parity])
                        )


def _literal_signed_word(
    source: int, steps: int, modulus: int
) -> tuple[tuple[str, ...], int]:
    result: list[str] = []
    current = source
    one_symbols = 0
    for _ in range(steps):
        result.append(_signed_innovation(current, modulus))
        one_symbols += current & 1
        current = (3 * current + 1) // 2 if current & 1 else current // 2
    return tuple(result), one_symbols


def _counts(word: tuple[str, ...]) -> tuple[int, ...]:
    counts = Counter(word)
    return tuple(counts[symbol] for symbol in SIGNED_SYMBOLS)


def _f5_counts(word: tuple[str, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    borrow = [0] * 6
    carry = [0] * 6
    for index, symbol in enumerate(word):
        phase = index % 6
        if symbol == "B1":
            borrow[phase] = (borrow[phase] + 1) % 5
        elif symbol in ("A1", "N1"):
            carry[phase] = (carry[phase] + 1) % 5
    return tuple(borrow), tuple(carry)


def _assert_f5_observation(
    observation: InnovationTapeObservation, word: tuple[str, ...]
) -> None:
    assert (observation.borrow_f5, observation.carry_f5) == _f5_counts(word)


@pytest.mark.parametrize(
    ("source", "physical_ticks", "expected_phase"),
    ((3, 3, 1), (3, 4, 0), (164, 7, 0)),
)
def test_complete_prefix_counts_and_pending_odd_half_step(
    source: int, physical_ticks: int, expected_phase: int
) -> None:
    result = compile_collatz_temporal_run_quotient(
        source,
        physical_ticks,
        ledger=ResourceLedger(),
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    observation = result.innovation_observation
    assert observation is not None and observation.producer_issued
    expected, one_symbols = _literal_signed_word(source, result.normalized_symbols, 49)
    expected_endpoint = source
    for _ in range(result.normalized_symbols):
        expected_endpoint = (
            (3 * expected_endpoint + 1) // 2
            if expected_endpoint & 1
            else expected_endpoint // 2
        )

    assert result.phase == expected_phase
    assert result.one_run_symbols == one_symbols
    assert observation.endpoint == expected_endpoint
    assert observation.physical_endpoint == result.endpoint
    assert observation.physical_ticks == physical_ticks
    assert observation.phase == expected_phase
    assert observation.normalized_steps == len(expected)
    assert observation.one_symbols == one_symbols
    assert observation.symbol_counts == _counts(expected)
    assert observation.sample == expected[:48]
    _assert_f5_observation(observation, expected)

    if expected_phase:
        # The final 3x+1 physical half-step is present in the endpoint and
        # clock, but its pending division contributes no second innovation.
        assert observation.physical_ticks == (
            observation.normalized_steps + observation.one_symbols + 1
        )
        assert result.endpoint == 3 * expected_endpoint + 1


def test_pumped_cycle_preserves_full_word_and_f5_counts_after_skipping() -> None:
    ledger = ResourceLedger()
    with ParityProgramBuilder(1, ledger) as builder:
        builder.append_cycle(100)
        program = builder.finish(1, steps=200, one_symbols=100)
        observation = observe_parity_program(
            program,
            49,
            ledger=ledger,
            physical_endpoint=1,
            physical_ticks=300,
            phase=0,
        )

    expected, one_symbols = _literal_signed_word(1, 200, 49)
    assert observation.producer_issued
    assert observation.symbol_counts == _counts(expected)
    assert observation.sample == expected[:48]
    _assert_f5_observation(observation, expected)
    assert observation.one_symbols == one_symbols == 100
    assert (
        ledger.counters["collatz_innovation_moore_cycle_skipped_motif_repetitions"] > 0
    )


def test_d8_program_batch_rejects_forged_high_fiber_and_equal_frame() -> None:
    ledger = ResourceLedger()
    source = (1 << 40) + 0xA5
    table = D8TemporalTable.for_ledger(ledger)
    with ParityProgramBuilder(source, ledger) as builder:
        frame = D8CylinderFrame(source)
        builder.begin_d8_batch(source, frame)

        equal_frame = D8CylinderFrame(source)
        assert equal_frame == frame and equal_frame is not frame
        *_, foreign_transition = table.transition_with_parity_word(equal_frame)
        with pytest.raises(ValueError, match="exact table-issued transition"):
            builder.append_d8_transition(foreign_transition)

        advanced, ones, _residue, _origin, _width, transition = (
            table.transition_with_parity_word(frame)
        )
        builder.append_d8_transition(transition)
        endpoint = advanced.materialize()
        assert endpoint & 255 == (endpoint + 256) & 255
        with pytest.raises(ValueError, match="exact frame"):
            builder.finish_d8_batch(endpoint + 256, advanced)

        builder.finish_d8_batch(endpoint, advanced)
        program = builder.finish(endpoint, steps=8, one_symbols=ones)
        assert program.producer_issued

    assert not program.producer_issued
    assert program.source == source
    assert program.endpoint == endpoint
    assert program.steps == 8


def test_d8_zero_local_window_uses_positive_cylinder_witness() -> None:
    ledger = ResourceLedger()
    source = 256
    frame = D8CylinderFrame(source)
    table = D8TemporalTable.for_ledger(ledger)
    with ParityProgramBuilder(source, ledger) as builder:
        builder.begin_d8_batch(source, frame)
        advanced, ones, _residue, _origin, _width, transition = (
            table.transition_with_parity_word(frame)
        )
        assert transition.source_local == 0
        assert transition.odd_mask == 0
        builder.append_d8_transition(transition)
        endpoint = advanced.materialize()
        assert endpoint == 1
        builder.finish_d8_batch(endpoint, advanced)
        program = builder.finish(endpoint, steps=8, one_symbols=ones)
        assert program.producer_issued
        observation = observe_parity_program(
            program,
            3,
            ledger=ledger,
            physical_endpoint=endpoint,
            physical_ticks=8,
            phase=0,
        )
        expected, _one_symbols = _literal_signed_word(source, 8, 3)
        assert observation.endpoint == endpoint
        assert observation.one_symbols == 0
        assert observation.symbol_counts == _counts(expected)


def test_d8_issuer_rejects_same_length_and_popcount_alternate_word() -> None:
    ledger = ResourceLedger()
    source = 3
    table = D8TemporalTable.for_ledger(ledger)
    frame = D8CylinderFrame(source)
    _advanced, _ones, _residue, _origin, _width, transition = (
        table.transition_with_parity_word(frame)
    )
    # T^8(3) has low-to-high parity mask 0xA3. 0xA5 keeps the first
    # bit and popcount but changes the second input, so endpoint/output
    # aliases must not authorize it.
    assert transition.odd_mask == 0xA3
    forged_mask = 0xA5
    assert forged_mask.bit_count() == transition.odd_mask.bit_count()
    assert forged_mask & 1 == transition.odd_mask & 1
    with pytest.raises(ValueError, match="exact action"):
        _D8ParityTransition._issue(
            transition.source_local,
            transition.endpoint_local,
            forged_mask,
            transition.action,
            transition.source_frame,
            transition.advanced_frame,
        )


def test_parity_builder_rejects_foreign_seam_before_observation() -> None:
    ledger = ResourceLedger()
    with ParityProgramBuilder(3, ledger) as builder:
        endpoint, _gain = builder.append_one_run(3, 1)
        assert endpoint == 5
        with pytest.raises(ValueError, match="exact source seam"):
            builder.append_zero_run(4, 1)

    assert (
        ledger.counters.get("collatz_query_local_innovation_observer_lookups", 0) == 0
    )
    assert ledger.entries == ledger.nodes == 0


def test_parity_builder_close_can_retry_release_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    builder = ParityProgramBuilder(1, ledger)
    builder.append_cycle(5)
    original_release = ledger.release
    calls = 0

    def fail_once(owner: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal calls
        calls += 1
        if calls == 1:
            raise RuntimeError("injected release failure")
        original_release(owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "release", fail_once)
    with pytest.raises(RuntimeError, match="injected release failure"):
        builder.close()
    assert len(builder._factors) == 0
    assert ledger.nodes > 0

    builder.close()
    builder.close()
    assert ledger.nodes == 0
    assert ledger.entries == 0
