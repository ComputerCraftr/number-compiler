"""Birth-driven periods: exact finite source proofs, not guessed infinite cycles."""

from dataclasses import replace
from random import Random
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.metric_keys.double_reverse import (
    DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS,
    DOUBLE_REVERSE_BIRTH_LAYER_PERIOD_COMPARISONS,
    DOUBLE_REVERSE_BIRTH_LAYER_PUBLICATIONS,
)
from number_compiler.sequences.double_reverse import (
    temporal_birth_ring as birth_ring_module,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    validate_source_record,
)
from number_compiler.sequences.double_reverse.boundary_cycles import (
    CANDIDATE_COMPONENTS,
    boundary_steps,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_bound_bank import _source_suffix
from number_compiler.sequences.double_reverse.temporal_birth_induction import (
    MAX_BIRTH_DURATION_BITS,
    CertifiedBirthClock,
    birth_clock_for_source,
)
from number_compiler.sequences.double_reverse.temporal_birth_ring import (
    BirthReturnBudgetExceeded,
    BirthRingPorts,
    BirthRingState,
    assert_birth_layer_step,
    certified_birth_ring,
    conditional_birth_return,
    odd_boundary_pairs,
    power_birth_model,
)
from number_compiler.sequences.double_reverse.temporal_diagonal_induction import (
    SeamGate,
    certified_closed_outer_pair_return,
    seam_gate,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import edge_phase


def _next(x: int) -> int:
    return int(str(x)[::-1]) << 1


def _phase(value: int) -> int | None:
    digits = str(value)
    if len(digits) < 4:
        return None
    return edge_phase(
        (int(digits[0]), int(digits[1])),
        (int(digits[-2]), int(digits[-1])),
    )


def test_birth_centered_step_matches_arithmetic_all_phases() -> None:
    for seed in (1, 196, 173488, 174388):
        value = seed
        seen = set()
        for _ in range(90):
            word = str(value)
            phase = _phase(value)
            pairs = min(8, (len(word) - 2) // 2)
            if phase is not None and pairs >= 1:
                seen.add(phase)
                state = BirthRingState(
                    tuple(map(int, word[:pairs])),
                    tuple(map(int, word[-pairs:])),
                    phase,
                )
                inlet = BirthRingPorts(int(word[pairs]), int(word[-pairs - 1]))
                after, _ = state.advance(inlet)
                intermediate = str(_next(value))
                actual_odd = tuple(
                    (int(intermediate[i]), int(intermediate[-1 - i]))
                    for i in range(pairs)
                )
                assert odd_boundary_pairs(state, inlet) == actual_odd
                target = str(_next(_next(value)))
                assert after == BirthRingState(
                    tuple(map(int, target[:pairs])),
                    tuple(map(int, target[-pairs:])),
                    (phase + 2) % 4,
                )
                if pairs >= 2:
                    assert_birth_layer_step(state, inlet)
            value = _next(value)
        assert seen == {0, 1, 2, 3}


def test_source_independent_layer_intertwining() -> None:
    rng = Random(11882)
    for phase in range(4):
        for width in range(2, 10):
            for _ in range(50):
                state = BirthRingState(
                    tuple(rng.randrange(10) for _ in range(width)),
                    tuple(rng.randrange(10) for _ in range(width)),
                    phase,
                )
                assert_birth_layer_step(
                    state, BirthRingPorts(rng.randrange(10), rng.randrange(10))
                )


def test_birth_modular_clock_predicts_every_source_step() -> None:
    for seed in (1, 196):
        with DoubleReverseTerm(seed, 300) as term:
            _entry, source = term._prepare_bank_source(
                max_prefix=min(32, term.generation - 2)
            )
            clock = birth_clock_for_source(source)
            assert clock.mod9_period == 6
            assert clock.width_mod9_period == 12
            assert clock.width_mod99_period == 120
            value = seed
            for _ in range(source.physical_prefix):
                value = _next(value)
            for steps in range(125):
                phase, width, residue = clock.state(steps)
                assert phase == (clock.phase + steps) % 4
                assert width == len(str(value))
                assert residue == value % 99
                value = _next(value)
            phase, width, residue = clock.state(120 * 10**10)
            assert phase == clock.phase and residue == clock.residue99
            assert width - clock.width == 60 * 10**10


@pytest.mark.validation
def test_seed_specific_periods_generated_by_born_inlets() -> None:
    expected = {
        196: (4, 12, 12, 12, 12, 12, 24, 48),
        1: (4, 12, 12, 12, 12, 12, 48, 48),
    }
    for seed, wanted in expected.items():
        # The source report establishes the seventh-layer distinction only
        # after a 144-F-step witnessed inlet horizon. Use one cone per seed;
        # shorter prefixes correctly leave that layer uncertified.
        with DoubleReverseTerm(seed, 1000, max_steps=1000, max_state_bits=8192) as term:
            record = term.birth_layer_periods(8, lookback_f_steps=144, max_states=1024)
            validate_source_record(record)
            measured_induction_rows = sum(
                layer.diagonal_induction.compared_rows
                for layer in record.layers
                if layer.diagonal_induction is not None
            )
            assert term.metrics()[DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS] == (
                measured_induction_rows
            )
            measured_period_comparisons = term.metrics()[
                DOUBLE_REVERSE_BIRTH_LAYER_PERIOD_COMPARISONS
            ]
            assert measured_period_comparisons > 0
            before_summary = term.metrics()[DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS]
            record.validated_projection()
            record.validated_projection()
            assert term.metrics()[DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS] == (
                before_summary
            )
            assert term.metrics()[DOUBLE_REVERSE_BIRTH_LAYER_PERIOD_COMPARISONS] == (
                measured_period_comparisons
            )
            got = tuple(
                layer.conditional_return.physical_pair_period
                if layer.conditional_return
                else None
                for layer in reversed(record.layers)
            )
            assert got == wanted
            assert record.f_steps == 144
            assert record.final_pairs[0].digits == (1, 8)
            assert record.independently_powered_pairs == 8
            assert record.outermost_pair_return is not None
            assert record.outermost_pair_return.outer_pair_return_steps == 4
            assert record.outermost_pair_return.all_binary_carry_words_covered
            for layer in record.layers:
                witness = layer.diagonal_induction
                if witness is not None:
                    assert not witness.indefinitely_certified
                    if witness.finite_all_physical_equal:
                        assert witness.compared_rows == witness.equal_bank_rows
                        assert witness.compared_rows == witness.agreeing_seam_rows
            assert not any(
                layer.indefinite_source_authorized for layer in record.layers
            )
            assert not record.layers[0].indefinite_source_authorized
            # The source seal covers every public packet field, not just the
            # headline phase. Restore after the expected refusal so teardown
            # can still inspect the record safely.
            original_phase = record.source_phase
            object.__setattr__(record, "source_phase", (original_phase + 1) % 4)
            with pytest.raises(ValueError, match="authority"):
                record.validated_projection()
            object.__setattr__(record, "source_phase", original_phase)


def test_seam_gate_is_the_exact_inlet_quotient_for_every_phase() -> None:
    expected_classes = (2, 4, 2, 1)
    for phase, count in enumerate(expected_classes):
        state = BirthRingState((1, 6, 3), (8, 2, 9), phase)
        gate_to_next: dict[SeamGate, BirthRingState] = {}
        next_to_gate: dict[BirthRingState, SeamGate] = {}
        for left in range(10):
            for right in range(10):
                inlet = BirthRingPorts(left, right)
                gate = seam_gate(state, inlet)
                next_state = state.advance(inlet)[0]
                assert gate_to_next.setdefault(gate, next_state) == next_state
                assert next_to_gate.setdefault(next_state, gate) == gate
        assert len(gate_to_next) == count
        assert len(next_to_gate) == count


def test_closed_outer_border_return_is_only_the_first_pair_claim() -> None:
    expected_pairs = ((1, 8), (1, 2), (4, 2), (4, 8))
    for edge in CANDIDATE_COMPONENTS[0]:
        theorem = certified_closed_outer_pair_return(edge)
        assert theorem.outer_pair_return_steps == 4
        assert theorem.all_binary_carry_words_covered
        assert (edge[0], edge[3]) == expected_pairs[theorem.phase]

    start = (1, 7, 4, 2)
    first = next(
        step.target for step in boundary_steps(start).steps if step.inward_carry == 0
    )
    at_t2 = next(
        step.target for step in boundary_steps(first).steps if step.inward_carry == 0
    )
    at_t3 = boundary_steps(at_t2).steps[0].target
    at_t4 = boundary_steps(at_t3).steps[0].target
    at_t5 = next(
        step.target for step in boundary_steps(at_t4).steps if step.inward_carry == 1
    )
    assert (first[0], first[3]) == (at_t5[0], at_t5[3])
    assert first != at_t5


def test_return_multiplier_is_not_assumed_to_be_two_or_three() -> None:
    state = BirthRingState((3, 8, 7, 8), (9, 8, 4, 5), 3)
    motif = (BirthRingPorts(4, 2), BirthRingPorts(3, 9))
    model = conditional_birth_return(state, motif, max_states=128)
    assert model.full_state_period == 10
    assert model.return_multiplier == 5
    assert model.gt_high_period == 1
    state_at_big, frame, same_model = power_birth_model(
        state, motif, 10**80 + 17, max_states=128
    )
    assert same_model == model
    assert state_at_big.pairs == 4 and len(frame) == 4


def test_public_birth_powers_respect_the_common_query_bit_budget() -> None:
    duration = 1 << MAX_BIRTH_DURATION_BITS
    clock = CertifiedBirthClock(0, 2, 2, 2, 1, 1, 1, (0, 0), (0, 0))
    with pytest.raises(ValueError, match="query bit budget"):
        clock.state(duration)
    with pytest.raises(ValueError, match="query bit budget"):
        power_birth_model(
            BirthRingState((1,), (8,), 0),
            (BirthRingPorts(0, 0),),
            duration,
        )


def test_public_conditional_models_enforce_the_production_workspace_caps() -> None:
    motif = (BirthRingPorts(0, 0),)
    with pytest.raises(ValueError, match="bounded input word"):
        conditional_birth_return(
            BirthRingState((1,) * 17, (8,) * 17, 0), motif, max_states=8
        )
    with pytest.raises(ValueError, match="bounded input word"):
        conditional_birth_return(BirthRingState((1,), (8,), 0), motif, max_states=1025)
    with pytest.raises(ValueError, match="bounded input word"):
        conditional_birth_return(
            BirthRingState((1,), (8,), 0), motif * 161, max_states=8
        )


def test_conditional_orbit_budget_refusal_is_typed() -> None:
    state = BirthRingState((3, 8, 7, 8), (9, 8, 4, 5), 3)
    motif = (BirthRingPorts(4, 2), BirthRingPorts(3, 9))
    with pytest.raises(BirthReturnBudgetExceeded, match="did not close"):
        conditional_birth_return(state, motif, max_states=1)


def test_unrelated_model_value_error_is_not_misreported_as_budget_refusal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forced_lasso(
        _letters: tuple[BirthRingPorts, ...], *, min_repeats: int = 3
    ) -> tuple[tuple[int, int], int]:
        assert min_repeats == 3
        return (0, 1), 0

    def fail_model(*_args: object, **_kwargs: object) -> Never:
        raise ValueError("injected unrelated model validation error")

    with DoubleReverseTerm(196, 64) as term:
        _entry, source = term._prepare_bank_source(
            max_prefix=min(32, term.generation - 2)
        )
        source = _source_suffix(source, min(12, source.f_steps))
        with monkeypatch.context() as poison:
            poison.setattr(birth_ring_module, "finite_suffix_period", forced_lasso)
            poison.setattr(
                birth_ring_module, "_enumerate_conditional_birth_model", fail_model
            )
            with pytest.raises(ValueError, match="unrelated model validation error"):
                certified_birth_ring(source, pairs=2, max_model_states=8)


def test_birth_layer_query_does_not_render_a_complete_temporal_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("birth layers must use causal ports, not full rendering")

    with DoubleReverseTerm(196, 64) as term:
        with monkeypatch.context() as poison:
            poison.setattr(DoubleReverseTerm, "digit", forbidden)
            poison.setattr(DoubleReverseTerm, "digits", forbidden)
            poison.setattr(DoubleReverseTerm, "iter_digits", forbidden)
            poison.setattr(DoubleReverseTerm, "materialize", forbidden)
            record = term.birth_layer_periods(4, lookback_f_steps=12, max_states=128)
        assert record.f_steps == 12
        assert record.final_pairs
        validate_source_record(record)
        rows = sum(
            layer.diagonal_induction.compared_rows
            for layer in record.layers
            if layer.diagonal_induction is not None
        )
        before = term.metrics()
        assert before[DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS] == rows
        record.validated_projection()
        record.validated_projection()
        after = term.metrics()
        for counter in (
            DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS,
            DOUBLE_REVERSE_BIRTH_LAYER_PERIOD_COMPARISONS,
        ):
            assert after[counter] == before[counter]
        assert not any(layer.indefinite_source_authorized for layer in record.layers)
        original_phase = record.source_phase
        try:
            object.__setattr__(record, "source_phase", (original_phase + 1) % 4)
            with pytest.raises(ValueError, match="authority"):
                record.validated_projection()
        finally:
            object.__setattr__(record, "source_phase", original_phase)


def test_failed_birth_publication_releases_its_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fail_before_publication(*_args: object, **_kwargs: object) -> Never:
        raise RuntimeError("injected birth publisher failure")

    with DoubleReverseTerm(196, 64) as term:
        _entry, source = term._prepare_bank_source(
            max_prefix=min(32, term.generation - 2)
        )
        source = _source_suffix(source, min(12, source.f_steps))
        ledger = source.ledger
        before = (ledger.entries, ledger.nodes)
        published = ledger.counters.get(
            DOUBLE_REVERSE_BIRTH_LAYER_PUBLICATIONS,
            0,
        )
        with monkeypatch.context() as poison:
            poison.setattr(
                birth_ring_module,
                "_certified_birth_ring_reserved",
                fail_before_publication,
            )
            with pytest.raises(RuntimeError, match="injected birth publisher failure"):
                certified_birth_ring(source, pairs=4, max_model_states=128)
        assert (ledger.entries, ledger.nodes) == before
        assert (
            ledger.counters.get(
                DOUBLE_REVERSE_BIRTH_LAYER_PUBLICATIONS,
                0,
            )
            == published
        )
        ledger.tighten_limits(ledger.nodes, ledger.entries)
        with pytest.raises(BlockContextBudgetExceeded):
            certified_birth_ring(source, pairs=4, max_model_states=128)
        assert (ledger.entries, ledger.nodes) == before


def test_forged_birth_ports_and_foreign_source_roots_are_rejected() -> None:
    with pytest.raises(ValueError, match="decimal digits"):
        BirthRingPorts(10, 0)
    with DoubleReverseTerm(196, 64) as term:
        _entry, source = term._prepare_bank_source(max_prefix=32)
        foreign_root = (source.root + 1) % len(source.arena.nodes)
        forged_root = replace(source, root=foreign_root)
        with pytest.raises(ValueError, match="pointed source"):
            certified_birth_ring(forged_root, pairs=2)
        forged_phase = replace(source, phase=(source.phase + 1) % 4)
        with pytest.raises(ValueError, match="pointed source"):
            certified_birth_ring(forged_phase, pairs=2)


def test_phase_two_birth_reanchors_the_canonical_outer_pair() -> None:
    # Phase-2 creates a *new* leading 1. The older ray bank follows the
    # previous leading 4 one cell inward and legitimately reports 7.
    state = BirthRingState((4,), (2,), 2)
    after, frames = state.advance(BirthRingPorts(0, 0))
    assert frames[0].digits == (4, 2)
    assert after.left == (1,) and after.right == (8,)
