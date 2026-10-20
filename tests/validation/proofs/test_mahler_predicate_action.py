"""Focused checks for the source-cylinder Mahler predicate residual."""

from __future__ import annotations

from collections.abc import Iterator
from fractions import Fraction

import pytest

from devtools.experiments.antihydra.mahler_predicate import (
    MahlerPredicateState,
    mahler_bit_action,
    mahler_odd_event_action,
)
from devtools.experiments.antihydra.source_safety import SourceSafetyWorkspace
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational as Q,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    SaturatingAffineAction,
)
from number_compiler.resources.ledger import ResourceLedger


def _literal_state(bits: tuple[int, ...]) -> MahlerPredicateState:
    margin: Fraction | None = None
    for bit in bits:
        roof = Fraction(9, 4) if bit == 0 else Fraction(3, 4)
        margin = roof if margin is None else min(roof, Fraction(3, 2) * (margin - bit))
    if margin is None:
        return MahlerPredicateState.initial()
    if margin <= 0:
        return MahlerPredicateState.failed()
    return MahlerPredicateState(False, Q(margin.numerator, margin.denominator))


def _temporal_bits(source: int, width: int) -> tuple[int, ...]:
    current = source
    bits: list[int] = []
    for _ in range(width):
        epsilon = current & 1
        bits.append(epsilon)
        current = (3 * current + epsilon) // 2
    return tuple(bits)


def test_source_cylinder_composes_exact_predicate_action() -> None:
    workspace = SourceSafetyWorkspace(
        ResourceLedger(max_nodes=20_000, max_cache_entries=50_000), max_width=10
    )
    for width in range(1, 11):
        for residue in range(1 << width):
            handle = workspace.cylinder(width, residue)
            block = workspace.view(handle)
            bits = _temporal_bits(residue, width)
            expected = _literal_state(bits)
            assert block.predicate_state == expected
            action = mahler_bit_action(bits[0])
            for bit in bits[1:]:
                action = action.then(mahler_bit_action(bit))
            assert block.predicate_action == action


def test_predicate_state_is_right_congruent_under_composed_actions() -> None:
    workspace = SourceSafetyWorkspace(
        ResourceLedger(max_nodes=10_000, max_cache_entries=20_000), max_width=8
    )
    first = workspace.view(workspace.cylinder(4, 3))
    second = workspace.view(workspace.cylinder(4, 12))
    composed = workspace.view(
        workspace.compose(workspace.cylinder(4, 3), workspace.cylinder(4, 12))
    )
    assert composed.predicate_action == first.predicate_action.then(
        second.predicate_action
    )
    assert composed.predicate_state == first.predicate_state.advance_action(
        second.predicate_action
    )


def test_equal_predicate_states_keep_distinct_source_geometry() -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=8)
    first = workspace.view(workspace.cylinder(1, 0))
    second = workspace.view(workspace.cylinder(4, 5))
    assert first.predicate_state == second.predicate_state
    assert first.endpoint != second.endpoint
    assert first.residue != second.residue


def test_zero_margin_is_forbidden_and_forbidden_is_canonical() -> None:
    zero_cap = SaturatingAffineAction(Q(1), Q(0), Q(0))
    forbidden = MahlerPredicateState.initial().advance_action(zero_cap)
    assert forbidden == MahlerPredicateState.failed()
    assert forbidden.semantic_key == ("mahler-predicate", "FORBIDDEN")
    assert forbidden.advance_bit(0) is forbidden


def test_predicate_rejects_positive_offset_and_malformed_states() -> None:
    with pytest.raises(ValueError, match="nonpositive offset"):
        MahlerPredicateState.initial().advance_action(
            SaturatingAffineAction(Q(1), Q(1))
        )
    with pytest.raises(TypeError, match="exact rational"):
        MahlerPredicateState(False, 1)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="forbidden"):
        MahlerPredicateState(True, Q(1))
    with pytest.raises(ValueError, match="positive"):
        MahlerPredicateState(False, Q(0))


def test_source_first_hole_selects_closed_odd_zero_observer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.experiments.antihydra import mahler_predicate
    from number_compiler.arithmetic.automata.program_word import from_values
    from number_compiler.arithmetic.fields.radix import digits_lsd

    expected: dict[int, tuple[int, SaturatingAffineAction]] = {}
    for source in range(1, 512, 2):
        current, exponent = source, 0
        action = SaturatingAffineAction.identity()
        while exponent == 0 or current % 2 == 0:
            bit = current % 2
            action = action.then(mahler_bit_action(bit))
            current = (3 * current + bit) // 2
            exponent += 1
        expected[source] = exponent, action

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("odd-event safety replayed temporal bits")

    monkeypatch.setattr(mahler_predicate, "mahler_bit_action", forbidden)
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=16)
    try:
        for source, (exponent, action) in expected.items():
            word = from_values(digits_lsd(source, 4))
            event = workspace.odd_zero_observer(word)
            assert event.source is word
            assert event.exponent == exponent
            assert event.predicate_action == action
            assert MahlerPredicateState.initial().advance_action(
                event.predicate_action
            ) == _literal_state((1,) + (0,) * (exponent - 1))
    finally:
        workspace.close()


def test_odd_event_cursor_does_not_scan_irregular_high_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.automata import program_word
    from number_compiler.sequences.collatz import root_germs

    word = program_word.from_values((3,) + tuple(i % 4 for i in range(256)))
    original_runs = program_word.iter_runs
    visited = 0

    def counted(
        source: program_word.SourceWord,
        *,
        metrics: program_word.RunTraversalMetrics | None = None,
    ) -> Iterator[tuple[int, int]]:
        nonlocal visited
        for row in original_runs(source, metrics=metrics):
            visited += 1
            assert visited == 1, "first hole visited an untouched source run"
            yield row

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("first-hole cursor rebuilt its untouched suffix")

    monkeypatch.setattr(root_germs, "iter_runs", counted)
    monkeypatch.setattr(program_word, "slice_runs", forbidden)
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=16)
    try:
        event = workspace.odd_zero_observer(word)
        assert event.exponent == 1 and visited == 1
        assert isinstance(event.residual, program_word.SourceWordSuffix)
        assert event.residual.source is word and event.residual.start == 1
        assert (
            0
            < workspace.ledger.counters["mahler_odd_zero_observer_source_nodes_visited"]
            < 64
        )
        assert (
            workspace.ledger.counters["mahler_odd_zero_observer_source_frontier_peak"]
            < 16
        )
    finally:
        workspace.close()


def test_odd_event_keeps_admission_and_physical_event_conventions_distinct() -> None:
    from number_compiler.arithmetic.automata.program_word import from_values, run
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=8)
    with pytest.raises(ValueError, match="positive and odd"):
        workspace.odd_zero_observer(from_values((2,)))
    with pytest.raises(BlockContextBudgetExceeded, match="odd-event width"):
        workspace.odd_zero_observer(run(1, 100_000))
    assert (
        workspace.ledger.counters["mahler_odd_zero_observer_source_nodes_visited"] > 0
    )
    for invalid in (0, -1, True):
        with pytest.raises(ValueError, match="positive"):
            mahler_odd_event_action(invalid)
    workspace.close()
    with pytest.raises(ValueError, match="closed"):
        workspace.odd_zero_observer(from_values((1,)))


def test_odd_event_instrumentation_counts_actual_early_and_failed_visits() -> None:
    from number_compiler.arithmetic.automata.program_word import from_values, run
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=8)
    try:
        workspace.odd_zero_observer(from_values((3,)))
        # Bounds, low digit, first-hole demand, and empty cut all perform
        # distinct metadata/traversal visits. No high suffix is inspected.
        assert (
            workspace.ledger.counters["mahler_odd_zero_observer_source_nodes_visited"]
            == 8
        )
        before = workspace.ledger.counters[
            "mahler_odd_zero_observer_source_nodes_visited"
        ]
        with pytest.raises(BlockContextBudgetExceeded):
            workspace.odd_zero_observer(run(1, 100_000))
        # An entire neutral run is one node; the implicit high zero supplies
        # the mismatch. Refused work is reported without a metrics scan.
        assert (
            workspace.ledger.counters["mahler_odd_zero_observer_source_nodes_visited"]
            - before
            == 7
        )
    finally:
        workspace.close()


def test_odd_zero_observer_is_not_live_source_safety_event_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.experiments.antihydra.source_safety import source_event
    from number_compiler.arithmetic.automata.program_word import from_values

    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=8)
    try:
        observer = workspace.odd_zero_observer(from_values((1,)))
        admitted = source_event(workspace, 1, Q(3, 8))
        assert observer.exponent == 2 and admitted.exponent == 1
        assert observer.predicate_action == mahler_odd_event_action(2)
        assert admitted.endpoint == 2 and admitted.next_fraction == Q(1, 16)

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("live source safety used the odd-zero observer")

        monkeypatch.setattr(workspace, "odd_zero_observer", forbidden)
        assert source_event(workspace, 1, Q(3, 8)) == admitted
    finally:
        workspace.close()
