"""Bounded pair witnesses for the source-selected B1 action."""

from __future__ import annotations

from collections.abc import Callable
from itertools import combinations
from typing import cast

import devtools.verification.comma_b1_moore_audit as moore_audit
from devtools.verification.comma_b1_moore_audit import (
    AUDIT_PHASES,
    FULL_AUDIT_COUNT,
    B1Action,
    audit_b1_phase_pairs,
    full_audit_command,
    structural_audit_command,
    structural_trace,
)
from devtools.verification.comma_b1_quotient import (
    B1State,
    observe_b1,
    offset_orbit,
    offset_representatives,
)
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
)
from number_compiler.sequences.comma.decisive_endpoint import (
    EndpointOutcome,
    EndpointRun,
)

_StructuralTrie = tuple[
    tuple[tuple[int | None, ...], ...],
    tuple[object, ...],
    tuple[int, ...],
    dict[tuple[int, ...], int],
]
_structural_trie = cast(
    Callable[[dict[tuple[int, ...], set[B1Action]]], _StructuralTrie],
    object.__getattribute__(moore_audit, "_structural_trie"),
)

# Recorded by the bounded 46*924 structural audit.  This is the language-only
# observation: no terminal action payloads are stored in these words.
_OBSERVED_STRUCTURAL_WORDS = (
    (22,),
    (22, 6),
    (22, 6, 1),
    (22, 6, 1, 2, 1, 6, 6, 1, 3),
    (22, 6, 1, 2, 1, 6, 6, 28),
    (22, 6, 1, 2, 1, 6, 6, 28, 3),
    (22, 6, 1, 2, 1, 22, 6),
    (22, 6, 1, 2, 1, 22, 6, 1, 3),
    (22, 6, 1, 2, 1, 22, 6, 28),
    (22, 6, 1, 2, 1, 22, 6, 28, 3),
    (22, 6, 1, 2, 6),
    (22, 6, 1, 2, 6, 6, 6, 1, 3),
    (22, 6, 1, 2, 6, 6, 6, 28),
    (22, 6, 1, 2, 6, 6, 6, 28, 3),
    (22, 6, 1, 2, 6, 22, 6, 1, 3),
    (22, 6, 1, 2, 6, 22, 6, 28),
    (22, 6, 1, 2, 6, 22, 6, 28, 3),
    (22, 6, 1, 3),
    (22, 6, 1, 3, 1, 6),
    (22, 6, 1, 3, 1, 6, 6, 1, 3),
    (22, 6, 1, 3, 1, 6, 6, 28),
    (22, 6, 1, 3, 1, 6, 6, 28, 3),
    (22, 6, 1, 3, 1, 22, 6),
    (22, 6, 1, 3, 1, 22, 6, 1, 3),
    (22, 6, 1, 3, 1, 22, 6, 28),
    (22, 6, 1, 3, 1, 22, 6, 28, 3),
    (22, 6, 1, 3, 6),
    (22, 6, 1, 3, 6, 6),
    (22, 6, 1, 3, 6, 6, 6),
    (22, 6, 1, 3, 6, 6, 6, 1, 3),
    (22, 6, 1, 3, 6, 6, 6, 28),
    (22, 6, 1, 3, 6, 6, 6, 28, 3),
    (22, 6, 1, 3, 6, 22, 6),
    (22, 6, 1, 3, 6, 22, 6, 1, 3),
    (22, 6, 1, 3, 6, 22, 6, 28),
    (22, 6, 1, 3, 6, 22, 6, 28, 3),
)


def _reference_action(offset: int, phase: int) -> B1Action:
    """Convert the independent chart teacher to the orbit-word key."""

    reference = observe_b1(B1State(offset_orbit(offset), phase)).observation
    if reference.kind == "live":
        return B1Action("live", reference.value, None, 1)
    if reference.kind == "fork":
        return B1Action("fork", None, reference.value, 0)
    if reference.kind == "landmine":
        return B1Action("landmine", None, None, 0)
    raise AssertionError(f"unknown chart observation: {reference}")


def test_all_1035_representative_pairs_have_an_exact_phase_witness() -> None:
    report = audit_b1_phase_pairs()
    representatives = offset_representatives()

    assert report.phases == AUDIT_PHASES
    assert report.representatives == representatives
    assert len(report.observations) == 46 * len(AUDIT_PHASES)
    assert report.pair_count == 46 * 45 // 2 == 1_035
    assert len(report.witnesses) == 1_035
    assert report.collisions == ()
    assert report.unique_action_counts == {0: 41, 1: 40}


def test_witnesses_match_independent_endpoint_calls() -> None:
    report = audit_b1_phase_pairs()
    by_key = {(item.fiber, item.phase): item.action for item in report.observations}
    witnesses = {(item.left.fiber, item.right.fiber): item for item in report.witnesses}
    representatives = report.representatives

    for left, right in combinations(range(46), 2):
        expected_phase = next(
            phase
            for phase in AUDIT_PHASES
            if _reference_action(representatives[left], phase)
            != _reference_action(representatives[right], phase)
        )
        witness = witnesses[left, right]
        assert witness.left.phase == witness.right.phase == expected_phase
        assert witness.left.action == by_key[left, expected_phase]
        assert witness.right.action == by_key[right, expected_phase]


def test_sector_work_is_not_part_of_the_terminal_observation() -> None:
    first = EndpointRun(EndpointOutcome("landmine"), strict_sector_advances=1)
    second = EndpointRun(EndpointOutcome("landmine"), strict_sector_advances=2)
    assert first.strict_sector_advances != second.strict_sector_advances
    assert B1Action.from_run(first) == B1Action.from_run(second)


def test_full_grid_is_explicitly_prepared_but_not_run_by_bounded_audit() -> None:
    command = full_audit_command()
    assert "comma_b1_moore_audit" in command
    assert "--full-source-grid" in command
    assert FULL_AUDIT_COUNT == 42_504


def test_structural_trace_is_a_language_record_with_an_explicit_guard_boundary() -> (
    None
):
    trace = structural_trace(0, 0)
    reference = observe_b1(B1State(offset_orbit(0), 0)).observation

    assert trace.word == tuple(entry.period for entry in trace.entries)
    assert trace.entries
    assert all(entry.phase == 0 for entry in trace.entries)
    assert trace.action.kind == reference.kind
    if reference.kind == "live":
        assert trace.action.live_fiber == reference.value
    elif reference.kind == "fork":
        assert trace.action.fork_a == reference.value
    else:
        assert reference.kind == "landmine"
    assert "--structural-moore" in structural_audit_command()


def test_language_minimization_ignores_terminal_payload_sets() -> None:
    words: dict[tuple[int, ...], set[B1Action]] = {
        (1,): {B1Action("live", 0, None, 1)},
        (2,): {B1Action("live", 1, None, 1)},
    }
    rows, outputs, _alphabet, _states = _structural_trie(words)
    minimized = minimize_finite_observer(rows, outputs)

    assert outputs == (False, True, True)
    assert minimized.classes == 2


def test_recorded_structural_dfa_accepts_all_36_words_without_payloads() -> None:
    """The 19-state result is only the observed period-word language."""

    word_actions: dict[tuple[int, ...], set[B1Action]] = {
        word: set() for word in _OBSERVED_STRUCTURAL_WORDS
    }
    rows, outputs, alphabet, _states = _structural_trie(word_actions)
    minimized = minimize_finite_observer(rows, outputs)

    assert len(word_actions) == 36
    assert alphabet == (1, 2, 3, 6, 22, 28)
    assert minimized.classes == 19

    def accepts(word: tuple[int, ...]) -> bool:
        state = 0
        for symbol in word:
            column = alphabet.index(symbol)
            target = rows[state][column]
            if target is None:
                return False
            state = target
        return bool(outputs[state])

    assert all(accepts(word) for word in _OBSERVED_STRUCTURAL_WORDS)


def test_same_period_word_has_different_exact_b1_actions() -> None:
    left = structural_trace(10, 40)
    right = structural_trace(10, 44)

    assert left.word == right.word == (22, 6, 1, 2, 1, 6, 6, 1, 3)
    assert left.action == B1Action("live", 13, None, 1)
    assert right.action == B1Action("live", 22, None, 1)
    assert left.action != right.action
