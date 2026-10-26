"""Regression tests for quotient-first outer 2rev10 pair transfers."""

from __future__ import annotations

from random import Random
from typing import NoReturn

import pytest

from number_compiler.sequences.double_reverse import temporal_depth_transfer_matrix
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    PeriodicBankFrame,
)
from number_compiler.sequences.double_reverse.temporal_birth_ring import (
    BirthRingPorts,
    BirthRingState,
    odd_boundary_pairs,
)
from number_compiler.sequences.double_reverse.temporal_certified_halo import (
    CertifiedHalo,
    ring_next_pair,
    ring_outer,
)
from number_compiler.sequences.double_reverse.temporal_depth_transfer_matrix import (
    ALL_PAIRS,
    BooleanPairMatrix,
    admitted_outer_port_classes,
    outer_port_class,
    outer_step_matrix,
    pair_index,
    rooted_finite_depth_trace,
    source_conditioned_depth_return,
)


def _literal_outer_step_matrix(
    current: BirthRingState, following: BirthRingState
) -> BooleanPairMatrix:
    """The pre-quotient implementation, retained as an independent oracle."""
    rows: list[int] = []
    for left, right in ALL_PAIRS:
        inlet = BirthRingPorts(left, right)
        if current.advance(inlet)[0] != following:
            rows.append(0)
            continue
        extended = BirthRingState(
            current.left + (left,), (right,) + current.right, current.phase
        )
        targets = 0
        for next_left in (0, 3):
            for next_right in (0, 5):
                evolved = extended.advance(BirthRingPorts(next_left, next_right))[0]
                assert (evolved.left[:-1], evolved.right[1:], evolved.phase) == (
                    following.left,
                    following.right,
                    following.phase,
                )
                targets |= 1 << pair_index((evolved.left[-1], evolved.right[0]))
        rows.append(targets)
    result = BooleanPairMatrix(tuple(rows))
    assert result.maximum_successors <= 4
    return result


def _random_ring(rng: Random, width: int, phase: int) -> BirthRingState:
    return BirthRingState(
        tuple(rng.randrange(10) for _ in range(width)),
        tuple(rng.randrange(10) for _ in range(width)),
        phase,
    )


def _literal_source_conditioned_rows(
    outer: tuple[BirthRingState, ...],
    source_halo: BirthRingState,
    initial_pair: tuple[int, int],
    odd_outer: tuple[tuple[tuple[int, int], ...], ...] | None = None,
) -> tuple[int, ...]:
    """Enumerate full candidate trajectories, then filter their observed traces.

    This intentionally does not share the production early-rejection schedule
    or its quotient classifier: a wrong filter cannot become its own oracle.
    """
    pairs = outer[0].pairs
    seam = source_halo.pairs - pairs - 1
    rows: list[int] = []
    for initial in ALL_PAIRS:
        candidate = BirthRingState(
            source_halo.left[:pairs] + (initial[0],) + source_halo.left[pairs + 1 :],
            source_halo.right[:seam] + (initial[1],) + source_halo.right[seam + 1 :],
            source_halo.phase,
        )
        trajectory = [CertifiedHalo(candidate, candidate.pairs)]
        for _ in outer[1:]:
            trajectory.append(trajectory[-1].step())
        observed = tuple(halo.outer(pairs) for halo in trajectory)
        observed_odd = tuple(
            odd_boundary_pairs(
                halo.outer(pairs),
                BirthRingPorts(*ring_next_pair(halo.state, pairs)),
            )
            for halo in trajectory[:-1]
        )
        matches = observed == outer and (odd_outer is None or observed_odd == odd_outer)
        endpoint = ring_next_pair(trajectory[-1].state, pairs)
        rows.append((1 << pair_index(endpoint)) if matches else 0)
    assert ring_next_pair(source_halo, pairs) == initial_pair
    return tuple(rows)


def test_outer_pair_matrix_matches_literal_oracle_for_all_rows() -> None:
    rng = Random(20261026)
    for phase in range(4):
        random_width = rng.randrange(3, 10)
        for width in (1, 2, 5, random_width):
            current = _random_ring(rng, width, phase)
            following = current.advance(
                BirthRingPorts(rng.randrange(10), rng.randrange(10))
            )[0]
            assert outer_step_matrix(current, following) == _literal_outer_step_matrix(
                current, following
            )


def test_guard_construction_does_not_enumerate_physical_inlet_pairs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    current = BirthRingState((1, 7), (6, 8), 0)
    following = current.advance(BirthRingPorts(3, 5))[0]

    def forbid_classification(
        _state: BirthRingState, _left: int, _right: int
    ) -> NoReturn:
        raise AssertionError("guard construction expanded physical inlet pairs")

    monkeypatch.setattr(
        temporal_depth_transfer_matrix, "outer_port_class", forbid_classification
    )
    assert admitted_outer_port_classes(current, following) == frozenset({(1, 0)})


def test_outer_pair_matrix_matches_oracle_for_tampered_following() -> None:
    rng = Random(20261027)
    for phase in range(4):
        current = _random_ring(rng, 5, phase)
        authentic = current.advance(BirthRingPorts(8, 3))[0]
        changed_left = ((authentic.left[0] + 1) % 10, *authentic.left[1:])
        tampered = BirthRingState(changed_left, authentic.right, authentic.phase)
        assert outer_step_matrix(current, tampered) == _literal_outer_step_matrix(
            current, tampered
        )


def test_outer_pair_matrix_uses_at_most_four_full_ring_guards(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    rng = Random(20261028)
    current = _random_ring(rng, 5, 0)
    following = current.advance(BirthRingPorts(9, 7))[0]
    original = BirthRingState.advance
    full_ring_calls = 0

    def count_outer_only(
        state: BirthRingState, inlet: BirthRingPorts
    ) -> tuple[BirthRingState, tuple[PeriodicBankFrame, ...]]:
        nonlocal full_ring_calls
        if state is not current:
            raise AssertionError("optimized matrix rebuilt an extended full ring")
        full_ring_calls += 1
        if full_ring_calls > 4:
            raise AssertionError(
                "outer guard quotient exceeded four representative advances"
            )
        return original(state, inlet)

    monkeypatch.setattr(BirthRingState, "advance", count_outer_only)
    matrix = outer_step_matrix(current, following)
    assert len(matrix.rows) == 100
    assert full_ring_calls <= 4


@pytest.mark.parametrize("tamper", ("width", "phase"))
def test_outer_pair_matrix_rejects_incompatible_following(tamper: str) -> None:
    current = BirthRingState((1, 7), (3, 8), 2)
    following = current.advance(BirthRingPorts(4, 6))[0]
    if tamper == "width":
        incompatible = BirthRingState(
            following.left[:-1], following.right[:-1], following.phase
        )
    else:
        incompatible = BirthRingState(
            following.left, following.right, (following.phase + 1) % 4
        )
    with pytest.raises(ValueError, match="compatible moving-boundary rings"):
        outer_step_matrix(current, incompatible)


def test_source_conditioned_rows_match_prequotient_halo_oracle() -> None:
    rng = Random(20261029)
    for phase in range(4):
        for width in (4, 5):
            pairs = 2
            source_halo = _random_ring(rng, width, phase)
            outer, _ = rooted_finite_depth_trace(
                source_halo, outer_pairs=pairs, f_steps=width - pairs - 1
            )
            outer = tuple(ring_outer(state, pairs) for state in outer)
            initial_pair = ring_next_pair(source_halo, pairs)
            result = source_conditioned_depth_return(outer, source_halo, initial_pair)
            assert result.action.rows == _literal_source_conditioned_rows(
                outer, source_halo, initial_pair
            )
            assert result.pointed_trace


def test_source_conditioned_keeps_odd_outer_guard_after_port_filter() -> None:
    pairs = 2
    source_halo = BirthRingState((9, 9, 9, 9), (9, 9, 9, 9), 1)
    outer, odd_rows = rooted_finite_depth_trace(
        source_halo, outer_pairs=pairs, f_steps=1
    )
    outer = tuple(ring_outer(state, pairs) for state in outer)
    assert odd_rows[0] is not None
    odd_outer = (odd_rows[0][:pairs],)
    initial_pair = ring_next_pair(source_halo, pairs)
    result = source_conditioned_depth_return(
        outer, source_halo, initial_pair, odd_outer=odd_outer
    )
    assert result.action.rows == _literal_source_conditioned_rows(
        outer, source_halo, initial_pair, odd_outer
    )


def test_source_conditioned_rejects_outer_guard_before_halo_advance(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    rng = Random(20261030)
    pairs = 2
    source_halo = _random_ring(rng, pairs + 2, 1)
    outer, _ = rooted_finite_depth_trace(source_halo, outer_pairs=pairs, f_steps=1)
    outer = tuple(ring_outer(state, pairs) for state in outer)
    accepted = admitted_outer_port_classes(outer[0], outer[1])
    rejected = next(
        pair for pair in ALL_PAIRS if outer_port_class(outer[0], *pair) not in accepted
    )
    initial_pair = ring_next_pair(source_halo, pairs)
    assert outer_port_class(outer[0], *initial_pair) in accepted

    original = CertifiedHalo.step
    first_step_candidates: set[tuple[int, int]] = set()

    def record_step(halo: CertifiedHalo) -> CertifiedHalo:
        if halo.certified_pairs == source_halo.pairs:
            first_step_candidates.add(ring_next_pair(halo.state, pairs))
        return original(halo)

    monkeypatch.setattr(CertifiedHalo, "step", record_step)
    result = source_conditioned_depth_return(outer, source_halo, initial_pair)
    assert rejected not in first_step_candidates
    assert initial_pair in first_step_candidates
    assert result.pointed_trace
