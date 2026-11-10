"""Finite depth transfer keeps one real 2rev10 source halo correlated."""

from __future__ import annotations

from typing import Never, cast

import pytest

from number_compiler.sequences.double_reverse import temporal_certified_halo
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_bound_bank import source_suffix
from number_compiler.sequences.double_reverse.temporal_birth_ring import (
    BirthRingPorts,
    BirthRingState,
    odd_boundary_pairs,
)
from number_compiler.sequences.double_reverse.temporal_certified_halo import (
    advance_halo_without_frames,
)
from number_compiler.sequences.double_reverse.temporal_depth_transfer_matrix import (
    CertifiedHalo,
    SourceConditionedDepthWindow,
    conditional_depth_return,
    rooted_finite_depth_trace,
    source_conditioned_depth_return,
    source_conditioned_depth_window,
    source_conditioned_depth_window_packet,
    source_issued_root_path,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReversePortAction,
)
from tests.support.reverse_add_source_data import double_reverse_orbit


def _orbit(seed: int, steps: int) -> tuple[str, ...]:
    return tuple(map(str, double_reverse_orbit(seed, steps)))


def _ring(word: str, pairs: int, phase: int) -> BirthRingState:
    return BirthRingState(
        tuple(map(int, word[:pairs])), tuple(map(int, word[-pairs:])), phase
    )


def _pair(word: str, position: int) -> tuple[int, int]:
    return int(word[position]), int(word[-1 - position])


def _phase(word: str) -> int:
    high, low = word[:2], word[-2:]
    if high == "17":
        if low == "42":
            return 1
        if low in ("68", "88"):
            return 0
    if high in ("48", "49"):
        if low == "42":
            return 2
        if low in ("68", "88"):
            return 3
    raise AssertionError((high, low))


def test_fast_halo_stencil_matches_canonical_ring_step() -> None:
    from random import Random

    rng = Random(20261017)
    for size in (1, 2, 4, 7):
        for phase in range(4):
            for _ in range(20):
                state = BirthRingState(
                    tuple(rng.randrange(10) for _ in range(size)),
                    tuple(rng.randrange(10) for _ in range(size)),
                    phase,
                )
                expected = state.advance(BirthRingPorts(0, 0))[0]
                assert advance_halo_without_frames(state) == expected


def test_certified_halo_discards_uncertified_inward_successors() -> None:
    words = _orbit(196, 818)
    initial = _ring(words[800], 8, _phase(words[800]))
    current = CertifiedHalo(initial, initial.pairs)
    for _ in range(6):
        current = current.step()

    authentic = _ring(words[812], 8, _phase(words[812]))
    assert current.certified_pairs == 2
    assert current.state.pairs == 2
    assert current.outer(2) == _ring(words[812], 2, _phase(words[812]))
    with pytest.raises(ValueError, match="not source-certified"):
        current.outer(3)
    replenished = current.refill(authentic)
    assert replenished.certified_pairs == 8
    assert replenished.outer(8) == authentic

    forged = BirthRingState((9, *authentic.left[1:]), authentic.right, authentic.phase)
    with pytest.raises(ArithmeticError, match="disagrees"):
        current.refill(forged)
    wrong_phase = BirthRingState(
        authentic.left, authentic.right, (authentic.phase + 1) % 4
    )
    with pytest.raises(ValueError, match="incompatible"):
        current.refill(wrong_phase)


def test_source_conditioned_matrix_removes_a_fresh_inlet_branch() -> None:
    words = _orbit(196, 820)
    first_index, pairs, period = 800, 1, 4
    phase = _phase(words[first_index])
    outer = tuple(
        _ring(
            words[first_index + 2 * tick], pairs, _phase(words[first_index + 2 * tick])
        )
        for tick in range(period // 2 + 1)
    )
    assert outer[0] == outer[-1]
    initial = _pair(words[first_index], pairs)
    independent = conditional_depth_return(outer)
    assert set(independent.pointed_returns(initial)) == {(7, 6), (7, 8)}

    steps = len(outer) - 1
    halo = _ring(words[first_index], pairs + 1 + steps, phase)
    odd_guard = tuple(
        tuple(_pair(words[first_index + 2 * tick + 1], j) for j in range(pairs))
        for tick in range(steps)
    )
    correlated = source_conditioned_depth_return(
        outer, halo, initial, odd_outer=odd_guard
    )
    assert correlated.pointed_endpoint(initial) == (7, 8)
    assert correlated.action.maximum_successors == 1
    assert correlated.infinite_period_certified is False
    assert not hasattr(correlated, "power")


def test_rooted_trace_uses_one_halo_across_multiple_conditional_cycles() -> None:
    words = _orbit(196, 820)
    start, pairs, one_period_steps, copies = 800, 1, 2, 3
    halo = _ring(
        words[start], pairs + 1 + one_period_steps * copies, _phase(words[start])
    )
    states, odd = rooted_finite_depth_trace(
        halo, outer_pairs=pairs, f_steps=one_period_steps * copies
    )
    path = tuple((state.left[pairs], state.right[0]) for state in states)
    for tick, state in enumerate(states):
        word = words[start + 2 * tick]
        assert state.left == tuple(map(int, word[: pairs + 1]))
        assert state.right == tuple(map(int, word[-(pairs + 1) :]))
    assert tuple(path[i * one_period_steps] for i in range(copies + 1)) == (
        (7, 6),
        (7, 8),
        (7, 8),
        (7, 6),
    )
    for tick, row in enumerate(odd):
        assert row == tuple(
            _pair(words[start + 2 * tick + 1], j) for j in range(pairs + 1)
        )
        source = _ring(
            words[start + 2 * tick], pairs + 1, _phase(words[start + 2 * tick])
        )
        inlet = BirthRingPorts(
            int(words[start + 2 * tick][pairs + 1]),
            int(words[start + 2 * tick][-(pairs + 2)]),
        )
        assert row == odd_boundary_pairs(source, inlet)


def test_source_correlated_transfer_refuses_an_incomplete_halo() -> None:
    outer = (BirthRingState((1,), (8,), 0), BirthRingState((1,), (8,), 2))
    too_short = BirthRingState((1, 7), (7, 8), 0)
    with pytest.raises(ValueError, match="incomplete or inconsistent"):
        source_conditioned_depth_return(outer, too_short, (7, 7))
    with pytest.raises(ValueError, match=r"K\+1\+duration"):
        rooted_finite_depth_trace(too_short, outer_pairs=1, f_steps=2)


def test_prepared_source_depth_matrix_is_a_finite_exact_window(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 128, max_state_bits=16384) as term:
        # Seed 196 is admitted only once its source cylinder has a 16-digit
        # physical prefix; preserve the actual authority bound here.
        _, source = term.prepare_bank_source(max_prefix=16)
        # Use the last four certified F steps so the genuine source has
        # reached the width needed by the 12-digit causal halo.
        steps = 4
        assert source.f_steps >= steps
        start = source.f_steps - steps
        ledger = source.ledger
        before_entries, before_nodes = ledger.entries, ledger.nodes
        live_reservations: list[tuple[int, int]] = []
        original_to_packet = SourceConditionedDepthWindow.to_packet
        original_pointed_window = DoubleReverseTemporalHashlife.pointed_window
        pointed_reads = 0

        def count_pointed_window(
            engine: DoubleReverseTemporalHashlife,
            root: int,
            f_steps: int,
            phase: int,
            start: int,
            count: int,
        ) -> tuple[int, ...]:
            nonlocal pointed_reads
            pointed_reads += 1
            return original_pointed_window(engine, root, f_steps, phase, start, count)

        def prohibit_refill_replay(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("one authenticated halo must supply both packets")

        monkeypatch.setattr(
            DoubleReverseTemporalHashlife, "pointed_window", count_pointed_window
        )
        monkeypatch.setattr(
            temporal_certified_halo,
            "build_source_continued_halo_trace",
            prohibit_refill_replay,
        )

        def assert_released(reservations: list[tuple[int, int]]) -> None:
            assert len(reservations) == 1
            assert ledger.entries == reservations[0][0] - 1024
            assert ledger.nodes == reservations[0][1] - 1024

        def checked_to_packet(
            window: SourceConditionedDepthWindow,
        ) -> dict[str, object]:
            live_reservations.append((ledger.entries, ledger.nodes))
            assert ledger.entries >= before_entries + 1024
            assert ledger.nodes >= before_nodes + 1024
            assert not hasattr(window, "power")
            return original_to_packet(window)

        monkeypatch.setattr(
            SourceConditionedDepthWindow, "to_packet", checked_to_packet
        )
        packet = source_conditioned_depth_window_packet(
            source,
            outer_pairs=1,
            start_f_steps=start,
            f_steps=steps,
        )
        assert pointed_reads == 2
        assert_released(live_reservations)
        assert packet["status"] == "available"
        assert packet["f_steps"] == steps
        assert packet["physical_duration"] == 2 * steps
        assert packet["infinite_period_certified"] is False
        assert packet["relation_semantics"] == "exact_fixed_halo_finite_relation"
        assert packet["source_root_assignment_joined"] is True
        start_generation = packet["start_generation"]
        assert isinstance(start_generation, int)
        continuation = packet["source_backed_continuation"]
        assert isinstance(continuation, dict)
        assert continuation["mode"] == "finite_source_backed_certified_halo"
        assert continuation["f_steps"] == steps
        assert continuation["physical_interval"] == [
            start_generation,
            start_generation + 2 * steps,
        ]
        assert continuation["refill_offsets_f_steps"] == []
        assert continuation["source_refill_count"] == 0
        assert continuation["halo_construction"] == "single_source_halo"
        assert continuation["block_f_steps"] == steps
        assert continuation["overlap_verified_on_every_refill"] is True
        assert continuation["minimum_certified_pairs"] == 2
        assert continuation["maximum_halo_pairs"] == 2 + steps
        assert continuation["infinite_period_certified"] is False
        transition_rows = packet["transition_rows"]
        assert isinstance(transition_rows, list)
        assert len(cast(list[object], transition_rows)) == 100

        source_words = _orbit(196, start_generation + 2 * steps)
        expected_trace = tuple(
            _pair(source_words[start_generation + 2 * tick], 1)
            for tick in range(steps + 1)
        )
        pointed_trace = packet["pointed_trace"]
        assert isinstance(pointed_trace, list)
        assert pointed_trace == [list(pair) for pair in expected_trace]

        failed_publication_reservations: list[tuple[int, int]] = []

        def fail_to_packet(
            _window: SourceConditionedDepthWindow,
        ) -> dict[str, object]:
            failed_publication_reservations.append((ledger.entries, ledger.nodes))
            assert ledger.entries >= before_entries + 1024
            assert ledger.nodes >= before_nodes + 1024
            raise ValueError("injected stale-authority publication failure")

        monkeypatch.setattr(SourceConditionedDepthWindow, "to_packet", fail_to_packet)
        with pytest.raises(ValueError, match="injected stale-authority") as failure:
            source_conditioned_depth_window_packet(
                source,
                outer_pairs=1,
                start_f_steps=start,
                f_steps=steps,
            )
        assert type(failure.value) is ValueError
        assert pointed_reads == 4
        assert_released(failed_publication_reservations)


def test_issued_adjacent_roots_supply_depth_halo_without_reopening_cones(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 128, max_state_bits=16384) as term:
        _, source = term.prepare_bank_source(max_prefix=16)
        source = source_suffix(source, 4)
        baseline = source_conditioned_depth_window(
            source, outer_pairs=1, start_f_steps=0, f_steps=4
        )

        root = source.root
        phase = source.phase
        actions: list[DoubleReversePortAction] = []
        for _ in range(source.f_steps):
            action = source.engine.advance_action(root, 1, phase)
            actions.append(action)
            root = source.engine.root_of(action.target)
            phase = action.phase_out
        issued = source_issued_root_path(source, tuple(actions))
        window_path = issued.windows(source, ((0, 4),))[0]

        nonadjacent = source.engine.advance_action(source.root, 2, source.phase)
        with pytest.raises(ValueError, match="nonadjacent"):
            source_issued_root_path(source, (nonadjacent,))

        def forbid_reopening(*_args: object, **_kwargs: object) -> tuple[int, ...]:
            raise AssertionError("issued adjacent roots already contain this halo")

        monkeypatch.setattr(
            DoubleReverseTemporalHashlife, "pointed_window", forbid_reopening
        )
        reused = source_conditioned_depth_window(
            source,
            outer_pairs=1,
            start_f_steps=0,
            f_steps=4,
            issued_path=window_path,
        )

        assert reused.source_halo == baseline.source_halo
        assert reused.initial_pair == baseline.initial_pair
        assert reused.outer_trace == baseline.outer_trace
        assert reused.odd_outer == baseline.odd_outer
        assert reused.transfer.pointed_trace == baseline.transfer.pointed_trace
        assert reused.transfer.action.rows == baseline.transfer.action.rows
