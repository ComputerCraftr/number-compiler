"""Exact packed 2rev10 windows and finite action-relative carry words."""

from __future__ import annotations

from itertools import product

import pytest

from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell
from number_compiler.sequences.double_reverse.temporal_digit_affine import (
    DigitCarryAffine,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_packed_ring import (
    RingWindowRequest,
    _certified_periodic_motif,
    _digits_to_masks,
    _mask_digit,
    _periodic_evolve,
    _two_step_row,
    _window_geometry,
    pointed_ring_windows,
)


def test_all_decimal_stencil_triples_match_packed_t2() -> None:
    for left, center, right in product(range(10), repeat=3):
        masks = _digits_to_masks(bytearray((left, center, right)))
        output, _, _ = _two_step_row(masks, 3)
        assert _mask_digit(output, 0) == stencil_cell(left, center, right)


def test_affine_composition_tracks_action_relative_phases() -> None:
    first = DigitCarryAffine.two_step(1, 0)
    second = DigitCarryAffine.two_step(0, 1)
    combined = first.then(second)
    assert combined.physical_ticks == 4
    assert combined.phase_counts == (1, 0, 0, 1)
    assert combined.offset == (3 * 1 + 4 * 0 + 2 * 0 + 1) % 5
    for residue in range(5):
        assert combined.apply(residue) == second.apply(first.apply(residue))


@pytest.mark.parametrize(("seed", "generation"), ((1, 32), (139, 66), (196, 32)))
def test_packed_paired_windows_match_exact_pointed_windows(
    seed: int, generation: int
) -> None:
    with DoubleReverseTerm(seed, generation, max_state_bits=16384) as term:
        if seed == 139:
            # Seed 139 has no admitted prefix in the historical 32-tick
            # window. Its independently certified entry is generation 34;
            # admit exactly that source before testing its remaining 16 F steps.
            term._adapter.temporal_hashlife.admit_extended_prefix(34)
            entry = term._certified_prefix_entry(
                max_prefix=34, require_even_remainder=True
            )
            assert entry.physical_steps == 34
            root, phase, steps, width = term._pointed_shape(entry)
            source = term._pointed_bank_source(entry, root, phase, steps, width)
        else:
            _, source = term._prepare_bank_source(max_prefix=32)
        engine = source.engine
        phase = source.phase
        root = source.root
        assert engine.certify(root) == phase
        for steps in (1, 2, 8, 16):
            width = source.width_in + sum(growth_ports(phase, steps))
            if width < 10:
                continue
            paired = (
                RingWindowRequest(0, 7, (0, 6)),
                RingWindowRequest(1, 7, (0, 6)),
            )
            results = pointed_ring_windows(engine, root, steps, phase, paired)
            for request, result in zip(paired, results, strict=True):
                expected = engine.pointed_window(
                    root, steps, phase, request.start, request.count
                )
                assert result.digits == expected
                for action in result.actions:
                    assert action.action.physical_ticks == 2 * steps
                    assert action.result_digit == expected[action.position]
                    assert action.action.apply(action.initial_digit % 5) == (
                        action.result_digit % 5
                    )


def test_packed_merge_accepts_odd_and_even_causal_spans() -> None:
    with DoubleReverseTerm(196, 32, max_state_bits=16384) as term:
        _, source = term._prepare_bank_source(max_prefix=32)
        engine = source.engine
        root = source.root
        phase = source.phase
        for requests in (
            (RingWindowRequest(0, 7, (0,)), RingWindowRequest(1, 7, (6,))),
            (RingWindowRequest(0, 7, (0,)), RingWindowRequest(0, 8, (7,))),
        ):
            results = pointed_ring_windows(engine, root, 4, phase, requests)
            for request, result in zip(requests, results, strict=True):
                assert result.digits == engine.pointed_window(
                    root, 4, phase, request.start, request.count
                )


def test_far_disjoint_windows_read_only_their_source_intervals_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 32, max_state_bits=16384) as term:
        _, source = term._prepare_bank_source(max_prefix=32)
        engine = source.engine
        # Use a later admitted endpoint: the bank-entry source itself is too
        # narrow for two independent causal windows near opposite borders.
        root = engine.advance(source.root, 128, source.phase)
        phase = engine.certify(root)
        assert phase is not None
        steps = 4
        source_width = engine.arena.nodes[root].length
        left_births, right_births = growth_ports(phase, steps)
        output_width = source_width + left_births + right_births
        requests = (
            RingWindowRequest(2, 1, (0,)),
            RingWindowRequest(output_width - 3, 1, (0,)),
        )
        expected_digits = tuple(
            engine.pointed_window(root, steps, phase, request.start, request.count)
            for request in requests
        )
        geometries = tuple(
            _window_geometry(steps, phase, request) for request in requests
        )
        ordered = tuple(sorted(geometries))
        assert ordered[0][1] < ordered[1][0]
        expected_source_slices = tuple(
            (max(0, begin), min(source_width, end))
            for begin, end in ordered
            if max(0, begin) < min(source_width, end)
        )
        assert len(expected_source_slices) == 2

        window_cones: list[tuple[int, int]] = []
        source_slices: list[tuple[int, int]] = []
        original_window = DoubleReverseTemporalHashlife._pointed_source_window
        original_part = DoubleReverseTemporalHashlife.part

        def capture_window(
            receiver: DoubleReverseTemporalHashlife,
            source_root: int,
            origin: int,
            radius: int,
        ) -> int:
            window_cones.append((origin - radius, origin + radius + 1))
            return original_window(receiver, source_root, origin, radius)

        def capture_part(
            receiver: DoubleReverseTemporalHashlife,
            source_root: int,
            begin: int,
            end: int,
        ) -> int:
            if source_root == root:
                source_slices.append((begin, end))
            return original_part(receiver, source_root, begin, end)

        monkeypatch.setattr(
            DoubleReverseTemporalHashlife, "_pointed_source_window", capture_window
        )
        monkeypatch.setattr(DoubleReverseTemporalHashlife, "part", capture_part)
        actual = pointed_ring_windows(engine, root, steps, phase, requests)

        assert tuple(result.digits for result in actual) == expected_digits
        assert tuple(window_cones) == ordered
        assert tuple(source_slices) == expected_source_slices


def test_periodic_shortcut_requires_the_complete_causal_slp() -> None:
    with DoubleReverseTerm(196, 32, max_state_bits=16384) as term:
        engine = term._adapter.temporal_hashlife
        motif = (1, 2, 3)
        repeated = engine.arena.repeat(engine.arena.word(motif), 40)

        for max_states in (0, 1):
            scratch_before = engine.ledger.inventory_owner(engine.scratch_owner)
            assert (
                _certified_periodic_motif(engine, repeated, max_states=max_states)
                is None
            )
            scratch_after = engine.ledger.inventory_owner(engine.scratch_owner)
            assert (scratch_after.entries, scratch_after.nodes) == (
                scratch_before.entries,
                scratch_before.nodes,
            )

        assert _certified_periodic_motif(engine, repeated) == motif

        edited = engine.arena.concat(
            engine.arena.concat(
                engine.arena.repeat(engine.arena.word(motif), 20),
                engine.arena.terminal(4),
            ),
            engine.arena.repeat(engine.arena.word(motif), 20),
        )
        assert _certified_periodic_motif(engine, edited) is None


def test_certified_periodic_evolution_matches_literal_ring_steps() -> None:
    with DoubleReverseTerm(196, 32, max_state_bits=16384) as term:
        engine = term._adapter.temporal_hashlife
        for motif in ((1,), (1, 4), (1, 2, 3), (1, 4, 7, 2)):
            for steps in (1, 2, 7, 64):
                evolved = _periodic_evolve(engine, motif, steps, (0,))
                assert evolved is not None
                result, actions = evolved
                row: tuple[int, ...] = motif
                for _ in range(steps):
                    row = tuple(
                        stencil_cell(
                            row[index],
                            row[(index + 1) % len(row)],
                            row[(index + 2) % len(row)],
                        )
                        for index in range(len(row))
                    )
                assert result == row
                action = actions[0]
                assert action.action.apply(action.initial_digit % 5) == (
                    action.result_digit % 5
                )
