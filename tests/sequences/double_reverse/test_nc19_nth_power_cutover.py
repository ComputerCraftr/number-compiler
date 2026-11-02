"""Exact source-owned end-to-end nth powering without duplicate full-word actions."""

from __future__ import annotations

import json
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_carry_spacetime import (
    temporal_square_cone,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReversePortAction,
    DoubleReverseTemporalHashlife,
)
from number_compiler.sequences.double_reverse.temporal_seed_morphism import (
    certified_seed_orbit_morphism,
)
from tests.sequences.double_reverse.packet_helpers import (
    integer_field,
    object_mapping,
    string_field,
)


def test_completed_scheduler_image_is_transported_not_repowered(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(168, 256) as term:
        exact_endpoint = term.endpoint_root()
        _entry, source = term.prepare_bank_source(max_prefix=32)

        def forbidden_new_power(
            self: DoubleReverseTemporalHashlife,
            root: int,
            steps: int,
            phase: int,
        ) -> Never:
            raise AssertionError("temporal observer reconstructed a second full word")

        monkeypatch.setattr(
            DoubleReverseTemporalHashlife, "advance_action", forbidden_new_power
        )
        morphism = certified_seed_orbit_morphism(
            source, steps=source.f_steps, completed_term=term
        )
        assert morphism.validate_source_authority().root == source.root
        assert morphism.last.root == exact_endpoint
        assert morphism.last.width == term.source_arena.nodes[exact_endpoint].length
        assert not morphism.all_depth_period_claim


def test_scheduler_transport_rejects_foreign_or_absent_image() -> None:
    with DoubleReverseTerm(168, 64) as left, DoubleReverseTerm(196, 64) as right:
        _entry, source = left.prepare_bank_source(max_prefix=32)
        with pytest.raises(ValueError, match="complete scheduler image"):
            certified_seed_orbit_morphism(
                source, steps=source.f_steps, completed_term=left
            )
        right.endpoint_root()
        with pytest.raises(ValueError, match="cannot transport"):
            certified_seed_orbit_morphism(
                source, steps=source.f_steps, completed_term=right
            )


def test_source_adapter_rejects_valid_action_from_another_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        arena = term.source_arena
        source = term.source_root
        phase = engine.certify(source)
        assert phase is not None
        source_digits = arena.materialize(source)
        foreign_digits = (
            *source_digits[:2],
            (source_digits[2] + 1) % 10,
            *source_digits[3:],
        )
        foreign_root = arena.word(foreign_digits)
        assert engine.certify(foreign_root) == phase
        foreign_action = engine.advance_action(foreign_root, 2, phase)
        original_advance = DoubleReverseTemporalHashlife.advance_action

        def return_foreign_source_action(
            owner: DoubleReverseTemporalHashlife,
            root: int,
            steps: int,
            phase_in: int,
        ) -> DoubleReversePortAction:
            if owner is engine and root == source and steps == 2:
                return foreign_action
            return original_advance(owner, root, steps, phase_in)

        monkeypatch.setattr(
            DoubleReverseTemporalHashlife,
            "advance_action",
            return_foreign_source_action,
        )
        with pytest.raises(ValueError, match="foreign temporal source seam"):
            term.endpoint_root()


def test_semantic_counter_batch_equals_individual_events() -> None:
    from number_compiler.resources.metric_keys import double_reverse as counters

    word = (1, 6, 8, 2) * 16
    results: list[tuple[int, ...]] = []
    measures: list[tuple[int, int, int]] = []
    for batched in (False, True):
        ledger = ResourceLedger()
        arena = LedgerSLPArena(ledger, "nc19-counts", "double_reverse_test")
        owner = ledger.register("nc19-counts-scratch", "workspace")
        visits = [0, 0, 0, 0]  # source, reused, computed, tile pairs

        def record_source_task(_is_node: bool, counts: list[int] = visits) -> None:
            counts[0] += 1

        def record_cone_visit(reused: bool, counts: list[int] = visits) -> None:
            counts[1 if reused else 2] += 1

        def record_tile_pair(counts: list[int] = visits) -> None:
            counts[3] += 1

        try:
            source = arena.word(word)
            result, _stats = temporal_square_cone(
                arena,
                source,
                16,
                scratch_owner=owner,
                on_source_task=None if batched else record_source_task,
                on_cone_visit=None if batched else record_cone_visit,
                on_tile_pair=None if batched else record_tile_pair,
                account_semantic_metrics=batched,
            )
            results.append(arena.materialize(result))
            if batched:
                measures.append(
                    (
                        ledger.counters[
                            counters.DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS
                        ],
                        ledger.counters[counters.DOUBLE_REVERSE_HASHLIFE_CONE_HITS],
                        ledger.counters[counters.DOUBLE_REVERSE_HASHLIFE_CONES],
                    )
                )
            else:
                measures.append((visits[0] + visits[3], visits[1], visits[2]))
            assert all(
                row.entries == 0 and row.nodes == 0
                for row in ledger.inventory()
                if row.owner == owner
            )
        finally:
            arena.dispose()
            ledger.retire_unpublished_owner(owner)
    assert results[0] == results[1]
    assert measures[0] == measures[1]


def test_combined_value_and_observer_uses_one_source_image(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                "64",
                "--info",
                "temporal.seed-morphism",
                "--format",
                "json",
            ],
            shared_cache=False,
        )
        == 0
    )
    raw_packet: object = json.loads(capsys.readouterr().out)
    packet = object_mapping(raw_packet)
    value = int(string_field(packet, "value"))
    x = 168
    for _ in range(64):
        x = 2 * int(str(x)[::-1])
    assert value == x
    info = object_mapping(packet["info"])
    morphism = object_mapping(info["temporal.seed-morphism"])
    endpoint = object_mapping(morphism["endpoint"])
    assert integer_field(endpoint, "width") == len(str(x))


def test_extended_1024_step_packed_diagonal_matches_exact_spacetime() -> None:
    from number_compiler.resources.metric_keys.double_reverse import (
        DOUBLE_REVERSE_HASHLIFE_CONE_HITS,
        DOUBLE_REVERSE_HASHLIFE_CONES,
        DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_EVALUATIONS,
        DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_OPERAND_BITS,
        DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS,
    )
    from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell

    source_word = (1, 6, 8, 2, 3, 7, 9, 0, 5, 4, 2, 9, 1, 8, 0, 6) * 256
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "nc19-4096-halo", "double_reverse_test")
    owner = ledger.register("nc19-4096-halo-scratch", "workspace")
    try:
        root = arena.repeat(arena.word(source_word[:16]), 256)
        output, stats = temporal_square_cone(
            arena, root, 1024, scratch_owner=owner, account_semantic_metrics=True
        )
        expected: tuple[int, ...] = source_word
        for _ in range(1024):
            expected = tuple(
                stencil_cell(expected[i], expected[i + 1], expected[i + 2])
                for i in range(len(expected) - 2)
            )
        assert arena.materialize(output) == expected
        assert stats.packed_row_evaluations == 1024
        assert stats.packed_row_operand_bits > 0
        assert stats.semantic_tiles == 0
        assert stats.temporal_cones == 0
        assert ledger.counters[DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_EVALUATIONS] == 1024
        assert ledger.counters[DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_OPERAND_BITS] == (
            stats.packed_row_operand_bits
        )
        assert ledger.counters[DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS] == (
            stats.source_traversal_tasks
            + stats.packed_row_evaluations
            + stats.packed_output_digit_visits
        )
        assert ledger.counters.get(DOUBLE_REVERSE_HASHLIFE_CONES, 0) == 0
        assert ledger.counters.get(DOUBLE_REVERSE_HASHLIFE_CONE_HITS, 0) == 0
        assert all(
            row.entries == 0 and row.nodes == 0
            for row in ledger.inventory()
            if row.owner == owner
        )
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(owner)
