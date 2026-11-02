"""Exact bounded temporal squaring of the normalized 2rev10 stencil."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from random import Random

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.double_reverse import (
    temporal_carry_spacetime as temporal_carry_spacetime_module,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell
from number_compiler.sequences.double_reverse.temporal_carry_spacetime import (
    TemporalSquarePublicationFailed,
    TemporalSquareScratchCapacityRefused,
    temporal_square_cone,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
)


def _replay(source: tuple[int, ...], steps: int) -> tuple[int, ...]:
    current = source
    for _ in range(steps):
        current = tuple(
            stencil_cell(current[index], current[index + 1], current[index + 2])
            for index in range(len(current) - 2)
        )
    return current


def _arena_and_scratch() -> tuple[ResourceLedger, LedgerSLPArena, int]:
    # Match the ordinary unbounded term owner. Capacity behavior is covered by
    # a separate test with an intentionally tight request-local ledger.
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "nc19-temporal-cone", "double_reverse_test")
    scratch_owner = ledger.register("nc19-temporal-cone-scratch", "workspace")
    return ledger, arena, scratch_owner


def _assert_released(ledger: ResourceLedger, scratch_owner: int) -> None:
    scratch = next(
        account for account in ledger.inventory() if account.owner == scratch_owner
    )
    assert scratch.entries == 0
    assert scratch.nodes == 0


def _assert_failure_traceback_has_no_semantic_graph(error: BaseException) -> None:
    """Check that retained tracebacks do not keep the large temporary DAG."""
    trace = error.__traceback__
    power = None
    while trace is not None:
        candidate = trace.tb_frame.f_locals.get("power")
        if type(candidate).__name__ == "_CarrySpacetimePower":
            power = candidate
        trace = trace.tb_next
    if power is None:
        # Constructor admission can refuse before the semantic arena exists.
        return
    assert object.__getattribute__(power, "_tiles") == []
    assert object.__getattribute__(power, "_intern") == {}
    assert object.__getattribute__(power, "_powers") == {}


@pytest.mark.parametrize("steps", (1, 2, 4, 8, 32, 128, 512))
def test_temporal_square_matches_independent_stencil_replay(steps: int) -> None:
    random = Random(0xAC19 + steps)
    source = tuple(random.randrange(10) for _ in range(4 * steps))
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.word(source)
        actual_root, stats = temporal_square_cone(
            arena, source_root, steps, scratch_owner=scratch_owner
        )
        assert arena.materialize(actual_root) == _replay(source, steps)
        assert arena.nodes[actual_root].length == 2 * steps
        if steps >= 64:
            assert stats.packed_row_evaluations == steps
            assert stats.packed_row_operand_bits > 0
            assert stats.packed_output_digit_visits == 6 * steps
            assert stats.temporal_cones == 0
            assert stats.semantic_tiles == 0
        else:
            assert stats.temporal_cones > 0
            assert stats.semantic_tiles >= 10
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_equal_content_with_different_slp_shapes_has_equal_powered_output() -> None:
    source = (1, 6, 8, 2) * 16
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        literal_root = arena.word(source)
        block_root = arena.repeat(arena.word((1, 6, 8, 2)), 16)
        literal_output, _ = temporal_square_cone(
            arena, literal_root, 16, scratch_owner=scratch_owner
        )
        block_output, _ = temporal_square_cone(
            arena, block_root, 16, scratch_owner=scratch_owner
        )
        expected = _replay(source, 16)
        assert arena.materialize(literal_output) == expected
        assert arena.materialize(block_output) == expected
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_packed_diagonal_preserves_reversed_source_orientation() -> None:
    # This asymmetric word catches a nibble-direction swap: the packed source
    # is read high digit first, while its planes are indexed from the low end.
    source = (9, 1, 7, 2, 8, 0, 3, 6) * 32
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.word(source)
        actual_root, stats = temporal_square_cone(
            arena, source_root, 64, scratch_owner=scratch_owner
        )
        assert arena.materialize(actual_root) == _replay(source, 64)
        assert stats.packed_row_evaluations == 64
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_source_traversal_is_bounded_and_scratch_is_released_on_refusal() -> None:
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.word((2, 8, 8, 2) * 128)
        before_nodes = len(arena.nodes)
        ledger.tighten_limits(
            max_nodes=ledger.nodes + 5,
            max_cache_entries=ledger.entries + 5,
        )
        with pytest.raises(TemporalSquareScratchCapacityRefused) as raised:
            temporal_square_cone(arena, source_root, 128, scratch_owner=scratch_owner)
        _assert_failure_traceback_has_no_semantic_graph(raised.value)
        assert len(arena.nodes) == before_nodes
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_packed_capacity_miss_falls_back_to_the_semantic_cone() -> None:
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.repeat(arena.terminal(0), 256)
        ledger.tighten_limits(
            max_nodes=ledger.nodes + 447,
            max_cache_entries=ledger.entries + 447,
        )
        output_root, stats = temporal_square_cone(
            arena,
            source_root,
            64,
            scratch_owner=scratch_owner,
            account_semantic_metrics=True,
        )
        assert arena.materialize(output_root) == (0,) * 128
        assert stats.temporal_cones > 0
        assert stats.packed_row_evaluations == 0
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_packed_publication_failure_is_not_reclassified_as_a_capacity_miss(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.repeat(arena.word((1, 6, 8, 2)), 64)
        checkpoint = len(arena.nodes)
        original_word = LedgerSLPArena.word

        def publish_then_refuse(owner: LedgerSLPArena, word: Sequence[int]) -> int:
            original_word(owner, word)
            raise TemporalSquareScratchCapacityRefused(
                "injected refusal after packed output publication"
            )

        monkeypatch.setattr(LedgerSLPArena, "word", publish_then_refuse)
        with pytest.raises(
            TemporalSquarePublicationFailed,
            match="publishing packed output",
        ):
            temporal_square_cone(arena, source_root, 64, scratch_owner=scratch_owner)
        assert len(arena.nodes) == checkpoint
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


@pytest.mark.parametrize("steps", (8, 64))
def test_metric_failure_rolls_back_unconsumed_temporal_output(
    monkeypatch: pytest.MonkeyPatch, steps: int
) -> None:
    from number_compiler.resources.metric_keys import double_reverse as keys

    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source = tuple((index * 7 + 3) % 10 for index in range(4 * steps))
        source_root = arena.word(source)
        node_checkpoint = len(arena.nodes)
        original_bump = ledger.bump
        failed = False
        fail_key = (
            keys.DOUBLE_REVERSE_HASHLIFE_CONES
            if steps < 64
            else keys.DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_EVALUATIONS
        )

        def fail_after_publication(name: str, amount: int = 1) -> None:
            nonlocal failed
            if name == fail_key and not failed:
                failed = True
                raise RuntimeError("injected temporal metric failure")
            original_bump(name, amount)

        monkeypatch.setattr(ledger, "bump", fail_after_publication)
        with pytest.raises(RuntimeError, match="injected temporal metric failure"):
            temporal_square_cone(
                arena,
                source_root,
                steps,
                scratch_owner=scratch_owner,
                account_semantic_metrics=True,
            )
        assert failed
        assert len(arena.nodes) == node_checkpoint
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_malformed_source_is_not_reclassified_as_capacity_refusal() -> None:
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.word((1, 2, 10, 3))
        with pytest.raises(ValueError, match="nondecimal") as raised:
            temporal_square_cone(arena, source_root, 1, scratch_owner=scratch_owner)
        assert not isinstance(raised.value, BlockContextBudgetExceeded)
        _assert_failure_traceback_has_no_semantic_graph(raised.value)
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_output_publication_failure_rolls_back_nodes_and_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    random = Random(0xC019)
    source = tuple(random.randrange(10) for _ in range(8))
    ledger, arena, scratch_owner = _arena_and_scratch()
    try:
        source_root = arena.word(source)
        checkpoint = len(arena.nodes)
        original_concat = LedgerSLPArena.concat
        appended = False

        def fail_after_first_output_node(
            owner: LedgerSLPArena, left: int, right: int
        ) -> int:
            nonlocal appended
            previous_size = len(owner.nodes)
            result = original_concat(owner, left, right)
            if len(owner.nodes) > previous_size and not appended:
                appended = True
                raise BlockContextBudgetExceeded("injected output publication failure")
            return result

        monkeypatch.setattr(LedgerSLPArena, "concat", fail_after_first_output_node)
        with pytest.raises(
            BlockContextBudgetExceeded, match="injected output publication failure"
        ) as raised:
            temporal_square_cone(arena, source_root, 2, scratch_owner=scratch_owner)
        _assert_failure_traceback_has_no_semantic_graph(raised.value)
        assert appended
        assert len(arena.nodes) == checkpoint
        _assert_released(ledger, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def test_cone_memo_publication_failure_rolls_back_completed_cone(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        ledger = term.resource_ledger
        source = term.source_root
        phase = engine.certify(source)
        assert phase is not None
        cone_owner = next(
            owner.owner
            for owner in ledger.inventory()
            if owner.name.endswith("-temporal-cones")
        )
        scratch_owner = next(
            owner
            for owner in ledger.inventory()
            if owner.role == "double_reverse_workspace"
        ).owner
        original_setitem = OwnedMemo[object, object].__setitem__
        original_rollback = LedgerSLPArena.rollback_unpublished_suffix
        failed = False
        rolled_back: list[int] = []

        def fail_cone_insert(
            memo: OwnedMemo[object, object], key: object, value: object
        ) -> None:
            nonlocal failed
            if memo.owner == cone_owner:
                failed = True
                raise RuntimeError("injected cone memo publication failure")
            original_setitem(memo, key, value)

        def record_rollback(
            arena: LedgerSLPArena,
            first_new_node: int,
            *,
            before_remove: Callable[[int], None] | None = None,
        ) -> None:
            previous_size = len(arena.nodes)
            original_rollback(
                arena,
                first_new_node,
                before_remove=before_remove,
            )
            rolled_back.append(previous_size - len(arena.nodes))

        monkeypatch.setattr(OwnedMemo, "__setitem__", fail_cone_insert)
        monkeypatch.setattr(
            LedgerSLPArena, "rollback_unpublished_suffix", record_rollback
        )
        with pytest.raises(
            RuntimeError, match="injected cone memo publication failure"
        ):
            engine.advance_action(source, 2, phase)
        assert failed
        assert rolled_back and rolled_back[0] > 0
        assert (
            next(
                owner for owner in ledger.inventory() if owner.owner == cone_owner
            ).entries
            == 0
        )
        scratch = next(
            owner for owner in ledger.inventory() if owner.owner == scratch_owner
        )
        assert scratch.entries == 0
        assert scratch.nodes == 0


def test_warm_issued_parent_skips_temporal_square_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 16) as term:
        engine = term.temporal_engine
        source = term.source_root
        phase = engine.certify(source)
        assert phase is not None
        issued = engine.advance_action(source, 8, phase)

        def forbid_temporal_square(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("warm parent attempted temporal cone discovery")

        monkeypatch.setattr(
            temporal_carry_spacetime_module,
            "temporal_square_cone",
            forbid_temporal_square,
        )
        monkeypatch.setattr(
            DoubleReverseTemporalHashlife,
            "_power_of_two",
            forbid_temporal_square,
        )
        assert engine.advance_action(source, 8, phase) is issued


def test_production_endpoint_consumes_temporally_squared_cones() -> None:
    from number_compiler.resources.metric_keys.double_reverse import (
        DOUBLE_REVERSE_HASHLIFE_CONES,
        DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_EVALUATIONS,
        DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS,
    )

    seed = 196
    physical_steps = 1056
    expected = seed
    for _ in range(physical_steps):
        expected = 2 * int(str(expected)[::-1])

    with DoubleReverseTerm(seed, physical_steps, max_state_bits=4096) as term:
        term.prepare_endpoint()
        assert term.materialize(max_bits=4096) == expected
        counters = term.metrics()
        assert (
            counters[DOUBLE_REVERSE_HASHLIFE_CONES] > 0
            or counters[DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_EVALUATIONS] > 0
        )
        assert counters[DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS] > 0
