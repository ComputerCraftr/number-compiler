from __future__ import annotations

import sys
from collections.abc import Hashable
from dataclasses import replace

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.projections.decimal_reversal import matches_bounded_query
from number_compiler.api.query_types import FiveReverseTermQuery
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedPhaseCoordinate,
    OrderedSourceCoverage,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.sequences.five_reverse import source_window as source_window_module
from number_compiler.sequences.five_reverse.ports import (
    FiveBorderPort,
    FiveCarryPort,
    FiveSourceTransfer,
)
from number_compiler.sequences.five_reverse.source_adapter import (
    FiveReverseAction,
    FiveReverseSource,
    FiveReverseSourceAdapter,
)
from number_compiler.sequences.five_reverse.source_window import FiveFiniteSourceWindow
from number_compiler.sequences.five_reverse.term import FiveReverseTerm
from tests.support.private_attributes import private_test_attribute


def _scratch_owner(term: FiveReverseTerm) -> int:
    matches = tuple(
        account
        for account in term.resource_ledger.inventory()
        if account.name == "five-reversal-scratch"
    )
    assert len(matches) == 1
    return matches[0].owner


def test_five_reverse_recurrence_uses_decimal_reversal_before_factor_five() -> None:
    assert FiveReverseTerm(1, 1).materialize(max_bits=8) == 5
    assert FiveReverseTerm(196, 1).materialize(max_bits=16) == 3455


def test_five_reverse_exact_fallback_respects_python_decimal_limit() -> None:
    limit = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640)
        source = 10**699 + 2
        with FiveReverseTerm(source, 1, max_state_bits=2400) as term:
            assert term.step_value(source) == 5 * (2 * 10**699 + 1)
    finally:
        sys.set_int_max_str_digits(limit)


def test_five_reverse_preserves_tight_scratch_budget() -> None:
    with FiveReverseTerm(512, 0) as term:
        ledger = term.resource_ledger
        ledger.tighten_limits(ledger.nodes + 8, ledger.entries + 8)
        assert term.step_value(512) == 1075


def test_five_reverse_small_exact_state_budget_is_not_rejected_by_a_loose_bound() -> (
    None
):
    assert FiveReverseTerm(1, 1, max_state_bits=3).materialize(max_bits=3) == 5
    with pytest.raises(BlockContextBudgetExceeded):
        FiveReverseTerm(1, 1, max_state_bits=2).materialize(max_bits=2)


def test_five_reverse_finite_exact_port_transfer_and_trace() -> None:
    term = FiveReverseTerm(1, 0, max_steps=2)
    packet = term.source_transfer(2, trace=True)
    assert type(packet) is FiveSourceTransfer
    assert packet.steps == 2
    assert isinstance(packet.initial_port, FiveBorderPort)
    assert packet.initial_port.decimal_width == 1
    assert len(packet.trace) == 2
    assert isinstance(packet.trace[0].source, FiveBorderPort)
    assert isinstance(packet.trace[0].target, FiveBorderPort)
    assert isinstance(packet.trace[1].source, FiveBorderPort)
    assert isinstance(packet.trace[1].target, FiveBorderPort)
    assert packet.trace[0].source.low_digits == (1,)
    assert packet.trace[0].target.low_digits == (5,)
    assert packet.trace[1].source.low_digits == (5,)
    assert packet.trace[1].target.low_digits == (5, 2)
    assert isinstance(packet.terminal_port, FiveBorderPort)
    assert packet.terminal_port.decimal_width == 2
    assert packet.physical_repeat_certified is False
    assert packet.future_repetition_claimed is False


def test_five_reverse_transfer_cannot_reset_the_query_step_budget() -> None:
    term = FiveReverseTerm(1, 1, max_steps=1)
    with pytest.raises(BlockContextBudgetExceeded):
        term.source_transfer(1)


def test_seed_196_uses_only_the_four_stage_guarded_window() -> None:
    term = FiveReverseTerm(196, 180, max_steps=184)
    packet = term.source_transfer(4, trace=True)
    assert packet.source_coverage == "guarded-four-stage-source-window"
    assert isinstance(packet.initial_port, FiveCarryPort)
    assert isinstance(packet.terminal_port, FiveCarryPort)
    assert (packet.initial_port.head3, packet.initial_port.tail3) == (348, 960)
    assert (packet.terminal_port.head3, packet.terminal_port.tail3) == (311, 260)
    assert packet.pascal_innovation() == (4, 0, 4, 2)
    assert tuple(
        (row.source.head3, row.source.tail3, row.target.head3, row.target.tail3)
        for row in packet.trace
        if isinstance(row.source, FiveCarryPort)
        and isinstance(row.target, FiveCarryPort)
    ) == (
        (348, 960, 348, 215),
        (348, 215, 256, 215),
        (256, 215, 256, 260),
        (256, 260, 311, 260),
    )
    with pytest.raises(BlockContextBudgetExceeded, match="remaining step budget"):
        FiveReverseTerm(196, 184, max_steps=184).source_transfer(1)


def test_seed_196_window_rejects_mutated_singleton_authority() -> None:
    window = source_window_module.SEED196_SOURCE_WINDOW
    original_borders = window.borders
    object.__setattr__(
        window, "borders", ((348, 960), (348, 216), *original_borders[2:])
    )
    try:
        with FiveReverseTerm(196, 180, max_steps=180) as term:
            with pytest.raises(ValueError, match="authority seal"):
                term.source_transfer(0)
    finally:
        object.__setattr__(window, "borders", original_borders)


def test_seed_196_cursor_revalidates_stage_type_and_incoming_growth() -> None:
    with FiveReverseTerm(196, 180, max_steps=184) as term:
        port = term.source_transfer(0).initial_port
        assert isinstance(port, FiveCarryPort)
        cursor = private_test_attribute(term, "_guarded_window")
        assert cursor is not None
        object.__setattr__(cursor, "stage", False)
        with pytest.raises(ValueError, match="malformed fields"):
            term.source_transfer(0)
        object.__setattr__(cursor, "stage", 0)

    with FiveReverseTerm(196, 181, max_steps=184) as term:
        port = term.source_transfer(0).initial_port
        assert isinstance(port, FiveCarryPort)
        assert type(port.width_growth) is int
        cursor = private_test_attribute(term, "_guarded_window")
        assert cursor is not None
        object.__setattr__(cursor, "incoming_growth", bool(1 - port.width_growth))
        with pytest.raises(ValueError, match="malformed fields"):
            term.source_transfer(0)
        object.__setattr__(cursor, "incoming_growth", port.width_growth)


def test_finite_source_window_accepts_zero_bit_zero_seed_metadata() -> None:
    metadata = FiveFiniteSourceWindow(
        seed=0,
        start_generation=0,
        terminal_generation=1,
        borders=((0, 0), (0, 0)),
        inlets=(0,),
        initial_state_bits=0,
        bits_added_per_step_bound=0,
    )
    assert metadata.state_bits_bound_through(0) == 0


def test_five_reverse_adapter_revalidates_mutated_source_and_action() -> None:
    with FiveReverseTerm(196, 1) as term:
        endpoint = term.issued_endpoint_view()
        source = endpoint.binding.source
        assert type(source) is FiveReverseSource
        adapter = FiveReverseSourceAdapter(
            term, term.resource_ledger, source, source.issuer
        )

        for corrupted_steps in (-1, True):
            action = FiveReverseAction(1)
            object.__setattr__(action, "steps", corrupted_steps)
            with pytest.raises(ValueError, match="horizon"):
                adapter.validate_action(action)

        original_seed = source.seed
        object.__setattr__(source, "seed", True)
        try:
            with pytest.raises(ValueError, match="foreign or malformed"):
                adapter.validate_source(source)
        finally:
            object.__setattr__(source, "seed", original_seed)


def test_five_reverse_padded_candidate_uses_authenticated_initial_image() -> None:
    with FiveReverseTerm(196, 0, max_steps=128) as term:
        initial = term.issued_endpoint_view()
        source = initial.binding.source
        assert type(source) is FiveReverseSource
        adapter = FiveReverseSourceAdapter(
            term, term.resource_ledger, source, source.issuer
        )
        candidate = adapter.padded_source_candidate(FiveReverseAction(128), initial)
        expected = 196
        for _ in range(128):
            expected = 5 * int(str(expected)[::-1])
        assert candidate.payload == expected
        assert candidate.extent == 128
        with pytest.raises(ValueError):
            adapter.padded_source_candidate(
                FiveReverseAction(2), replace(initial, payload=197)
            )


def test_five_reverse_wide_source_production_avoids_chronological_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = 10**143 + 12345
    expected = seed
    for _ in range(256):
        expected = 5 * int(str(expected)[::-1])

    def poisoned(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("production replayed the source")

    monkeypatch.setattr(FiveReverseSourceAdapter, "_apply_steps", poisoned)
    with FiveReverseTerm(seed, 256, max_steps=256) as term:
        assert term.materialize(max_bits=4096) == expected


def test_five_reverse_padded_source_uses_same_ledger_and_msd_order() -> None:
    with FiveReverseTerm(196, 0, max_steps=128) as term:
        with FiveReverseTerm(196, 0, max_steps=128) as other:
            arena = LedgerSLPArena(term.resource_ledger, "five-padded", "five_test")
            foreign = LedgerSLPArena(other.resource_ledger, "five-foreign", "five_test")
            expected = 196
            for _ in range(128):
                expected = 5 * int(str(expected)[::-1])
            root = term.publish_padded_source(arena, 128)
            assert arena.materialize(root) == tuple(int(d) for d in str(expected))
            with pytest.raises(ValueError, match="another source ledger"):
                term.publish_padded_source(foreign, 128)
            arena.dispose()
            foreign.dispose()


def test_five_reverse_owner_cache_admission_rejects_boolean_state_tampering() -> None:
    query = FiveReverseTermQuery(index=1, seed=1, max_steps=1)
    compiler = NumberCompiler(shared_cache=False)
    term = FiveReverseTerm(1, 1, max_steps=1)
    assert matches_bounded_query(term, query, compiler)
    for field, original in (
        ("seed", term.seed),
        ("generation", term.generation),
        ("max_steps", term.max_steps),
        ("max_state_bits", term.max_state_bits),
    ):
        object.__setattr__(term, field, True)
        assert not matches_bounded_query(term, query, compiler)
        with pytest.raises(ValueError, match="source/action binding changed"):
            term.check_open()
        object.__setattr__(term, field, original)
        assert matches_bounded_query(term, query, compiler)
    term.dispose()


def test_seed_196_digit_band_uses_guarded_ports_and_exact_fallback_after_exit() -> None:
    term = FiveReverseTerm(196, 180, max_steps=184)
    packet = term.digit_band(4, 3, 97, trace=True)
    assert packet.source_coverage == "guarded-four-stage-source-window"
    assert packet.physical_ticks == 4
    assert len(packet.trace) == 4
    assert packet.phase_coordinate is OrderedPhaseCoordinate.SOURCE_MOD45
    assert (packet.start_phase, packet.terminal_phase) == (25, 10)
    assert packet.matrix_multiplications == 24
    assert packet.source_letters_read == 12
    assert len(term.digit_band(4, 4, 97).matrices) == 1


def test_seed_196_source_window_falls_back_below_its_state_bit_bound() -> None:
    with pytest.raises(BlockContextBudgetExceeded):
        with FiveReverseTerm(196, 180, max_steps=180, max_state_bits=8) as term:
            term.source_transfer(0)

    with FiveReverseTerm(196, 180, max_steps=180, max_state_bits=1087) as term:
        packet = term.source_transfer(0)
        assert packet.source_coverage is OrderedSourceCoverage.EXACT_BOUNDED_WINDOW
        assert isinstance(packet.initial_port, FiveBorderPort)

    with FiveReverseTerm(196, 184, max_steps=184) as term:
        packet = term.source_transfer(0)
        assert packet.source_coverage is OrderedSourceCoverage.EXACT_BOUNDED_WINDOW
        assert isinstance(packet.initial_port, FiveBorderPort)


def test_five_reverse_relative_reuse_rebinds_to_receiver_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def force_chronological_children(
        _adapter: FiveReverseSourceAdapter,
        _action: Hashable,
        _source: SourceImageView,
        _demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        return None

    monkeypatch.setattr(
        FiveReverseSourceAdapter,
        "apply_composite",
        force_chronological_children,
    )
    with FiveReverseTerm(0, 2, max_steps=2, max_state_bits=1) as term:
        assert term.materialize(max_bits=1) == 0
        endpoint = term.issued_endpoint_view()
        assert endpoint.binding.action == FiveReverseAction(2)
        assert endpoint.binding.extent == 2


def test_source_image_views_are_bound_to_the_issuing_term_and_payload() -> None:
    issuer = FiveReverseTerm(196, 1)
    foreign = FiveReverseTerm(196, 1)
    view = issuer.issued_endpoint_view()
    issuer.require_issued_view(view)
    assert type(view.payload) is int
    with pytest.raises(ValueError):
        foreign.require_issued_view(view)
    with pytest.raises(ValueError):
        issuer.require_issued_view(replace(view, payload=view.payload + 1))

    source = view.binding.source
    assert type(source) is FiveReverseSource
    adapter = FiveReverseSourceAdapter(
        issuer, issuer.resource_ledger, source, source.issuer
    )
    with pytest.raises(ValueError):
        adapter.project(view, SourceImageDemand("unrecognized"))


def test_five_reverse_source_window_obeys_zero_resource_budgets() -> None:
    node_limited = FiveReverseTerm(196, 180, max_context_nodes=0)
    with pytest.raises(BlockContextBudgetExceeded):
        node_limited.source_transfer(0)
    scratch = next(
        account
        for account in node_limited.resource_ledger.inventory()
        if account.owner == _scratch_owner(node_limited)
    )
    assert (scratch.entries, scratch.nodes) == (0, 0)

    with pytest.raises(BlockContextBudgetExceeded):
        FiveReverseTerm(196, 180, max_cache_entries=0)


def test_five_reverse_disposal_can_retry_after_a_cleanup_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = FiveReverseTerm(196, 180, max_steps=180)
    term.source_transfer(0)
    original = term.resource_ledger.mark_disposed
    attempts = 0

    def fail_once(owner: int) -> None:
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            raise RuntimeError("injected owner retirement failure")
        original(owner)

    monkeypatch.setattr(term.resource_ledger, "mark_disposed", fail_once)
    with pytest.raises(RuntimeError, match="injected owner retirement failure"):
        term.dispose()
    assert not term.is_usable
    term.dispose()
    scratch = next(
        account
        for account in term.resource_ledger.inventory()
        if account.owner == _scratch_owner(term)
    )
    assert scratch.disposed


def test_five_reverse_retries_scratch_release_after_initialization_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = FiveReverseTerm(196, 180, max_steps=180)

    def fail_window_validation(_self: FiveReverseTerm, _window: object) -> None:
        raise ArithmeticError("injected guarded-window validation failure")

    original_release = term.resource_ledger.release
    release_attempts = 0

    def fail_release_once(owner: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal release_attempts
        if owner == _scratch_owner(term) and entries == 1 and nodes == 8:
            release_attempts += 1
            if release_attempts == 1:
                raise RuntimeError("injected scratch release failure")
        original_release(owner, entries, nodes)

    monkeypatch.setattr(term.resource_ledger, "release", fail_release_once)
    with monkeypatch.context() as window_fault:
        window_fault.setattr(
            FiveReverseTerm, "_validate_guarded_window", fail_window_validation
        )
        with pytest.raises(RuntimeError, match="injected scratch release failure"):
            term.source_transfer(0)
    scratch = next(
        account
        for account in term.resource_ledger.inventory()
        if account.owner == _scratch_owner(term)
    )
    assert (scratch.entries, scratch.nodes) == (1, 8)

    term.source_transfer(0)
    scratch = next(
        account
        for account in term.resource_ledger.inventory()
        if account.owner == _scratch_owner(term)
    )
    assert (scratch.entries, scratch.nodes) == (1, 8)

    term.dispose()
    scratch = next(
        account
        for account in term.resource_ledger.inventory()
        if account.owner == _scratch_owner(term)
    )
    assert (scratch.entries, scratch.nodes) == (0, 0)
    assert scratch.disposed
