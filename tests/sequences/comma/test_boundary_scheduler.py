"""Source-bound scheduler checks for interior cycles and boundary prefixes."""

from __future__ import annotations

from collections.abc import Callable
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.comma import action_arena, certificates
from number_compiler.sequences.comma.action_arena import (
    CommaActionArena,
    CommaActionID,
    CommaActionRecord,
)
from number_compiler.sequences.comma.arithmetic import cycle_transfer
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.image_adapter import (
    BoundaryPrefixCursor,
    CommaImagePayload,
    CommaOccurrenceID,
    CommaSource,
)
from number_compiler.sequences.comma.occurrence import BoundaryOccurrence
from number_compiler.sequences.comma.power import (
    FIRST_FORK_INDEX,
    CommaTerm,
)


def test_closed_phase_formula_matches_every_literal_phase_and_guard() -> None:
    for leading in range(1, 10):
        for entering in range(10):
            transfer = cycle_transfer(leading, entering)
            digit = entering
            displacement = maximum_guard = 0
            for _ in range(transfer.period):
                maximum_guard = max(
                    maximum_guard,
                    displacement + 10 * digit + (leading + 1 if leading < 9 else 9),
                )
                displacement += 10 * digit + leading
                digit = (digit + leading) % 10
            assert digit == entering
            assert transfer.displacement == displacement
            assert transfer.maximum_guard == maximum_guard


def test_decimal_output_uses_charged_shared_radix_stream() -> None:
    term = CommaTerm(20_000)
    assert tuple(term.iter_digits()) == (4, 0, 4, 9, 3, 0, 1)
    assert term.ledger.counters["comma_stream_emitted_digits"] == 7
    assert term.ledger.counters["comma_stream_workspace_peak_slots"] > 0
    assert term.ledger.counters["comma_stream_workspace_peak_integer_bits"] > 0

    early = CommaTerm(20_000)
    stream = early.iter_digits()
    assert next(stream) == 4
    stream.close()
    assert early.ledger.counters["comma_stream_emitted_digits"] == 1
    assert early.ledger.counters["comma_stream_requests"] == 1
    assert early.ledger.counters["comma_stream_cancellations"] == 1
    assert early.ledger.counters["comma_stream_failures"] == 0


def test_binding_audit_does_not_allocate_images(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = CommaTerm(22)
    term.materialize()
    snapshot = term.audit_snapshot()
    assert snapshot.occurrences
    view = term.scheduler.source_image_core().view(snapshot.occurrences[-1].image)
    counters = dict(term.ledger.counters)

    def forbidden(_scheduler: TileScheduler) -> Never:
        raise AssertionError("audit called the allocating image accessor")

    monkeypatch.setattr(TileScheduler, "source_image_core", forbidden)
    term.adapter.audit_image_binding(view.binding, view.payload, None)
    with pytest.raises(ValueError, match="failure prefix"):
        term.adapter.audit_image_binding(view.binding, view.payload, 0)
    assert dict(term.ledger.counters) == counters


@pytest.mark.parametrize(
    ("index", "copies", "source", "first", "second", "prior_compatible_hit"),
    ((22, 1, 1024, 1484, 1944, 0), (201, 2, 10057, 10977, 11897, 1)),
)
def test_interior_cycle_relative_reuse_rebinds_the_exact_occurrence(
    index: int,
    copies: int,
    source: int,
    first: int,
    second: int,
    prior_compatible_hit: int,
) -> None:
    term = CommaTerm(index)
    assert term.materialize() == source
    action = term.arena.cycles(1, source % 10, copies)
    evaluated = term.ledger.counters["comma_evaluated_transitions"]
    before = term.ledger.counters.get("source_image_relative_transfer_hits", 0)
    first_image = term.scheduler.source_image(
        term.adapter, _current_source(term), action
    )
    after_first = term.ledger.counters.get("source_image_relative_transfer_hits", 0)
    first_application_hits = after_first - before
    # A source-compatible earlier occurrence may already have supplied this
    # exact relative transfer, especially after complete-cycle IDs are
    # canonicalized by phase coset. Count the second application separately.
    rebindings_before_second = term.ledger.counters.get(
        "comma_relative_cycle_rebindings", 0
    )
    second_image = term.scheduler.source_image(term.adapter, first_image, action)
    first_payload = cast(
        CommaImagePayload, term.scheduler.source_image_core().view(first_image).payload
    )
    second_payload = cast(
        CommaImagePayload,
        term.scheduler.source_image_core().view(second_image).payload,
    )
    assert first_payload == CommaImagePayload(first, index + 10 * copies)
    assert second_payload == CommaImagePayload(second, index + 20 * copies)
    after_second = term.ledger.counters["source_image_relative_transfer_hits"]
    second_application_hits = after_second - after_first
    assert first_application_hits == prior_compatible_hit
    assert second_application_hits == 1
    assert term.ledger.counters["comma_relative_cycle_rebindings"] == (
        rebindings_before_second + 1
    )
    assert term.ledger.counters["comma_evaluated_transitions"] == evaluated
    huge = term.arena.cycles(1, source % 10, 10**20)
    with pytest.raises(ValueError, match="unadmitted seam"):
        term.scheduler.source_image(term.adapter, second_image, huge)


def test_boundary_prefix_uses_exact_source_and_stops_before_fork(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def first_winning_child(**_: object) -> int:
        return 19_999_999_999

    monkeypatch.setattr(certificates, "require_selected_child", first_winning_child)
    term = CommaTerm(FIRST_FORK_INDEX + 1, certificate_version="test-boundary")
    assert term.materialize() == 19_999_999_999
    state = BoundaryState("N", 2, 10)
    template = term.arena.boundary_template(state)
    total = template.weight.evaluate(10)
    assert template.outcome == "fork"
    action = _boundary_prefix(term.arena, state, 10, total)
    source = _current_source(term)
    evaluated = term.ledger.counters["comma_evaluated_transitions"]
    image = term.scheduler.source_image(term.adapter, source, action)
    payload = cast(
        CommaImagePayload, term.scheduler.source_image_core().view(image).payload
    )
    assert payload.value == template.endpoint.evaluate(10)
    assert payload.absolute_index == FIRST_FORK_INDEX + 1 + total
    assert (
        term.scheduler.source_projection(
            term.adapter, image, SourceImageDemand("value")
        ).value
        == payload.value
    )
    assert term.scheduler.source_projection(
        term.adapter, image, SourceImageDemand("width")
    ).value == len(str(payload.value))
    assert term.ledger.counters["comma_boundary_prefix_applications"] == 1
    assert term.ledger.counters["comma_boundary_represented_transitions"] == total
    assert term.ledger.counters["comma_evaluated_transitions"] == evaluated
    assert term.ledger.counters["comma_boundary_template_publications"] == 1
    assert term.ledger.counters["comma_boundary_seal_checks"] > 0
    arena_snapshot = term.arena.audit_snapshot()
    assert term.ledger.counters["comma_boundary_seal_retained_slots"] == (
        len(arena_snapshot.boundary_seal_nodes) + len(arena_snapshot.boundary_seals)
    )
    assert term.ledger.counters["comma_boundary_seal_retained_integer_bits"] > 0
    receiver_source = BoundaryOccurrence(state, 10)
    receiver_action = term.arena.boundary_prefix_occurrence(receiver_source, 6)
    translated_source = BoundaryOccurrence(state, 934)
    assert (
        term.arena.boundary_prefix_occurrence(translated_source, 6) == receiver_action
    )
    receiver_image = term.scheduler.source_image(
        term.adapter, _current_source(term), receiver_action
    )
    receiver_payload = cast(
        CommaImagePayload,
        term.scheduler.source_image_core().view(receiver_image).payload,
    )
    assert receiver_payload.value == template.point(10, 6)
    assert receiver_payload.absolute_index == FIRST_FORK_INDEX + 1 + 6
    assert receiver_payload.boundary_cursor is not None
    assert receiver_payload.boundary_cursor.transitions == 6
    foreign_cursor_payload = CommaImagePayload(
        receiver_payload.value,
        receiver_payload.absolute_index,
        receiver_payload.certificate_version,
        BoundaryPrefixCursor(BoundaryState("Z", 2, 10), 10, 6),
    )
    with pytest.raises(ValueError, match="cursor authority"):
        term.adapter.audit_image_binding(
            term.scheduler.source_image_core().view(receiver_image).binding,
            foreign_cursor_payload,
            None,
        )
    identity_image = term.scheduler.source_image(
        term.adapter, receiver_image, term.arena.identity
    )
    identity_view = term.scheduler.source_image_core().view(identity_image)
    identity_payload = cast(CommaImagePayload, identity_view.payload)
    assert identity_payload.boundary_cursor is receiver_payload.boundary_cursor
    assert term.adapter.audit_image_binding(
        identity_view.binding, identity_payload, None
    ) == (receiver_payload.boundary_cursor,)
    aliased_cursor_payload = CommaImagePayload(
        identity_payload.value,
        identity_payload.absolute_index,
        identity_payload.certificate_version,
        BoundaryPrefixCursor(state, 10, 6),
    )
    with pytest.raises(ValueError, match="identity changed its source payload"):
        term.adapter.audit_image_binding(
            identity_view.binding, aliased_cursor_payload, None
        )
    continued_image = term.scheduler.source_image(
        term.adapter, receiver_image, receiver_action
    )
    continued_payload = cast(
        CommaImagePayload,
        term.scheduler.source_image_core().view(continued_image).payload,
    )
    continued_binding = term.scheduler.source_image_core().view(continued_image).binding
    continued_action = term.arena.node(
        cast(action_arena.CommaActionID, continued_binding.action)
    )
    assert continued_payload.value == template.point(10, 12)
    assert continued_payload.absolute_index == FIRST_FORK_INDEX + 1 + 12
    # Scheduler bindings describe the action relative to this receiving image;
    # the payload cursor carries the cumulative boundary position.
    assert continued_binding.extent == 6
    assert continued_action.kind == "boundary-prefix-occurrence"
    assert continued_action.steps == 6
    assert continued_payload.boundary_cursor is not None
    assert continued_payload.boundary_cursor.state == state
    assert continued_payload.boundary_cursor.exponent == 10
    assert continued_payload.boundary_cursor.transitions == 12
    with pytest.raises(ValueError, match="another source occurrence"):
        term.scheduler.source_image(term.adapter, image, action)
    with pytest.raises(ValueError, match="crosses its next branch"):
        _boundary_prefix(term.arena, state, 10, total + 1)
    with pytest.raises(ValueError, match="lifting is not yet admitted"):
        _boundary_prefix(term.arena, state, 934, 1)
    audit = audit_registered_payloads(term.ledger)
    assert audit.unknown_payloads == 0
    assert audit.forbidden_future_payloads == 0
    cursor = identity_payload.boundary_cursor
    assert cursor is not None
    original_transitions = cursor.transitions
    object.__setattr__(cursor, "transitions", original_transitions + 1)
    try:
        assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(cursor, "transitions", original_transitions)
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads == 0
    assert term.ledger.counters["comma_boundary_explicit_audit_component_checks"] > 0
    assert term.ledger.counters["comma_boundary_explicit_audit_operand_bits"] > 0
    assert all(
        item.accounting_delta == 0
        for item in term.ledger.inventory()
        if item.name.startswith("comma-boundary-")
    )
    forged = term.arena.intern_record(
        ("boundary-prefix", state, 934, 1),
        CommaActionRecord(
            "boundary-prefix", 1, boundary_source=state, boundary_exponent=934
        ),
    )
    with pytest.raises(ValueError, match="lifting is not yet admitted"):
        term.scheduler.source_image(term.adapter, source, forged)
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


def testboundary_template_budget_refusal_publishes_no_partial_state() -> None:
    term = CommaTerm(1, max_states=100)
    with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
        term.arena.boundary_template(BoundaryState("N", 2, 10))
    assert len(term.arena.audit_snapshot().boundary_templates) == 0
    assert len(term.arena.audit_snapshot().boundary_nodes) == 0
    assert all(
        item.accounting_delta == 0
        for item in term.ledger.inventory()
        if item.name.startswith("comma-boundary-")
    )


def test_seal_work_refusal_leaves_no_template_or_seal() -> None:
    state = BoundaryState("N", 2, 10)
    construction_charges: list[int] = []
    construct_macro(state, charge=construction_charges.append)
    term = CommaTerm(1)
    spent = term.ledger.counters.get("comma_work", 0)
    term.arena.max_work = spent + sum(construction_charges)
    with pytest.raises(ValueError, match="comma construction exceeds"):
        term.arena.boundary_template(state)
    _assert_empty_boundary_publication(term)


def test_seal_construction_failure_releases_reserved_storage(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = CommaTerm(1)

    def fail_seal(_template: object) -> object:
        raise RuntimeError("injected seal failure")

    monkeypatch.setattr(action_arena, "_template_seal", fail_seal)
    with pytest.raises(RuntimeError, match="injected seal failure"):
        term.arena.boundary_template(BoundaryState("N", 2, 10))
    _assert_empty_boundary_publication(term)


def test_mutatedboundary_template_and_action_fail_closed() -> None:
    from number_compiler.sequences.comma.boundary_quotient import AffineWeight

    term = CommaTerm(1)
    state = BoundaryState("N", 2, 10)
    template = term.arena.boundary_template(state)
    object.__setattr__(template, "weight", AffineWeight(0, 0, 1))
    audit = audit_registered_payloads(term.ledger)
    assert audit.forbidden_future_payloads > 0

    other = CommaTerm(1)
    action = other.arena.one_cycle(1, 4)
    node = other.arena.node(action)
    object.__setattr__(node, "maximum_guard", 0)
    with pytest.raises(ValueError, match="publication was altered"):
        other.arena.node(action)
    audit = audit_registered_payloads(other.ledger)
    assert audit.forbidden_future_payloads > 0


def test_mutated_boundary_components_fail_before_private_scheduler_demand(
    monkeypatch: pytest.MonkeyPatch,
) -> None:

    def first_winning_child(**_kwargs: object) -> int:
        return 19_999_999_999

    monkeypatch.setattr(
        certificates,
        "require_selected_child",
        first_winning_child,
    )
    term = CommaTerm(FIRST_FORK_INDEX + 1, certificate_version="test-boundary")
    assert term.materialize() == 19_999_999_999
    state = BoundaryState("N", 2, 10)
    template = term.arena.boundary_template(state)
    action = _boundary_prefix(term.arena, state, 10, 6)
    fragment = template.sector_fragments[1]
    prefix = template.prefix_displacements[1]
    weight_prefix = template.prefix_weights[1]
    raw_seal = object.__getattribute__(template, "_component_seal")
    assert type(raw_seal) is tuple
    original_seal = cast(tuple[object, ...], raw_seal)
    mutations: tuple[tuple[object, str, object, object], ...] = (
        (fragment, "displacement", fragment.displacement, fragment.displacement + 1),
        (
            fragment,
            "entering_digit",
            fragment.entering_digit,
            fragment.entering_digit + 1,
        ),
        (
            prefix,
            "numerator_offset",
            prefix.numerator_offset,
            prefix.numerator_offset + 1,
        ),
        (
            weight_prefix,
            "numerator_offset",
            weight_prefix.numerator_offset,
            weight_prefix.numerator_offset + 1,
        ),
        (
            template,
            "ordered_children",
            template.ordered_children,
            template.ordered_children[:1],
        ),
        (
            template,
            "ordered_children",
            template.ordered_children,
            template.ordered_children[::-1],
        ),
        (
            template,
            "exponent_delta",
            template.exponent_delta,
            template.exponent_delta + 1,
        ),
        (template, "_component_seal", original_seal, (*original_seal,)),
        (
            template.endpoint,
            "numerator_offset",
            template.endpoint.numerator_offset,
            template.endpoint.numerator_offset + 1,
        ),
    )
    for target, attribute, original, replacement in mutations:
        object.__setattr__(target, attribute, replacement)
        try:
            with pytest.raises(ValueError, match="template publication was altered"):
                term.scheduler.source_image(term.adapter, _current_source(term), action)
            assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0
        finally:
            object.__setattr__(target, attribute, original)


def test_mutated_boundary_state_is_rejected_before_hash_or_equality() -> None:
    class HashEqualityTrap:
        def __init__(self) -> None:
            self.hash_calls = 0
            self.equality_calls = 0

        def __hash__(self) -> int:
            self.hash_calls += 1
            return 7

        def __eq__(self, _other: object) -> bool:
            self.equality_calls += 1
            return True

    term = CommaTerm(1)
    invalid = BoundaryState("N", 2, 10)
    invalid_kind = HashEqualityTrap()
    object.__setattr__(invalid, "kind", invalid_kind)
    with pytest.raises(ValueError, match="noncanonical scalar fields"):
        term.arena.boundary_template(invalid)
    with pytest.raises(ValueError, match="noncanonical scalar fields"):
        _boundary_prefix(term.arena, invalid, 10, 1)
    assert invalid_kind.hash_calls == 0
    assert invalid_kind.equality_calls == 0

    published = BoundaryState("N", 2, 10)
    _boundary_prefix(term.arena, published, 10, 1)
    published_kind = HashEqualityTrap()
    object.__setattr__(published, "kind", published_kind)
    audit = audit_registered_payloads(term.ledger)
    assert audit.forbidden_future_payloads > 0
    assert published_kind.hash_calls == 0
    assert published_kind.equality_calls == 0


def _assert_empty_boundary_publication(term: CommaTerm) -> None:
    assert len(term.arena.audit_snapshot().boundary_templates) == 0
    snapshot = term.arena.audit_snapshot()
    assert len(snapshot.boundary_seals) == 0
    assert len(snapshot.boundary_nodes) == 0
    assert len(snapshot.boundary_seal_nodes) == 0
    assert all(
        item.accounting_delta == 0
        for item in term.ledger.inventory()
        if item.name.startswith("comma-boundary-")
    )


def _current_source(term: CommaTerm) -> CommaSource | CommaOccurrenceID:
    return cast(
        CommaSource | CommaOccurrenceID,
        object.__getattribute__(term, "_source"),
    )


def _boundary_prefix(
    arena: CommaActionArena,
    state: BoundaryState,
    exponent: int,
    transitions: int,
) -> CommaActionID:
    constructor = cast(
        Callable[[BoundaryState, int, int], CommaActionID],
        object.__getattribute__(arena, "_boundary_prefix"),
    )
    return constructor(state, exponent, transitions)
