"""Source-bound scheduler checks for interior cycles and boundary prefixes."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.comma import action_arena, certificates
from number_compiler.sequences.comma.action_arena import _Action
from number_compiler.sequences.comma.arithmetic import cycle_transfer
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.power import (
    FIRST_FORK_INDEX,
    CommaImagePayload,
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


@pytest.mark.parametrize(
    ("index", "copies", "source", "first", "second"),
    ((22, 1, 1024, 1484, 1944), (201, 2, 10057, 10977, 11897)),
)
def test_interior_cycle_relative_reuse_rebinds_the_exact_occurrence(
    index: int,
    copies: int,
    source: int,
    first: int,
    second: int,
) -> None:
    term = CommaTerm(index)
    assert term.materialize() == source
    action = term.arena.cycles(1, source % 10, copies)
    evaluated = term.ledger.counters["comma_evaluated_transitions"]
    before = term.ledger.counters.get("source_image_relative_transfer_hits", 0)
    first_image = term.scheduler.source_image(term.adapter, term._source, action)
    second_image = term.scheduler.source_image(term.adapter, first_image, action)
    first_payload = cast(
        CommaImagePayload, term.scheduler._source_image_core().view(first_image).payload
    )
    second_payload = cast(
        CommaImagePayload,
        term.scheduler._source_image_core().view(second_image).payload,
    )
    assert first_payload == CommaImagePayload(first, index + 10 * copies)
    assert second_payload == CommaImagePayload(second, index + 20 * copies)
    assert term.ledger.counters["source_image_relative_transfer_hits"] == before + 1
    assert term.ledger.counters["comma_relative_cycle_rebindings"] == 1
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
    template = term.arena._boundary_template(state)
    total = template.weight.evaluate(10)
    assert template.outcome == "fork"
    action = term.arena._boundary_prefix(state, 10, total)
    source = term._source
    evaluated = term.ledger.counters["comma_evaluated_transitions"]
    image = term.scheduler.source_image(term.adapter, source, action)
    payload = cast(
        CommaImagePayload, term.scheduler._source_image_core().view(image).payload
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
    assert term.ledger.counters["comma_boundary_seal_retained_slots"] == (
        len(term.arena._boundary_seal_nodes) + len(term.arena._boundary_seals)
    )
    assert term.ledger.counters["comma_boundary_seal_retained_integer_bits"] > 0
    with pytest.raises(ValueError, match="another source occurrence"):
        term.scheduler.source_image(term.adapter, image, action)
    with pytest.raises(ValueError, match="crosses its next branch"):
        term.arena._boundary_prefix(state, 10, total + 1)
    with pytest.raises(ValueError, match="lifting is not yet admitted"):
        term.arena._boundary_prefix(state, 934, 1)
    audit = audit_registered_payloads(term.ledger)
    assert audit.unknown_payloads == 0
    assert audit.forbidden_future_payloads == 0
    assert all(
        item.accounting_delta == 0
        for item in term.ledger.inventory()
        if item.name.startswith("comma-boundary-")
    )
    forged = term.arena._intern(
        ("boundary-prefix", state, 934, 1),
        _Action("boundary-prefix", 1, boundary_source=state, boundary_exponent=934),
    )
    with pytest.raises(ValueError, match="lifting is not yet admitted"):
        term.scheduler.source_image(term.adapter, source, forged)
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


def test_boundary_template_budget_refusal_publishes_no_partial_state() -> None:
    term = CommaTerm(1, max_states=100)
    with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
        term.arena._boundary_template(BoundaryState("N", 2, 10))
    assert len(term.arena._boundary_templates) == 0
    assert len(term.arena._boundary_nodes) == 0
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
        term.arena._boundary_template(state)
    _assert_empty_boundary_publication(term)


def test_seal_construction_failure_releases_reserved_storage(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = CommaTerm(1)

    def fail_seal(_template: object) -> object:
        raise RuntimeError("injected seal failure")

    monkeypatch.setattr(action_arena, "_template_seal", fail_seal)
    with pytest.raises(RuntimeError, match="injected seal failure"):
        term.arena._boundary_template(BoundaryState("N", 2, 10))
    _assert_empty_boundary_publication(term)


def test_mutated_boundary_template_and_action_fail_closed() -> None:
    from number_compiler.sequences.comma.boundary_quotient import AffineWeight

    term = CommaTerm(1)
    state = BoundaryState("N", 2, 10)
    template = term.arena._boundary_template(state)
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


@pytest.mark.parametrize(
    "component",
    [
        "fragment",
        "phase",
        "prefix",
        "weight_prefix",
        "children",
        "child_order",
        "exponent_gain",
        "endpoint",
    ],
)
def test_mutated_boundary_component_fails_before_private_scheduler_demand(
    monkeypatch: pytest.MonkeyPatch, component: str
) -> None:
    monkeypatch.setattr(
        certificates,
        "require_selected_child",
        lambda **_: 19_999_999_999,
    )
    term = CommaTerm(FIRST_FORK_INDEX + 1, certificate_version="test-boundary")
    assert term.materialize() == 19_999_999_999
    state = BoundaryState("N", 2, 10)
    template = term.arena._boundary_template(state)
    action = term.arena._boundary_prefix(state, 10, 6)
    if component == "fragment":
        fragment = template.sector_fragments[1]
        object.__setattr__(fragment, "displacement", fragment.displacement + 1)
    elif component == "phase":
        fragment = template.sector_fragments[1]
        object.__setattr__(fragment, "entering_digit", fragment.entering_digit + 1)
    elif component == "prefix":
        prefix = template.prefix_displacements[1]
        object.__setattr__(prefix, "numerator_offset", prefix.numerator_offset + 1)
    elif component == "weight_prefix":
        prefix = template.prefix_weights[1]
        object.__setattr__(prefix, "numerator_offset", prefix.numerator_offset + 1)
    elif component == "children":
        object.__setattr__(template, "ordered_children", template.ordered_children[:1])
    elif component == "child_order":
        object.__setattr__(
            template, "ordered_children", template.ordered_children[::-1]
        )
    elif component == "exponent_gain":
        object.__setattr__(template, "exponent_delta", template.exponent_delta + 1)
    else:
        object.__setattr__(
            template.endpoint,
            "numerator_offset",
            template.endpoint.numerator_offset + 1,
        )
    with pytest.raises(ValueError, match="template publication was altered"):
        term.scheduler.source_image(term.adapter, term._source, action)
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


def _assert_empty_boundary_publication(term: CommaTerm) -> None:
    assert len(term.arena._boundary_templates) == 0
    assert len(term.arena._boundary_seals) == 0
    assert len(term.arena._boundary_nodes) == 0
    assert len(term.arena._boundary_seal_nodes) == 0
    assert all(
        item.accounting_delta == 0
        for item in term.ledger.inventory()
        if item.name.startswith("comma-boundary-")
    )
