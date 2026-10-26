"""Total Antihydra arithmetic terms share one source-bound cylinder owner."""

from __future__ import annotations

from collections.abc import Callable, Iterator
from typing import cast

import pytest

from number_compiler.api.antihydra_observation import AntihydraRunKind, observe_run
from number_compiler.api.number_api import AntihydraTermPayload, NumberCompiler
from number_compiler.api.query_types import AntihydraTermQuery
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceID,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    Cylinder,
    admitted_arithmetic_cylinder,
    arithmetic_from_word,
    arithmetic_kernel,
    physical_roof,
)
from number_compiler.sequences.antihydra.runtime import (
    AntihydraArithmeticTerm,
    ArithmeticResult,
    ArithmeticSegment,
    CylinderEngine,
    run,
)


def _reference(returns: int) -> tuple[int, int, int, int | None]:
    h, balance, minimum = 8, 0, 0
    first_failure: int | None = None
    for index in range(returns):
        balance += -1 if h & 1 else 2
        minimum = min(minimum, balance)
        if balance < 0 and first_failure is None:
            first_failure = index
        h += h // 2
    return h, balance, minimum, first_failure


@pytest.mark.parametrize("width,residue", ((1, 0), (8, 173)))
def test_admitted_constructor_is_the_canonical_bounded_kernel(
    width: int, residue: int
) -> None:
    assert admitted_arithmetic_cylinder(residue, width) == arithmetic_kernel(
        residue, width
    )


@pytest.mark.parametrize("width,residue", ((9, 341), (64, (1 << 63) + 17)))
def test_admitted_constructor_owns_wide_source_parity(width: int, residue: int) -> None:
    admitted = admitted_arithmetic_cylinder(residue, width)
    assert admitted == arithmetic_from_word(residue, width, admitted.parity_word)
    with pytest.raises(ValueError, match="kernel width"):
        arithmetic_kernel(residue, width)


@pytest.mark.parametrize(
    "first_width,first_residue,second_width,second_residue",
    ((1, 1, 2, 3), (3, 5, 2, 1), (4, 13, 3, 6)),
)
def test_joined_antihydra_cylinders_match_both_consumers_on_high_fibers(
    first_width: int,
    first_residue: int,
    second_width: int,
    second_residue: int,
) -> None:
    first = admitted_arithmetic_cylinder(first_residue, first_width)
    second = admitted_arithmetic_cylinder(second_residue, second_width)
    joined = first.then(second)
    first_roof, second_roof = physical_roof(first), physical_roof(second)
    joined_roof = first_roof.then(second_roof)
    assert joined_roof.residue == joined.residue
    assert joined_roof.output == joined.output
    assert (joined_roof.delta, joined_roof.minimum) == (
        joined.delta,
        joined.minimum,
    )
    for high in (1, 2, (1 << 70) + 3):
        source = joined.residue + (high << joined.width)
        middle, middle_ledger = first.advance(source, 100)
        assert joined.advance(source, 100) == second.advance(middle, middle_ledger)
        middle, middle_ledger, left1, right1 = first_roof.apply(source, 100)
        target, target_ledger, left2, right2 = second_roof.apply(middle, middle_ledger)
        assert joined_roof.apply(source, 100) == (
            target,
            target_ledger,
            left1 + left2,
            right1 + right2,
        )
        with pytest.raises(ValueError, match="safe admitted"):
            joined_roof.apply(source, -joined.minimum - 1)


def test_zero_width_physical_cylinder_is_a_composition_identity() -> None:
    identity = Cylinder(0, 0, 0, 0, 0, 0, 0, 0, 0)
    for residue in (0, 1):
        cylinder = physical_roof(arithmetic_kernel(residue, 1))
        assert identity.then(cylinder) == cylinder
        assert cylinder.then(identity) == cylinder


@pytest.mark.parametrize("returns", (0, 1, 7, 64, 65, 257))
def test_total_arithmetic_result_matches_source_recurrence(returns: int) -> None:
    term = AntihydraArithmeticTerm(returns)
    result = term.result()
    assert (result.h, result.balance, result.minimum, result.first_failure_index) == (
        _reference(returns)
    )
    assert result.returns == returns
    assert len(term.segments) <= (returns + 63) // 64
    assert not term.engine.memo
    assert term.ledger.counters.get("physical_roof_evaluations", 0) == 0


def test_total_arithmetic_uses_balanced_scheduler_images_without_endpoint_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden_advance(
        _block: ArithmeticCylinder, _h: int, _balance: int
    ) -> tuple[int, int]:
        raise AssertionError("total arithmetic replayed a growing endpoint")

    monkeypatch.setattr(ArithmeticCylinder, "advance", forbidden_advance)
    term = AntihydraArithmeticTerm(1024)
    result = term.result()
    assert (result.h, result.balance, result.minimum) == _reference(1024)[:3]
    workspace = term.arithmetic_workspace
    assert type(workspace) is AntihydraArithmeticImageWorkspace
    assert type(workspace.scheduler) is TileScheduler
    assert workspace.scheduler.is_source_only
    assert workspace.scheduler.ledger is term.ledger
    initial_support = term.audit_snapshot()
    assert initial_support.segment_count == 0 and not initial_support.segments_ready
    assert term.ledger.counters.get("source_image_first_child_contexts", 0) == 0
    assert term.ledger.counters.get("source_image_second_child_contexts", 0) == 0
    assert (
        term.ledger.counters["antihydra_arithmetic_run_contraction_publications"] == 1
    )
    assert term.ledger.counters["antihydra_arithmetic_balanced_effect_requests"] == 1
    operand_work = term.ledger.counters[
        "antihydra_arithmetic_transport_operand_bits"
    ] + term.ledger.counters.get("antihydra_arithmetic_composition_operand_bits", 0)
    assert operand_work < 24 * result.returns
    assert term.ledger.counters.get("antihydra_arithmetic_temporal_run_actions", 0) == 0
    support_id = workspace.summary().support
    assert support_id is not None
    support = workspace.support_node(support_id)
    assert support.saturated and support.branch_word is None
    assert support.children is None
    assert len(term.segments) == 16
    assert term.ledger.counters.get("physical_roof_evaluations", 0) == 0


@pytest.mark.parametrize("returns", (65, 129, 257))
def test_complete_antihydra_temporal_image_keeps_guard_and_mahler_support(
    returns: int,
) -> None:
    from number_compiler.sequences.antihydra.mahler_action import associated_action

    term = AntihydraArithmeticTerm(returns)
    arithmetic = term.result()
    workspace = term.arithmetic_workspace
    assert type(workspace) is AntihydraArithmeticImageWorkspace
    expected_h, expected_balance, expected_minimum, expected_failure = _reference(
        returns
    )
    assert (
        arithmetic.h,
        arithmetic.balance,
        arithmetic.minimum,
        arithmetic.first_failure_index,
    ) == (expected_h, expected_balance, expected_minimum, expected_failure)
    assert term.ledger.counters.get("source_image_second_child_contexts", 0) == 0

    # Chronological support is materialized only for an explicit guarded consumer.
    segments = list(workspace.branch_segments())
    assert sum(width for _start, width, _word in segments) == returns
    h = 8
    for start, width, word in segments:
        assert start < returns
        for offset in range(width):
            assert (word >> offset) & 1 == h & 1
            h += h // 2
    assert h == expected_h

    packet = associated_action(arithmetic)
    assert packet["extent"] == returns
    assert packet["source_binding"] == arithmetic.source_binding
    assert term.ledger.counters.get("arithmetic_block_applications", 0) == 0
    assert not term.physical_publications


def test_number_api_is_lazy_and_reuses_arithmetic_owner_for_info_and_physical(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiler = NumberCompiler()
    projected = compiler.project(AntihydraTermQuery(129))
    assert type(projected.payload) is AntihydraTermPayload
    owner = projected.payload.term
    assert owner.audit_snapshot().result is None
    assert owner.audit_snapshot().segment_count == 0
    reused = compiler.project(AntihydraTermQuery(129)).payload
    assert type(reused) is AntihydraTermPayload
    assert reused.term is owner

    expected = _reference(129)[0]
    assert projected.materialize(max_bits=4096) == expected
    arithmetic_result = owner.result()
    arithmetic_work = owner.ledger.counters.get("arithmetic_block_applications", 0)
    assert arithmetic_work == 0 and owner.audit_snapshot().segment_count == 0
    assert projected.payload.info()["h"] == expected
    assert (
        owner.ledger.counters.get("arithmetic_block_applications", 0) == arithmetic_work
    )
    assert owner.ledger.counters.get("physical_roof_evaluations", 0) == 0
    reference = run(129)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("physical roof rediscovered arithmetic branches")

    monkeypatch.setattr(
        "number_compiler.sequences.antihydra.blocks.arithmetic_kernel", forbidden
    )
    monkeypatch.setattr(
        "number_compiler.sequences.antihydra.runtime.arithmetic_kernel", forbidden
    )
    physical = projected.payload.physical_run()
    assert (
        physical.h,
        physical.balance,
        physical.minimum,
        physical.left,
        physical.right,
        physical.halted,
    ) == (
        reference.h,
        reference.balance,
        reference.minimum,
        reference.left,
        reference.right,
        reference.halted,
    )
    assert (
        owner.ledger.counters["arithmetic_block_applications"]
        == owner.audit_snapshot().segment_count
    )
    assert owner.ledger.counters["arithmetic_block_applications"] > arithmetic_work
    assert owner.ledger.counters.get("physical_roof_evaluations", 0) > 0
    assert owner.ledger.counters.get("physical_roof_branch_discovery_steps", 0) == 0
    assert physical.returns == reference.returns
    assert physical.physical_ticks != physical.returns
    assert physical.odd_events == arithmetic_result.odd_events


def test_arithmetic_budgets_and_blank_source_are_fail_closed() -> None:
    compiler = NumberCompiler()
    with pytest.raises(ValueError, match="budget"):
        compiler.project(AntihydraTermQuery(17, max_steps=16))
    with pytest.raises(ValueError, match="budget"):
        compiler.project(AntihydraTermQuery(17, max_state_bits=16))
    limited = NumberCompiler(max_context_nodes=128, max_cache_entries=64)
    payload = limited.project(AntihydraTermQuery(1)).payload
    assert type(payload) is AntihydraTermPayload
    assert payload.term.engine.capacity == 64


def test_antihydra_query_has_no_seed_parameter() -> None:
    constructor = cast(Callable[..., AntihydraTermQuery], AntihydraTermQuery)
    with pytest.raises(TypeError, match="unexpected keyword"):
        constructor(1, seed=8)


def test_output_budget_refuses_before_arithmetic_execution() -> None:
    compiler = NumberCompiler()
    with pytest.raises(ValueError):
        compiler.nth(AntihydraTermQuery(1000), max_bits=32)
    payload = compiler.project(AntihydraTermQuery(1000)).payload
    assert type(payload) is AntihydraTermPayload
    assert payload.term.audit_snapshot().result is None
    assert payload.term.audit_snapshot().segment_count == 0
    assert compiler.nth(AntihydraTermQuery(0), max_bits=4) == 8


def test_failed_result_publication_rolls_back_retained_support() -> None:
    term = AntihydraArithmeticTerm(8)
    term.max_state_bits = 4
    with pytest.raises(ValueError, match="state exceeds"):
        term.result()
    failed_support = term.audit_snapshot()
    assert failed_support.result is None and failed_support.segment_count == 0
    assert term.arithmetic_workspace is None
    row = next(
        item
        for item in term.ledger.inventory()
        if item.role == "arithmetic_cylinder_support"
    )
    assert row.entries == row.nodes == 0
    assert term.ledger.counters["arithmetic_publication_rollbacks"] == 1
    assert all(
        row.entries == row.nodes == 0
        for row in term.ledger.inventory()
        if row.name.startswith("dyadic-return-images-")
    )


def test_failed_lazy_segment_publication_preserves_arithmetic_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    original = AntihydraArithmeticImageWorkspace.segments

    def partial(
        workspace: AntihydraArithmeticImageWorkspace,
    ) -> Iterator[tuple[int, ArithmeticCylinder]]:
        yield next(original(workspace))
        raise RuntimeError("injected lazy segment failure")

    with monkeypatch.context() as patch:
        patch.setattr(AntihydraArithmeticImageWorkspace, "segments", partial)
        with pytest.raises(RuntimeError, match="injected lazy segment failure"):
            _ = term.segments
    support = term.audit_snapshot()
    assert support.result is result
    assert support.segment_count == 0 and not support.segments_ready
    row = next(
        item
        for item in term.ledger.inventory()
        if item.role == "arithmetic_cylinder_support"
    )
    assert row.entries == row.nodes == 0
    result.require_source()
    assert len(term.segments) == 1


@pytest.mark.parametrize("target", ("source", "image", "action", "provenance"))
def test_balanced_arithmetic_authority_rejects_mutated_internal_nodes(
    target: str,
) -> None:
    term = AntihydraArithmeticTerm(128)
    result = term.result()
    workspace = term.arithmetic_workspace
    assert type(workspace) is AntihydraArithmeticImageWorkspace
    assert not workspace.construction_stack
    if target == "source":
        source_node = workspace.sources[workspace.root_source.local_id]
        object.__setattr__(source_node, "residue", source_node.residue ^ 1)
    elif target == "image":
        image_node = next(image for image in workspace.images if image.summary.width)
        object.__setattr__(
            image_node.summary.transfer,
            "offset",
            image_node.summary.transfer.offset + 1,
        )
    elif target == "action":
        action_node = workspace.actions[workspace.root_action.local_id]
        object.__setattr__(action_node, "width", action_node.width + 1)
    else:
        root_image = workspace.images[workspace.root_payload.local_id]
        object.__setattr__(
            root_image,
            "source",
            DyadicReturnSourceID(workspace.owner, workspace.SOURCE_KIND, 999),
        )
    with pytest.raises(ValueError, match="Antihydra arithmetic"):
        result.require_source()


def test_arithmetic_support_is_charged_and_auditable() -> None:
    term = AntihydraArithmeticTerm(130)
    term.result()
    report = audit_registered_payloads(term.ledger)
    assert report.forbidden_future_payloads == 0
    assert report.unknown_payloads == 0
    row = next(
        item
        for item in term.ledger.inventory()
        if item.role == "arithmetic_cylinder_support"
    )
    assert row.entries == row.nodes == 0
    assert len(term.segments) == 3
    row = next(
        item
        for item in term.ledger.inventory()
        if item.role == "arithmetic_cylinder_support"
    )
    assert row.entries == row.nodes == 3

    result = term.result()
    object.__setattr__(result, "h", result.h + 1)
    with pytest.raises(ValueError, match="result was changed"):
        term.result()
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize(
    "field,replacement",
    (
        ("requested", 8),
        ("returns", 8),
        ("h", 999),
        ("balance", 999),
        ("minimum", 999),
        ("left", 999),
        ("right", 999),
        ("halted", True),
    ),
)
def test_cached_physical_result_rejects_scalar_forgery(
    field: str, replacement: object
) -> None:
    term = AntihydraArithmeticTerm(7)
    result = term.physical_run()
    object.__setattr__(result, field, replacement)
    with pytest.raises(ValueError, match="physical result was changed"):
        term.physical_run()
    assert audit_registered_payloads(term.ledger).forbidden_future_payloads > 0


def test_total_h7_arithmetic_continues_past_guarded_first_failure() -> None:
    # 7,10,15,22 has chronological parity word 0101 (low bit first).
    block = arithmetic_from_word(7, 4, 0b0101)
    assert block.advance(7, 0) == (33, 2)
    assert block.minimum == -1

    term = AntihydraArithmeticTerm(0)
    h, balance, _left, _right, completed, halted = term.apply_physical_block(
        block, 7, 0, 0, 0, 0
    )
    assert (h, balance, completed, halted) == (7, -1, 1, True)


def test_repeated_engine_execution_has_distinct_charged_publications() -> None:
    engine = CylinderEngine()
    first = engine.execute(64)
    second = engine.execute(64)
    first.require_source()
    second.require_source()
    assert first is not second
    rows = [row for row in engine.ledger.inventory() if row.role == "physical_result"]
    assert len(rows) == 2
    assert all(row.entries == 1 and row.nodes == 2 for row in rows)
    audit = audit_registered_payloads(engine.ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)


@pytest.mark.parametrize(
    "field,offset",
    (
        ("width", -1),
        ("residue", 1),
        ("output", 1),
        ("delta", 1),
        ("minimum", 1),
        ("parity_word", 1),
    ),
)
def test_retained_arithmetic_fields_are_bound_to_the_source_trajectory(
    field: str,
    offset: int,
) -> None:
    term = AntihydraArithmeticTerm(64)
    arithmetic = term.result()
    physical = term.physical_run()
    block = term.segments[0].cylinder
    replacement = getattr(block, field) + offset
    object.__setattr__(block, field, replacement)

    with pytest.raises(ValueError, match="arithmetic support was changed"):
        arithmetic.require_source()
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        physical.require_source()
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        term.physical_run()


def test_consistent_but_foreign_arithmetic_word_is_not_source_admissible() -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    original = term.segments[0]
    block = original.cylinder
    foreign = arithmetic_from_word(block.residue, block.width, block.parity_word ^ 1)
    term.segments[0] = ArithmeticSegment(original.start, foreign)

    with pytest.raises(ValueError, match="arithmetic support was changed"):
        result.require_source()


def test_boolean_segment_coordinate_is_rejected_by_runtime_and_audit() -> None:
    term = AntihydraArithmeticTerm(64)
    result = term.result()
    physical = term.physical_run()
    object.__setattr__(term.segments[0], "start", False)
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        result.require_source()
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        physical.require_source()
    audit = audit_registered_payloads(term.ledger)
    assert audit.forbidden_future_payloads + audit.unknown_payloads > 0


@pytest.mark.parametrize(
    "kind",
    (
        AntihydraRunKind.CLOCK,
        AntihydraRunKind.MODULAR,
        AntihydraRunKind.TAPE,
        AntihydraRunKind.TWISTED,
        AntihydraRunKind.SPACETIME,
        AntihydraRunKind.HASSE,
        AntihydraRunKind.HENSEL,
        AntihydraRunKind.MAHLER,
        AntihydraRunKind.TROPICAL,
        AntihydraRunKind.FACTOR,
    ),
)
def test_every_direct_observer_rejects_mutated_retained_support(
    kind: AntihydraRunKind,
) -> None:
    result = run(64)
    block = result.arithmetic_term.segments[0].cylinder
    object.__setattr__(block, "parity_word", block.parity_word ^ 1)

    with pytest.raises(ValueError, match="arithmetic support was changed"):
        observe_run(result, kind=kind, modulus=3, width=2, sign=1, precision=8)


def test_retained_support_rejects_forged_segment_and_cylinder_types() -> None:
    for field in ("segment", "cylinder"):
        term = AntihydraArithmeticTerm(64)
        result = term.result()
        if field == "segment":
            term.segments[0] = cast(ArithmeticSegment, object())
        else:
            object.__setattr__(term.segments[0], "cylinder", object())
        with pytest.raises(ValueError, match="arithmetic support was changed"):
            result.require_source()


def test_retained_support_validation_streams_and_charges_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(128)
    result = term.physical_run()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    original = workspace.segments
    before = term.ledger.counters.get("arithmetic_result_validation_reconstructions", 0)
    result.require_source()
    assert (
        term.ledger.counters["arithmetic_result_validation_reconstructions"] - before
        == term.audit_snapshot().segment_count
    )

    first = term.segments[0].cylinder
    object.__setattr__(first, "parity_word", first.parity_word ^ 1)

    def first_then_forbidden() -> Iterator[tuple[int, ArithmeticCylinder]]:
        yield next(original())
        raise AssertionError("validation eagerly reconstructed later segments")

    monkeypatch.setattr(workspace, "segments", first_then_forbidden)
    with pytest.raises(ValueError, match="arithmetic support was changed"):
        result.require_source()


def test_run_rejects_forged_arithmetic_publication_type() -> None:
    result = run(8)

    class ForgedArithmeticResult:
        def require_source(self) -> None:
            return None

    object.__setattr__(
        result.arithmetic_term,
        "_result",
        cast(ArithmeticResult, ForgedArithmeticResult()),
    )
    with pytest.raises(ValueError, match="unbound Antihydra arithmetic result"):
        result.require_source()


@pytest.mark.parametrize("extent", (256, 1024, 4096))
def test_public_arithmetic_operand_growth_stays_balanced(extent: int) -> None:
    term = AntihydraArithmeticTerm(extent, max_state_bits=extent + 4)
    result = term.result()
    assert result.h == _reference(extent)[0]
    operand_bits = sum(
        value
        for name, value in term.ledger.counters.items()
        if name.endswith("operand_bits")
    )
    # Includes source discovery, coefficient construction, and public endpoint
    # projection. The bound rejects growing-exact-source replay at each run.
    assert operand_bits <= 12 * extent * extent.bit_length()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    support_id = workspace.summary().support
    assert support_id is not None
    support = workspace.support_node(support_id)
    assert support.saturated and support.branch_word is None
    assert support.children is None
