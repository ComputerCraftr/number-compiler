"""Injected old residue/prefix bindings must fail independent retained audits."""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import TYPE_CHECKING, cast

import pytest

from devtools.verification.collatz_carry_ranges import (
    CarryRangeSummary,
    CarryRangeTransfer,
)
from devtools.verification.lazy_collatz import (
    CollatzLazyView,
    LazyCollatzApplication,
    SummaryKey,
)
from devtools.verification.lazy_collatz_range import RangeKey
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.resources.ledger import ResourceScope
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


def _forensic_mapping(value: object) -> MutableMapping[object, object]:
    """Type an owner snapshot's backing store for deliberate corruption cases."""
    if not isinstance(value, MutableMapping):
        raise AssertionError("payload audit did not expose a mutable backing store")
    return cast(MutableMapping[object, object], value)


def app_and_future() -> tuple[LazyCollatzApplication, CollatzLazyView]:
    seed = 0x91AD
    source = tuple((seed >> index) & 1 for index in range(seed.bit_length()))
    app = LazyCollatzApplication(2, 1, source)
    return app, app.advance_physical(1).view


def assert_forbidden(ledger: ResourceLedger) -> None:
    before = ledger.snapshot()
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0
    assert report.resource_accounting_mismatch == 0
    assert ledger.snapshot() == before


def _microblock_program(term: PoweredCollatzTerm) -> ActionProgramID:
    return term.source_image_program()


def test_exact_microblock_payload_under_an_unrelated_role_is_rejected() -> None:
    term = PoweredCollatzTerm(0x91AD, 3)
    owner = term.resource_ledger.register("forged-microblock-query", "query_memo")
    storage: LedgerDict[object, object]
    storage = term.resource_ledger.make_dict(owner)
    term.resource_ledger.reserve(owner, entries=1)
    storage[MicroblockKey(_microblock_program(term), 3, 0, 0, "binary")] = (
        ExactMicroblock(5, 3)
    )
    assert_forbidden(term.resource_ledger)


def test_spoofed_exact_microblock_role_without_cache_owner_is_rejected() -> None:
    term = PoweredCollatzTerm(0x91AD, 3)
    owner = term.resource_ledger.register(
        "forged-microblock-owner", "exact_microblock", ResourceScope.INDEX_OWNED
    )
    storage: LedgerDict[object, object]
    storage = term.resource_ledger.make_dict(owner)
    term.resource_ledger.reserve(owner, entries=1)
    storage[MicroblockKey(_microblock_program(term), 3, 0, 0, "binary")] = (
        ExactMicroblock(1, 1)
    )
    assert_forbidden(term.resource_ledger)


def test_owned_capped_microblocks_remain_allowed() -> None:
    term = PoweredCollatzTerm(140137, 11)
    from number_compiler.projection.lazy_radix import collatz_radix_digit

    assert collatz_radix_digit(term, 3, 3) == 2
    cache = MicroblockCache.shared(term.resource_ledger)
    assert len(cache) <= cache.MAX_ENTRIES
    assert cache.payload_bytes <= cache.MAX_PAYLOAD_BYTES
    report = collect_ledger_metrics(term.resource_ledger)
    assert report.forbidden_future_payloads == 0
    assert report.representation_boundary_complete == 1
    assert report.resource_audit_complete == 1


def test_microblock_record_rejects_unbounded_or_numeric_alias_payloads() -> None:
    with pytest.raises(ValueError):
        ExactMicroblock(1 << 64, 64)
    with pytest.raises(ValueError):
        ExactMicroblock(0, 65)
    with pytest.raises(ValueError):
        ExactMicroblock(True, 1)


@pytest.mark.parametrize("memo", ["prefix", "mul3", "event"])
def test_injected_future_prefix_observations_fail_actual_container_audit(
    memo: str,
) -> None:
    app, view = app_and_future()
    prefix = CollatzLazyView(view.source, view.program, 7, False)
    application_snapshot = app.payload_audit_snapshot()
    if memo == "prefix":
        result = app.range_summary(prefix)
        summary_store = _forensic_mapping(application_snapshot.summary_store)
        app.ledger.reserve(application_snapshot.summary_owner, entries=1, nodes=1)
        summary_store[SummaryKey(view.program, 7)] = result
        # Callback omission cannot conceal an actual map's relation.
        app.ledger.register_container(
            application_snapshot.summary_owner,
            summary_store,
            node_count=lambda: len(summary_store),
            payloads=lambda: (),
        )
    elif memo == "mul3":
        transfer = CarryRangeTransfer(app.mul3_summary(prefix))
        app.ledger.reserve(application_snapshot.mul3_owner, entries=1, nodes=1)
        _forensic_mapping(application_snapshot.mul3_store)[
            SummaryKey(view.program, 7)
        ] = transfer
    else:
        result = app.range_evaluator.event_summary(view.program, 7)
        range_snapshot = app.range_evaluator.payload_audit_snapshot()
        app.ledger.reserve(range_snapshot.events_owner, entries=1, nodes=1)
        _forensic_mapping(range_snapshot.events_store)[RangeKey(view.program, 0, 7)] = (
            result
        )
    assert_forbidden(app.ledger)


def test_prefix_records_cannot_get_source_authority_from_foreign_zero_id() -> None:
    app, _ = app_and_future()
    foreign = ActionProgramID(ArenaToken("lazy-collatz"), "program", 0)
    application_snapshot = app.payload_audit_snapshot()
    app.ledger.reserve(application_snapshot.summary_owner, entries=1, nodes=1)
    _forensic_mapping(application_snapshot.summary_store)[SummaryKey(foreign, 8)] = (
        CarryRangeSummary(8, 0, 1, 7)
    )
    assert_forbidden(app.ledger)


@pytest.mark.parametrize("role", ["query_memo", "exact_source"])
def test_moving_a_future_prefix_pair_into_another_role_does_not_authorize_it(
    role: str,
) -> None:
    app, view = app_and_future()
    owner = app.ledger.register("renamed-observation", role)
    storage: LedgerList[object]
    storage = app.ledger.make_list(owner)
    app.ledger.reserve(owner, entries=1, nodes=1)
    storage.append((SummaryKey(view.program, 7), CarryRangeSummary(7, 0, 0, 6)))
    assert_forbidden(app.ledger)


def test_original_prefixes_and_aligned_future_carry_cells_remain_distinct_and_allowed() -> (
    None
):
    app, view = app_and_future()
    app.range_summary(app.initial)
    app.mul3_summary(app.initial)
    app.range_evaluator.event_summary(app.initial.program, app.initial.width)
    for width in range(1, 17):
        app.range_summary(CollatzLazyView(view.source, view.program, width, False))
    application_snapshot = app.payload_audit_snapshot()
    range_snapshot = app.range_evaluator.audit_snapshot()
    range_payload_snapshot = app.range_evaluator.payload_audit_snapshot()
    assert _forensic_mapping(application_snapshot.summary_store)
    assert application_snapshot.mul3_payloads
    assert _forensic_mapping(range_payload_snapshot.events_store)
    assert any(key.program == view.program for key in range_snapshot.ranges)
    assert collect_ledger_metrics(app.ledger).representation_boundary_complete == 1


def test_future_one_cell_or_overlapping_binding_cannot_impersonate_a_dyadic_action() -> (
    None
):
    app, view = app_and_future()
    effect = app.range_evaluator.range_effect(view.program, 0, 8)
    action = app.range_evaluator.intern_record(effect)
    range_payload_snapshot = app.range_evaluator.payload_audit_snapshot()
    # Range bindings are entry-accounted; the owned memo declares zero nodes
    # per entry, so reserve only the retained mapping slot.
    app.ledger.reserve(range_payload_snapshot.ranges_owner, entries=1)
    _forensic_mapping(range_payload_snapshot.ranges_store)[
        RangeKey(view.program, 1, 8)
    ] = action
    assert_forbidden(app.ledger)
