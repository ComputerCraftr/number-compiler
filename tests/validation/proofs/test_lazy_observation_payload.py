"""Injected old residue/prefix bindings must fail independent retained audits."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from devtools.proofs.lazy_collatz import (
    CarryRangeSummary,
    CarryRangeTransfer,
    CollatzLazyView,
    LazyCollatzApplication,
    _SummaryKey,
)
from devtools.proofs.lazy_collatz_range import _RangeKey
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.projection.microblock_cache import ExactMicroblock, MicroblockKey
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


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
    if term.effect is None:
        raise AssertionError("test requires a positive powered term")
    return term._compiler.reference(term.effect)


def test_exact_microblock_payload_under_an_unrelated_role_is_rejected() -> None:
    term = PoweredCollatzTerm(0x91AD, 3)
    owner = term._ledger.register("forged-microblock-query", "query_memo")
    storage: LedgerDict[object, object]
    storage = term._ledger.make_dict(owner)
    term._ledger.reserve(owner, entries=1)
    storage[MicroblockKey(_microblock_program(term), 3, 0, 0, "binary")] = (
        ExactMicroblock(5, 3)
    )
    assert_forbidden(term._ledger)


def test_spoofed_exact_microblock_role_without_cache_owner_is_rejected() -> None:
    term = PoweredCollatzTerm(0x91AD, 3)
    owner = term._ledger.register(
        "forged-microblock-owner", "exact_microblock", "INDEX_OWNED"
    )
    storage: LedgerDict[object, object]
    storage = term._ledger.make_dict(owner)
    term._ledger.reserve(owner, entries=1)
    storage[MicroblockKey(_microblock_program(term), 3, 0, 0, "binary")] = (
        ExactMicroblock(1, 1)
    )
    assert_forbidden(term._ledger)


def test_owned_capped_microblocks_remain_allowed() -> None:
    term = PoweredCollatzTerm(140137, 11)
    from number_compiler.projection.lazy_radix import collatz_radix_digit

    assert collatz_radix_digit(term, 3, 3) == 2
    cache = term._microblocks
    assert len(cache) <= cache.MAX_ENTRIES
    assert cache.payload_bytes <= cache.MAX_PAYLOAD_BYTES
    report = collect_ledger_metrics(term._ledger)
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
    if memo == "prefix":
        result = app.range_summary(prefix)
        app.ledger.reserve(app._summary_owner, entries=1, nodes=1)
        app._summaries[_SummaryKey(view.program, 7)] = result
        # Callback omission cannot conceal an actual map's relation.
        app.ledger.register_container(
            app._summary_owner,
            app._summaries,
            node_count=lambda: len(app._summaries),
            payloads=lambda: (),
        )
    elif memo == "mul3":
        transfer = CarryRangeTransfer(app.mul3_summary(prefix))
        app._mul3_summaries[_SummaryKey(view.program, 7)] = transfer
    else:
        result = app._range_evaluator.event_summary(view.program, 7)
        app._range_evaluator._events[_RangeKey(view.program, 0, 7)] = result
    assert_forbidden(app.ledger)


def test_prefix_records_cannot_get_source_authority_from_foreign_zero_id() -> None:
    app, _ = app_and_future()
    foreign = ActionProgramID(ArenaToken("lazy-collatz"), "program", 0)
    app.ledger.reserve(app._summary_owner, entries=1, nodes=1)
    app._summaries[_SummaryKey(foreign, 8)] = CarryRangeSummary(8, 0, 1, 7)
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
    storage.append((_SummaryKey(view.program, 7), CarryRangeSummary(7, 0, 0, 6)))
    assert_forbidden(app.ledger)


def test_original_prefixes_and_aligned_future_carry_cells_remain_distinct_and_allowed() -> (
    None
):
    app, view = app_and_future()
    app.range_summary(app.initial)
    app.mul3_summary(app.initial)
    app._range_evaluator.event_summary(app.initial.program, app.initial.width)
    for width in range(1, 17):
        app.range_summary(CollatzLazyView(view.source, view.program, width, False))
    assert app._summaries and app._mul3_summaries and app._range_evaluator._events
    assert any(key.program == view.program for key in app._range_evaluator._ranges)
    assert collect_ledger_metrics(app.ledger).representation_boundary_complete == 1


def test_future_one_cell_or_overlapping_binding_cannot_impersonate_a_dyadic_action() -> (
    None
):
    app, view = app_and_future()
    effect = app._range_evaluator.range_effect(view.program, 0, 8)
    action = app._range_evaluator._intern(effect)
    app._range_evaluator._ranges[_RangeKey(view.program, 1, 8)] = action
    assert_forbidden(app.ledger)
