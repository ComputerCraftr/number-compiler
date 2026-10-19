"""Primitive directed transfers share the canonical result memo."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.tiles.tile_directed_transfer_memo import (
    lookup_directed_transfer,
    lookup_prepared_directed_transfer,
    prepare_directed_transfer,
    publish_directed_transfer,
    publish_prepared_directed_transfer,
)
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import DirectedTransferKey
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.assertions import assert_rejected_atomically
from tests.support.dataclass_records import replace_record
from tests.support.tile_kernel import make_tile_runtime_source

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileLease
    from number_compiler.resources.ledger import ResourceLedger


def _binding() -> tuple[
    ResourceLedger,
    CompletedResultArena,
    PrimitiveTileKernelAdapter,
    TileLease,
    DirectedTransferKey,
    int,
]:
    ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(3), (0, 1, 2, 3))
    )
    incoming = adapter.initial_ports(action)[0]
    state = incoming
    law = adapter.primitive_law(action)
    for symbol in (0, 1, 2, 3):
        state = law.advance(BoundarySide.LEFT, state, symbol)
    key = DirectedTransferKey(
        action,
        source.tile,
        0,
        incoming,
        adapter.wiring(action),
    )
    return ledger, scheduler.results, adapter, source, key, state


def test_directed_transfer_reuses_exact_exit_and_retires_with_input() -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    assert lookup_directed_transfer(results, key) is None
    assert publish_directed_transfer(results, key, outgoing) == outgoing
    before = ledger.snapshot()
    assert lookup_directed_transfer(results, key) == outgoing
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert after.counters["tile_directed_transfer_early_hits"] == 1
    source.close()
    assert key not in results._memo
    assert not results._reverse


def test_directed_transfer_direction_and_scan_order_are_distinct() -> None:
    _ledger, results, adapter, source, left_key, left_exit = _binding()
    law = adapter.primitive_law(left_key.action)
    right_exit = adapter.initial_ports(left_key.action)[1]
    for symbol in reversed((0, 1, 2, 3)):
        right_exit = law.advance(BoundarySide.RIGHT, right_exit, symbol)
    right_key = replace(
        left_key,
        side=1,
        incoming_state=adapter.initial_ports(left_key.action)[1],
    )
    try:
        publish_directed_transfer(results, left_key, left_exit)
        publish_directed_transfer(results, right_key, right_exit)
        assert lookup_directed_transfer(results, left_key) == left_exit
        assert lookup_directed_transfer(results, right_key) == right_exit
        assert left_key != right_key
    finally:
        source.close()


def test_directed_transfer_numeric_aliases_reject_before_lookup() -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    try:
        publish_directed_transfer(results, key, outgoing)
        for field, bad in (
            ("side", False),
            ("side", 0.0),
            ("incoming_state", True),
            ("incoming_state", 0.0),
        ):
            malformed = replace_record(key, {field: bad})
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                lookup_directed_transfer(results, malformed)
            after = ledger.snapshot()
            assert (after.entries, after.nodes, after.counters) == (
                before.entries,
                before.nodes,
                before.counters,
            )
    finally:
        source.close()


def test_directed_transfer_rejects_composite_action_and_boolean_exit() -> None:
    ledger, results, adapter, source, key, outgoing = _binding()
    try:
        composite = adapter.power(key.action, 2)
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="primitive"):
            lookup_directed_transfer(
                results,
                replace(
                    key,
                    action=composite,
                ),
            )
        with pytest.raises(TypeError, match="exact integer"):
            publish_directed_transfer(results, key, bool(outgoing))
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
    finally:
        source.close()


def test_directed_transfer_publication_rolls_back_at_budget() -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    try:
        ledger.max_cache_entries = ledger.entries
        before = ledger.snapshot()
        with pytest.raises(BlockContextBudgetExceeded):
            publish_directed_transfer(results, key, outgoing)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert not results._memo
        assert not results._reverse
    finally:
        source.close()


def test_directed_transfer_has_read_only_independent_inventory() -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    try:
        publish_directed_transfer(results, key, outgoing)
        before = ledger.snapshot()
        metrics = collect_ledger_metrics(ledger)
        assert ledger.snapshot() == before
        assert metrics.resource_audit_complete == 1
        assert metrics.resource_accounting_mismatch == 0
    finally:
        source.close()


def test_prepared_directed_transfer_binds_exact_validated_key() -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    try:
        request = prepare_directed_transfer(results, key)
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            replace(request, key=replace(key, incoming_state=True))
        with pytest.raises(ValueError, match="cardinality changed"):
            replace(request, exit_cardinality=True)
        assert ledger.snapshot() == before
        assert (
            publish_prepared_directed_transfer(
                results,
                request,
                outgoing,
            )
            == outgoing
        )
    finally:
        source.close()


def test_prepared_directed_transfer_rechecks_tile_liveness() -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    request = prepare_directed_transfer(results, key)
    source.close()
    before = ledger.snapshot()
    with pytest.raises((KeyError, ValueError)):
        lookup_prepared_directed_transfer(results, request)
    with pytest.raises((KeyError, ValueError)):
        publish_prepared_directed_transfer(results, request, outgoing)
    assert ledger.snapshot() == before
    assert key not in results._memo
    assert not results._reverse


def test_prepared_directed_transfer_rejects_foreign_arena() -> None:
    _ledger, results, _adapter, source, key, _outgoing = _binding()
    _other_ledger, other, _other_adapter, other_source, _other_key, _ = _binding()
    try:
        request = prepare_directed_transfer(results, key)
        assert_rejected_atomically(
            other.ledger,
            lambda: lookup_prepared_directed_transfer(other, request),
            ValueError,
            match="another result arena",
        )
    finally:
        source.close()
        other_source.close()


@pytest.mark.parametrize(
    ("target", "field", "bad"),
    (
        ("key", "incoming_state", True),
        ("key", "incoming_state", 0.0),
        ("key", "side", True),
        ("action", "local_id", 1_000_000),
        ("input", "local_id", 1_000_000),
        ("signature", "local_id", 1_000_000),
        ("wiring", "orientation", True),
    ),
)
def test_prepared_transfer_rejects_same_object_key_mutation(
    target: str,
    field: str,
    bad: object,
) -> None:
    ledger, results, _adapter, source, key, outgoing = _binding()
    action = type(key.action)(key.action.owner, key.action.kind, key.action.local_id)
    tile = type(key.input)(key.input.owner, key.input.kind, key.input.local_id)
    old_signature = key.wiring.signature
    signature = type(old_signature)(
        old_signature.owner,
        old_signature.kind,
        old_signature.local_id,
    )
    wiring = ResultWiring(signature, key.wiring.orientation, key.wiring.phase)
    prepared_key = DirectedTransferKey(
        action,
        tile,
        key.side,
        key.incoming_state,
        wiring,
    )
    try:
        publish_directed_transfer(results, key, outgoing)
        request = prepare_directed_transfer(results, prepared_key)
        mutation_target = {
            "key": prepared_key,
            "action": action,
            "input": tile,
            "signature": signature,
            "wiring": wiring,
        }[target]
        object.__setattr__(mutation_target, field, bad)
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            lookup_prepared_directed_transfer(results, request)
        with pytest.raises((TypeError, ValueError)):
            publish_prepared_directed_transfer(results, request, outgoing)
        assert ledger.snapshot() == before
        assert results._memo[key] == outgoing
    finally:
        source.close()
