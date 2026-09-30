"""Completed tile results retain output roots without owning future content."""

from __future__ import annotations

import pickle
from copy import copy, deepcopy
from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_result_records import (
    PoweredInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseKey as _ReverseKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseValue as _ReverseValue,
)
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileID
from tests.support.assertions import assert_rejected_atomically
from tests.support.tile_results import (
    _published_setup,
    _setup,
    assert_retention_and_peaks_unchanged,
)


def test_completed_result_warm_lookup_pins_output_and_retires_with_input() -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    published = results.publish(key, result)
    assert type(published) is ResultLease
    assert published.result == result
    output_lease.close()
    assert tiles.resolve(published.output).symbol == 0
    warm = results.lookup(key)
    assert warm is not None and warm.result == result
    assert results.retained_results == 1
    assert ledger.counters["completed_result_early_hits"] == 1

    input_lease.close()
    assert results.retained_results == 0
    assert published.output == result.output
    warm.close()
    published.close()
    with pytest.raises(ValueError, match="stale or unpublished"):
        tiles.resolve(result.output)


def test_observed_input_ports_validate_before_result_publication() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    observed = replace(result, observed_input_ports=(1,))
    held = results.publish(key, observed)
    assert held.result.observed_input_ports == (1,)
    held.close()

    with pytest.raises(TypeError, match="observed input ports"):
        replace(result, observed_input_ports=(True,))
    before = tuple(
        (item.owner, item.entries, item.nodes) for item in ledger.inventory()
    )
    with pytest.raises(ValueError, match="outside its finite domain"):
        results.publish(key, replace(result, observed_input_ports=(3,)))
    assert (
        tuple((item.owner, item.entries, item.nodes) for item in ledger.inventory())
        == before
    )
    output_lease.close()
    input_lease.close()


def test_warm_result_port_admission_is_read_only_semantic_validation() -> None:
    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        key,
        _unused_result_binding,
        held,
        before,
    ) = _published_setup()
    warm = results.lookup(key)
    assert warm is not None
    after = ledger.snapshot()
    assert after.counters.get("semantic_function_evaluations", 0) == (
        before.counters.get("semantic_function_evaluations", 0)
    )
    assert after.counters.get("semantic_function_decision_visits", 0) == (
        before.counters.get("semantic_function_decision_visits", 0)
    )
    assert after.counters["completed_result_port_validation_requests"] > (
        before.counters.get("completed_result_port_validation_requests", 0)
    )
    warm.close()
    held.close()
    output_lease.close()
    input_lease.close()


def test_result_lease_inspection_is_counter_neutral_but_still_validates() -> None:
    (
        ledger,
        _,
        _,
        _unused_results_binding,
        input_lease,
        output_lease,
        _unused_key_binding,
        result,
        held,
        before,
    ) = _published_setup()
    assert held.output == result.output
    assert held.result == result
    assert ledger.snapshot() == before
    old_ports = result.outgoing_ports
    object.__setattr__(result, "outgoing_ports", (99,))
    try:
        with pytest.raises(ValueError, match="finite domain"):
            _ = held.result
        assert ledger.snapshot() == before
    finally:
        object.__setattr__(result, "outgoing_ports", old_ports)
    held.close()
    output_lease.close()
    input_lease.close()


def test_same_input_output_has_one_reverse_membership() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    output_lease.close()
    same = replace(result, output=input_lease.tile)
    lease = results.publish(key, same)
    inventory = {item.owner: item for item in ledger.inventory()}
    assert inventory[results._reverse_owner].entries == 2  # head + one membership
    lease.close()
    input_lease.close()
    assert results.retained_results == 0
    assert len(results._reverse) == 0


def test_input_retirement_removes_result_but_result_lease_keeps_output() -> None:
    _, _, tiles, results, input_lease, output_lease, key, result = _setup()
    lease = results.publish(key, result)
    output_lease.close()
    input_lease.close()
    assert results.retained_results == 0
    assert tiles.point(lease.output, 0) == 0
    lease.close()


def test_result_close_rejects_swapped_tile_and_foreign_issuer_before_release() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    lease = results.publish(key, result)
    original_tile = lease._tile
    original_issuer = lease._issuer
    try:
        lease._tile = input_lease
        before = ledger.entries, ledger.nodes, ledger.inventory()
        with pytest.raises(ValueError, match="pins another output"):
            lease.close()
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == before
        assert lease._closed is False
        lease._tile = original_tile

        lease._issuer = cast(CompletedResultArena, object())
        before = ledger.entries, ledger.nodes, ledger.inventory()
        with pytest.raises(ValueError, match="issuer"):
            lease.close()
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == before
        assert lease._closed is False
    finally:
        lease._tile = original_tile
        lease._issuer = original_issuer
        lease.close()
        output_lease.close()
        input_lease.close()


@pytest.mark.parametrize("bad_port", (True, 1.0, -1, 3))
def test_invalid_ports_reject_before_warm_lookup_or_mutation(bad_port: object) -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    lease = results.publish(key, result)
    before = ledger.snapshot()
    bad = replace(key, ports=(cast("int", bad_port),))
    with pytest.raises((TypeError, ValueError)):
        results.lookup(bad)
    assert ledger.snapshot() == before
    lease.close()
    output_lease.close()
    input_lease.close()


def test_foreign_action_and_signature_reject_before_lookup() -> None:
    (
        ledger,
        actions,
        _,
        results,
        input_lease,
        output_lease,
        key,
        _unused_result_binding,
        lease,
        before,
    ) = _published_setup()
    foreign = replace(
        key,
        action=FieldCellActionID(ArenaToken("foreign"), key.action.kind, 0),
    )
    with pytest.raises(ValueError):
        results.lookup(foreign)
    wrong_signature = replace(
        key,
        wiring=replace(
            key.wiring,
            signature=type(key.wiring.signature)(
                ArenaToken("foreign-signature"),
                key.wiring.signature.kind,
                0,
            ),
        ),
    )
    with pytest.raises(ValueError):
        results.lookup(wrong_signature)
    assert ledger.snapshot() == before
    assert actions.signature(key.action) == key.wiring.signature
    lease.close()
    output_lease.close()
    input_lease.close()


def test_exhausted_budget_rejects_publication_without_retained_mutation() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    ledger.tighten_limits(None, ledger.entries)
    before = ledger.snapshot()
    with pytest.raises(Exception, match="cache budget exceeded"):
        results.publish(key, result)
    after = ledger.snapshot()
    assert (
        after.entries,
        after.nodes,
        after.peak_entries,
        after.peak_nodes,
        after.inventory,
    ) == (
        before.entries,
        before.nodes,
        before.peak_entries,
        before.peak_nodes,
        before.inventory,
    )
    assert results.retained_results == 0
    assert not results._reverse
    output_lease.close()
    input_lease.close()


def test_constructor_rejects_unowned_action_callbacks() -> None:
    ledger, actions, tiles, results, input_lease, output_lease, _, _ = _setup()
    assert_rejected_atomically(
        ledger,
        lambda: CompletedResultArena(
            tiles,
            results.interfaces,
            action_authority=object(),
            validate_action=lambda _value: None,
            signature_for=actions.signature,
        ),
        ValueError,
        match="real action authority",
    )
    output_lease.close()
    input_lease.close()


@pytest.mark.parametrize(
    "name",
    (
        "validate_input",
        "validate_output",
        "validate_fused_action",
        "validate_fused_wiring",
    ),
)
def test_constructor_rejects_unbound_optional_action_authority_hooks(name: str) -> None:
    ledger, actions, tiles, results, input_lease, output_lease, _, _ = _setup()
    setattr(actions, name, lambda *_args: None)
    assert_rejected_atomically(
        ledger,
        lambda: CompletedResultArena(
            tiles,
            results.interfaces,
            action_authority=actions,
            validate_action=actions.validate_action,
            signature_for=actions.signature,
        ),
        ValueError,
        match="bound .* validator",
    )
    output_lease.close()
    input_lease.close()


@pytest.mark.parametrize("fail_at", range(1, 7))
def test_reverse_index_fault_rolls_back_current_state_and_old_links(
    monkeypatch: pytest.MonkeyPatch,
    fail_at: int,
) -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    first = results.publish(key, result)
    second_key = replace(key, ports=(2,))
    before_entries, before_nodes = ledger.entries, ledger.nodes
    before_peak = ledger.peak_entries
    before_memo = dict(results._memo)
    before_reverse = dict(results._reverse)
    before_refs = dict(tiles._refs)
    before_leases = dict(tiles._leases)
    calls = 0
    original = type(results)._write_reverse

    def fail_boundary(
        self: CompletedResultArena, reverse_key: _ReverseKey, value: _ReverseValue
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == fail_at:
            raise RuntimeError("injected reverse publication failure")
        original(self, reverse_key, value)

    monkeypatch.setattr(type(results), "_write_reverse", fail_boundary)
    with pytest.raises(RuntimeError, match="injected"):
        results.publish(second_key, result)
    assert (ledger.entries, ledger.nodes) == (before_entries, before_nodes)
    assert dict(results._memo) == before_memo
    assert dict(results._reverse) == before_reverse
    assert dict(tiles._refs) == before_refs
    assert dict(tiles._leases) == before_leases
    assert ledger.peak_entries >= max(before_peak, before_entries + 4)
    first.close()
    output_lease.close()
    input_lease.close()


def test_result_extent_must_equal_exact_output_tile_extent() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="disagrees"):
        results.publish(key, replace(result, relative_extent=0))
    assert_retention_and_peaks_unchanged(ledger, before)
    output_lease.close()
    input_lease.close()


def test_result_lease_rejects_copy_serialization_close_and_corruption() -> None:
    _, _, _, results, input_lease, output_lease, key, result = _setup()
    lease = results.publish(key, result)
    with pytest.raises(TypeError, match="issued"):
        ResultLease(results, key, result, lease._tile, object())
    with pytest.raises(TypeError, match="cannot be copied"):
        copy(lease)
    with pytest.raises(TypeError, match="cannot be copied"):
        deepcopy(lease)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(lease)
    original_key = lease._key
    object.__setattr__(
        lease,
        "_key",
        replace(key, input=TileID(ArenaToken("foreign"), "canonical-tile", 0)),
    )
    with pytest.raises(ValueError, match="different arena"):
        _ = lease.result
    object.__setattr__(lease, "_key", original_key)
    lease.close()
    with pytest.raises(ValueError, match="closed"):
        _ = lease.result
    with pytest.raises(ValueError, match="closed"):
        _ = lease.output
    output_lease.close()
    input_lease.close()


def test_ledger_query_eviction_clears_result_and_reverse_indexes() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    lease = results.publish(key, result)
    evicted = ledger.evict_query_memos()
    assert results._memo_owner in evicted
    assert results.retained_results == 0
    assert not results._reverse
    assert lease.result == result
    lease.close()
    output_lease.close()
    input_lease.close()


def test_independent_result_inventory_detects_reverse_link_corruption() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    lease = results.publish(key, result)
    containers = dict(ledger.iter_containers())
    approved, invalid = audit_tile_results(results, containers)
    assert not invalid
    assert id(results) in approved
    member = next(
        reverse_key
        for reverse_key in results._reverse
        if type(reverse_key).__name__ == "_ReverseMember"
    )
    original = results._reverse[member]
    results._reverse[member] = cast(_ReverseValue, None)
    _, damaged = audit_tile_results(results, containers)
    assert damaged
    results._reverse[member] = original
    lease.close()
    output_lease.close()
    input_lease.close()


def test_public_result_inventory_separates_semantic_bindings_and_complete_results() -> (
    None
):
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, _, tiles, results, source, output, key, result = _setup()
    interface_key = PoweredInterfaceKey(key.action, key.input, key.wiring)
    results.publish_interface(interface_key, result.outgoing)
    with results.publish(key, result) as held:
        before = ledger.snapshot()
        metrics = collect_ledger_metrics(ledger)
        assert ledger.snapshot() == before
        assert metrics.tile_execution_memo_entries == 2
        assert (
            metrics.completed_result_entries == metrics.powered_interface_entries == 1
        )
        assert metrics.completed_result_reverse_index_entries == len(results._reverse)
        assert metrics.canonical_tile_nodes == len(tiles._nodes)
        assert metrics.tile_root_leases == len(tiles._leases)
        assert (
            metrics.resource_audit_complete
            == metrics.representation_boundary_complete
            == 1
        )
        assert (
            metrics.resource_accounting_mismatch
            == metrics.forbidden_future_payloads
            == 0
        )
        ledger.evict_query_memos()
        after = collect_ledger_metrics(ledger)
        assert after.completed_result_entries == after.powered_interface_entries == 0
        assert after.completed_result_reverse_index_entries == 0
        assert held.result == result
    source.close()
    output.close()
    final = collect_ledger_metrics(ledger)
    assert final.canonical_tile_nodes == final.tile_root_leases == 0
    assert final.canonical_tile_peak >= 2
    assert final.tile_retirements == 2


def test_causal_region_result_uses_shared_memo_and_exact_output_content() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, tiles, results, source, output, key, result = _setup()
    parent = tiles.join(source.tile, output.tile)
    root_key = replace(key, input=parent.tile)
    left_key, right_key = (replace(root_key, region=(offset, 0)) for offset in (0, 1))
    with (
        results.publish(left_key, result) as left,
        results.publish(right_key, result) as right,
    ):
        assert left.output == right.output
        assert results.retained_results == 2
        _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
        assert not invalid
        assert results.lookup(root_key) is None
        repeated = results.lookup(left_key)
        assert repeated is not None
        with repeated:
            assert repeated.result == result
        parent.close()
        assert results.retained_results == 0
        assert left.output == right.output
    output.close()
    source.close()


def test_whole_causal_region_normalizes_to_existing_complete_result() -> None:
    _, _, _, results, source, output, key, result = _setup()
    whole = replace(key, region=(0, 0))
    with results.publish(key, result):
        found = results.lookup(whole)
        assert found is not None
        with found:
            assert found.result == result
        with results.publish(whole, result):
            assert results.retained_results == 1
        assert next(iter(results._memo)) == key
    output.close()
    source.close()


@pytest.mark.parametrize(
    "region", ((True, 0), (0, 0.0), (0, -1), (-1, 0), (0, 2), (1, 1), (2, 0))
)
def test_causal_region_rejects_before_lookup_or_ledger_mutation(
    region: tuple[bool, int] | tuple[int, float] | tuple[int, int],
) -> None:
    ledger, _, tiles, results, source, output, key, _result = _setup()
    parent = tiles.join(source.tile, output.tile)
    request = replace(key, input=parent.tile, region=cast("tuple[int, int]", region))
    assert_rejected_atomically(
        ledger, lambda: results.lookup(request), (TypeError, ValueError)
    )
    parent.close()
    output.close()
    source.close()


def test_causal_region_cannot_publish_an_incomplete_parent_as_a_leaf() -> None:
    ledger, _, tiles, results, source, output, key, result = _setup()
    parent = tiles.join(source.tile, output.tile)
    request = replace(key, input=parent.tile, region=(0, 0))
    wrong = replace(
        result, output=parent.tile, relative_extent=tiles.resolve(parent.tile).extent
    )
    before = ledger.entries, ledger.nodes, dict(results._memo), dict(results._reverse)
    with pytest.raises(ValueError, match="output level"):
        results.publish(request, wrong)
    assert (
        ledger.entries,
        ledger.nodes,
        dict(results._memo),
        dict(results._reverse),
    ) == before
    parent.close()
    output.close()
    source.close()
