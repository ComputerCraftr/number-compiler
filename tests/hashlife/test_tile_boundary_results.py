"""Completed tile results retain output roots without owning future content."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    FusedInterfaceKey,
    PoweredInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseKey as _ReverseKey,
    ReverseValue as _ReverseValue,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileID
from tests.support.tile_results import _ChangingAlphabetAuthority, _setup


def test_boundary_operands_are_indexed_and_outgoing_tiles_are_leased() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics
    from number_compiler.resources.payload_audit import audit_registered_payloads
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    alphabet = tiles.resolve(key.input).alphabet
    incoming = tiles.leaf(alphabet, 2)
    outgoing = tiles.join(output_lease.tile, output_lease.tile)
    boundary_key = replace(
        key,
        boundaries=BoundaryTileOperands(
            BoundaryTileView(incoming.tile, -2, 1, 1),
            None,
        ),
    )
    boundary_result = replace(
        result,
        outgoing_boundaries=BoundaryTileOperands(
            None,
            BoundaryTileView(outgoing.tile, 3, 1, 0),
        ),
    )
    held = results.publish(boundary_key, boundary_result)
    assert len(held._boundary_tiles) == 1
    assert held.result.outgoing_boundaries.right is not None
    approved, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert not invalid and id(boundary_key) in approved
    payloads = audit_registered_payloads(ledger)
    assert (
        payloads.forbidden_future_payloads,
        payloads.unbounded_future_integers,
        payloads.unknown_payloads,
    ) == (0, 0, 0)
    ledger.bump("tile_boundary_transfer_requests", 2)
    ledger.bump("tile_boundary_transfer_frames", 5)
    ledger.bump("tile_boundary_transfer_parent_observations", 3)
    ledger.bump("tile_boundary_transfer_descents", 1)
    ledger.bump("tile_boundary_transfer_workspace_peak", 4)
    before_metrics = ledger.snapshot()
    metrics = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before_metrics
    assert metrics.boundary_tile_operand_references == 2
    assert metrics.boundary_tile_unique_live == 2
    assert metrics.boundary_tile_leases == metrics.boundary_tile_lease_peak == 1
    assert metrics.boundary_tile_operand_extent_total == 2
    assert metrics.boundary_tile_operand_source_offset_total == 0
    assert (
        metrics.tile_boundary_transfer_requests,
        metrics.tile_boundary_transfer_frames,
        metrics.tile_boundary_transfer_parent_observations,
        metrics.tile_boundary_transfer_descents,
        metrics.tile_boundary_transfer_workspace_peak,
    ) == (2, 5, 3, 1, 4)
    outgoing.close()
    assert tiles.resolve(held.result.outgoing_boundaries.right.tile).level == 1
    incoming.close()
    assert results.retained_results == 0
    assert held.result == boundary_result
    held.close()
    output_lease.close()
    input_lease.close()
    assert ledger.counters["completed_result_tile_retirements"] >= 1


def test_result_lease_reports_boundary_operands_after_memo_retirement() -> None:
    """Lease-owned result operands remain inventoried after their key is evicted."""
    from number_compiler.resources.metric_collection import collect_ledger_metrics
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, tiles, results, source, output, key, result = _setup()
    boundary = tiles.leaf(tiles.resolve(result.output).alphabet, 2)
    view = BoundaryTileView(boundary.tile, 3, 1)
    retained = replace(
        result,
        outgoing_boundaries=BoundaryTileOperands(None, view),
    )
    first = results.publish(key, retained)
    second = results.lookup(key)
    assert second is not None
    boundary.close()
    source.close()
    assert results.retained_results == 0
    assert results._leased_boundary_operands.records[view] == 2
    before = ledger.snapshot()
    metrics = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    assert metrics.boundary_tile_memo_operand_references == 0
    assert metrics.boundary_tile_leased_operand_references == 2
    assert metrics.boundary_tile_leased_operand_unique_live == 1
    assert metrics.boundary_tile_operand_references == 1
    assert metrics.boundary_tile_unique_live == 1
    assert metrics.boundary_tile_operand_extent_total == 1
    approved, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert not invalid and id(results._leased_boundary_operands.records) in approved
    results._leased_boundary_operands.records[view] = True
    _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert (results._leased_boundary_operands.owner, id(view)) in invalid
    results._leased_boundary_operands.records[view] = 2
    first.close()
    assert results._leased_boundary_operands.records[view] == 1
    second.close()
    assert not results._leased_boundary_operands.records
    output.close()


def test_boundary_operands_reject_wrong_scope_and_shape_before_warm_lookup() -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    held = results.publish(key, result)
    before = ledger.snapshot()
    foreign = TileID(ArenaToken("foreign-boundary"), "canonical-tile", 0)
    bad_values = (
        BoundaryTileOperands(BoundaryTileView(foreign, 0, 1), None),
        BoundaryTileOperands(BoundaryTileView(key.input, 0, 2), None),
    )
    for boundaries in bad_values:
        with pytest.raises(ValueError):
            results.lookup(replace(key, boundaries=boundaries))
        assert ledger.snapshot() == before
    with pytest.raises(TypeError):
        results.lookup(replace(key, boundaries=True))  # type: ignore[arg-type]
    assert ledger.snapshot() == before
    held.close()
    output_lease.close()
    input_lease.close()


def test_boundary_tile_views_validate_and_identify_exact_source_slices() -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    parent = tiles.join(key.input, key.input)
    first = BoundaryTileView(parent.tile, 7, 1, 0, 0)
    second = BoundaryTileView(parent.tile, 7, 1, 0, 1)
    assert first != second and hash(first) != hash(second)
    first_key = replace(
        key,
        input=parent.tile,
        boundaries=BoundaryTileOperands(first, None),
    )
    second_key = replace(
        key,
        input=parent.tile,
        boundaries=BoundaryTileOperands(second, None),
    )
    first_lease = results.publish(first_key, result)
    second_lease = results.publish(second_key, result)
    warm_first = results.lookup(first_key)
    warm_second = results.lookup(second_key)
    assert warm_first is not None and warm_second is not None
    assert first_key != second_key and results.retained_results == 2
    warm_first.close()
    warm_second.close()
    before = ledger.entries, ledger.nodes, dict(results._memo)
    for offset in (True, 1.5, -1):
        with pytest.raises((TypeError, ValueError)):
            BoundaryTileView(parent.tile, source_offset=offset)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="source offset"):
        results.lookup(
            replace(
                key,
                input=parent.tile,
                boundaries=BoundaryTileOperands(
                    BoundaryTileView(parent.tile, source_offset=3),
                    None,
                ),
            )
        )
    with pytest.raises(ValueError, match="extent"):
        results.lookup(
            replace(
                key,
                input=parent.tile,
                boundaries=BoundaryTileOperands(
                    BoundaryTileView(parent.tile, relative_extent=2, source_offset=1),
                    None,
                ),
            )
        )
    assert (ledger.entries, ledger.nodes, dict(results._memo)) == before
    parent.close()
    assert results.retained_results == 0
    first_lease.close()
    second_lease.close()
    output_lease.close()
    input_lease.close()


@pytest.mark.parametrize("fused", (False, True))
def test_interface_boundary_tiles_are_reverse_indexed_and_retire_cleanly(
    fused: bool,
) -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    boundary = tiles.leaf(tiles.resolve(key.input).alphabet, 2)
    operands = BoundaryTileOperands(BoundaryTileView(boundary.tile, -1, 1), None)
    request = (
        FusedInterfaceKey(
            key.action,
            key.input,
            key.ports,
            key.wiring,
            boundaries=operands,
        )
        if fused
        else PoweredInterfaceKey(key.action, key.input, key.wiring, operands)
    )
    if fused:
        results.publish_fused_interface(request, result.outgoing)  # type: ignore[arg-type]
    else:
        results.publish_interface(request, result.outgoing)  # type: ignore[arg-type]
    approved, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert not invalid and id(request) in approved
    assert results.retained_entries == 1
    boundary.close()
    assert results.retained_entries == 0
    assert not results._reverse and not results._variants
    output_lease.close()
    input_lease.close()


def test_boundary_tiles_require_the_exact_input_and_output_alphabet() -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    other = tiles.intern_alphabet(
        TileAlphabet(
            3,
            2,
            2,
            2,
            "another-cell-interpretation",
            "v2",
        )
    )
    foreign_content = tiles.leaf(other, 1)
    operands = BoundaryTileOperands(
        BoundaryTileView(foreign_content.tile, 0, 1),
        None,
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="alphabet interpretation"):
        results.lookup(replace(key, boundaries=operands))
    with pytest.raises(ValueError, match="alphabet interpretation"):
        results.publish(
            key,
            replace(result, outgoing_boundaries=operands),
        )
    after = ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert after.counters["completed_result_port_validation_requests"] == (
        before.counters.get("completed_result_port_validation_requests", 0) + 1
    )
    foreign_content.close()
    output_lease.close()
    input_lease.close()


def test_outgoing_boundary_aliases_share_one_exact_tile_lease() -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    view = BoundaryTileView(result.output, 0, 1)
    aliased = replace(
        result,
        outgoing_boundaries=BoundaryTileOperands(view, view),
    )
    held = results.publish(key, aliased)
    assert held._boundary_tiles == ()
    assert results._boundary_lease_count == 0
    assert sum(tile == result.output for tile in tiles._leases.values()) == 2
    output_lease.close()
    assert held.output == result.output
    held.close()
    input_lease.close()
    assert (
        ledger.counters["tile_lease_acquisitions"]
        == ledger.counters["tile_lease_releases"]
    )


def test_fused_boundary_reverse_publication_failure_rolls_back_every_tile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, tiles, results, input_lease, output_lease, key, result = _setup()
    boundary = tiles.leaf(tiles.resolve(key.input).alphabet, 2)
    fused = FusedInterfaceKey(
        key.action,
        key.input,
        key.ports,
        key.wiring,
        boundaries=BoundaryTileOperands(
            BoundaryTileView(boundary.tile, 0, 1),
            None,
        ),
    )
    before = (
        ledger.entries,
        ledger.nodes,
        dict(results._memo),
        dict(results._reverse),
        dict(results._variants),
    )
    calls = 0
    original = type(results)._write_reverse

    def fail_boundary(
        self: CompletedResultArena, reverse_key: _ReverseKey, value: _ReverseValue
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise RuntimeError("injected boundary-index failure")
        original(self, reverse_key, value)

    monkeypatch.setattr(type(results), "_write_reverse", fail_boundary)
    with pytest.raises(RuntimeError, match="boundary-index"):
        results.publish_fused_interface(fused, result.outgoing)
    assert (ledger.entries, ledger.nodes) == before[:2]
    assert dict(results._memo) == before[2]
    assert dict(results._reverse) == before[3]
    assert dict(results._variants) == before[4]
    boundary.close()
    output_lease.close()
    input_lease.close()


def test_fused_consumer_boundary_has_independent_identity_and_retirement() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, tiles, results, source, output, key, result = _setup()
    alphabet = tiles.resolve(source.tile).alphabet
    # A parent ensures that this consumer operand is distinct from both roots.
    boundary = tiles.join(source.tile, output.tile)
    operands = BoundaryTileOperands(BoundaryTileView(boundary.tile, -2, 2))
    plain = FusedInterfaceKey(key.action, key.input, key.ports, key.wiring)
    consumer = replace(plain, consumer_boundaries=operands)
    producer = replace(plain, boundaries=operands)
    assert len({plain, consumer, producer}) == 3
    for request in (plain, consumer, producer):
        results.publish_fused_interface(request, result.outgoing)
    assert results.retained_fused_interfaces == 3
    before = ledger.snapshot()
    _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert not invalid
    assert ledger.snapshot() == before
    assert tiles.resolve(boundary.tile).alphabet == alphabet
    boundary.close()
    assert results.retained_fused_interfaces == 1
    assert results.lookup_fused_interface(plain) == result.outgoing
    _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert not invalid
    output.close()
    source.close()


def test_fused_consumer_boundary_failure_rolls_back_both_reverse_indexes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, tiles, results, source, output, key, result = _setup()
    boundary = tiles.join(source.tile, output.tile)
    consumer = FusedInterfaceKey(
        key.action,
        key.input,
        key.ports,
        key.wiring,
        consumer_boundaries=BoundaryTileOperands(
            BoundaryTileView(boundary.tile, -2, 2)
        ),
    )
    before = (
        ledger.entries,
        ledger.nodes,
        dict(results._memo),
        dict(results._reverse),
        dict(results._variants),
    )
    original = type(results)._write_reverse
    calls = 0

    def fail_after_input(
        self: CompletedResultArena, reverse_key: _ReverseKey, value: _ReverseValue
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise RuntimeError("consumer reverse-index failure")
        original(self, reverse_key, value)

    with monkeypatch.context() as poison:
        poison.setattr(type(results), "_write_reverse", fail_after_input)
        with pytest.raises(RuntimeError, match="consumer reverse-index"):
            results.publish_fused_interface(consumer, result.outgoing)
    assert (
        ledger.entries,
        ledger.nodes,
        dict(results._memo),
        dict(results._reverse),
        dict(results._variants),
    ) == before
    boundary.close()
    output.close()
    source.close()


def test_fusion_validates_each_child_input_and_output_alphabet() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, actions, tiles, results, source, old_output, old_key, old_result = _setup(
        authority_type=_ChangingAlphabetAuthority,
    )
    source_alphabet = tiles.resolve(source.tile).alphabet
    mid_alphabet = tiles.intern_alphabet(TileAlphabet(4, 3, 3, 2, "middle", "v1"))
    final_alphabet = tiles.intern_alphabet(TileAlphabet(5, 4, 4, 3, "final", "v1"))
    assert isinstance(actions, _ChangingAlphabetAuthority)
    actions.tiles, actions.domains = (
        tiles,
        (source_alphabet, mid_alphabet, final_alphabet),
    )
    middle = tiles.leaf(mid_alphabet, 1)
    final = tiles.leaf(final_alphabet, 2)
    source_ports = BoundPorts(
        old_key.ports,
        old_key.wiring,
        BoundaryTileOperands(BoundaryTileView(source.tile, 0, 1)),
    )
    middle_ports = replace(
        source_ports,
        boundaries=BoundaryTileOperands(BoundaryTileView(middle.tile, 0, 1)),
    )
    final_ports = replace(
        source_ports,
        boundaries=BoundaryTileOperands(BoundaryTileView(final.tile, 0, 1)),
    )
    key = replace(
        old_key,
        boundaries=middle_ports.boundaries,
        fusion=FusedBoundaryContract(source_ports, middle_ports),
    )
    final_exits = replace(final_ports, ports=old_result.outgoing_ports)
    result = replace(
        old_result,
        output=final.tile,
        relative_extent=1,
        outgoing_boundaries=final_ports.boundaries,
        fusion=FusedBoundaryContract(middle_ports, final_exits),
    )
    with results.publish(key, result) as lease:
        assert lease.result == result
        _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
        assert not invalid
        before = ledger.snapshot()
        forged = replace(
            key,
            boundaries=source_ports.boundaries,
            fusion=FusedBoundaryContract(source_ports, source_ports),
        )
        with pytest.raises(ValueError, match="child input domain"):
            results.lookup(forged)
        assert ledger.snapshot() == before
        bad_result = replace(
            result, fusion=FusedBoundaryContract(source_ports, final_exits)
        )
        with pytest.raises(ValueError, match="child output domain"):
            results.publish(key, bad_result)
        # The producer output operand has an independent lease and domain.
        middle.close()
        final.close()
        assert lease.result.fusion is not None
        assert lease.result.fusion.producer.boundaries == middle_ports.boundaries
    old_output.close()
    source.close()
