"""Completed tile results retain output roots without owning future content."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.semantic_structures import (
    COMPONENT_ROLES,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    FusedInterfaceKey,
    PoweredInterfaceKey,
    SpatialInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseKey as _ReverseKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseValue as _ReverseValue,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from tests.support.assertions import assert_rejected_atomically
from tests.support.tile_results import (
    _setup,
    assert_result_stores_unchanged,
    assert_retention_and_peaks_unchanged,
    assert_valid_tile_payloads,
    fused_setup,
    incoming_setup,
)


def test_fused_result_contract_keeps_producer_and_consumer_contexts_distinct() -> None:

    ledger, _, tiles, results, input_lease, output_lease, key, result, incoming = (
        incoming_setup()
    )
    outgoing = tiles.leaf(tiles.resolve(key.input).alphabet, 1)
    key_consumer = BoundPorts(key.ports, key.wiring, key.boundaries)
    key_producer = BoundPorts(
        (2,),
        key.wiring,
        BoundaryTileOperands(BoundaryTileView(incoming.tile, -1, 1), None),
    )
    fused_key = replace(
        key,
        fusion=FusedBoundaryContract(key_producer, key_consumer),
    )
    result_boundaries = BoundaryTileOperands(
        None,
        BoundaryTileView(outgoing.tile, 1, 1, 1),
    )
    result_consumer = BoundPorts(result.outgoing_ports, key.wiring, result_boundaries)
    result_producer = BoundPorts(
        (1,),
        key.wiring,
        BoundaryTileOperands(BoundaryTileView(output_lease.tile, 0, 1), None),
    )
    fused_result = replace(
        result,
        outgoing_boundaries=result_boundaries,
        fusion=FusedBoundaryContract(result_producer, result_consumer),
    )
    held = results.publish(fused_key, fused_result)
    assert held.result.fusion == fused_result.fusion
    assert held.result.fusion is not None
    assert held.result.fusion.producer != held.result.fusion.consumer
    # output_lease aliases one producer operand; only the distinct outgoing
    # boundary needs another lease.
    assert len(held._boundary_tiles) == 1
    assert_valid_tile_payloads(ledger, results, fused_key)
    held.close()
    outgoing.close()
    incoming.close()
    output_lease.close()
    input_lease.close()


def test_fused_contract_rejects_consumer_aliases_before_warm_lookup() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    consumer = BoundPorts(key.ports, key.wiring, key.boundaries)
    fused_key = replace(
        key,
        fusion=FusedBoundaryContract(BoundPorts((2,), key.wiring), consumer),
    )
    result_consumer = BoundPorts(
        result.outgoing_ports,
        key.wiring,
        result.outgoing_boundaries,
    )
    fused_result = replace(
        result,
        fusion=FusedBoundaryContract(BoundPorts((1,), key.wiring), result_consumer),
    )
    held = results.publish(fused_key, fused_result)
    before = ledger.entries, ledger.nodes, dict(results._memo), dict(results._reverse)
    with pytest.raises(TypeError, match="bound ports"):
        results.lookup(
            replace(
                fused_key,
                fusion=FusedBoundaryContract(
                    BoundPorts((True,), key.wiring),
                    consumer,
                ),
            )
        )
    with pytest.raises(ValueError, match="consumer disagrees"):
        results.lookup(
            replace(
                fused_key,
                fusion=FusedBoundaryContract(
                    BoundPorts((2,), key.wiring),
                    BoundPorts((0,), key.wiring),
                ),
            )
        )
    assert_result_stores_unchanged(ledger, results, before[:4])
    held.close()
    output_lease.close()
    input_lease.close()


def test_spatial_interface_pair_hits_before_reduction_without_tile_index() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    spatial = SpatialInterfaceKey(result.outgoing, result.outgoing, key.wiring)
    before_reverse = dict(results._reverse)
    assert results.lookup_spatial_interface(spatial) is None
    assert (
        results.publish_spatial_interface(spatial, result.outgoing) == result.outgoing
    )
    assert results.lookup_spatial_interface(spatial) == result.outgoing
    assert (
        results.publish_spatial_interface(spatial, result.outgoing) == result.outgoing
    )
    assert results._reverse == before_reverse
    assert results.retained_results == 0
    assert results.retained_interfaces == 0
    assert results.retained_interface_compositions == 1
    assert ledger.counters["spatial_interface_composition_requests"] == 2
    assert ledger.counters["spatial_interface_composition_early_hits"] == 1
    assert ledger.counters["spatial_interface_composition_publication_requests"] == 2
    assert ledger.counters["spatial_interface_composition_publications"] == 1
    assert ledger.counters["spatial_interface_composition_late_aliases"] == 1
    approved, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert not invalid
    assert id(spatial) in approved
    payloads = audit_registered_payloads(ledger)
    assert (
        payloads.forbidden_future_payloads,
        payloads.unbounded_future_integers,
        payloads.unknown_payloads,
    ) == (0, 0, 0)
    output_lease.close()
    input_lease.close()


def test_spatial_interface_pair_validates_scoped_children_before_warm_hit() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    spatial = SpatialInterfaceKey(result.outgoing, result.outgoing, key.wiring)
    results.publish_spatial_interface(spatial, result.outgoing)
    foreign = LocalInterfaceID(
        ArenaToken("foreign-spatial-interface"),
        result.outgoing.kind,
        0,
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        results.lookup_spatial_interface(replace(spatial, left=foreign))
    with pytest.raises(TypeError):
        results.lookup_spatial_interface(
            replace(spatial, left=cast(LocalInterfaceID, True))
        )
    assert ledger.snapshot() == before
    output_lease.close()
    input_lease.close()


def test_fused_interface_shares_memo_and_retires_with_input() -> None:

    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        _unused_key_binding,
        result,
        fused,
    ) = fused_setup(publish=False)
    assert results.lookup_fused_interface(fused) is None
    assert results.publish_fused_interface(fused, result.outgoing) == result.outgoing
    assert results.lookup_fused_interface(fused) == result.outgoing
    assert results.publish_fused_interface(fused, result.outgoing) == result.outgoing
    assert results.retained_fused_interfaces == 1
    assert results.retained_results == results.retained_interfaces == 0
    assert ledger.counters["fused_interface_requests"] == 2
    assert ledger.counters["fused_interface_early_hits"] == 1
    assert ledger.counters["fused_interface_publication_requests"] == 2
    assert ledger.counters["fused_interface_publications"] == 1
    assert ledger.counters["fused_interface_late_aliases"] == 1
    assert_valid_tile_payloads(ledger, results, fused)
    ledger.evict_query_memos()
    assert results.retained_fused_interfaces == 0
    assert not results._reverse and not results._variants
    input_lease.close()
    output_lease.close()


def test_fused_interface_keeps_producer_and_result_wirings_distinct() -> None:
    ledger, actions, _tiles, results, input_lease, output_lease, key, result = _setup()
    functions = results.interfaces.functions
    producer_port = FinitePort(PortVariable(0, 0, "producer", 0), 2)
    producer_signature = FunctionSignature((producer_port,), BOOL)
    zero = functions.atom(producer_signature, 0)
    one = functions.atom(producer_signature, 1)
    producer_declared = results.interfaces.intern_interface(
        MacroInterface(
            SemanticIdentity("tile-results-producer-v1", ("producer",)),
            (producer_port,),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
            phase_count=2,
        )
    )
    producer_interface = results.interfaces.intern(
        producer_declared,
        MacroComponents(*(zero for _ in COMPONENT_ROLES)),
    )
    producer_wiring = ResultWiring(producer_declared, 0, 1)
    actions.heterogeneous_fused_wiring = True
    fused = FusedInterfaceKey(
        key.action,
        key.input,
        (1,),
        key.wiring,
        producer_wiring,
    )
    assert results.publish_fused_interface(fused, result.outgoing) == result.outgoing
    assert results.lookup_fused_interface(fused) == result.outgoing
    # The produced interface belongs to the consumer/result signature.
    with pytest.raises(ValueError, match="another port signature"):
        results.publish_fused_interface(fused, producer_interface)

    before = ledger.snapshot()
    foreign = replace(
        producer_declared,
        owner=ArenaToken("foreign-producer-signature"),
    )
    with pytest.raises(ValueError):
        results.lookup_fused_interface(
            replace(
                fused,
                producer_wiring=ResultWiring(foreign, 0, 1),
            )
        )
    assert ledger.snapshot() == before
    output_lease.close()
    input_lease.close()


def test_warm_fused_lookup_rejects_tampered_normalization_without_repair() -> None:
    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        _unused_key_binding,
        _unused_result_binding,
        fused,
    ) = fused_setup(publish=True)
    forged = replace(fused)
    object.__setattr__(forged, "producer_wiring", None)
    before = ledger.snapshot()
    with pytest.raises(TypeError, match="producer"):
        results.lookup_fused_interface(forged)
    assert forged.producer_wiring is None
    assert ledger.snapshot() == before
    output_lease.close()
    input_lease.close()


def test_fused_equal_wiring_spelling_has_one_canonical_key() -> None:
    _, _, _, _, input_lease, output_lease, key, _, legacy = fused_setup(publish=False)
    explicit = FusedInterfaceKey(
        key.action,
        key.input,
        key.ports,
        key.wiring,
        key.wiring,
    )
    assert legacy == explicit
    assert hash(legacy) == hash(explicit)
    output_lease.close()
    input_lease.close()


def test_fused_interface_rejects_numeric_and_foreign_aliases_before_warm_hit() -> None:
    ledger, actions, _, results, input_lease, output_lease, key, result, fused = (
        fused_setup(publish=True)
    )
    before = ledger.snapshot()
    with pytest.raises(TypeError):
        results.lookup_fused_interface(replace(fused, ports=(True,)))
    with pytest.raises(TypeError):
        results.publish_fused_interface(
            replace(fused, ports=(True,)),
            result.outgoing,
        )
    foreign = FieldCellActionID(ArenaToken("foreign-fused-action"), key.action.kind, 0)
    with pytest.raises(ValueError):
        results.lookup_fused_interface(replace(fused, action=foreign))
    with pytest.raises(ValueError):
        results.publish_fused_interface(replace(fused, action=foreign), result.outgoing)
    assert ledger.snapshot() == before
    actions.fused_enabled = False
    before_unsupported = ledger.snapshot()
    with pytest.raises(ValueError, match="not an admitted fused pair"):
        results.lookup_fused_interface(fused)
    with pytest.raises(ValueError, match="not an admitted fused pair"):
        results.publish_fused_interface(fused, result.outgoing)
    assert ledger.snapshot() == before_unsupported
    actions.fused_enabled = True
    input_lease.close()
    output_lease.close()


@pytest.mark.parametrize("fail_at", (1, 2))
def test_fused_interface_reverse_publication_failure_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
    fail_at: int,
) -> None:
    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        _unused_key_binding,
        result,
        fused,
    ) = fused_setup(publish=False)
    before = ledger.entries, ledger.nodes, dict(results._memo), dict(results._reverse)
    calls = 0
    original = type(results)._write_reverse

    def fail_boundary(
        self: CompletedResultArena, reverse_key: _ReverseKey, value: _ReverseValue
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == fail_at:
            raise RuntimeError("injected fused reverse failure")
        original(self, reverse_key, value)

    monkeypatch.setattr(type(results), "_write_reverse", fail_boundary)
    with pytest.raises(RuntimeError, match="injected fused"):
        results.publish_fused_interface(fused, result.outgoing)
    assert_result_stores_unchanged(ledger, results, before[:4])
    assert not results._variants
    output_lease.close()
    input_lease.close()


def test_fused_interface_budget_rejects_before_retained_mutation() -> None:
    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        _unused_key_binding,
        result,
        fused,
    ) = fused_setup(publish=False)
    ledger.tighten_limits(None, ledger.entries)
    before = ledger.snapshot()
    with pytest.raises(Exception, match="cache budget exceeded"):
        results.publish_fused_interface(fused, result.outgoing)
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
    assert after.counters.get("fused_interface_publication_requests", 0) == (
        before.counters.get("fused_interface_publication_requests", 0) + 1
    )
    assert not results._memo and not results._reverse and not results._variants
    output_lease.close()
    input_lease.close()


def test_spatial_interface_budget_counts_valid_publication_attempt_only() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    spatial = SpatialInterfaceKey(result.outgoing, result.outgoing, key.wiring)
    ledger.tighten_limits(None, ledger.entries)
    before = ledger.snapshot()
    with pytest.raises(Exception, match="cache budget exceeded"):
        results.publish_spatial_interface(spatial, result.outgoing)
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
    assert (
        after.counters.get(
            "spatial_interface_composition_publication_requests",
            0,
        )
        == before.counters.get(
            "spatial_interface_composition_publication_requests",
            0,
        )
        + 1
    )
    assert not results._memo
    assert_rejected_atomically(
        ledger,
        lambda: results.publish_spatial_interface(
            replace(spatial, left=cast("LocalInterfaceID", True)), result.outgoing
        ),
        TypeError,
    )
    output_lease.close()
    input_lease.close()


def test_fused_interface_inventory_rejects_boolean_variant_count() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        _unused_key_binding,
        _unused_result_binding,
        _unused_fused_binding,
    ) = fused_setup(publish=True)
    variant = next(iter(results._variants))
    results._variants[variant] = True
    _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
    assert (results._variant_owner, id(variant)) in invalid
    results._variants[variant] = 1
    input_lease.close()
    output_lease.close()


def test_fused_interface_inventory_rejects_swapped_admission_authority() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    (
        ledger,
        _,
        _,
        results,
        input_lease,
        output_lease,
        _unused_key_binding,
        _unused_result_binding,
        _unused_fused_binding,
    ) = fused_setup(publish=True)
    original = results._validate_fused_action
    try:
        results._validate_fused_action = lambda _action: None
        _, invalid = audit_tile_results(results, dict(ledger.iter_containers()))
        assert invalid
    finally:
        results._validate_fused_action = original
        output_lease.close()
        input_lease.close()
    output_lease.close()


def test_parametric_interface_shares_memo_and_retires_with_input() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    interface_key = PoweredInterfaceKey(key.action, key.input, key.wiring)
    assert results.lookup_interface(interface_key) is None
    assert results.publish_interface(interface_key, result.outgoing) == result.outgoing
    assert results.lookup_interface(interface_key) == result.outgoing
    assert results.publish_interface(interface_key, result.outgoing) == result.outgoing
    result_lease = results.publish(key, result)
    assert results.retained_entries == 2
    assert results.retained_results == results.retained_interfaces == 1
    assert ledger.counters["powered_interface_requests"] == 2
    assert ledger.counters["powered_interface_early_hits"] == 1
    assert (
        ledger.counters["powered_interface_requests"]
        - ledger.counters["powered_interface_early_hits"]
        == 1
    )
    assert ledger.counters["powered_interface_publication_requests"] == 2
    assert ledger.counters["powered_interface_publications"] == 1
    assert ledger.counters["powered_interface_late_aliases"] == 1
    input_lease.close()
    assert results.retained_entries == 0
    result_lease.close()
    output_lease.close()


def test_parametric_interface_rejects_wrong_signature_before_publication() -> None:
    ledger, _, _, results, input_lease, output_lease, key, result = _setup()
    interface_key = PoweredInterfaceKey(key.action, key.input, key.wiring)
    before = ledger.snapshot()
    foreign = type(result.outgoing)(ArenaToken("foreign"), result.outgoing.kind, 0)
    with pytest.raises(ValueError):
        results.publish_interface(interface_key, foreign)
    assert_retention_and_peaks_unchanged(ledger, before)
    output_lease.close()
    input_lease.close()
