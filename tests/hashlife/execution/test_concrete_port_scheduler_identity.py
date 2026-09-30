from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeVar, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortStateID,
    VirtualInterfaceID,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    Residual as _canonical_Residual,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    VirtualBinding as _canonical_VirtualBinding,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    VirtualInterface as _canonical_VirtualInterface,
)
from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
    ConcretePortScheduler,
)
from number_compiler.hashlife.execution.continuations.provider_layers import (
    ProviderLayer,
    ProviderLayerID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads


@dataclass
class _Adapter:
    ledger: ResourceLedger
    sources: SourceCellArena
    owner: ArenaToken
    primitive: FieldCellActionID
    composed: FieldCellActionID

    def validate_action(self, action: FieldCellActionID) -> object:
        if type(action) is not FieldCellActionID:
            raise TypeError("expected field action")
        action.validate(self.owner, "audit-action")
        if action.local_id not in (0, 1):
            raise ValueError("stale field action")
        return action

    def children(
        self,
        action: FieldCellActionID,
    ) -> None | tuple[FieldCellActionID, FieldCellActionID]:
        self.validate_action(action)
        return None if action == self.primitive else (self.primitive, self.primitive)

    def primitive_initial(self, action: FieldCellActionID, side: int) -> int:
        self.validate_action(action)
        return side

    def primitive_advance(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int:
        self.validate_action(action)
        return (state + symbol + side) & 1

    def primitive_state_count(
        self,
        action: FieldCellActionID,
        side: int,
    ) -> int:
        self.validate_action(action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError(side)
        return 2

    def primitive_advance_cell(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        cell: SourceCellID,
        reverse: bool,
    ) -> int:
        self.validate_action(action)
        self.sources.resolve(cell)
        if type(reverse) is not bool:
            raise TypeError(reverse)
        return state

    def blank_initial_is_stable(
        self,
        action: FieldCellActionID,
        side: int,
    ) -> bool:
        self.validate_action(action)
        return False

    def primitive_emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        self.validate_action(action)
        return left ^ symbol ^ right


def _runtime() -> tuple[
    ResourceLedger,
    ConcretePortScheduler,
    FieldCellActionID,
    FieldCellActionID,
    SourceCellID,
]:
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource((1,), 2, blank=2, extent=1, alphabet_size=2),
    )
    geometry.span((1,), 2, 1)
    sources = SourceCellArena(geometry)
    cell = sources.intern(0, 0)
    owner = ArenaToken("audit-actions")
    primitive = FieldCellActionID(owner, "audit-action", 0)
    composed = FieldCellActionID(owner, "audit-action", 1)
    return (
        ledger,
        ConcretePortScheduler(
            _Adapter(ledger, sources, owner, primitive, composed),
        ),
        primitive,
        composed,
        cell,
    )


def test_public_operations_validate_scoped_inputs_before_warm_memo_lookup() -> None:
    ledger, scheduler, primitive, _composed, cell = _runtime()
    assert scheduler.advance(primitive, 0, 0, cell) == 1
    assert scheduler.emit(primitive, 0, cell, 1) == 0
    before = ledger.snapshot()
    invalid_actions: tuple[object, ...] = (
        primitive.local_id,
        True,
        FieldCellActionID(ArenaToken("foreign"), primitive.kind, primitive.local_id),
        FieldCellActionID(primitive.owner, "wrong-kind", primitive.local_id),
        FieldCellActionID(primitive.owner, primitive.kind, 2),
    )
    for invalid in invalid_actions:
        with pytest.raises((TypeError, ValueError, IndexError)):
            scheduler.advance(cast(FieldCellActionID, invalid), 0, 0, cell)
    foreign_cell = SourceCellID(ArenaToken("foreign"), cell.kind, cell.local_id)
    with pytest.raises(ValueError):
        scheduler.advance(primitive, 0, 0, foreign_cell)
    with pytest.raises(TypeError):
        scheduler.advance(primitive, True, 0, cell)
    with pytest.raises(TypeError):
        scheduler.advance(primitive, 0, 0, cell, reverse=cast(bool, 1))
    with pytest.raises(TypeError):
        scheduler.emit(primitive, True, cell, 1)
    with pytest.raises(ValueError, match="outside its port"):
        scheduler.advance(primitive, 0, 2, cell)
    with pytest.raises(ValueError, match="outside its port"):
        scheduler.emit(primitive, 0, cell, 2)
    after = ledger.snapshot()
    assert after.entries == before.entries
    assert after.nodes == before.nodes


def test_stale_and_cross_action_composed_ports_reject_before_task_lookup() -> None:
    ledger, scheduler, primitive, composed, cell = _runtime()
    state = scheduler.initial(composed, 0)
    assert type(state) is PortStateID
    before = ledger.snapshot()
    with pytest.raises(TypeError):
        scheduler.advance(composed, 0, 0, cell)
    with pytest.raises(TypeError):
        scheduler.advance(primitive, 0, state, cell)
    after = ledger.snapshot()
    assert after.entries == before.entries
    assert after.nodes == before.nodes
    scheduler.clear()
    cleared = ledger.snapshot()
    with pytest.raises(ValueError, match="stale concrete port state"):
        scheduler.advance(composed, 0, state, cell)
    final = ledger.snapshot()
    assert final.entries == cleared.entries
    assert final.nodes == cleared.nodes


def _virtual_fixture() -> tuple[
    ResourceLedger,
    ConcretePortScheduler,
    _canonical_VirtualInterface,
    _canonical_VirtualBinding,
]:
    ledger, scheduler, primitive, composed, cell = _runtime()
    record = _canonical_VirtualInterface(primitive, 0, (0, 1))
    binding = _canonical_VirtualBinding(
        composed,
        0,
        cell,
        None,
        0,
        0,
        False,
    )
    return ledger, scheduler, record, binding


def test_virtual_interface_publication_is_atomic_and_counted_as_one_node() -> None:
    ledger, scheduler, record, binding = _virtual_fixture()
    before = ledger.snapshot()
    ledger.tighten_limits(before.nodes + 1, before.entries + 2)
    with pytest.raises(BlockContextBudgetExceeded):
        scheduler._publish_virtual(binding, record)
    rejected = ledger.snapshot()
    assert (rejected.entries, rejected.nodes) == (before.entries, before.nodes)
    assert scheduler._virtual == {}
    assert scheduler._virtual_keys == {}
    assert scheduler._virtual_bindings == {}
    assert scheduler._next_virtual == 0

    ledger, scheduler, record, binding = _virtual_fixture()
    initial = ledger.snapshot()
    interface = scheduler._publish_virtual(binding, record)
    inventory = {item.name: item for item in ledger.inventory()}
    semantic = next(
        item for name, item in inventory.items() if name.endswith("-virtual")
    )
    keys = next(
        item for name, item in inventory.items() if name.endswith("-virtual-keys")
    )
    bindings = next(
        item for name, item in inventory.items() if name.endswith("-virtual-bindings")
    )
    assert (semantic.entries, semantic.nodes) == (1, 1)
    assert (semantic.observed_entries, semantic.observed_nodes) == (1, 1)
    assert (keys.entries, keys.nodes) == (1, 0)
    assert (bindings.entries, bindings.nodes, bindings.evictable) == (1, 0, True)
    assert scheduler.resolve_virtual(interface) == record
    payloads = audit_registered_payloads(ledger)
    assert payloads.forbidden_future_payloads == 0
    assert payloads.unbounded_future_integers == 0
    assert payloads.unknown_payloads == 0

    scheduler.clear()
    cleared = ledger.snapshot()
    assert scheduler.resolve_virtual(interface) == record
    assert not scheduler._virtual_bindings
    assert (cleared.entries, cleared.nodes) == (
        initial.entries + 2,
        initial.nodes + 1,
    )


def test_uncertified_constant_residual_rejects_before_mutation() -> None:
    ledger, scheduler, _primitive, composed, _cell = _runtime()
    before = ledger.snapshot()
    record = _canonical_Residual(
        composed,
        1,
        None,
        None,
        None,
        1,
        False,
        0,
    )
    with pytest.raises(ValueError, match="directed-port certificate"):
        scheduler._intern_residual(record)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert not scheduler._residuals
    assert not scheduler._residual_keys


def test_virtual_interface_ids_reject_aliases_before_warm_lookup() -> None:
    ledger, scheduler, primitive, _composed, _cell = _runtime()
    interface = scheduler._intern_virtual(
        _canonical_VirtualInterface(primitive, 0, (0, 1)),
    )
    before = ledger.snapshot()
    invalid: tuple[object, ...] = (
        interface.local_id,
        True,
        0.0,
        VirtualInterfaceID(ArenaToken("foreign"), interface.kind, interface.local_id),
        VirtualInterfaceID(interface.owner, "wrong-kind", interface.local_id),
        VirtualInterfaceID(interface.owner, interface.kind, interface.local_id + 1),
    )
    for value in invalid:
        with pytest.raises((TypeError, ValueError)):
            scheduler.resolve_virtual(cast(VirtualInterfaceID, value))
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    payloads = audit_registered_payloads(ledger)
    assert payloads.forbidden_future_payloads == 0
    assert payloads.unbounded_future_integers == 0
    assert payloads.unknown_payloads == 0


def test_virtual_semantic_key_excludes_source_and_occurrence_identity() -> None:
    _ledger, scheduler, primitive, composed, cell = _runtime()
    record = _canonical_VirtualInterface(primitive, 1, (1, 0))
    binding = _canonical_VirtualBinding(
        composed,
        1,
        cell,
        None,
        0,
        1,
        True,
    )
    interface = scheduler._publish_virtual(binding, record)
    retained = scheduler.resolve_virtual(interface)
    assert retained == record
    assert tuple(field.name for field in retained.__dataclass_fields__.values()) == (
        "consumer",
        "side",
        "outputs",
    )
    assert isinstance(retained.outputs, tuple)
    assert all(type(value) is int for value in retained.outputs)
    assert record in scheduler._virtual_keys
    assert binding in scheduler._virtual_bindings


def test_provider_layers_are_scoped_constant_size_linked_nodes() -> None:
    ledger, scheduler, primitive, _composed, _cell = _runtime()
    first = scheduler.layers.intern(None, ProviderLayer(primitive, 0, 1))
    second = scheduler.layers.intern(first, ProviderLayer(primitive, 1, 0))
    assert scheduler.layers.resolve(second).previous == first
    assert scheduler.layers.intern(first, ProviderLayer(primitive, 1, 0)) == second
    assert all(
        not any(isinstance(value, tuple) for value in (node.previous, node.layer))
        for node in scheduler.layers._nodes.values()
    )
    before = ledger.snapshot()
    invalid: tuple[object, ...] = (
        second.local_id,
        True,
        0.0,
        ProviderLayerID(ArenaToken("foreign"), second.kind, second.local_id),
        ProviderLayerID(second.owner, "wrong-kind", second.local_id),
        ProviderLayerID(second.owner, second.kind, second.local_id + 1),
    )
    for value in invalid:
        with pytest.raises((TypeError, ValueError)):
            scheduler.layers.resolve(cast(ProviderLayerID, value))
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)

    payloads = audit_registered_payloads(ledger)
    assert payloads.forbidden_future_payloads == 0
    assert payloads.unbounded_future_integers == 0
    assert payloads.unknown_payloads == 0

    scheduler.clear()
    assert scheduler.layers._nodes == {}
    with pytest.raises(ValueError, match="stale provider-layer reference"):
        scheduler.layers.resolve(second)
    third = scheduler.layers.intern(None, ProviderLayer(primitive, 0, 1))
    assert third.local_id > second.local_id


def test_composed_point_retains_layer_ids_instead_of_stage_tuples() -> None:
    _ledger, scheduler, _primitive, composed, cell = _runtime()
    assert scheduler.point(composed, cell, 0) == 1
    assert len(scheduler.layers._nodes) == 1
    assert all(
        not any(
            type(item) is tuple
            and any(type(nested) is ProviderLayer for nested in item)
            for item in key
        )
        for key in scheduler._memo
    )
    assert all(
        residual.layer is None or type(residual.layer) is ProviderLayerID
        for residual in scheduler._residuals.values()
    )


def test_boundary_projection_validates_before_a_warm_residual_lookup() -> None:
    from number_compiler.hashlife.execution.continuations.concrete_boundary import (
        project_boundary,
    )

    ledger, scheduler, primitive, composed, _cell = _runtime()
    state = scheduler.initial(composed, 0)
    opposite = scheduler.initial(primitive, 1)
    assert project_boundary(scheduler, composed, 0, state, opposite) == 0
    before = ledger.snapshot()
    for invalid in (True, 1.0, -1, 2):
        with pytest.raises((TypeError, ValueError)):
            project_boundary(scheduler, composed, 0, state, cast("int", invalid))
    with pytest.raises((TypeError, ValueError)):
        project_boundary(scheduler, composed, True, state, opposite)
    with pytest.raises((TypeError, ValueError)):
        project_boundary(scheduler, primitive, 0, state, opposite)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    scheduler.clear()
    with pytest.raises(ValueError, match="stale"):
        project_boundary(scheduler, composed, 0, state, opposite)


@pytest.mark.parametrize("sort", ("port", "residual", "virtual", "layer"))
def test_unallocated_concrete_id_rejects_before_backing_map_lookup(
    monkeypatch: pytest.MonkeyPatch, sort: str
) -> None:
    ledger, scheduler, _, composed, _ = _runtime()
    scheduler.initial(composed, 0)
    if sort == "port":
        attribute = "_ports"
        probe = _probe(scheduler.resolve_port, scheduler._port_id(scheduler._next_port))
    elif sort == "residual":
        attribute = "_residuals"
        probe = _probe(
            scheduler.resolve_residual, scheduler._residual_id(scheduler._next_residual)
        )
    elif sort == "virtual":
        attribute = "_virtual"
        probe = _probe(
            scheduler.resolve_virtual, scheduler._virtual_id(scheduler._next_virtual)
        )
    else:
        attribute = "_nodes"
        probe = _probe(
            scheduler.layers.resolve,
            scheduler.layers._handle(scheduler.layers._next_id),
        )

    class Unreachable(dict[object, object]):
        def __getitem__(self, key: object) -> None:
            pytest.fail("unallocated ID reached the backing map")

    before = ledger.snapshot()
    with monkeypatch.context() as patch:
        patch.setattr(
            scheduler.layers if sort == "layer" else scheduler, attribute, Unreachable()
        )
        with pytest.raises(ValueError, match="allocated range"):
            probe()
    assert ledger.snapshot() == before


def test_port_allocation_range_is_monotonic_across_query_eviction() -> None:
    _, scheduler, _, composed, _ = _runtime()
    first = scheduler.initial(composed, 0)
    scheduler.clear()
    second = scheduler.initial(composed, 0)
    assert isinstance(first, PortStateID) and isinstance(second, PortStateID)
    assert second.local_id > first.local_id
    assert second.local_id >= len(scheduler._ports)
    scheduler.resolve_port(second)
    with pytest.raises(ValueError, match="stale"):
        scheduler.resolve_port(first)


HandleT = TypeVar("HandleT", bound=ArenaHandle)


def _probe(
    resolve: Callable[[HandleT], object], handle: HandleT
) -> Callable[[], object]:
    return lambda: resolve(handle)
