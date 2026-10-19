from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import TypeGuard, TypeVar

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
    ResidualBindingID,
    VirtualInterfaceID,
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


def _is_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    return type(value) is tuple


def _call_untyped(
    operation: Callable[..., object], *args: object, **kwargs: object
) -> object:
    """Exercise a runtime boundary with intentionally ill-typed test inputs."""
    return operation(*args, **kwargs)


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
            _call_untyped(scheduler.advance, invalid, 0, 0, cell)
    foreign_cell = SourceCellID(ArenaToken("foreign"), cell.kind, cell.local_id)
    with pytest.raises(ValueError):
        scheduler.advance(primitive, 0, 0, foreign_cell)
    with pytest.raises(TypeError):
        scheduler.advance(primitive, True, 0, cell)
    with pytest.raises(TypeError):
        _call_untyped(scheduler.advance, primitive, 0, 0, cell, reverse=1)
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


def _publish_virtual_through_public_path(
    scheduler: ConcretePortScheduler,
    action: FieldCellActionID,
    cell: SourceCellID,
) -> VirtualInterfaceID:
    left = scheduler.advance(action, 0, scheduler.initial(action, 0), cell)
    right = scheduler.advance(action, 1, scheduler.initial(action, 1), cell)
    scheduler.emit(action, left, cell, right)
    snapshot = scheduler.audit_snapshot()
    assert snapshot.virtual_bindings
    return next(iter(snapshot.virtual_bindings.values()))


def test_virtual_interface_publication_is_atomic_and_counted_per_interface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, scheduler, _primitive, composed, cell = _runtime()
    left = scheduler.advance(composed, 0, scheduler.initial(composed, 0), cell)
    right = scheduler.advance(composed, 1, scheduler.initial(composed, 1), cell)
    before = scheduler.audit_snapshot()
    before_virtual = dict(before.virtual)
    before_virtual_keys = dict(before.virtual_keys)
    before_virtual_bindings = dict(before.virtual_bindings)
    virtual_owners = (
        before.virtual_owner,
        before.virtual_key_owner,
        before.virtual_binding_owner,
    )
    before_virtual_accounts = tuple(
        ledger.inventory_owner(owner) for owner in virtual_owners
    )
    original_reserve_many = ledger.reserve_many

    def reject_virtual_batch(
        reservations: Iterable[tuple[int, int, int]],
    ) -> None:
        batch = tuple(reservations)
        if batch == (
            (before.virtual_owner, 1, 1),
            (before.virtual_key_owner, 1, 0),
            (before.virtual_binding_owner, 1, 0),
        ):
            current = ledger.snapshot()
            ledger.tighten_limits(current.nodes, current.entries + 1)
        original_reserve_many(batch)

    monkeypatch.setattr(ledger, "reserve_many", reject_virtual_batch)
    with pytest.raises(BlockContextBudgetExceeded):
        scheduler.emit(composed, left, cell, right)
    rejected = scheduler.audit_snapshot()
    assert rejected.virtual is before.virtual
    assert rejected.virtual_keys is before.virtual_keys
    assert rejected.virtual_bindings is before.virtual_bindings
    assert dict(rejected.virtual) == before_virtual == {}
    assert dict(rejected.virtual_keys) == before_virtual_keys == {}
    assert dict(rejected.virtual_bindings) == before_virtual_bindings == {}
    assert rejected.next_virtual == before.next_virtual == 0
    assert tuple(ledger.inventory_owner(owner) for owner in virtual_owners) == (
        before_virtual_accounts
    )

    ledger, scheduler, _primitive, composed, cell = _runtime()
    initial_ledger = ledger.snapshot()
    interface = _publish_virtual_through_public_path(scheduler, composed, cell)
    record = scheduler.resolve_virtual(interface)
    published = scheduler.audit_snapshot()
    semantic = ledger.inventory_owner(published.virtual_owner)
    keys = ledger.inventory_owner(published.virtual_key_owner)
    bindings = ledger.inventory_owner(published.virtual_binding_owner)
    assert (semantic.entries, semantic.nodes) == (2, 2)
    assert (semantic.observed_entries, semantic.observed_nodes) == (2, 2)
    assert (keys.entries, keys.nodes) == (2, 0)
    assert (bindings.entries, bindings.nodes, bindings.evictable) == (2, 0, True)
    assert scheduler.resolve_virtual(interface) == record
    payloads = audit_registered_payloads(ledger)
    assert payloads.forbidden_future_payloads == 0
    assert payloads.unbounded_future_integers == 0
    assert payloads.unknown_payloads == 0

    scheduler.clear()
    cleared = ledger.snapshot()
    assert scheduler.resolve_virtual(interface) == record
    assert not scheduler.audit_snapshot().virtual_bindings
    assert (cleared.entries, cleared.nodes) == (
        initial_ledger.entries + 4,
        initial_ledger.nodes + 2,
    )


def test_virtual_interface_ids_reject_aliases_before_warm_lookup() -> None:
    ledger, scheduler, _primitive, composed, cell = _runtime()
    interface = _publish_virtual_through_public_path(scheduler, composed, cell)
    before = ledger.snapshot()
    next_virtual = scheduler.audit_snapshot().next_virtual
    invalid: tuple[object, ...] = (
        interface.local_id,
        True,
        0.0,
        VirtualInterfaceID(ArenaToken("foreign"), interface.kind, interface.local_id),
        VirtualInterfaceID(interface.owner, "wrong-kind", interface.local_id),
        VirtualInterfaceID(interface.owner, interface.kind, next_virtual),
    )
    for value in invalid:
        with pytest.raises((TypeError, ValueError)):
            _call_untyped(scheduler.resolve_virtual, value)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    payloads = audit_registered_payloads(ledger)
    assert payloads.forbidden_future_payloads == 0
    assert payloads.unbounded_future_integers == 0
    assert payloads.unknown_payloads == 0


def test_virtual_semantic_key_excludes_source_and_occurrence_identity() -> None:
    _ledger, scheduler, _primitive, composed, cell = _runtime()
    interface = _publish_virtual_through_public_path(scheduler, composed, cell)
    retained = scheduler.resolve_virtual(interface)
    assert tuple(field.name for field in retained.__dataclass_fields__.values()) == (
        "consumer",
        "side",
        "outputs",
    )
    outputs = retained.outputs
    assert _is_object_tuple(outputs)
    assert all(type(value) is int for value in outputs)
    snapshot = scheduler.audit_snapshot()
    assert retained in snapshot.virtual_keys
    assert interface in snapshot.virtual_bindings.values()


def test_provider_layers_are_scoped_constant_size_linked_nodes() -> None:
    ledger, scheduler, primitive, _composed, _cell = _runtime()
    first = scheduler.layers.intern(None, ProviderLayer(primitive, 0, 1))
    second = scheduler.layers.intern(first, ProviderLayer(primitive, 1, 0))
    assert scheduler.layers.resolve(second).previous == first
    assert scheduler.layers.intern(first, ProviderLayer(primitive, 1, 0)) == second
    assert all(
        not any(isinstance(value, tuple) for value in (node.previous, node.layer))
        for node in scheduler.layers.audit_snapshot().nodes.values()
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
            _call_untyped(scheduler.layers.resolve, value)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)

    payloads = audit_registered_payloads(ledger)
    assert payloads.forbidden_future_payloads == 0
    assert payloads.unbounded_future_integers == 0
    assert payloads.unknown_payloads == 0

    scheduler.clear()
    assert not scheduler.layers.audit_snapshot().nodes
    with pytest.raises(ValueError, match="stale provider-layer reference"):
        scheduler.layers.resolve(second)
    third = scheduler.layers.intern(None, ProviderLayer(primitive, 0, 1))
    assert third.local_id > second.local_id


def test_composed_point_retains_layer_ids_instead_of_stage_tuples() -> None:
    _ledger, scheduler, _primitive, composed, cell = _runtime()
    assert scheduler.point(composed, cell, 0) == 1
    snapshot = scheduler.audit_snapshot()
    assert len(snapshot.layers.nodes) == 1
    assert all(
        not any(
            type(item) is tuple
            and any(type(nested) is ProviderLayer for nested in item)
            for item in key
        )
        for key in snapshot.memo
    )
    assert all(
        residual.layer is None or type(residual.layer) is ProviderLayerID
        for residual in snapshot.residuals.values()
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
            _call_untyped(project_boundary, scheduler, composed, 0, state, invalid)
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
    scheduler_snapshot = scheduler.audit_snapshot()
    layer_snapshot = scheduler_snapshot.layers
    if sort == "port":
        attribute = "_ports"
        probe = _probe(
            scheduler.resolve_port,
            PortStateID(
                scheduler_snapshot.owner,
                scheduler_snapshot.port_kind,
                scheduler_snapshot.next_port,
            ),
        )
    elif sort == "residual":
        attribute = "_residuals"
        probe = _probe(
            scheduler.resolve_residual,
            ResidualBindingID(
                scheduler_snapshot.owner,
                scheduler_snapshot.residual_kind,
                scheduler_snapshot.next_residual,
            ),
        )
    elif sort == "virtual":
        attribute = "_virtual"
        probe = _probe(
            scheduler.resolve_virtual,
            VirtualInterfaceID(
                scheduler_snapshot.owner,
                scheduler_snapshot.virtual_kind,
                scheduler_snapshot.next_virtual,
            ),
        )
    else:
        attribute = "_nodes"
        probe = _probe(
            scheduler.layers.resolve,
            ProviderLayerID(
                layer_snapshot.owner, layer_snapshot.kind, layer_snapshot.next_id
            ),
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
    assert second.local_id >= len(scheduler.audit_snapshot().ports)
    scheduler.resolve_port(second)
    with pytest.raises(ValueError, match="stale"):
        scheduler.resolve_port(first)


HandleT = TypeVar("HandleT", bound=ArenaHandle)


def _probe(
    resolve: Callable[[HandleT], object], handle: HandleT
) -> Callable[[], object]:
    return lambda: resolve(handle)
