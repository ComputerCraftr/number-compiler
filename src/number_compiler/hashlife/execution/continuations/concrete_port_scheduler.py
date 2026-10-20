"""Iterative fused spacetime scheduler over scoped source cells."""

from __future__ import annotations

from collections.abc import Callable, Mapping, MutableMapping
from typing import Protocol, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_directed_residual import (
    validate_residual,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    ComposedPort as _ComposedPort,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
    PortStateID,
    ResidualBindingID,
    VirtualInterfaceID,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    Residual as _Residual,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    VirtualBinding as _VirtualBinding,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    VirtualInterface as _VirtualInterface,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeValueID,
)
from number_compiler.hashlife.execution.continuations.provider_layers import (
    ProviderLayer,
    ProviderLayerArena,
    ProviderLayerID,
)
from number_compiler.hashlife.execution.continuations.virtual_port_transfers import (
    validate_virtual_transfer,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
)
from number_compiler.hashlife.observation.concrete_port_queries import (
    active_width,
    observe_point,
    range_cells,
)
from number_compiler.resources.field_image_audit_contracts import (
    ConcretePortSchedulerAuditSnapshot,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


class ConcretePortAdapter(Protocol):
    ledger: ResourceLedger
    sources: SourceCellArena

    def validate_action(self, action: FieldCellActionID) -> object: ...
    def children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...
    def primitive_initial(self, action: FieldCellActionID, side: int) -> int: ...
    def primitive_state_count(self, action: FieldCellActionID, side: int) -> int: ...
    def primitive_advance(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int: ...
    def primitive_advance_cell(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        cell: SourceCellID,
        reverse: bool,
    ) -> int: ...
    def primitive_emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int: ...
    def blank_initial_is_stable(
        self,
        action: FieldCellActionID,
        side: int,
    ) -> bool: ...


class ConcretePortScheduler:
    """Execute fused temporal diamonds with one nonrecursive task stack."""

    _PORT_KIND = "concrete-port-state"
    _RESIDUAL_KIND = "concrete-residual-binding"
    _VIRTUAL_KIND = "concrete-virtual-interface"

    def __init__(self, adapter: ConcretePortAdapter) -> None:
        self.adapter = adapter
        self.ledger, self.sources = adapter.ledger, adapter.sources
        self.owner = ArenaToken("concrete-port-scheduler")
        self.ledger.register_execution_root(self)
        prefix = f"concrete-port-{len(self.ledger.inventory())}"
        self._port_owner = self.ledger.register(prefix + "-states", "query_memo")
        self._port_key_owner = self.ledger.register(
            prefix + "-state-keys", "query_memo"
        )
        self._residual_owner = self.ledger.register(prefix + "-residuals", "query_memo")
        self._residual_key_owner = self.ledger.register(
            prefix + "-residual-keys", "query_memo"
        )
        self._memo_owner = self.ledger.register(prefix + "-tasks", "observation_memo")
        self.layers = ProviderLayerArena(
            self.ledger,
            prefix + "-provider-layers",
            adapter.validate_action,
            self.validate_atom,
        )
        self._virtual_owner = self.ledger.register(
            prefix + "-virtual", "transfer_summary"
        )
        self._virtual_key_owner = self.ledger.register(
            prefix + "-virtual-keys", "transfer_summary"
        )
        self._virtual_binding_owner = self.ledger.register(
            prefix + "-virtual-bindings", "spatial_binding"
        )
        self._ports: MutableMapping[int, _ComposedPort] = self.ledger.make_dict(
            self._port_owner,
        )
        self._port_keys: MutableMapping[_ComposedPort, int] = self.ledger.make_dict(
            self._port_key_owner,
        )
        self._residuals: MutableMapping[int, _Residual] = self.ledger.make_dict(
            self._residual_owner,
        )
        self._residual_keys: MutableMapping[_Residual, int] = self.ledger.make_dict(
            self._residual_key_owner,
        )
        self._memo: MutableMapping[tuple[object, ...], PortAtom] = (
            self.ledger.make_dict(
                self._memo_owner,
            )
        )
        self._virtual: MutableMapping[int, _VirtualInterface] = self.ledger.make_dict(
            self._virtual_owner
        )
        self._virtual_keys: MutableMapping[_VirtualInterface, int] = (
            self.ledger.make_dict(self._virtual_key_owner)
        )
        self._virtual_bindings: MutableMapping[_VirtualBinding, VirtualInterfaceID] = (
            self.ledger.make_dict(self._virtual_binding_owner)
        )

        def port_count() -> int:
            return len(self._ports)

        def residual_count() -> int:
            return len(self._residuals)

        def virtual_count() -> int:
            return len(self._virtual)

        for owner, container in (
            (self._port_owner, self._ports),
            (self._port_key_owner, self._port_keys),
            (self._residual_owner, self._residuals),
            (self._residual_key_owner, self._residual_keys),
            (self._memo_owner, self._memo),
            (self._virtual_owner, self._virtual),
            (self._virtual_key_owner, self._virtual_keys),
            (self._virtual_binding_owner, self._virtual_bindings),
        ):
            node_counter: Callable[[], int] | None = None
            if owner == self._port_owner:
                node_counter = port_count
            elif owner == self._residual_owner:
                node_counter = residual_count
            elif owner == self._virtual_owner:
                node_counter = virtual_count
            self.ledger.register_container(
                owner,
                container,
                payloads=container.items,
                node_count=node_counter,
                evict=(
                    None
                    if owner in (self._virtual_owner, self._virtual_key_owner)
                    else self.clear
                ),
            )
        self._next_port = 0
        self._next_residual = 0
        self._next_virtual = 0

    def audit_snapshot(self) -> ConcretePortSchedulerAuditSnapshot:
        """Return read-only views of the exact scheduler stores for audits."""
        ports: Mapping[int, _ComposedPort] = self._ports
        port_keys: Mapping[_ComposedPort, int] = self._port_keys
        residuals: Mapping[int, _Residual] = self._residuals
        residual_keys: Mapping[_Residual, int] = self._residual_keys
        memo: Mapping[tuple[object, ...], PortAtom] = self._memo
        virtual: Mapping[int, _VirtualInterface] = self._virtual
        virtual_keys: Mapping[_VirtualInterface, int] = self._virtual_keys
        virtual_bindings: Mapping[_VirtualBinding, VirtualInterfaceID] = (
            self._virtual_bindings
        )
        return ConcretePortSchedulerAuditSnapshot(
            self.ledger,
            self.owner,
            self._PORT_KIND,
            self._RESIDUAL_KIND,
            self._VIRTUAL_KIND,
            self._next_port,
            self._next_residual,
            self._next_virtual,
            self._port_owner,
            ports,
            self._port_key_owner,
            port_keys,
            self._residual_owner,
            residuals,
            self._residual_key_owner,
            residual_keys,
            self._memo_owner,
            memo,
            self._virtual_owner,
            virtual,
            self._virtual_key_owner,
            virtual_keys,
            self._virtual_binding_owner,
            virtual_bindings,
            self.layers.audit_snapshot(),
        )

    def clear(self) -> None:
        self.layers.clear()
        for owner, container in (
            (self._memo_owner, self._memo),
            (self._port_key_owner, self._port_keys),
            (self._port_owner, self._ports),
            (self._residual_key_owner, self._residual_keys),
            (self._residual_owner, self._residuals),
            (self._virtual_binding_owner, self._virtual_bindings),
        ):
            count = len(container)
            container.clear()
            self.ledger.release(
                owner,
                entries=count,
                nodes=(
                    count if owner in (self._port_owner, self._residual_owner) else 0
                ),
            )

    def _port_id(self, local_id: int) -> PortStateID:
        return PortStateID(self.owner, self._PORT_KIND, local_id)

    def _residual_id(self, local_id: int) -> ResidualBindingID:
        return ResidualBindingID(self.owner, self._RESIDUAL_KIND, local_id)

    def _virtual_id(self, local_id: int) -> VirtualInterfaceID:
        return VirtualInterfaceID(self.owner, self._VIRTUAL_KIND, local_id)

    def resolve_virtual(self, interface: VirtualInterfaceID) -> _VirtualInterface:
        if type(interface) is not VirtualInterfaceID:
            raise TypeError("expected a scoped virtual interface")
        interface.validate(self.owner, self._VIRTUAL_KIND, size=self._next_virtual)
        try:
            return self._virtual[interface.local_id]
        except KeyError as exc:
            raise ValueError("stale virtual interface") from exc

    def _intern_virtual(self, record: _VirtualInterface) -> VirtualInterfaceID:
        self.adapter.validate_action(record.consumer)
        if type(record.side) is not int or record.side not in (0, 1):
            raise ValueError("virtual interface has another bounded port domain")
        validate_virtual_transfer(
            self.adapter,
            record.consumer,
            record.side,
            record.outputs,
        )
        found = self._virtual_keys.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.CONCRETE_VIRTUAL_INTERFACE_ALIAS_HITS)
            return self._virtual_id(found)
        self.ledger.reserve_many(
            ((self._virtual_owner, 1, 1), (self._virtual_key_owner, 1, 0)),
        )
        local_id = self._next_virtual
        self._next_virtual += 1
        self._virtual[local_id] = record
        self._virtual_keys[record] = local_id
        self.ledger.bump(_execution_keys.CONCRETE_VIRTUAL_INTERFACE_PUBLICATIONS)
        return self._virtual_id(local_id)

    def publish_virtual(
        self,
        binding: _VirtualBinding,
        record: _VirtualInterface,
    ) -> VirtualInterfaceID:
        self._validate_virtual_binding(binding)
        self.adapter.validate_action(record.consumer)
        children = self.adapter.children(binding.parent)
        if (
            record.side != binding.side
            or children is None
            or record.consumer != children[1]
        ):
            raise ValueError("virtual interface belongs to another consumer port")
        validate_virtual_transfer(
            self.adapter,
            record.consumer,
            record.side,
            record.outputs,
        )
        found_binding = self._virtual_bindings.get(binding)
        if found_binding is not None:
            self.resolve_virtual(found_binding)
            return found_binding
        found = self._virtual_keys.get(record)
        if found is not None:
            self.ledger.reserve(self._virtual_binding_owner, entries=1)
            result = self._virtual_id(found)
            self._virtual_bindings[binding] = result
            self.ledger.bump(_execution_keys.CONCRETE_VIRTUAL_INTERFACE_ALIAS_HITS)
            return result
        self.ledger.reserve_many(
            (
                (self._virtual_owner, 1, 1),
                (self._virtual_key_owner, 1, 0),
                (self._virtual_binding_owner, 1, 0),
            )
        )
        local_id = self._next_virtual
        self._next_virtual += 1
        result = self._virtual_id(local_id)
        self._virtual[local_id] = record
        self._virtual_keys[record] = local_id
        self._virtual_bindings[binding] = result
        self.ledger.bump(_execution_keys.CONCRETE_VIRTUAL_INTERFACE_PUBLICATIONS)
        return result

    def _validate_virtual_binding(self, binding: _VirtualBinding) -> None:
        if type(binding) is not _VirtualBinding:
            raise TypeError("expected one virtual interface binding")
        self.adapter.validate_action(binding.parent)
        self.validate_side(binding.side)
        if type(binding.cell) is not SourceCellID:
            raise TypeError("virtual interface requires a scoped source cell")
        self.sources.resolve(binding.cell)
        self.layers.validate_optional(binding.layer)
        self.validate_atom(binding.anchor)
        self.validate_atom(binding.argument)
        if type(binding.reverse) is not bool:
            raise TypeError("virtual interface direction must be Boolean")

    def resolve_port(self, state: PortStateID) -> _ComposedPort:
        if type(state) is not PortStateID:
            raise TypeError("expected a scoped concrete port state")
        state.validate(self.owner, self._PORT_KIND, size=self._next_port)
        try:
            return self._ports[state.local_id]
        except KeyError as exc:
            raise ValueError("stale concrete port state") from exc

    def resolve_residual(self, residual: ResidualBindingID) -> _Residual:
        if type(residual) is not ResidualBindingID:
            raise TypeError("expected a scoped residual binding")
        residual.validate(self.owner, self._RESIDUAL_KIND, size=self._next_residual)
        try:
            return self._residuals[residual.local_id]
        except KeyError as exc:
            raise ValueError("stale concrete residual binding") from exc

    def intern_port(self, record: _ComposedPort) -> PortStateID:
        self.adapter.validate_action(record.action)
        self.validate_side(record.side)
        self.validate_atom(record.anchor)
        self.resolve_residual(record.residual)
        found = self._port_keys.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.CONCRETE_PORT_STATE_ALIAS_HITS)
            return self._port_id(found)
        self.ledger.reserve_many(
            ((self._port_owner, 1, 1), (self._port_key_owner, 1, 0)),
        )
        local_id = self._next_port
        self._next_port += 1
        self._ports[local_id] = record
        self._port_keys[record] = local_id
        self.ledger.bump(_execution_keys.CONCRETE_PORT_STATE_PUBLICATIONS)
        return self._port_id(local_id)

    def intern_residual(self, record: _Residual) -> ResidualBindingID:
        """Hash-cons a validated residual under this scheduler's ledger."""
        validate_residual(self, record)
        found = self._residual_keys.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.CONCRETE_RESIDUAL_ALIAS_HITS)
            return self._residual_id(found)
        self.ledger.reserve_many(
            ((self._residual_owner, 1, 1), (self._residual_key_owner, 1, 0))
        )
        local_id = self._next_residual
        self._next_residual += 1
        self._residuals[local_id] = record
        self._residual_keys[record] = local_id
        self.ledger.bump(_execution_keys.CONCRETE_RESIDUAL_PUBLICATIONS)
        return self._residual_id(local_id)

    def validate_atom(self, state: object) -> None:
        if type(state) is int:
            return
        if type(state) is PortStateID:
            self.resolve_port(state)
            return
        if type(state) is RuntimeValueID:
            validator = getattr(self.adapter, "validate_canonical_atom", None)
            if validator is None:
                raise TypeError("adapter does not admit canonical runtime ports")
            cast(Callable[[RuntimeValueID], object], validator)(state)
            return
        raise TypeError("concrete port is neither an exact scalar nor scoped state")

    def validate_side(self, side: object) -> int:
        if type(side) is not int:
            raise TypeError("concrete port side must be an exact integer")
        if side not in (0, 1):
            raise ValueError("concrete port side must be zero or one")
        return side

    def validate_action_state(
        self,
        action: FieldCellActionID,
        side: int,
        state: PortAtom,
    ) -> None:
        children = self.adapter.children(action)
        if type(state) is RuntimeValueID:
            validator = getattr(self.adapter, "validate_canonical_atom", None)
            if validator is None:
                raise TypeError("adapter does not admit canonical runtime ports")
            cast(Callable[[RuntimeValueID], object], validator)(state)
            return
        if children is None:
            if type(state) is not int:
                raise TypeError("primitive concrete port requires an exact scalar")
            count = self.adapter.primitive_state_count(action, side)
            if type(count) is not int or count <= 0:
                raise ValueError("primitive concrete port has an invalid state count")
            if not 0 <= state < count:
                raise ValueError("primitive concrete port state lies outside its port")
            return
        if type(state) is not PortStateID:
            raise TypeError("composed concrete port requires a scoped state")
        record = self.resolve_port(state)
        if record.action != action or record.side != side:
            raise ValueError("concrete port state belongs to another action or side")

    def initial(self, action: FieldCellActionID, side: int) -> PortAtom:
        self.adapter.validate_action(action)
        side = self.validate_side(side)
        return self.run(("INIT", action, side))

    @staticmethod
    def opposite(side: int) -> int:
        return 1 - side

    def cell_parts(
        self,
        cell: SourceCellID,
        reverse: bool,
    ) -> tuple[SourceCellID, SourceCellID]:
        left, right = self.sources.children(cell)
        return (right, left) if reverse else (left, right)

    def advance(
        self,
        action: FieldCellActionID,
        side: int,
        state: PortAtom,
        cell: SourceCellID,
        *,
        reverse: bool = False,
    ) -> PortAtom:
        self.adapter.validate_action(action)
        side = self.validate_side(side)
        self.validate_action_state(action, side, state)
        if type(cell) is not SourceCellID:
            raise TypeError("concrete advance requires a scoped source cell")
        self.sources.resolve(cell)
        if type(reverse) is not bool:
            raise TypeError("concrete traversal direction must be Boolean")
        return self.run(("ADV", action, side, state, cell, None, reverse))

    def emit(
        self,
        action: FieldCellActionID,
        left: PortAtom,
        symbol_cell: SourceCellID,
        right: PortAtom,
    ) -> int:
        self.adapter.validate_action(action)
        self.validate_action_state(action, 0, left)
        self.validate_action_state(action, 1, right)
        if type(symbol_cell) is not SourceCellID:
            raise TypeError("concrete emission requires a scoped source cell")
        node = self.sources.resolve(symbol_cell)
        if node.level:
            raise ValueError("concrete emission requires one source leaf")
        result = self.run(("EMIT", action, left, right, symbol_cell, None))
        if type(result) is not int:
            raise AssertionError("concrete emission returned a structured port")
        return result

    def boundary(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
    ) -> PortAtom:
        state = self.initial(action, side)
        cells = range_cells(self.sources, source, start, end)
        ordered = cells if side == 0 else tuple(reversed(cells))
        for cell in ordered:
            state = self.advance(action, side, state, cell, reverse=side == 1)
        return state

    def point(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        coordinate: int,
    ) -> int:
        return observe_point(self, action, source, coordinate)

    def width(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
    ) -> int:
        return active_width(self, action, source)

    def run(self, root: tuple[object, ...]) -> PortAtom:
        from number_compiler.hashlife.execution.continuations.concrete_dependencies import (
            run_tasks,
        )

        return run_tasks(self, root)

    def cached_result(self, key: tuple[object, ...]) -> PortAtom | None:
        """Read a completed task without exposing the retained memo."""
        return self._memo.get(key)

    @property
    def virtual_bindings(self) -> Mapping[_VirtualBinding, VirtualInterfaceID]:
        """Read the scheduler's admitted virtual interface bindings."""
        return self._virtual_bindings

    def store_result(self, key: tuple[object, ...], value: PortAtom) -> None:
        if key in self._memo:
            return
        self.ledger.reserve(self._memo_owner, entries=1)
        self._memo[key] = value
        self.ledger.bump(_execution_keys.CONCRETE_PORT_TASK_EVALUATIONS)
        if key and type(key[0]) is str:
            self.ledger.bump(f"concrete_port_{str(key[0]).lower()}_evaluations")


__all__ = [
    "ConcretePortAdapter",
    "ConcretePortScheduler",
    "PortAtom",
    "PortStateID",
    "ProviderLayer",
    "ProviderLayerID",
    "ResidualBindingID",
    "VirtualInterfaceID",
]
