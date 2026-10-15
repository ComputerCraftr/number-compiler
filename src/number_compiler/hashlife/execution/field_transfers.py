"""Parametric bounded transfers used by point and width observations.

Transfers are deliberately separate from exact recursive future images.  A
transfer binds one original source macrocell to a complete bounded interface
and one coordinate output morphism.  It has no child-image references and is
parametric over the values admitted by its port signature.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryArena,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
    LocalInterfaceID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.stores import make_node_index


@dataclass(frozen=True, slots=True)
class FieldTransferID(ArenaHandle):
    """Scoped identity of one bounded source-bound transfer."""


@dataclass(frozen=True, slots=True)
class FieldTransferRecord:
    """Complete parametric behavior plus conservative observation geometry.

    ``extent_bound`` is solely an admission bound.  The exact activity and
    extent may depend on the incoming port and remain executable components of
    ``interface``; publishing one concrete :class:`FieldImageSummary` here
    would falsely specialize a parametric transfer before that port is bound.
    """

    level: int
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    geometry: FieldGeometryID
    extent_bound: int

    def __post_init__(self) -> None:
        if type(self.level) is not int or self.level < 0:
            raise ValueError("field transfer level must be a nonnegative exact integer")
        if type(self.interface) is not LocalInterfaceID:
            raise TypeError("field transfer requires a bounded local interface")
        if type(self.output) is not CoordinateOutputMorphismID:
            raise TypeError("field transfer requires a coordinate output morphism")
        if type(self.geometry) is not FieldGeometryID:
            raise TypeError("field transfer requires normalized local geometry")
        if type(self.extent_bound) is not int or self.extent_bound < 0:
            raise ValueError("field transfer requires a nonnegative exact extent bound")


@dataclass(frozen=True, slots=True)
class FieldTransferRequestKey:
    """Occurrence binding; the signature is a schema, never a port value."""

    action: FieldCellActionID
    source: SourceBindingID
    geometry: FieldGeometryID
    signature: PortSignatureID


@dataclass(frozen=True, slots=True)
class _TransferKey:
    """Canonical behavior only; occurrence admission bounds stay on records."""

    level: int
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    geometry: FieldGeometryID


class FieldTransferArena:
    """Lifetime-stable semantic transfers with evictable occurrence bindings."""

    _nodes: MutableMapping[int, FieldTransferRecord]
    _keys: MutableMapping[_TransferKey, int]

    _KIND = "field-transfer"

    def __init__(
        self,
        ledger: ResourceLedger,
        sources: SourceCellArena,
        geometries: FieldGeometryArena,
        interfaces: DiamondQuotientArena,
        *,
        action_owner: ArenaToken,
        output_owner: ArenaToken,
        action_validate: Callable[[FieldCellActionID], object],
        output_validate: Callable[[CoordinateOutputMorphismID], None],
        action_kind: str = "field-cell-action",
        output_kind: str = "coordinate-output-morphism",
    ) -> None:
        if any(
            owner.ledger is not ledger for owner in (sources, geometries, interfaces)
        ):
            raise ValueError("field-transfer arenas require one index ledger")
        if not callable(action_validate) or not callable(output_validate):
            raise TypeError("field-transfer arenas require allocated-range validators")
        if type(action_owner) is not ArenaToken or type(output_owner) is not ArenaToken:
            raise TypeError("field-transfer semantic owners require arena tokens")
        if (
            type(action_kind) is not str
            or not action_kind
            or type(output_kind) is not str
            or not output_kind
        ):
            raise ValueError("field-transfer semantic sorts must be nonempty strings")
        self.ledger = ledger
        self.sources = sources
        self.geometries = geometries
        self.interfaces = interfaces
        self.action_owner = action_owner
        self.output_owner = output_owner
        self.action_kind = action_kind
        self.output_kind = output_kind
        self._action_validate = action_validate
        self._output_validate = output_validate
        self.owner = ArenaToken("field-transfers")
        self._next_id = 0
        self.ledger.register_execution_root(self)
        prefix = f"field-transfers-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "field_transfer")
        self._key_owner = ledger.register(
            prefix + "-interner", "field_transfer_interner"
        )
        self._binding_owner = ledger.register(
            prefix + "-bindings", "field_transfer_binding"
        )
        self._observation_owner = ledger.register(
            prefix + "-observation-bindings",
            "observation_memo",
        )
        self._nodes, self._keys = make_node_index(
            ledger, self._node_owner, self._key_owner
        )
        self._bindings: MutableMapping[FieldTransferRequestKey, FieldTransferID] = (
            ledger.make_dict(self._binding_owner)
        )
        self._observation_bindings: MutableMapping[
            tuple[FieldTransferID, SourceBindingID], None
        ] = ledger.make_dict(self._observation_owner)
        ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=self._nodes.items,
        )
        ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )
        ledger.register_container(
            self._binding_owner,
            self._bindings,
            payloads=self._bindings.items,
            evict=self.clear_bindings,
        )
        ledger.register_container(
            self._observation_owner,
            self._observation_bindings,
            payloads=self._observation_bindings.items,
            evict=self.clear_bindings,
        )

    def _handle(self, local_id: int) -> FieldTransferID:
        return FieldTransferID(self.owner, self._KIND, local_id)

    def resolve(self, reference: FieldTransferID) -> FieldTransferRecord:
        if type(reference) is not FieldTransferID:
            raise TypeError("expected a bounded field-transfer ID")
        reference.validate(self.owner, self._KIND, size=self._next_id)
        found = self._nodes.get(reference.local_id)
        if found is None:
            raise ValueError("field-transfer ID is stale or was never published")
        return found

    def validate_request(self, key: FieldTransferRequestKey) -> None:
        """Validate every scoped component before consulting a transfer cache."""
        if type(key) is not FieldTransferRequestKey:
            raise TypeError("expected a canonical field-transfer request")
        if type(key.action) is not FieldCellActionID:
            raise TypeError("field-transfer request requires a field action")
        key.action.validate(self.action_owner, self.action_kind)
        if type(key.source) is SourceCellID:
            key.source.validate(self.sources.owner, self.sources._KIND)
        elif type(key.source) is SourceForestID:
            key.source.validate(self.sources.owner, self.sources._FOREST_KIND)
        else:
            raise TypeError("field-transfer request requires a scoped source binding")
        if type(key.geometry) is not FieldGeometryID:
            raise TypeError("field-transfer request requires normalized geometry")
        key.geometry.validate(self.geometries.owner, self.geometries._KIND)
        if type(key.signature) is not PortSignatureID:
            raise TypeError("field-transfer request requires a port signature")
        key.signature.validate(self.interfaces.owner, self.interfaces.signature_kind)
        # Resolve allocated ranges only after every request handle passed the
        # structural owner/kind phase.
        self._action_validate(key.action)
        if type(key.source) is SourceCellID:
            self.sources.resolve(key.source)
        else:
            assert type(key.source) is SourceForestID
            self.sources.resolve_forest(key.source)
        geometry = self.geometries.resolve(key.geometry)
        signature = self.interfaces.interface(key.signature)
        if geometry.phase_count != signature.phase_count:
            raise ValueError("field geometry has another interface phase domain")

    # Retained for independent payload auditors.
    def _validate_request(self, key: FieldTransferRequestKey) -> None:
        self.validate_request(key)

    def probe(self, key: FieldTransferRequestKey) -> FieldTransferID | None:
        self.validate_request(key)
        self.ledger.bump(_execution_keys.FIELD_TRANSFER_BINDING_REQUESTS)
        result = self._bindings.get(key)
        if result is not None:
            self.resolve(result)
            self.ledger.bump(_execution_keys.FIELD_TRANSFER_BINDING_EARLY_HITS)
        return result

    def validate_observation_source(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
    ) -> None:
        """Require a source occurrence actually published for this transfer."""
        self.resolve(transfer)
        if type(source) is SourceCellID:
            self.sources.resolve(source)
        elif type(source) is SourceForestID:
            self.sources.resolve_forest(source)
        else:
            raise TypeError(
                "field-transfer observation requires a scoped source binding"
            )
        if (transfer, source) not in self._observation_bindings:
            raise ValueError("field transfer was not published for this source binding")

    def publish(
        self,
        key: FieldTransferRequestKey,
        record: FieldTransferRecord,
    ) -> FieldTransferID:
        self.validate_request(key)
        if type(record) is not FieldTransferRecord:
            raise TypeError("field-transfer publication requires a complete record")
        record.__post_init__()
        interface_record = self.interfaces.resolve(record.interface)
        if interface_record.signature != key.signature:
            raise ValueError("field transfer interface has another port signature")
        normalized_geometry = self.geometries.resolve(record.geometry)
        if record.geometry != key.geometry:
            raise ValueError("field-transfer geometry differs from its request")
        if normalized_geometry.spatial_level != record.level:
            raise ValueError("field-transfer level differs from normalized geometry")
        record.output.validate(self.output_owner, self.output_kind)
        self._output_validate(record.output)
        bound = self._bindings.get(key)
        if bound is not None:
            if self.resolve(bound) != record:
                raise ValueError("field-transfer request already has another result")
            return bound
        semantic = _TransferKey(
            record.level,
            record.interface,
            record.output,
            record.geometry,
        )
        local_id = self._keys.get(semantic)
        if local_id is not None:
            existing = self._nodes[local_id]
            if existing.extent_bound != record.extent_bound:
                raise ValueError(
                    "equal field-transfer behavior has inconsistent admission bounds"
                )
        reservations: list[tuple[int, int, int]] = [
            (self._binding_owner, 1, 0),
            (self._observation_owner, 1, 0),
        ]
        if local_id is None:
            reservations.extend(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        self.ledger.reserve_many(reservations)
        if local_id is None:
            local_id = self._next_id
            self._nodes[local_id] = record
            self._keys[semantic] = local_id
            self._next_id += 1
            self.ledger.bump(_execution_keys.NEW_FIELD_TRANSFER_NODES)
        else:
            self.ledger.bump(_execution_keys.FIELD_TRANSFER_SEMANTIC_ALIAS_HITS)
        result = self._handle(local_id)
        self._bindings[key] = result
        self._observation_bindings[(result, key.source)] = None
        self.ledger.bump(_execution_keys.FIELD_TRANSFER_BINDING_PUBLICATIONS)
        return result

    def clear_bindings(self) -> None:
        count = len(self._bindings)
        observation_count = len(self._observation_bindings)
        self._bindings.clear()
        self._observation_bindings.clear()
        self.ledger.release(self._binding_owner, entries=count)
        self.ledger.release(self._observation_owner, entries=observation_count)

    def clear(self) -> None:
        """Evict occurrence/query bindings while preserving canonical IDs."""
        self.clear_bindings()

    @property
    def retained_transfers(self) -> int:
        return len(self._nodes)

    @property
    def retained_bindings(self) -> int:
        return len(self._bindings)


__all__ = [
    "FieldTransferArena",
    "FieldTransferID",
    "FieldTransferRecord",
    "FieldTransferRequestKey",
]
