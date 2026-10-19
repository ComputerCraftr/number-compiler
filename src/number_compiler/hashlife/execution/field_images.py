"""Canonical original cells and recursive semantic future images.

An occurrence binding mentions a source cell.  The interned future image does
not: its identity is the complete recursive behavior assembled from canonical
child images, one bounded interface, one coordinate morphism, and geometry.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import Protocol, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicTile,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    existing_join as existing_dyadic_join,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryArena,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_image_domains import (
    FieldImageDomain,
    FieldImageDomainEntry,
    FieldImageDomainKey,
    FieldImageInterfaceAuthority,
    FieldImageOutputAuthority,
    FieldInterfaceArena,
    register_field_image_domain,
    validate_field_image_authorities,
)
from number_compiler.hashlife.execution.field_image_summaries import (
    FieldImageSummary,
    FieldImageSummaryRef,
    ParametricFieldImageSummary,
)
from number_compiler.hashlife.execution.source_image_seals import (
    TypedPayloadKey,
    require_immutable_key,
)
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.resources.field_image_audit_contracts import (
    RecursiveFieldImageAuditSnapshot,
    SourceCellArenaAuditSnapshot,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.stores import (
    NodeIndexFactory,
    append_indexed_node,
)


@dataclass(frozen=True, slots=True)
class SourceCellID(ArenaHandle):
    """Scoped identity of immutable original-source geometry."""


@dataclass(frozen=True, slots=True)
class SourceForestID(ArenaHandle):
    """Scoped identity of a complete immutable original-source dyadic forest."""


SourceBindingID = SourceCellID | SourceForestID


@dataclass(frozen=True, slots=True)
class FieldImageID(ArenaHandle):
    """Scoped identity of a recursive semantic future macrocell."""


@dataclass(frozen=True, slots=True)
class SourceCellRecord:
    level: int
    source_tile: DyadicTile
    left: int = -1
    right: int = -1
    uniform_symbol: int | None = None

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.level, self.left, self.right)):
            raise TypeError("source-cell metadata requires exact integers")
        if type(self.source_tile) is not DyadicTile:
            raise TypeError("source cells require canonical immutable source tiles")
        if self.level < 0 or self.source_tile.level != self.level:
            raise ValueError("invalid original-source cell")
        if self.level == 0 and (self.left != -1 or self.right != -1):
            raise ValueError("source leaf cannot own child cells")
        if self.level > 0 and (self.left < 0 or self.right < 0):
            raise ValueError("source parent requires canonical children")
        if self.level == 0 and self.uniform_symbol != self.source_tile.symbol:
            raise ValueError("source leaf uniform summary disagrees with its symbol")
        if self.uniform_symbol is not None and type(self.uniform_symbol) is not int:
            raise TypeError("source uniform summary requires an exact symbol")

    @property
    def width(self) -> int:
        return 1 << self.level


@dataclass(frozen=True, slots=True)
class SourceForestRecord:
    """Canonical left-to-right cover of one complete source occurrence."""

    cells: tuple[SourceCellID, ...]
    extent: int

    def __post_init__(self) -> None:
        if type(self.cells) is not tuple or not self.cells:
            raise ValueError("source forest requires a nonempty canonical cover")
        if type(self.extent) is not int or self.extent < 1:
            raise ValueError("source forest requires a positive exact extent")
        if any(type(cell) is not SourceCellID for cell in self.cells):
            raise TypeError("source forest contains another handle sort")
        owner = self.cells[0].owner
        if any(
            cell.owner is not owner or cell.kind != "source-cell" for cell in self.cells
        ):
            raise ValueError("source forest cells must belong to one source arena")


class SourceCellArena:
    """Scoped structural view of immutable original-source geometry."""

    _nodes: MutableSequence[SourceCellRecord]
    _keys: MutableMapping[DyadicTile, int]

    _KIND = "source-cell"
    _FOREST_KIND = "source-forest"

    def __init__(self, source: SourceGeometry) -> None:
        self.source = source
        self.ledger = source.ledger
        self.owner = ArenaToken("source-cells")
        self.ledger.register_execution_root(self)
        prefix = f"source-cells-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "source_cell")
        self._key_owner = self.ledger.register(
            prefix + "-interner", "source_cell_interner"
        )
        self._nodes, self._keys = NodeIndexFactory[SourceCellRecord, DyadicTile].dense(
            self.ledger, self._node_owner, self._key_owner
        )
        self._forest_node_owner = self.ledger.register(
            prefix + "-forest-nodes", "source_forest"
        )
        self._forest_key_owner = self.ledger.register(
            prefix + "-forest-keys", "source_forest_interner"
        )
        self._forests, self._forest_keys = NodeIndexFactory[
            SourceForestRecord, tuple[tuple[int, ...], int]
        ].dense(self.ledger, self._forest_node_owner, self._forest_key_owner)

    def _handle(self, local_id: int) -> SourceCellID:
        return SourceCellID(self.owner, self._KIND, local_id)

    @property
    def source_kind(self) -> str:
        """Nominal handle kind for original source cells."""
        return self._KIND

    @property
    def forest_kind(self) -> str:
        """Nominal handle kind for complete source forests."""
        return self._FOREST_KIND

    def _forest_handle(self, local_id: int) -> SourceForestID:
        return SourceForestID(self.owner, self._FOREST_KIND, local_id)

    def resolve(self, reference: SourceCellID) -> SourceCellRecord:
        if type(reference) is not SourceCellID:
            raise TypeError("expected an original source-cell ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def resolve_forest(self, reference: SourceForestID) -> SourceForestRecord:
        if type(reference) is not SourceForestID:
            raise TypeError("expected an original source-forest ID")
        reference.validate(self.owner, self._FOREST_KIND, size=len(self._forests))
        return self._forests[reference.local_id]

    def audit_snapshot(self) -> SourceCellArenaAuditSnapshot:
        """Expose current stores read-only to the explicit forensic auditor."""
        return SourceCellArenaAuditSnapshot(
            self.ledger,
            self.owner,
            self._KIND,
            self._node_owner,
            self._nodes,
            self._key_owner,
            self._keys,
            self._FOREST_KIND,
            self._forest_node_owner,
            self._forests,
            self._forest_key_owner,
            self._forest_keys,
        )

    def forest(self, start: int, extent: int) -> SourceForestID:
        """Intern a complete occurrence using only existing original source cells."""
        if type(start) is not int or type(extent) is not int:
            raise TypeError("source forest geometry requires exact integers")
        if start < 0 or extent < 1:
            raise ValueError("source forest geometry is outside the source")
        end = start + extent
        tiles = self.source.range_tiles(start, end)
        position = start
        cells: list[SourceCellID] = []
        for tile in tiles:
            cells.append(self.intern(position, tile.level))
            position += tile.width
        if position != end:
            raise AssertionError("source range did not produce an exact dyadic cover")
        return self.forest_from_cells(tuple(cells))

    def forest_from_cells(self, cells: tuple[SourceCellID, ...]) -> SourceForestID:
        """Intern a canonical contiguous cover assembled from source-cell IDs."""
        if type(cells) is not tuple or not cells:
            raise ValueError("source forest requires a nonempty cell cover")
        for cell in cells:
            self.resolve(cell)
        extent = sum(self.resolve(cell).width for cell in cells)
        record = SourceForestRecord(cells, extent)
        key = tuple(cell.local_id for cell in record.cells), extent
        found = self._forest_keys.get(key)
        if found is not None:
            self.ledger.bump(_execution_keys.SOURCE_FOREST_INTERNER_HITS)
            return self._forest_handle(found)
        found = append_indexed_node(
            self.ledger,
            self._forests,
            self._forest_keys,
            self._forest_node_owner,
            self._forest_key_owner,
            key,
            record,
        )
        self.ledger.bump(_execution_keys.SOURCE_FOREST_PUBLICATIONS)
        return self._forest_handle(found)

    def forest_read(self, forest: SourceForestID, coordinate: int) -> int:
        """Read through the scoped forest binding without consulting occurrence maps."""
        record = self.resolve_forest(forest)
        if type(coordinate) is not int or not 0 <= coordinate < record.extent:
            raise IndexError(coordinate)
        offset = coordinate
        for cell in record.cells:
            node = self.resolve(cell)
            if offset >= node.width:
                offset -= node.width
                continue
            self.ledger.bump(_execution_keys.SOURCE_FOREST_LEAF_READS)
            return self._read_tile(node.source_tile, offset)
        raise AssertionError("source forest extent disagrees with its cells")

    @staticmethod
    def _read_tile(tile: DyadicTile, coordinate: int) -> int:
        current = tile
        offset = coordinate
        while current.level:
            left, right = current.left, current.right
            if left is None or right is None:
                raise AssertionError("source parent has no canonical children")
            if offset < left.width:
                current = left
            else:
                offset -= left.width
                current = right
        if current.symbol is None:
            raise AssertionError("source leaf has no symbol")
        return current.symbol

    def binding_extent(self, source: SourceBindingID) -> int:
        """Return exact immutable geometry for a scoped cell or forest binding."""
        if type(source) is SourceCellID:
            return self.resolve(source).width
        if type(source) is SourceForestID:
            return self.resolve_forest(source).extent
        raise TypeError("expected a scoped source binding")

    def binding_read(self, source: SourceBindingID, coordinate: int) -> int:
        """Read an original symbol solely through the supplied scoped binding."""
        if type(coordinate) is not int:
            raise TypeError("source coordinate must be an exact integer")
        extent = self.binding_extent(source)
        if not 0 <= coordinate < extent:
            raise IndexError(coordinate)
        if type(source) is SourceForestID:
            return self.forest_read(source, coordinate)
        if type(source) is not SourceCellID:
            raise TypeError("expected a scoped source binding")
        self.ledger.bump(_execution_keys.SOURCE_CELL_BINDING_READS)
        return self._read_tile(self.resolve(source).source_tile, coordinate)

    def intern(self, start: int, level: int) -> SourceCellID:
        if type(start) is not int or type(level) is not int:
            raise TypeError("source coordinates require exact integers")
        if start < 0 or level < 0:
            raise ValueError("negative source geometry")
        tile = self.source.tile_at(start, level)
        if tile is None:
            raise ValueError("source cell is not an existing dyadic subtree")
        found = self._keys.get(tile)
        if found is not None:
            self.ledger.bump(_execution_keys.SOURCE_CELL_INTERNER_HITS)
            return self._handle(found)
        pending: list[tuple[DyadicTile, bool]] = [(tile, False)]
        while pending:
            current, ready = pending.pop()
            if current in self._keys:
                continue
            if current.level and not ready:
                if current.left is None or current.right is None:
                    raise AssertionError("source parent has no canonical children")
                pending.append((current, True))
                if current.right not in self._keys:
                    pending.append((current.right, False))
                if current.left not in self._keys:
                    pending.append((current.left, False))
                continue
            left = right = -1
            if current.level:
                if current.left is None or current.right is None:
                    raise AssertionError("source parent has no canonical children")
                left = self._keys[current.left]
                right = self._keys[current.right]
            if current.level == 0:
                uniform_symbol = current.symbol
            else:
                left_uniform = self._nodes[left].uniform_symbol
                right_uniform = self._nodes[right].uniform_symbol
                uniform_symbol = (
                    left_uniform
                    if left_uniform is not None and left_uniform == right_uniform
                    else None
                )
            record = SourceCellRecord(
                current.level,
                current,
                left,
                right,
                uniform_symbol,
            )
            append_indexed_node(
                self.ledger,
                self._nodes,
                self._keys,
                self._node_owner,
                self._key_owner,
                current,
                record,
            )
            self.ledger.bump(_execution_keys.SOURCE_CELL_PUBLICATIONS)
        return self._handle(self._keys[tile])

    def children(self, source: SourceCellID) -> tuple[SourceCellID, SourceCellID]:
        record = self.resolve(source)
        if record.level == 0:
            raise ValueError("a source leaf has no children")
        return self._handle(record.left), self._handle(record.right)

    def existing_join(
        self,
        left: SourceCellID,
        right: SourceCellID,
    ) -> SourceCellID | None:
        """Return an already interned immutable source parent, never allocate."""
        left_record, right_record = self.resolve(left), self.resolve(right)
        parent = existing_dyadic_join(
            left_record.source_tile,
            right_record.source_tile,
        )
        if parent is None:
            return None
        local_id = self._keys.get(parent)
        return None if local_id is None else self._handle(local_id)

    def symbol(self, source: SourceCellID) -> int:
        record = self.resolve(source)
        if record.level != 0:
            raise ValueError("only original leaves contain symbols")
        if record.source_tile.symbol is None:
            raise AssertionError("source leaf has no symbol")
        self.ledger.bump(_execution_keys.SOURCE_LEAF_VISITS)
        return record.source_tile.symbol

    def alphabet(self) -> tuple[int, int]:
        """Return immutable source alphabet metadata without exposing its digits."""
        original = self.source._construction.source
        return original.base, original.blank


@dataclass(frozen=True, slots=True)
class FieldImageRecord:
    level: int
    left: FieldImageID | None
    right: FieldImageID | None
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    geometry: FieldGeometryID
    summary: FieldImageSummaryRef

    def __post_init__(self) -> None:
        if type(self.level) is not int:
            raise TypeError("field image level requires an exact integer")
        if self.level < 0:
            raise ValueError("negative field-image level")
        has_left, has_right = self.left is not None, self.right is not None
        if has_left != has_right:
            raise ValueError("field images require zero or two canonical children")
        if self.level == 0 and has_left:
            raise ValueError("image leaf cannot own children")
        if self.level > 0 and not has_left:
            raise ValueError(
                "field-image parents require two recursive child references"
            )
        if has_left and (
            type(self.left) is not FieldImageID
            or type(self.right) is not FieldImageID
            or self.left.owner is not self.right.owner
            or self.left.kind != self.right.kind
        ):
            raise TypeError("field image children require one scoped image arena")
        if type(self.interface) is not LocalInterfaceID:
            raise TypeError("field image requires a bounded local interface")
        if type(self.output) is not CoordinateOutputMorphismID:
            raise TypeError("field image requires a coordinate output morphism")
        if type(self.geometry) is not FieldGeometryID:
            raise TypeError("field image requires normalized geometry")
        if type(self.summary) not in (FieldImageSummary, ParametricFieldImageSummary):
            raise TypeError("field image requires an activity/extent summary")
        self.summary.__post_init__()
        if (
            type(self.summary) is ParametricFieldImageSummary
            and self.summary.interface != self.interface
        ):
            raise ValueError("parametric image summary has another local interface")


@dataclass(frozen=True, slots=True, eq=False)
class ImageRequestKey:
    action: FieldCellActionID
    source: SourceBindingID
    geometry: FieldGeometryID
    signature: PortSignatureID
    # An active boundary belongs to this source occurrence, not to the
    # canonical arithmetic action or the interned semantic image.
    active_extent: int | None = None
    # Optional adapter-owned recurrence context. It is deliberately in the
    # occurrence key, so a context-qualified request cannot hit an image
    # produced for another temporal/geometry state.
    context: object | None = None

    def __hash__(self) -> int:
        return hash(
            (
                self.action,
                self.source,
                self.geometry,
                self.signature,
                self.active_extent,
                TypedPayloadKey(self.context),
            )
        )

    def __eq__(self, other: object) -> bool:
        return (
            type(other) is ImageRequestKey
            and self.action == other.action
            and self.source == other.source
            and self.geometry == other.geometry
            and self.signature == other.signature
            and self.active_extent == other.active_extent
            and TypedPayloadKey(self.context) == TypedPayloadKey(other.context)
        )


@dataclass(frozen=True, slots=True)
class FieldImageSemanticKey:
    level: int
    left: FieldImageID | None
    right: FieldImageID | None
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    geometry: FieldGeometryID
    summary: FieldImageSummaryRef


class _InterfaceRecord(Protocol):
    signature: PortSignatureID


class RecursiveFieldImageArena:
    """Strong canonical recursive images with evictable occurrence bindings.

    A field-image node is a constant-size semantic record, not exact digit
    geometry.  Its ID therefore remains resolvable for the index lifetime.
    Source occurrence bindings may be discarded and reconstructed around those
    stable semantic identities. Publishers retaining authenticated occurrences
    can retain their binding authority for the arena lifetime instead. Those
    bindings remain charged and are released explicitly by ``clear_bindings``.
    """

    _nodes: MutableMapping[int, FieldImageRecord]
    _keys: MutableMapping[FieldImageSemanticKey, int]

    _KIND = "field-image"

    def __init__(
        self,
        ledger: ResourceLedger,
        sources: SourceCellArena,
        geometries: FieldGeometryArena,
        interfaces: FieldInterfaceArena,
        *,
        action_owner: ArenaToken,
        output_owner: ArenaToken,
        signature_owner: ArenaToken,
        action_validate: Callable[[FieldCellActionID], object],
        output_validate: Callable[[CoordinateOutputMorphismID], object],
        signature_for: Callable[[FieldCellActionID, FieldGeometryID], PortSignatureID],
        action_authority: object | None = None,
        output_authority: object | None = None,
        signature_authority: object | None = None,
        action_kind: str = "field-cell-action",
        output_kind: str = "coordinate-output-morphism",
        signature_kind: str = "diamond-semantic-signature",
        retain_occurrence_authority: bool = False,
    ) -> None:
        if type(retain_occurrence_authority) is not bool:
            raise TypeError("field image authority retention requires a boolean")
        if any(
            owner.ledger is not ledger for owner in (sources, geometries, interfaces)
        ):
            raise ValueError("field-image arenas require one index ledger")
        self.ledger = ledger
        self.sources = sources
        self.geometries = geometries
        self.interfaces = interfaces
        if not all(
            callable(item)
            for item in (
                action_validate,
                output_validate,
                signature_for,
            )
        ):
            raise TypeError("field-image arenas require allocated-range validators")
        if type(action_owner) is not ArenaToken or type(output_owner) is not ArenaToken:
            raise TypeError("field-image semantic owners require arena tokens")
        if (
            type(action_kind) is not str
            or not action_kind
            or type(output_kind) is not str
            or not output_kind
        ):
            raise ValueError("field-image semantic sorts must be nonempty strings")
        if signature_owner is not interfaces.owner:
            raise ValueError("field-image signatures must belong to the quotient arena")
        if type(signature_kind) is not str or not signature_kind:
            raise ValueError("field-image signatures require a scoped semantic sort")
        if any(
            item is None
            for item in (
                action_authority,
                output_authority,
                signature_authority,
            )
        ):
            raise ValueError("field-image authorities must be supplied together")
        assert action_authority is not None
        assert output_authority is not None
        assert signature_authority is not None
        validate_field_image_authorities(
            ledger,
            action_authority,
            action_validate,
            output_authority,
            output_validate,
            signature_authority,
            signature_for,
        )
        self.action_owner = action_owner
        self.output_owner = output_owner
        self.signature_owner = signature_owner
        self.action_kind = action_kind
        self.output_kind = output_kind
        self.signature_kind = signature_kind
        self._action_validate = action_validate
        self._output_validate = output_validate
        self.owner = ArenaToken("field-images")
        self._next_id = 0
        self.ledger.register_execution_root(self)
        prefix = f"field-images-{len(ledger.inventory())}"
        self._domain_owner = ledger.register(
            prefix + "-domains", "field_image_semantic_domain"
        )
        self._domains: MutableMapping[FieldImageDomainKey, FieldImageDomainEntry] = (
            ledger.make_dict(self._domain_owner)
        )
        self.ledger.register_container(
            self._domain_owner,
            self._domains,
            payloads=self._domains.items,
        )
        register_field_image_domain(
            self.ledger,
            self._domain_owner,
            self._domains,
            interfaces,
            action_owner=action_owner,
            action_kind=action_kind,
            action_validate=action_validate,
            output_owner=output_owner,
            output_kind=output_kind,
            output_validate=output_validate,
            signature_kind=signature_kind,
            signature_for=signature_for,
            action_authority=action_authority,
            output_authority=output_authority,
            signature_authority=signature_authority,
        )
        self._node_owner = ledger.register(prefix + "-nodes", "field_image")
        self._key_owner = ledger.register(prefix + "-interner", "field_image_interner")
        self._binding_owner = ledger.register(prefix + "-bindings", "spatial_binding")
        self._nodes, self._keys = NodeIndexFactory[
            FieldImageRecord, FieldImageSemanticKey
        ].sparse(ledger, self._node_owner, self._key_owner)
        self._bindings: MutableMapping[ImageRequestKey, FieldImageID] = (
            ledger.make_dict(self._binding_owner)
        )
        self.ledger.register_container(
            self._binding_owner,
            self._bindings,
            node_count=lambda: 0,
            payloads=self._bindings.items,
            evict=None if retain_occurrence_authority else self.clear_bindings,
        )

    def admit_domain(
        self,
        interfaces: FieldInterfaceArena,
        *,
        action_owner: ArenaToken,
        action_kind: str,
        action_validate: Callable[[FieldCellActionID], object],
        output_owner: ArenaToken,
        output_kind: str,
        output_validate: Callable[[CoordinateOutputMorphismID], object],
        signature_kind: str,
        signature_for: Callable[[FieldCellActionID, FieldGeometryID], PortSignatureID],
        action_authority: object,
        output_authority: object,
        signature_authority: object,
    ) -> None:
        """Admit one exact semantic sort tuple into the shared image arena."""
        register_field_image_domain(
            self.ledger,
            self._domain_owner,
            self._domains,
            interfaces,
            action_owner=action_owner,
            action_kind=action_kind,
            action_validate=action_validate,
            output_owner=output_owner,
            output_kind=output_kind,
            output_validate=output_validate,
            signature_kind=signature_kind,
            signature_for=signature_for,
            action_authority=action_authority,
            output_authority=output_authority,
            signature_authority=signature_authority,
        )

    def _domain(self, action: FieldCellActionID) -> FieldImageDomain:
        if type(action) is not FieldCellActionID:
            raise TypeError("image request requires a field action")
        ArenaHandle.__post_init__(action)
        found = self._domains.get(
            FieldImageDomainKey("action", action.owner, action.kind)
        )
        if type(found) is not FieldImageDomain:
            raise ValueError("field action belongs to a different arena or node kind")
        action.validate(found.action_owner, found.action_kind)
        found.action_validate(action)
        return found

    def resolve_interface(self, reference: LocalInterfaceID) -> _InterfaceRecord:
        """Resolve an interface through its exact admitted semantic domain."""
        if type(reference) is not LocalInterfaceID:
            raise TypeError("field image requires a local interface ID")
        ArenaHandle.__post_init__(reference)
        found = self._domains.get(
            FieldImageDomainKey("interface", reference.owner, reference.kind),
        )
        if type(found) is not FieldImageInterfaceAuthority:
            raise ValueError("local interface belongs to an unregistered image domain")
        return cast(_InterfaceRecord, found.arena.resolve(reference))

    def _handle(self, local_id: int) -> FieldImageID:
        return FieldImageID(self.owner, self._KIND, local_id)

    def resolve(self, reference: FieldImageID) -> FieldImageRecord:
        if type(reference) is not FieldImageID:
            raise TypeError("expected a recursive field-image ID")
        reference.validate(self.owner, self._KIND, size=self._next_id)
        found = self._nodes.get(reference.local_id)
        if found is None:
            raise ValueError("field-image ID is stale or was never published")
        return found

    def audit_snapshot(self) -> RecursiveFieldImageAuditSnapshot:
        """Expose current stores read-only to the explicit forensic auditor."""
        return RecursiveFieldImageAuditSnapshot(
            self.ledger,
            self.owner,
            self._KIND,
            self._next_id,
            self._domain_owner,
            self._domains,
            self._node_owner,
            self._nodes,
            self._key_owner,
            self._keys,
            self._binding_owner,
            self._bindings,
        )

    def validate_request(self, key: ImageRequestKey) -> None:
        """Validate every scoped component before consulting an image cache."""
        if type(key) is not ImageRequestKey:
            raise TypeError("expected a canonical image request")
        domain = self._domain(key.action)
        if type(key.source) is SourceCellID:
            key.source.validate(self.sources.owner, self.sources.source_kind)
        elif type(key.source) is SourceForestID:
            key.source.validate(self.sources.owner, self.sources.forest_kind)
        else:
            raise TypeError("image request requires a scoped source binding")
        if type(key.geometry) is not FieldGeometryID:
            raise TypeError("image request requires normalized geometry")
        key.geometry.validate(self.geometries.owner, self.geometries.geometry_kind)
        if type(key.signature) is not PortSignatureID:
            raise TypeError("image request requires a scoped port signature")
        key.signature.validate(domain.interfaces.owner, domain.signature_kind)
        if type(key.source) is SourceCellID:
            self.sources.resolve(key.source)
        else:
            assert type(key.source) is SourceForestID
            self.sources.resolve_forest(key.source)
        if key.active_extent is not None and (
            type(key.active_extent) is not int
            or not 0 <= key.active_extent <= self.sources.binding_extent(key.source)
        ):
            raise ValueError("image request active extent lies outside its source")
        if key.context is not None:
            require_immutable_key(key.context, "provider image request context")
        geometry = self.geometries.resolve(key.geometry)
        # The quotient arena owns every production signature.  Validating its
        # allocated range closes the same-owner forged-integer hole before the
        # binding mapping can be consulted.
        signature = domain.interfaces.interface(key.signature)
        expected_signature = domain.signature_for(key.action, key.geometry)
        if type(expected_signature) is not PortSignatureID:
            raise TypeError("field image signature compiler returned another sort")
        if expected_signature != key.signature:
            raise ValueError(
                "field action has another port signature than its normalized signature"
            )
        if geometry.phase_count != signature.phase_count:
            raise ValueError("field geometry has another interface phase domain")

    def validate_action(self, action: FieldCellActionID) -> None:
        """Validate the scoped sort and allocated action range in that order."""
        self._domain(action)

    def validate_output(self, output: CoordinateOutputMorphismID) -> None:
        """Validate a coordinate morphism's sort, owner, and allocated range."""
        if type(output) is not CoordinateOutputMorphismID:
            raise TypeError("field image requires a coordinate output morphism")
        ArenaHandle.__post_init__(output)
        found = self._domains.get(
            FieldImageDomainKey("output", output.owner, output.kind),
        )
        if type(found) is not FieldImageOutputAuthority:
            raise ValueError(
                "coordinate output belongs to an unregistered image domain"
            )
        output.validate(found.owner, found.kind)
        found.validate(output)

    # Retained for independent payload auditors; execution uses the public
    # spelling above so the validation boundary is explicit.
    def _validate_request(self, key: ImageRequestKey) -> None:
        self.validate_request(key)

    def probe(self, key: ImageRequestKey) -> FieldImageID | None:
        self.validate_request(key)
        self.ledger.bump(_execution_keys.FIELD_IMAGE_BINDING_REQUESTS)
        found = self._bindings.get(key)
        if found is not None:
            self.resolve(found)
            self.ledger.bump(_execution_keys.FIELD_IMAGE_BINDING_EARLY_HITS)
        return found

    def validate_binding(self, key: ImageRequestKey, image: FieldImageID) -> None:
        """Prove one exact occurrence binding without changing metrics or state."""
        self.validate_request(key)
        self.resolve(image)
        if self._bindings.get(key) != image:
            raise ValueError("field image was not published for this occurrence")

    def validate_occurrence(
        self,
        image: FieldImageID,
        source: SourceBindingID,
        action: FieldCellActionID,
        active_extent: int | None = None,
        context: object | None = None,
    ) -> None:
        """Prove an image's exact source/action occurrence without mutation."""
        record = self.resolve(image)
        signature = self.resolve_interface(record.interface).signature
        self.validate_binding(
            ImageRequestKey(
                action, source, record.geometry, signature, active_extent, context
            ),
            image,
        )

    def publish(self, key: ImageRequestKey, record: FieldImageRecord) -> FieldImageID:
        self.validate_request(key)
        if type(record) is not FieldImageRecord:
            raise TypeError("field image publication requires a complete record")
        record.__post_init__()
        domain = self._domain(key.action)
        if (
            record.interface.owner is not domain.interfaces.owner
            or record.interface.kind != domain.interfaces.interface_kind
            or record.output.owner is not domain.output_owner
            or record.output.kind != domain.output_kind
        ):
            raise ValueError("field image result belongs to another semantic domain")
        interface_record = domain.interfaces.resolve(record.interface)
        if interface_record.signature != key.signature:
            raise ValueError("field image interface has another port signature")
        if type(record.summary) is ParametricFieldImageSummary:
            record.summary.validate_range(domain.interfaces)
        normalized_geometry = self.geometries.resolve(record.geometry)
        if record.geometry != key.geometry:
            raise ValueError("field image geometry differs from its request")
        if normalized_geometry.spatial_level != record.level:
            raise ValueError("field image level differs from normalized geometry")
        record.output.validate(domain.output_owner, domain.output_kind)
        (
            self._output_validate
            if domain.output_owner is self.output_owner
            and domain.output_kind == self.output_kind
            else domain.output_validate
        )(record.output)
        if record.left is not None and record.right is not None:
            left = self.resolve(record.left)
            right = self.resolve(record.right)
            if left.level >= record.level or right.level >= record.level:
                raise ValueError("field image children must be spatially smaller")
        if key in self._bindings:
            existing = self._bindings[key]
            if self.resolve(existing) != record:
                raise ValueError(
                    "field image request already has a different semantic result"
                )
            return existing
        semantic = FieldImageSemanticKey(
            record.level,
            record.left,
            record.right,
            record.interface,
            record.output,
            record.geometry,
            record.summary,
        )
        existing_id = self._keys.get(semantic)
        reservations = [(self._binding_owner, 1, 0)]
        if existing_id is None:
            reservations.extend(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        self.ledger.reserve_many(tuple(reservations))
        if existing_id is None:
            existing_id = self._next_id
            self._next_id += 1
            self._nodes[existing_id] = record
            self._keys[semantic] = existing_id
            self.ledger.bump(_execution_keys.NEW_FIELD_IMAGE_NODES)
        else:
            self.ledger.bump(_execution_keys.FIELD_IMAGE_SEMANTIC_ALIAS_HITS)
        result = self._handle(existing_id)
        self._bindings[key] = result
        self.ledger.bump(_execution_keys.FIELD_IMAGE_BINDING_PUBLICATIONS)
        return result

    def children(self, image: FieldImageID) -> tuple[FieldImageID, FieldImageID]:
        record = self.resolve(image)
        if record.left is None or record.right is None:
            raise ValueError("a field-image leaf has no children")
        self.resolve(record.left)
        self.resolve(record.right)
        return record.left, record.right

    @property
    def retained_images(self) -> int:
        return len(self._nodes)

    @property
    def retained_bindings(self) -> int:
        return len(self._bindings)

    def clear_bindings(self) -> None:
        count = len(self._bindings)
        self._bindings.clear()
        self.ledger.release(self._binding_owner, entries=count)


__all__ = [
    "FieldImageSemanticKey",
    "FieldImageID",
    "FieldImageRecord",
    "FieldImageSummary",
    "FieldImageSummaryRef",
    "ImageRequestKey",
    "ParametricFieldImageSummary",
    "RecursiveFieldImageArena",
    "SourceBindingID",
    "SourceCellArena",
    "SourceCellID",
    "SourceCellRecord",
    "SourceForestID",
    "SourceForestRecord",
]
