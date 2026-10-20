"""Shared scoped sorts and normalized geometry for algebraic field actions."""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_actions as _actions_keys,
)
from number_compiler.resources.stores import (
    NodeIndexFactory,
    append_indexed_node,
)


@dataclass(frozen=True, slots=True)
class FieldCellActionID(ArenaHandle):
    """Source-independent temporal field action."""


@dataclass(frozen=True, slots=True)
class CoordinateOutputMorphismID(ArenaHandle):
    """Coordinate-parametric output behavior, never an emitted tape."""


@dataclass(frozen=True, slots=True)
class FieldGeometryID(ArenaHandle):
    """Canonical geometry metadata kept outside semantic arithmetic state."""


@dataclass(frozen=True, slots=True)
class FieldGeometry:
    """Normalized local wiring for a dyadic macrocell.

    Absolute origins, generations, complete source widths, source identities,
    and frame displacements deliberately have no slot here.  Those values are
    occurrence/cocycle metadata; admitting them to this interner would split
    otherwise identical parent transfers before their first cache probe.
    """

    spatial_level: int
    orientation: int = 0
    phase: int = 0
    phase_count: int = 1
    halo_left: int = 0
    halo_right: int = 0

    def __post_init__(self) -> None:
        values = (
            self.spatial_level,
            self.orientation,
            self.phase,
            self.phase_count,
            self.halo_left,
            self.halo_right,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("field geometry requires exact integer metadata")
        if self.spatial_level < 0 or self.orientation not in (0, 1):
            raise ValueError("invalid spatial level or orientation")
        if (
            not 1 <= self.phase_count <= 1 << 64
            or not 0 <= self.phase < self.phase_count
        ):
            raise ValueError("field phase is outside its finite domain")
        if self.halo_left < 0 or self.halo_right < 0:
            raise ValueError("negative field geometry")

    def mirrored(self) -> FieldGeometry:
        return FieldGeometry(
            self.spatial_level,
            self.orientation ^ 1,
            self.phase,
            self.phase_count,
            self.halo_right,
            self.halo_left,
        )


@dataclass(frozen=True, slots=True)
class FieldGeometryAuditSnapshot:
    """Read-only references to the exact stores used by an explicit audit."""

    ledger: ResourceLedger
    owner: ArenaToken
    node_kind: str
    node_owner: int
    nodes: Sequence[FieldGeometry]
    key_owner: int
    keys: Mapping[FieldGeometry, int]


class FieldGeometryArena:
    """Index-owned interner for geometry that cannot hide arithmetic payloads."""

    _nodes: MutableSequence[FieldGeometry]
    _keys: MutableMapping[FieldGeometry, int]

    _KIND = "field-geometry"

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ArenaToken("field-geometry")
        self.ledger.register_execution_root(self)
        prefix = f"field-geometry-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "field_geometry")
        self._key_owner = ledger.register(
            prefix + "-interner", "field_geometry_interner"
        )
        self._nodes, self._keys = NodeIndexFactory[FieldGeometry, FieldGeometry].dense(
            ledger, self._node_owner, self._key_owner
        )

    def scoped_handle(self, local_id: int) -> FieldGeometryID:
        return FieldGeometryID(self.owner, self._KIND, local_id)

    @property
    def geometry_kind(self) -> str:
        """Nominal handle kind for this geometry arena."""
        return self._KIND

    def resolve(self, reference: FieldGeometryID) -> FieldGeometry:
        if type(reference) is not FieldGeometryID:
            raise TypeError("expected a field geometry ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def audit_snapshot(self) -> FieldGeometryAuditSnapshot:
        """Expose current stores read-only to the explicit forensic auditor."""
        return FieldGeometryAuditSnapshot(
            self.ledger,
            self.owner,
            self._KIND,
            self._node_owner,
            self._nodes,
            self._key_owner,
            self._keys,
        )

    def intern(self, geometry: FieldGeometry) -> FieldGeometryID:
        if type(geometry) is not FieldGeometry:
            raise TypeError("expected normalized field geometry")
        geometry.__post_init__()
        found = self._keys.get(geometry)
        if found is not None:
            self.ledger.bump(_actions_keys.FIELD_GEOMETRY_INTERNER_HITS)
            return self.scoped_handle(found)
        local_id = append_indexed_node(
            self.ledger,
            self._nodes,
            self._keys,
            self._node_owner,
            self._key_owner,
            geometry,
            geometry,
        )
        self.ledger.bump(_actions_keys.FIELD_GEOMETRY_PUBLICATIONS)
        return self.scoped_handle(local_id)

    def child(self, parent: FieldGeometryID, side: int) -> FieldGeometryID:
        """Return normalized geometry for one spatial child without recursion."""
        geometry = self.resolve(parent)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("field child side must be zero or one")
        if geometry.spatial_level == 0:
            raise ValueError("field leaf has no child geometry")
        return self.intern(
            FieldGeometry(
                geometry.spatial_level - 1,
                geometry.orientation,
                geometry.phase,
                geometry.phase_count,
                geometry.halo_left,
                geometry.halo_right,
            )
        )


__all__ = [
    "CoordinateOutputMorphismID",
    "FieldCellActionID",
    "FieldGeometry",
    "FieldGeometryAuditSnapshot",
    "FieldGeometryArena",
    "FieldGeometryID",
]
