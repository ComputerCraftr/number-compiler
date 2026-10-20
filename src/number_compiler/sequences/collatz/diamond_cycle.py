"""Source-certified finite physical Collatz cycle, independent of orbit length.

Only canonical original sources 1, 4 and 2 qualify. A three-state phase action
is the complete restriction of physical Collatz to this invariant set; no
future digit field or discovered itinerary is constructed.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


@dataclass(frozen=True, slots=True)
class PhysicalCycleProjection:
    source: ArenaToken
    root: ActionProgramID
    phase: int
    extent: int

    def __post_init__(self) -> None:
        if (
            type(self.source) is not ArenaToken
            or type(self.root) is not ActionProgramID
            or self.root.kind != "diamond-action"
            or type(self.phase) is not int
            or self.phase not in (0, 1, 2)
            or type(self.extent) is not int
            or self.extent < 3
        ):
            raise ValueError("invalid physical cycle certificate")

    def point(self, position: int) -> int:
        if type(position) is not int or position < 0:
            raise ValueError("point coordinate must be nonnegative")
        if position >= self.extent:
            raise IndexError(position)
        high = (0, 2, 1)[self.phase]
        return 2 if position > high else int(position == high)

    def active_width(self, maximum: int | None = None) -> int:
        if maximum is None:
            maximum = self.extent
        if type(maximum) is not int or not 0 <= maximum <= self.extent:
            raise ValueError("width bound must fit the original source extent")
        return min(maximum, (1, 3, 2)[self.phase])


def physical_cycle(
    runtime: DiamondRuntime, root: ActionProgramID
) -> PhysicalCycleProjection | None:
    """Certify the actual source and complete action DAG before phase reduction."""
    runtime.actions.resolve(root)
    geometry = runtime.cells.source_geometry
    source = geometry.construction.source
    source_root = geometry.source_root
    if source.base != 2 or source.blank != 2 or source_root is None:
        return None
    extent = source_root.length
    if extent < 3:
        return None  # A clipped 1 -> 4 transition does not preserve this cycle.
    digits = source.digits
    if digits == (1,):
        phase = 0
    elif digits == (0, 0, 1):
        phase = 1
    elif digits == (0, 1):
        phase = 2
    else:
        return None  # Leading active zeros are not canonical cycle fields.
    pending = [(root, False)]
    residues: dict[ActionProgramID, int] = {}
    while pending:
        action, ready = pending.pop()
        if action in residues:
            continue
        node = runtime.actions.resolve(action)
        runtime.ledger.bump(_collatz_keys.PHYSICAL_CYCLE_ACTION_VISITS)
        if node.kind == "identity":
            residues[action] = 0
        elif node.kind == "atom":
            primitive = runtime.actions.primitive(action)
            if type(primitive) is CollatzPhysicalBlockEffect:
                residues[action] = primitive.exponent % 3
            else:
                hooks = runtime.family_hooks
                if hooks is None or not hooks.owns_compatibility(primitive):
                    return None
                hooks.validate_compatibility(primitive)
                residues[action] = primitive.exponent % 3
        else:
            first, second = (
                runtime.actions.reference(node.first),
                runtime.actions.reference(node.second),
            )
            if not ready:
                pending.extend(((action, True), (second, False), (first, False)))
            else:
                residues[action] = (residues[first] + residues[second]) % 3
    runtime.ledger.bump(_collatz_keys.PHYSICAL_CYCLE_SOURCE_CERTIFICATIONS)
    return PhysicalCycleProjection(
        geometry.token, root, (phase + residues[root]) % 3, extent
    )


def validate_physical_cycle(
    runtime: DiamondRuntime, root: ActionProgramID, value: object
) -> bool:
    """Validate the sealed projection's cheap source/action binding.

    The constructor above performs the complete immutable-action proof once.
    Applications retain its exact returned object; later query and resource
    audits only need to check that it remains bound to that source and root.
    """
    if type(value) is not PhysicalCycleProjection:
        return False
    geometry = runtime.cells.source_geometry
    source = geometry.source_root
    return (
        value.root == root
        and value.source is geometry.token
        and source is not None
        and value.extent == source.length
        and value.phase in (0, 1, 2)
    )


def cycle_point(value: object, position: int) -> int:
    if type(value) is not PhysicalCycleProjection:
        raise TypeError("expected a physical Collatz cycle projection")
    return value.point(position)


def cycle_active_width(value: object, maximum: int | None) -> int:
    if type(value) is not PhysicalCycleProjection:
        raise TypeError("expected a physical Collatz cycle projection")
    return value.active_width(maximum)
