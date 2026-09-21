"""Experimental family-neutral contract for a powered bounded local interface.

The codec is the finite transfer substrate beneath a complete field action.  It
does not own source cells, proof-machine states, exact tiles, or image trees.
Spatial and temporal composition return a bounded interface together with one
coordinate-parametric output morphism; activity, extent, growth, termination,
normalization, and frame channels remain the field adapter's responsibility.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID


@dataclass(frozen=True, slots=True)
class PoweredLocalEffect:
    """Output-complete bounded effect, without an occurrence binding."""

    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID

    def __post_init__(self) -> None:
        if type(self.interface) is not LocalInterfaceID:
            raise TypeError("powered local effect requires a local-interface ID")
        if type(self.output) is not CoordinateOutputMorphismID:
            raise TypeError("powered local effect requires an output-morphism ID")


@runtime_checkable
class PoweredLocalCodec(Protocol):
    """Compose bounded local effects without flattening a continuation domain.

    ``compose_temporal(before, after, ...)`` applies ``before`` and then
    ``after``.  Implementations must canonicalize all proved automorphisms
    before publishing either returned handle.
    """

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def leaf_interface(
        self,
        action: FieldCellActionID,
        source_symbol: int,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> PoweredLocalEffect:
        """Compile one immutable original-source symbol."""
        ...

    def compose_spatial(
        self,
        action: FieldCellActionID,
        left: PoweredLocalEffect,
        right: PoweredLocalEffect,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> PoweredLocalEffect:
        """Compose adjacent effects after a canonical parent-cache miss."""
        ...

    def compose_temporal(
        self,
        before: FieldCellActionID,
        after: FieldCellActionID,
        source: PoweredLocalEffect,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> PoweredLocalEffect:
        """Substitute ``after`` through ``before`` without emitting a midpoint."""
        ...

    def transformed(
        self,
        effect: PoweredLocalEffect,
        transform: ActionTransform,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> PoweredLocalEffect:
        """Apply only a certified mirror/conjugacy automorphism."""
        ...

    def observe_output(
        self,
        effect: PoweredLocalEffect,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int:
        """Observe one coordinate without allocating exact future geometry."""
        ...


__all__ = ["PoweredLocalCodec", "PoweredLocalEffect"]
