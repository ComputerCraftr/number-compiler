"""Typed finite ports and exact boundary operands for tile execution."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.tiles.tile_boundaries import (
    EMPTY_BOUNDARY_TILES,
    BoundaryTileOperands,
)


@dataclass(frozen=True, slots=True)
class ResultWiring:
    """Normalized finite wiring; absolute coordinates never enter an identity."""

    signature: PortSignatureID
    orientation: int = 0
    phase: int = 0

    def __post_init__(self) -> None:
        if type(self.signature) is not PortSignatureID:
            raise TypeError("result wiring requires a scoped port signature")
        if type(self.orientation) is not int or self.orientation not in (0, 1):
            raise ValueError("result orientation must be zero or one")
        if type(self.phase) is not int or self.phase < 0:
            raise ValueError("result phase requires a nonnegative exact integer")


@dataclass(frozen=True, slots=True)
class BoundPorts:
    """One temporal edge's finite assignment and exact spatial operands."""

    ports: tuple[int, ...]
    wiring: ResultWiring
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES

    def __post_init__(self) -> None:
        if type(self.ports) is not tuple or any(
            type(value) is not int for value in self.ports
        ):
            raise TypeError("bound ports require exact immutable integers")
        if type(self.wiring) is not ResultWiring:
            raise TypeError("bound ports require normalized wiring")
        self.wiring.__post_init__()
        if type(self.boundaries) is not BoundaryTileOperands:
            raise TypeError("bound ports require exact boundary operands")
        self.boundaries.__post_init__()

    @property
    def signature(self) -> PortSignatureID:
        """Return the single signature authority carried by the wiring."""
        return self.wiring.signature

    @property
    def finite_port_values(self) -> tuple[int, ...]:
        """Descriptive spelling for the finite assignment."""
        return self.ports

    @property
    def boundary_tiles(self) -> BoundaryTileOperands:
        """Descriptive spelling for the exact spatial operands."""
        return self.boundaries


@dataclass(frozen=True, slots=True)
class FusedBoundaryContract:
    """Distinct producer and consumer contexts for one temporal fusion edge."""

    producer: BoundPorts
    consumer: BoundPorts

    def __post_init__(self) -> None:
        if (
            type(self.producer) is not BoundPorts
            or type(self.consumer) is not BoundPorts
        ):
            raise TypeError("fused boundary contracts require exact bound ports")
        self.producer.__post_init__()
        self.consumer.__post_init__()


__all__ = ["BoundPorts", "FusedBoundaryContract", "ResultWiring"]
