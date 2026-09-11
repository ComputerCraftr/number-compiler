"""Constant-size records used by the concrete port scheduler."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeValueID,
)
from number_compiler.hashlife.execution.continuations.provider_layers import (
    ProviderLayerID,
)
from number_compiler.hashlife.execution.field_images import SourceCellID


@dataclass(frozen=True, slots=True)
class PortStateID(ArenaHandle):
    """Scoped boundary state produced by a composed action."""


@dataclass(frozen=True, slots=True)
class ResidualBindingID(ArenaHandle):
    """Scoped source-bound continuation residual."""


@dataclass(frozen=True, slots=True)
class VirtualInterfaceID(ArenaHandle):
    """Scoped bounded function induced by a virtual provider macrocell."""


PortAtom: TypeAlias = int | PortStateID | RuntimeValueID


@dataclass(frozen=True, slots=True)
class ComposedPort:
    action: FieldCellActionID
    side: int
    anchor: PortAtom
    residual: ResidualBindingID


@dataclass(frozen=True, slots=True)
class Residual:
    action: FieldCellActionID
    side: int
    previous: ResidualBindingID | None
    cell: SourceCellID | None
    layer: ProviderLayerID | None
    anchor_after: PortAtom
    reverse: bool = False
    constant_result: PortAtom | None = None


@dataclass(frozen=True, slots=True)
class VirtualInterface:
    consumer: FieldCellActionID
    side: int
    outputs: object


@dataclass(frozen=True, slots=True)
class VirtualBinding:
    parent: FieldCellActionID
    side: int
    cell: SourceCellID
    layer: ProviderLayerID | None
    anchor: PortAtom
    argument: PortAtom
    reverse: bool


__all__ = [
    "ComposedPort",
    "PortAtom",
    "PortStateID",
    "Residual",
    "ResidualBindingID",
    "VirtualBinding",
    "VirtualInterface",
    "VirtualInterfaceID",
]
