"""Typed payloads shared by the causal scheduler and its resource owner."""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from typing import Protocol, TypeAlias, TypeGuard, runtime_checkable

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    CausalLeafInterface,
)
from number_compiler.hashlife.execution.tile_causal_results import CausalCompletedOutput
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tiles import TileID


@dataclass(frozen=True, slots=True)
class CausalPrefix:
    """Exact temporal prefix carried between adjacent causal actions."""

    action: FieldCellActionID
    side: int
    producer_seed: int
    consumer_seed: int
    view: BoundaryTileView | None = None
    consumer_view: BoundaryTileView | None = None
    explicit_edge: bool = False


CausalState: TypeAlias = int | CausalPrefix
CausalSpatialValue: TypeAlias = TileID | CausalState
CausalMemoArgument: TypeAlias = (
    FieldCellActionID | TileID | CausalState | BoundaryTileView | bool
)
CausalMemoArguments: TypeAlias = tuple[CausalMemoArgument, ...]
CausalMemoKey: TypeAlias = tuple[str, CausalMemoArguments]
CausalChildStates: TypeAlias = tuple[
    tuple[CausalState, CausalState], tuple[CausalState, CausalState]
]


@runtime_checkable
class CausalSpatialBuffer(Protocol):
    """A budgeted typed spatial sequence retained by a causal task result."""

    def __len__(self) -> int: ...

    def __getitem__(self, index: int, /) -> CausalSpatialValue: ...

    def __iter__(self) -> Iterator[CausalSpatialValue]: ...

    def append(self, value: CausalSpatialValue, /) -> None: ...

    def reverse(self) -> None: ...

    def close(self) -> None: ...


CausalTaskValue: TypeAlias = (
    CausalState
    | bool
    | CausalCompletedOutput
    | CausalInterfacePayload
    | CausalLeafInterface
    | ReverseBoundOutput
    | BoundaryTileView
    | CausalSpatialBuffer
    | CausalChildStates
)


class CausalResultReader(Protocol):
    """A heterogeneous task-result stack consumed at typed operation seams."""

    def pop(self) -> CausalTaskValue: ...


def require_causal_state(value: object) -> CausalState:
    """Narrow one heterogeneous task result at a state-consuming seam."""
    if type(value) is int:
        return value
    if type(value) is CausalPrefix:
        return value
    raise TypeError("causal task returned another state sort")


def pop_causal_state(values: CausalResultReader) -> CausalState:
    """Read a state result from a heterogeneous operation stack."""
    return require_causal_state(values.pop())


def pop_completed_output(values: CausalResultReader) -> CausalCompletedOutput:
    """Read a completed producer result at its consumer boundary."""
    value = values.pop()
    if type(value) is not CausalCompletedOutput:
        raise TypeError("causal task returned another completed-output sort")
    return value


def pop_interface_payload(values: CausalResultReader) -> CausalInterfacePayload:
    """Read an admitted interface payload at its consumer boundary."""
    value = values.pop()
    if type(value) is not CausalInterfacePayload:
        raise TypeError("causal task returned another interface-payload sort")
    return value


def pop_leaf_interface(values: CausalResultReader) -> CausalLeafInterface:
    """Read one leaf interface result at its consumer boundary."""
    value = values.pop()
    if type(value) is not CausalLeafInterface:
        raise TypeError("causal task returned another leaf-interface sort")
    return value


def pop_reverse_bound_output(values: CausalResultReader) -> ReverseBoundOutput:
    """Read an authenticated reverse-output fold at its consumer boundary."""
    value = values.pop()
    if type(value) is not ReverseBoundOutput:
        raise TypeError("causal task returned another reverse-output sort")
    return value


def pop_boundary_view(values: CausalResultReader) -> BoundaryTileView:
    """Read a normalized boundary result at its adjacent-action consumer."""
    value = values.pop()
    if type(value) is not BoundaryTileView:
        raise TypeError("causal task returned another boundary-view sort")
    return value


def pop_spatial_buffer(values: CausalResultReader) -> CausalSpatialBuffer:
    """Read a charged spatial buffer transferred between task stages."""
    return require_spatial_buffer(values.pop())


def require_spatial_buffer(value: object) -> CausalSpatialBuffer:
    """Narrow a retained buffer at the operation that owns its next stage."""
    if not isinstance(value, CausalSpatialBuffer):
        raise TypeError("causal task returned another spatial-buffer sort")
    return value


def spatial_buffer_tile_at(buffer: CausalSpatialBuffer, index: int) -> TileID:
    """Read a tile-owned entry from a spatial buffer at a typed consumer seam."""
    value = buffer[index]
    if type(value) is not TileID:
        raise TypeError("causal spatial buffer contains another tile sort")
    return value


def spatial_buffer_state_at(buffer: CausalSpatialBuffer, index: int) -> CausalState:
    """Read a state-owned entry from a spatial buffer at a consumer seam."""
    return require_causal_state(buffer[index])


def pop_exact_integer(values: CausalResultReader) -> int:
    """Read an exact integer result, excluding Boolean subclasses."""
    value = values.pop()
    if type(value) is not int:
        raise TypeError("causal task returned another integer sort")
    return value


def pop_boolean(values: CausalResultReader) -> bool:
    """Read an exact Boolean result from a task such as parent promotion."""
    value = values.pop()
    if type(value) is not bool:
        raise TypeError("causal task returned another Boolean sort")
    return value


def pop_child_states(values: CausalResultReader) -> CausalChildStates:
    """Read the four child boundary states produced by a child-state task."""
    return require_child_states(values.pop())


def require_child_states(value: object) -> CausalChildStates:
    """Narrow a child-state packet returned across the public task boundary."""
    if not _is_object_pair(value):
        raise TypeError("causal task returned another child-state sort")
    left, right = value
    if not _is_object_pair(left) or not _is_object_pair(right):
        raise TypeError("causal task returned another child-state sort")
    return (
        (
            require_causal_state(left[0]),
            require_causal_state(left[1]),
        ),
        (
            require_causal_state(right[0]),
            require_causal_state(right[1]),
        ),
    )


def _is_object_pair(value: object) -> TypeGuard[tuple[object, object]]:
    """Recognize an exact binary tuple at a heterogeneous result boundary."""
    return is_exact_object_tuple(value) and len(value) == 2
