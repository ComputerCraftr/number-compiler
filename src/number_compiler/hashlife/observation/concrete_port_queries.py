"""Point and extent observations over a concrete port scheduler."""

from __future__ import annotations

from collections.abc import Callable
from typing import Protocol, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger


class ConcretePortQueryRuntime(Protocol):
    @property
    def adapter(self) -> object: ...

    @property
    def sources(self) -> SourceCellArena: ...

    @property
    def ledger(self) -> ResourceLedger: ...

    def boundary(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
    ) -> PortAtom: ...

    def emit(
        self,
        action: FieldCellActionID,
        left: PortAtom,
        symbol_cell: SourceCellID,
        right: PortAtom,
    ) -> int: ...

    def point(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        coordinate: int,
    ) -> int: ...


def range_cells(
    sources: SourceCellArena,
    source: SourceBindingID,
    start: int,
    end: int,
) -> tuple[SourceCellID, ...]:
    """Select the largest source cells exactly covering one coordinate range."""
    extent = sources.binding_extent(source)
    if any(type(value) is not int for value in (start, end)):
        raise TypeError("concrete port range requires exact coordinates")
    if not 0 <= start <= end <= extent:
        raise ValueError("concrete port range lies outside its source")
    roots = (
        (source,)
        if type(source) is SourceCellID
        else sources.resolve_forest(cast(SourceForestID, source)).cells
    )
    selected: list[tuple[int, SourceCellID]] = []
    origin = 0
    for root in roots:
        width = sources.resolve(root).width
        low, high = max(start, origin), min(end, origin + width)
        if low < high:
            pending = [(root, origin)]
            while pending:
                current, current_origin = pending.pop()
                node = sources.resolve(current)
                finish = current_origin + node.width
                if finish <= low or high <= current_origin:
                    continue
                if low <= current_origin and finish <= high:
                    selected.append((current_origin, current))
                    continue
                left, right = sources.children(current)
                middle = current_origin + sources.resolve(left).width
                pending.extend(((right, middle), (left, current_origin)))
        origin += width
    selected.sort(key=lambda item: item[0])
    return tuple(cell for _, cell in selected)


def observe_point(
    scheduler: ConcretePortQueryRuntime,
    action: FieldCellActionID,
    source: SourceBindingID,
    coordinate: int,
) -> int:
    extent = scheduler.sources.binding_extent(source)
    if type(coordinate) is not int or not 0 <= coordinate < extent:
        raise IndexError(coordinate)
    left = scheduler.boundary(action, source, 0, 0, coordinate)
    right = scheduler.boundary(action, source, 1, coordinate + 1, extent)
    leaf = range_cells(scheduler.sources, source, coordinate, coordinate + 1)
    if len(leaf) != 1 or scheduler.sources.resolve(leaf[0]).level:
        raise AssertionError("point range did not select one source leaf")
    return scheduler.emit(action, left, leaf[0], right)


def active_width(
    scheduler: ConcretePortQueryRuntime,
    action: FieldCellActionID,
    source: SourceBindingID,
) -> int:
    validate = cast(
        Callable[[FieldCellActionID], object],
        getattr(scheduler.adapter, "validate_action"),
    )
    validate(action)
    output_blank = getattr(scheduler.adapter, "output_blank", None)
    if output_blank is None:
        raise TypeError("concrete port adapter has no output blank semantics")
    blank = cast(Callable[[FieldCellActionID], int], output_blank)(action)
    low, high = 0, scheduler.sources.binding_extent(source)
    while low < high:
        middle = (low + high) // 2
        if scheduler.point(action, source, middle) == blank:
            high = middle
        else:
            low = middle + 1
        scheduler.ledger.bump("concrete_port_width_descents")
    return low


__all__ = ["active_width", "observe_point", "range_cells"]
