"""Explicit independent-plane DAG checkpoints for bounded research epochs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Protocol, cast

from devtools.experiments.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
    TemporalCell,
)
from devtools.experiments.reverse_add.factored_planes import PlaneAlgebra, PlaneID
from number_compiler.arithmetic.automata import program_word as words


class _PlaneCarrier(Protocol):
    planes: PlaneAlgebra


def _array(value: object, name: str) -> list[object]:
    if type(value) is not list:
        raise ValueError(f"invalid plane archive {name}")
    return cast(list[object], value)


def export_plane_roots(
    carrier: _PlaneCarrier,
    roots: tuple[PlaneID, ...],
) -> dict[str, object]:
    """Serialize any aligned tuple of owned plane handles.

    Checkpoints retain only canonical rope nodes and root indices.  The cell
    type belongs to the caller because the reverse/add diagnostics have
    several three-plane endpoint records with the same shape.
    """
    resolved = tuple(carrier.planes.resolve(p) for p in roots)
    identifiers: dict[int, int] = {}
    nodes: list[tuple[str, int, int]] = []
    pending = [(r, False) for r in resolved]
    while pending:
        node, ready = pending.pop()
        if node.node_id in identifiers:
            continue
        if node.symbol is not None:
            record = "run", node.symbol, node.length
        else:
            if node.left is None or node.right is None:
                raise ValueError("checkpoint node lost its children")
            if not ready:
                pending.extend(((node, True), (node.right, False), (node.left, False)))
                continue
            record = (
                "concat",
                identifiers[node.left.node_id],
                identifiers[node.right.node_id],
            )
        identifiers[node.node_id] = len(nodes)
        nodes.append(record)
    return {"nodes": nodes, "roots": [identifiers[r.node_id] for r in resolved]}


def export_planes(
    carrier: FactoredReverseCarrier, cell: TemporalCell
) -> dict[str, object]:
    """Serialize the original three-channel factored carrier cell."""
    return export_plane_roots(carrier, (cell.domain, cell.f5, cell.half))


def import_plane_roots(
    carrier: _PlaneCarrier,
    archive: Mapping[str, object],
    *,
    kinds: tuple[str, ...] = ("domain", "f5", "bool"),
) -> tuple[PlaneID, ...]:
    """Restore aligned plane handles for a caller-owned cell type."""
    nodes = _array(archive.get("nodes"), "nodes")
    roots = _array(archive.get("roots"), "roots")
    if not 0 < len(nodes) <= 100000 or len(roots) != len(kinds):
        raise ValueError("invalid plane archive shape")
    built: list[words.CanonicalWord] = []
    for raw_record in nodes:
        if type(raw_record) is not list and type(raw_record) is not tuple:
            raise ValueError("invalid plane archive record")
        record = cast(tuple[object, ...], raw_record)
        if len(record) != 3:
            raise ValueError("invalid plane archive record")
        kind, first, second = record
        if type(kind) is not str or type(first) is not int or type(second) is not int:
            raise ValueError("plane archive requires typed parameters")
        if kind == "run" and 0 <= first < 5 and second > 0:
            built.append(words.run(first, second))
        elif kind == "concat" and 0 <= first < len(built) and 0 <= second < len(built):
            built.append(words.concat(built[first], built[second]))
        else:
            raise ValueError("invalid plane archive node")
    root_indices: list[int] = []
    for raw_index in roots:
        if type(raw_index) is not int or not 0 <= raw_index < len(built):
            raise ValueError("invalid plane archive root")
        root_indices.append(raw_index)
    return tuple(
        carrier.planes.issue_existing(kind, built[index])
        for kind, index in zip(kinds, root_indices, strict=True)
    )


def import_planes(
    carrier: FactoredReverseCarrier, archive: Mapping[str, object]
) -> TemporalCell:
    roots = _array(archive.get("roots"), "roots")
    if len(roots) != 3:
        raise ValueError("invalid plane archive roots")
    cell = TemporalCell(*import_plane_roots(carrier, archive))
    carrier.validate(cell)
    return cell
