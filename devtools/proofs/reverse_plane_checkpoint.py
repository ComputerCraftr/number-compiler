"""Explicit independent-plane DAG checkpoints for bounded research epochs."""

from __future__ import annotations

from typing import Any, Protocol

from number_compiler.arithmetic.automata import program_word as words
from number_compiler.sequences.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
    TemporalCell,
)
from number_compiler.sequences.reverse_add.factored_planes import PlaneAlgebra, PlaneID


class _PlaneCarrier(Protocol):
    planes: PlaneAlgebra


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
    archive: dict[str, Any],
    *,
    kinds: tuple[str, ...] = ("domain", "f5", "bool"),
) -> tuple[PlaneID, ...]:
    """Restore aligned plane handles for a caller-owned cell type."""
    nodes, roots = archive["nodes"], archive["roots"]
    if (
        type(nodes) is not list
        or not 0 < len(nodes) <= 100000
        or type(roots) is not list
        or len(roots) != len(kinds)
    ):
        raise ValueError("invalid plane archive shape")
    built: list[words.CanonicalWord] = []
    for record in nodes:
        if type(record) is not list and type(record) is not tuple:
            raise ValueError("invalid plane archive record")
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
    if any(type(i) is not int or not 0 <= i < len(built) for i in roots):
        raise ValueError("invalid plane archive root")
    return tuple(
        carrier.planes._issue(kind, built[i])
        for kind, i in zip(kinds, roots, strict=True)
    )


def import_planes(
    carrier: FactoredReverseCarrier, archive: dict[str, Any]
) -> TemporalCell:
    roots = archive.get("roots") if type(archive) is dict else None
    if type(roots) is not list or len(roots) != 3:
        raise ValueError("invalid plane archive roots")
    cell = TemporalCell(*import_plane_roots(carrier, archive))
    carrier.validate(cell)
    return cell
