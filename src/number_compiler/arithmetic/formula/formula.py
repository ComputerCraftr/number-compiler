"""Canonical exact positional coefficient formulas for reverse-and-add.

The semantic state is only :class:`FormulaRoot`: bit planes that reconstruct the
exact pair coefficient at every position. Width is intrinsic to those roots.
Construction and closed evaluation live in separate mixins; this module is the
stable public facade.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.formula.construction import FormulaBuildMixin
from number_compiler.arithmetic.formula.evaluation import FormulaEvalMixin
from number_compiler.arithmetic.formula.types import Expr, RadixSpec, _bits


class FormulaArena(FormulaBuildMixin, FormulaEvalMixin):
    """Hash-consed formula IR with canonical Boolean set algebra."""

    __slots__ = ()

    @property
    def node_count(self) -> int:
        """Total canonical nodes constructed in this arena.

        This is an explicit work metric for regression/benchmark accounting; it
        is not part of semantic state.
        """
        return len(self._nodes)


@dataclass(frozen=True, slots=True)
class FormulaRoot:
    """Entire persistent state: exact positional coefficient planes only."""

    planes: tuple[Expr, ...]

    def __post_init__(self) -> None:
        if not self.planes:
            raise ValueError("empty formula root")
        width = self.planes[0].width
        if any(p.width != width for p in self.planes):
            raise ValueError("plane width mismatch")

    @property
    def width(self) -> int:
        return self.planes[0].width

    @property
    def plane_count(self) -> int:
        return len(self.planes)

    @property
    def parity(self) -> int:
        return self.width & 1

    @property
    def half_length(self) -> int:
        return (self.width + 1) // 2


def canonical_root_key(root: FormulaRoot) -> tuple[int, tuple[int, ...]]:
    """Arena-local canonical key for one exact positional formula root.

    Every compiler/view cache should key semantic arguments through this helper
    instead of inventing structural aliases or materialized fingerprints.
    """
    return root.width, tuple(p.id for p in root.planes)


def literal_planes(
    values: Sequence[int], arena: FormulaArena, plane_count: int
) -> tuple[Expr, ...]:
    """Ingest already-admitted scalar values into the canonical literal planes."""
    planes: list[Expr] = []
    for bit in range(plane_count):
        mask = 0
        for i, value in enumerate(values):
            if (value >> bit) & 1:
                mask |= 1 << i
        planes.append(arena.literal(mask, len(values)))
    return tuple(planes)


def root_from_values(
    values: Sequence[int], arena: FormulaArena, spec: RadixSpec
) -> FormulaRoot:
    from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

    forbid_in_powered_jump("root_from_values")
    vals = tuple(map(int, values))
    if not vals or any(not 0 <= v <= spec.pair_max for v in vals):
        raise ValueError("pair coefficient out of range")
    planes = literal_planes(vals, arena, spec.plane_count)
    root = FormulaRoot(tuple(planes))
    # Compiler metadata only; FormulaRoot remains planes-only semantic state.
    from number_compiler.arithmetic.formula.summary import (
        register_summary,
        summary_from_values,
    )

    register_summary(arena, root, spec, summary_from_values(vals, spec))
    return root


def variable_root(width: int, arena: FormulaArena, spec: RadixSpec) -> FormulaRoot:
    return FormulaRoot(
        tuple(arena.variable(bit, width) for bit in range(spec.plane_count))
    )


def reachable(roots: Iterable[Expr]) -> dict[int, Expr]:
    seen: dict[int, Expr] = {}
    stack = list(roots)
    while stack:
        node = stack.pop()
        if node.id in seen:
            continue
        seen[node.id] = node
        stack.extend(node.args)
    return seen


def formula_metrics(root: FormulaRoot) -> dict[str, int]:
    seen = reachable(root.planes)
    refs = sum(len(n.args) for n in seen.values())
    id_bits = _bits(max(1, len(seen)))
    param_bits = sum(n.local_param_bits for n in seen.values())
    # Long-lived formulas can be deep.  Compute depth iteratively.
    depth: dict[int, int] = {}
    pending = list(root.planes)
    while pending:
        node = pending[-1]
        if node.id in depth:
            pending.pop()
            continue
        missing = [a for a in node.args if a.id not in depth]
        if missing:
            pending.extend(missing)
            continue
        depth[node.id] = 1 if not node.args else 1 + max(depth[a.id] for a in node.args)
        pending.pop()
    return {
        "nodes": len(seen),
        "references": refs,
        "parameter_bits": param_bits,
        "description_bits": param_bits + len(seen) + refs * id_bits,
        "depth": max((depth[p.id] for p in root.planes), default=0),
        "width": root.width,
        "planes": root.plane_count,
    }


__all__ = [
    "Expr",
    "FormulaArena",
    "FormulaRoot",
    "RadixSpec",
    "canonical_root_key",
    "formula_metrics",
    "reachable",
    "root_from_values",
    "variable_root",
]
