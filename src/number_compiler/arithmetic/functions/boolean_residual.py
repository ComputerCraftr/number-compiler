"""Exact bounded-cone behavioral normalization for FormulaArena Boolean masks.

Temporal carry-slab squaring can produce different AND/OR/XOR syntax for the
same local Boolean function.  This module canonicalizes only *bounded* cones by
complete truth-table proof and retains the result as a reduced ordered decision
DAG of ``ITE`` Expr nodes.  Wide cones stay structural.

The truth table is transient proof work, not retained semantic state.  Every
retained decision node is an ordinary hash-consed Expr and all references are
charged by the usual formula metrics.  No fingerprint, finite sample, or
probabilistic equality authorizes a merge.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from number_compiler.arithmetic.formula.formula import FormulaArena, reachable
from number_compiler.arithmetic.formula.types import Expr

_BOOLEAN_KINDS = frozenset(
    ("ZERO", "ONES", "NOT", "AND", "OR", "XOR", "ITE", "BOOLFUNC")
)


@dataclass(frozen=True, slots=True)
class BooleanResidualStats:
    max_arity: int
    visited_nodes: int
    boolean_nodes_seen: int
    decision_normalizations: int
    wide_cones_left_structural: int
    max_normalized_arity: int
    truth_table_proof_bits: int
    input_reachable_nodes: int
    output_reachable_nodes: int
    input_description_bits: int
    output_description_bits: int


def _description_bits(roots: Sequence[Expr]) -> tuple[int, int]:
    seen = reachable(tuple(roots))
    refs = sum(len(node.args) for node in seen.values())
    bits = sum(node.local_param_bits for node in seen.values()) + refs * max(
        1, len(seen).bit_length()
    )
    return len(seen), bits


def _eval_small(
    spec: tuple[tuple[Expr, ...], int], assignment: int, positions: dict[int, int]
) -> int:
    atoms, table = spec
    local = 0
    for j, atom in enumerate(atoms):
        local |= ((assignment >> positions[atom.id]) & 1) << j
    return (table >> local) & 1


def _atom_spec(expr: Expr) -> tuple[tuple[Expr, ...], int]:
    return ((expr,), 0b10)


def _bdd_from_table(
    arena: FormulaArena,
    atoms: tuple[Expr, ...],
    table: int,
    *,
    width: int,
) -> Expr:
    """Build the reduced ordered decision DAG for ``table`` over sorted atoms."""
    if not atoms:
        return arena.ones(width) if table & 1 else arena.zero(width)

    # Bottom-up ROBDD construction.  ``current[prefix]`` is the canonical
    # residual after all variables below ``level`` have been fixed.  This is
    # equivalent to the former recursive builder but has bounded Python stack
    # use and makes the work table explicit.
    arity = len(atoms)
    current = [
        arena.ones(width) if (table >> prefix) & 1 else arena.zero(width)
        for prefix in range(1 << arity)
    ]
    for level in range(arity - 1, -1, -1):
        stride = 1 << level
        next_level: list[Expr] = []
        for prefix in range(stride):
            low = current[prefix]
            high = current[prefix | stride]
            next_level.append(arena.ite(atoms[level], low, high))
        current = next_level
    return current[0]


def _compose_truth_table(
    kind: str,
    children: Sequence[Expr],
    child_specs: Sequence[tuple[tuple[Expr, ...], int]],
    *,
    node_table: int | None,
    max_arity: int,
) -> tuple[tuple[Expr, ...], int] | None:
    atom_by_id: dict[int, Expr] = {}
    for atoms, _table in child_specs:
        for atom in atoms:
            atom_by_id[atom.id] = atom
    atoms = tuple(sorted(atom_by_id.values(), key=lambda x: x.id))
    if len(atoms) > max_arity:
        return None
    positions = {atom.id: j for j, atom in enumerate(atoms)}
    table = 0
    for assignment in range(1 << len(atoms)):
        values = [_eval_small(spec, assignment, positions) for spec in child_specs]
        if kind == "NOT":
            value = 1 ^ values[0]
        elif kind == "AND":
            value = int(all(values))
        elif kind == "OR":
            value = int(any(values))
        elif kind == "XOR":
            value = 0
            for bit in values:
                value ^= bit
        elif kind == "ITE":
            value = values[2] if values[0] else values[1]
        elif kind == "BOOLFUNC":
            if node_table is None:
                raise AssertionError("BOOLFUNC missing table")
            local = 0
            for j, bit in enumerate(values):
                local |= bit << j
            value = (int(node_table) >> local) & 1
        else:
            raise AssertionError(kind)
        table |= int(value) << assignment
    return atoms, table


def _rebuild_nonboolean(
    arena: FormulaArena, root: Expr, args: tuple[Expr, ...]
) -> Expr:
    k = root.kind
    if not root.args:
        return root
    if k == "SHL":
        return arena.shl(args[0], int(root.param[0]))
    if k == "SHR":
        return arena.shr(args[0], int(root.param[0]))
    if k == "MIRROR":
        return arena.mirror(args[0])
    if k == "PAD_RIGHT":
        return arena.resize(args[0], root.width)
    if k == "CROP":
        return arena.crop(args[0], root.width)
    if k == "PRED":
        return arena.predicate(str(root.param[0]), int(root.param[1]), args)
    if k == "COEFFMAP":
        return arena.coeffmap(
            str(root.param[0]),
            int(root.param[1]),
            int(root.param[2]),
            int(root.param[3]),
            args,
        )
    raise AssertionError(f"unsupported non-Boolean formula kind: {k}")


def _local_boolean_cost(root: Expr, atom_ids: frozenset[int]) -> tuple[int, int, int]:
    """Count only Boolean decision syntax above the supplied semantic atoms."""
    seen: set[int] = set()
    refs = param_bits = 0

    stack = [root]
    while stack:
        node = stack.pop()
        if node.id in atom_ids or node.id in seen:
            continue
        if node.kind not in _BOOLEAN_KINDS:
            continue
        seen.add(node.id)
        refs += len(node.args)
        param_bits += node.local_param_bits
        stack.extend(node.args)
    return len(seen), refs, param_bits


def normalize_boolean_residuals(
    arena: FormulaArena,
    roots: Sequence[Expr],
    *,
    max_arity: int = 4,
) -> tuple[tuple[Expr, ...], BooleanResidualStats]:
    """Return exact locally behavior-minimized roots.

    A bounded cone is completely evaluated over its abstract non-Boolean leaves,
    then rebuilt as a reduced ordered ITE DAG.  A wider cone is retained exactly
    in structural form.
    """
    roots = tuple(roots)
    max_arity = int(max_arity)
    if not roots or not 1 <= max_arity <= 10:
        raise ValueError((len(roots), max_arity))
    input_nodes, input_bits = _description_bits(roots)
    memo: dict[int, Expr] = {}
    spec_memo: dict[int, tuple[tuple[Expr, ...], int] | None] = {}
    semantic_rep: dict[tuple[tuple[int, ...], int], Expr] = {}
    visited = boolean_seen = normalized = wide = max_seen_arity = proof_bits = 0

    def spec_for(expr: Expr) -> tuple[tuple[Expr, ...], int]:
        found = spec_memo.get(expr.id, ...)
        if found is not ... and found is not None:
            return found
        spec: tuple[tuple[Expr, ...], int]
        if expr.kind == "ZERO":
            spec = ((), 0)
        elif expr.kind == "ONES":
            spec = ((), 1)
        else:
            spec = _atom_spec(expr)
        return spec

    def normalize_root(root: Expr) -> Expr:
        nonlocal visited, boolean_seen, normalized, wide, max_seen_arity, proof_bits
        if root.id in memo:
            return memo[root.id]
        stack: list[tuple[Expr, bool]] = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node.id in memo:
                continue
            if not ready and node.args:
                stack.append((node, True))
                for child in reversed(node.args):
                    if child.id not in memo:
                        stack.append((child, False))
                continue

            visited += 1
            k = node.kind
            if not node.args:
                out = node
                if k == "ZERO":
                    spec_memo[out.id] = ((), 0)
                elif k == "ONES":
                    spec_memo[out.id] = ((), 1)
                else:
                    spec_memo[out.id] = None
            else:
                args = tuple(memo[arg.id] for arg in node.args)
                if k in _BOOLEAN_KINDS:
                    boolean_seen += 1
                    child_specs = tuple(spec_for(arg) for arg in args)
                    composed = _compose_truth_table(
                        k,
                        args,
                        child_specs,
                        node_table=int(node.param[0]) if k == "BOOLFUNC" else None,
                        max_arity=max_arity,
                    )
                    if composed is None:
                        wide += 1
                        if k == "NOT":
                            out = arena.not_(args[0])
                        elif k == "AND":
                            out = arena.and_many(args, node.width)
                        elif k == "OR":
                            out = arena.or_many(args, node.width)
                        elif k == "XOR":
                            out = arena.xor_many(args, node.width)
                        elif k == "ITE":
                            out = arena.ite(args[0], args[1], args[2])
                        elif k == "BOOLFUNC":
                            out = arena.boolfunc(args, int(node.param[0]))
                        elif k in ("ZERO", "ONES"):
                            out = node
                        else:
                            raise AssertionError(k)
                        spec_memo[out.id] = None
                    else:
                        atoms, table = composed
                        arity = len(atoms)
                        max_seen_arity = max(max_seen_arity, arity)
                        proof_bits += 1 << arity
                        key = (tuple(atom.id for atom in atoms), int(table))
                        prior = semantic_rep.get(key)
                        if prior is not None:
                            out = prior
                        else:
                            if k == "NOT":
                                structural = arena.not_(args[0])
                            elif k == "AND":
                                structural = arena.and_many(args, node.width)
                            elif k == "OR":
                                structural = arena.or_many(args, node.width)
                            elif k == "XOR":
                                structural = arena.xor_many(args, node.width)
                            elif k == "ITE":
                                structural = arena.ite(args[0], args[1], args[2])
                            elif k == "BOOLFUNC":
                                structural = arena.boolfunc(args, int(node.param[0]))
                            elif k in ("ZERO", "ONES"):
                                structural = node
                            else:
                                raise AssertionError(k)
                            candidate = _bdd_from_table(
                                arena, atoms, table, width=node.width
                            )
                            atom_ids = frozenset(atom.id for atom in atoms)
                            scost = _local_boolean_cost(structural, atom_ids)
                            ccost = _local_boolean_cost(candidate, atom_ids)
                            out = candidate if ccost <= scost else structural
                            semantic_rep[key] = out
                        spec_memo[out.id] = (atoms, table)
                        normalized += 1
                else:
                    out = _rebuild_nonboolean(arena, node, args)
                    spec_memo[out.id] = None
            memo[node.id] = out
        return memo[root.id]

    output = tuple(normalize_root(root) for root in roots)
    output_nodes, output_bits = _description_bits(output)
    return output, BooleanResidualStats(
        max_arity=max_arity,
        visited_nodes=visited,
        boolean_nodes_seen=boolean_seen,
        decision_normalizations=normalized,
        wide_cones_left_structural=wide,
        max_normalized_arity=max_seen_arity,
        truth_table_proof_bits=proof_bits,
        input_reachable_nodes=input_nodes,
        output_reachable_nodes=output_nodes,
        input_description_bits=input_bits,
        output_description_bits=output_bits,
    )


__all__ = ["BooleanResidualStats", "normalize_boolean_residuals"]
