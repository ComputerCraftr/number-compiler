"""Evaluation and substitution for canonical coefficient formulas.

Evaluation is not semantic state.  Closed-bit caching lives in FormulaArena and
uses compact per-expression bitmasks rather than per-(node,position) Python
objects.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from typing import Any

from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump
from number_compiler.arithmetic.formula.bit_semantics import (
    coefficient_bit,
    coefficient_dependencies,
    constant_bit,
    predicate_bit,
    shift_position,
)
from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot
from number_compiler.arithmetic.formula.types import Expr


def eval_bit(
    root: Expr,
    i: int,
    env: Mapping[int, int] | None = None,
    memo: dict[tuple[int, int], int] | None = None,
) -> int:
    """Evaluate one bit with an explicit continuation stack."""
    forbid_in_powered_jump("eval_bit")
    i = int(i)
    if not 0 <= i < root.width:
        raise IndexError(i)
    if memo is None:
        memo = {}
    env = {} if env is None else env

    def known(node: Expr, pos: int) -> bool:
        return (node.id, pos) in memo

    def get(node: Expr, pos: int) -> int:
        return memo[(node.id, pos)]

    def store(node: Expr, pos: int, value: int) -> None:
        memo[(node.id, pos)] = int(value) & 1

    stack: list[tuple[Any, ...]] = [("VISIT", root, i)]
    while stack:
        frame = stack.pop()
        tag, node, pos = frame[0], frame[1], frame[2]
        if tag == "VISIT":
            if known(node, pos):
                continue
            k = node.kind
            constant = constant_bit(node, pos)
            if constant is not None:
                store(node, pos, constant)
                continue
            if k == "VAR":
                slot = int(node.param[0])
                if slot not in env:
                    raise KeyError(f"missing VAR slot {slot}")
                store(node, pos, (int(env[slot]) >> pos) & 1)
                continue
            if k == "NOT":
                child = node.args[0]
                stack.append(("NOT", node, pos, child, pos))
                stack.append(("VISIT", child, pos))
                continue
            if k == "AND":
                stack.append(("AND", node, pos, 0))
                continue
            if k == "OR":
                stack.append(("OR", node, pos, 0))
                continue
            if k == "XOR":
                stack.append(("XOR", node, pos, 0, 0))
                continue
            if k in ("SHL", "SHR", "MIRROR"):
                q = node.width - 1 - pos if k == "MIRROR" else shift_position(node, pos)
                if not 0 <= q < node.width:
                    store(node, pos, 0)
                    continue
                child = node.args[0]
                stack.append(("COPY", node, pos, child, q))
                stack.append(("VISIT", child, q))
                continue
            if k == "PAD_RIGHT":
                child = node.args[0]
                if pos >= child.width:
                    store(node, pos, 0)
                    continue
                stack.append(("COPY", node, pos, child, pos))
                stack.append(("VISIT", child, pos))
                continue
            if k == "CROP":
                child = node.args[0]
                stack.append(("COPY", node, pos, child, pos))
                stack.append(("VISIT", child, pos))
                continue
            if k == "ITE":
                selector = node.args[0]
                stack.append(("ITE_SELECT", node, pos, selector))
                stack.append(("VISIT", selector, pos))
                continue
            if k == "BOOLFUNC":
                deps = tuple((arg, pos) for arg in node.args)
                stack.append(("BOOLFUNC_FINISH", node, pos, deps))
                for child, q in reversed(deps):
                    if not known(child, q):
                        stack.append(("VISIT", child, q))
                continue
            if k == "PRED":
                stack.append(("PRED", node, pos, 0, 0))
                continue
            if k == "COEFFMAP":
                coeff_deps = coefficient_dependencies(node, pos)
                if coeff_deps is None:
                    store(node, pos, 0)
                    continue
                stack.append(("COEFF_FINISH", node, pos, tuple(coeff_deps)))
                for child, q in reversed(coeff_deps):
                    if not known(child, q):
                        stack.append(("VISIT", child, q))
                continue
            raise AssertionError(k)

        if tag == "NOT":
            child, q = frame[3], frame[4]
            store(node, pos, 1 ^ get(child, q))
            continue
        if tag == "COPY":
            child, q = frame[3], frame[4]
            store(node, pos, get(child, q))
            continue
        if tag == "AND":
            idx = int(frame[3])
            if idx >= len(node.args):
                store(node, pos, 1)
                continue
            child = node.args[idx]
            if not known(child, pos):
                stack.append(("AND", node, pos, idx))
                stack.append(("VISIT", child, pos))
                continue
            if get(child, pos) == 0:
                store(node, pos, 0)
                continue
            stack.append(("AND", node, pos, idx + 1))
            continue
        if tag == "OR":
            idx = int(frame[3])
            if idx >= len(node.args):
                store(node, pos, 0)
                continue
            child = node.args[idx]
            if not known(child, pos):
                stack.append(("OR", node, pos, idx))
                stack.append(("VISIT", child, pos))
                continue
            if get(child, pos) == 1:
                store(node, pos, 1)
                continue
            stack.append(("OR", node, pos, idx + 1))
            continue
        if tag == "XOR":
            idx, acc = int(frame[3]), int(frame[4])
            if idx >= len(node.args):
                store(node, pos, acc)
                continue
            child = node.args[idx]
            if not known(child, pos):
                stack.append(("XOR", node, pos, idx, acc))
                stack.append(("VISIT", child, pos))
                continue
            stack.append(("XOR", node, pos, idx + 1, acc ^ get(child, pos)))
            continue
        if tag == "ITE_SELECT":
            selector = frame[3]
            branch = node.args[2] if get(selector, pos) else node.args[1]
            stack.append(("COPY", node, pos, branch, pos))
            if not known(branch, pos):
                stack.append(("VISIT", branch, pos))
            continue
        if tag == "BOOLFUNC_FINISH":
            assignment = 0
            for j, (child, q) in enumerate(frame[3]):
                assignment |= get(child, q) << j
            store(node, pos, (int(node.param[0]) >> assignment) & 1)
            continue
        if tag == "PRED":
            idx, coeff = int(frame[3]), int(frame[4])
            if idx >= len(node.args):
                store(node, pos, predicate_bit(node, coeff))
                continue
            child = node.args[idx]
            if not known(child, pos):
                stack.append(("PRED", node, pos, idx, coeff))
                stack.append(("VISIT", child, pos))
                continue
            stack.append(("PRED", node, pos, idx + 1, coeff | (get(child, pos) << idx)))
            continue
        if tag == "COEFF_FINISH":
            store(node, pos, coefficient_bit(node, pos, get))
            continue
        raise AssertionError(tag)

    return get(root, i)


def iter_values(
    root: FormulaRoot,
    env: Mapping[int, int] | None = None,
    *,
    reverse: bool = False,
) -> Iterator[int]:
    """Yield exact radix values without first allocating a complete value tuple.

    The evaluator memo is shared across yielded positions, preserving the same
    DAG reuse as :func:`materialize_values`.  ``reverse=True`` is useful for
    textual most-significant-digit-first output and avoids a second reversed
    copy of an already materialized word.
    """
    forbid_in_powered_jump("iter_values")
    memo: dict[tuple[int, int], int] = {}
    positions = range(root.width - 1, -1, -1) if reverse else range(root.width)
    for i in positions:
        yield sum(
            eval_bit(plane, i, env, memo) << b for b, plane in enumerate(root.planes)
        )


def materialize_values(
    root: FormulaRoot, env: Mapping[int, int] | None = None
) -> tuple[int, ...]:
    forbid_in_powered_jump("materialize_values")
    return tuple(iter_values(root, env))


def value_at(root: FormulaRoot, i: int, env: Mapping[int, int] | None = None) -> int:
    forbid_in_powered_jump("value_at")
    memo: dict[tuple[int, int], int] = {}
    return sum(
        eval_bit(plane, i, env, memo) << b for b, plane in enumerate(root.planes)
    )


def substitute(
    root: Expr,
    mapping: Mapping[int, Expr],
    arena: FormulaArena,
    memo: dict[int, Expr] | None = None,
) -> Expr:
    """Substitute a formula DAG iteratively, preserving shared descendants.

    Temporal composition can create very deep but highly shared DAGs.  Recursive
    substitution made Python call-stack depth an accidental power limit; this
    postorder worklist visits every reached source node at most once instead.
    """
    if memo is None:
        memo = {}
    found = memo.get(root.id)
    if found is not None:
        return found

    stack: list[tuple[Expr, bool]] = [(root, False)]
    while stack:
        node, ready = stack.pop()
        if node.id in memo:
            continue
        if node.kind == "VAR" and node.id in mapping:
            out = mapping[node.id]
            if out.width != node.width:
                raise ValueError((node.width, out.width))
            memo[node.id] = out
            continue
        if not ready and node.args:
            stack.append((node, True))
            for child in reversed(node.args):
                if child.id not in memo:
                    stack.append((child, False))
            continue

        args = tuple(memo[a.id] for a in node.args)
        k = node.kind
        if k == "ZERO":
            out = arena.zero(node.width)
        elif k == "ONES":
            out = arena.ones(node.width)
        elif k == "LITERAL":
            out = arena.literal(int(node.param[0]), node.width)
        elif k == "VAR":
            out = arena.variable(int(node.param[0]), node.width)
        elif k == "RANGE":
            out = arena.range_mask(int(node.param[0]), int(node.param[1]), node.width)
        elif k == "NOT":
            out = arena.not_(args[0])
        elif k == "AND":
            out = arena.and_many(args, node.width)
        elif k == "OR":
            out = arena.or_many(args, node.width)
        elif k == "XOR":
            out = arena.xor_many(args, node.width)
        elif k == "SHL":
            out = arena.shl(args[0], int(node.param[0]))
        elif k == "SHR":
            out = arena.shr(args[0], int(node.param[0]))
        elif k == "MIRROR":
            out = arena.mirror(args[0])
        elif k == "PAD_RIGHT":
            out = arena.resize(args[0], node.width)
        elif k == "CROP":
            out = arena.crop(args[0], node.width)
        elif k == "ITE":
            out = arena.ite(args[0], args[1], args[2])
        elif k == "BOOLFUNC":
            out = arena.boolfunc(args, int(node.param[0]))
        elif k == "PRED":
            out = arena.predicate(str(node.param[0]), int(node.param[1]), args)
        elif k == "COEFFMAP":
            out = arena.coeffmap(
                str(node.param[0]),
                int(node.param[1]),
                int(node.param[2]),
                int(node.param[3]),
                args,
            )
        else:
            raise AssertionError(k)
        memo[node.id] = out

    return memo[root.id]


def substitute_root(
    root: FormulaRoot,
    inputs: FormulaRoot,
    replacement: FormulaRoot,
    arena: FormulaArena,
) -> FormulaRoot:
    if (
        inputs.width != replacement.width
        or inputs.plane_count != replacement.plane_count
    ):
        raise ValueError("input/replacement shape mismatch")
    mapping = {src.id: dst for src, dst in zip(inputs.planes, replacement.planes)}
    memo: dict[int, Expr] = {}
    return FormulaRoot(tuple(substitute(p, mapping, arena, memo) for p in root.planes))


__all__ = [
    "eval_bit",
    "iter_values",
    "materialize_values",
    "substitute",
    "substitute_root",
    "value_at",
]
