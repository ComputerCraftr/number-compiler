from __future__ import annotations

from dataclasses import dataclass
from typing import Any, TypeVar

from number_compiler.arithmetic.formula.bit_semantics import (
    constant_bit,
    shift_position,
    coefficient_dependencies,
    coefficient_bit,
    predicate_bit,
)
from number_compiler.arithmetic.formula.types import Expr, FormulaStorage

_MetaT = TypeVar("_MetaT")


@dataclass(frozen=True, slots=True)
class _EvalFrame:
    tag: str
    node: Expr
    position: int
    child: Expr | None = None
    child_position: int = 0
    index: int = 0
    accumulator: int = 0
    dependencies: tuple[tuple[Expr, int], ...] = ()


class FormulaEvalMixin(FormulaStorage):
    """Closed evaluation, compiler metadata, and accounting for FormulaArena."""

    __slots__ = ()

    def eval_closed_bit(self, root: Expr, position: int) -> int:
        """Public closed-bit evaluator; forbidden inside powered jumps."""
        from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

        forbid_in_powered_jump("eval_closed_bit")
        return self._eval_closed_bit_unchecked(root, position)

    def _eval_closed_bit_unchecked(self, root: Expr, position: int) -> int:
        """Internal closed-bit kernel for proof-certified scalar queries.

        Callers inside a powered jump must wrap this through a narrowly-scoped
        theorem primitive (for example carry-slab prefix-length recovery) and
        charge every probe in JumpAudit.  General point evaluation remains
        prohibited by :meth:`eval_closed_bit`.
        """
        position = int(position)
        if not 0 <= position < root.width:
            raise IndexError(position)

        known = self._closed_known
        values = self._closed_values

        def is_known(node: Expr, pos: int) -> bool:
            return bool((known.get(node.id, 0) >> pos) & 1)

        def get(node: Expr, pos: int) -> int:
            return (values.get(node.id, 0) >> pos) & 1

        def store(node: Expr, pos: int, value: int) -> None:
            if is_known(node, pos):
                return
            mask = 1 << pos
            known[node.id] = known.get(node.id, 0) | mask
            if value:
                values[node.id] = values.get(node.id, 0) | mask
            self._closed_bit_count += 1

        # Typed VISIT frames evaluate a node; continuation
        # frames resume one parent after the requested child has been cached.
        stack = [_EvalFrame("VISIT", root, position)]

        def schedule_copy(node: Expr, pos: int, child: Expr, child_pos: int) -> None:
            stack.append(
                _EvalFrame("COPY", node, pos, child=child, child_position=child_pos)
            )
            stack.append(_EvalFrame("VISIT", child, child_pos))

        while stack:
            frame = stack.pop()
            tag, node, pos = frame.tag, frame.node, frame.position

            if tag == "VISIT":
                if is_known(node, pos):
                    continue
                kind = node.kind
                constant = constant_bit(node, pos)
                if constant is not None:
                    store(node, pos, constant)
                    continue
                if kind == "VAR":
                    raise KeyError("closed expression contains VAR")
                if kind == "NOT":
                    child = node.args[0]
                    stack.append(
                        _EvalFrame("NOT", node, pos, child=child, child_position=pos)
                    )
                    stack.append(_EvalFrame("VISIT", child, pos))
                    continue
                if kind == "AND":
                    stack.append(_EvalFrame("AND", node, pos, index=0))
                    continue
                if kind == "OR":
                    stack.append(_EvalFrame("OR", node, pos, index=0))
                    continue
                if kind == "XOR":
                    stack.append(_EvalFrame("XOR", node, pos, index=0, accumulator=0))
                    continue
                if kind == "SHL":
                    q = shift_position(node, pos)
                    if q < 0:
                        store(node, pos, 0)
                        continue
                    child = node.args[0]
                    schedule_copy(node, pos, child, q)
                    continue
                if kind == "SHR":
                    q = shift_position(node, pos)
                    if q >= node.width:
                        store(node, pos, 0)
                        continue
                    child = node.args[0]
                    schedule_copy(node, pos, child, q)
                    continue
                if kind == "MIRROR":
                    q = node.width - 1 - pos
                    child = node.args[0]
                    schedule_copy(node, pos, child, q)
                    continue
                if kind == "PAD_RIGHT":
                    child = node.args[0]
                    if pos >= child.width:
                        store(node, pos, 0)
                        continue
                    schedule_copy(node, pos, child, pos)
                    continue
                if kind == "CROP":
                    child = node.args[0]
                    schedule_copy(node, pos, child, pos)
                    continue
                if kind == "ITE":
                    selector = node.args[0]
                    stack.append(_EvalFrame("ITE_SELECT", node, pos, child=selector))
                    stack.append(_EvalFrame("VISIT", selector, pos))
                    continue
                if kind == "BOOLFUNC":
                    deps = tuple((arg, pos) for arg in node.args)
                    stack.append(
                        _EvalFrame("BOOLFUNC_FINISH", node, pos, dependencies=deps)
                    )
                    for child, q in reversed(deps):
                        if not is_known(child, q):
                            stack.append(_EvalFrame("VISIT", child, q))
                    continue
                if kind == "PRED":
                    stack.append(_EvalFrame("PRED", node, pos, index=0, accumulator=0))
                    continue
                if kind == "COEFFMAP":
                    coeff_deps = coefficient_dependencies(node, pos)
                    if coeff_deps is None:
                        store(node, pos, 0)
                        continue
                    stack.append(
                        _EvalFrame(
                            "COEFF_FINISH", node, pos, dependencies=tuple(coeff_deps)
                        )
                    )
                    for child, q in reversed(coeff_deps):
                        if not is_known(child, q):
                            stack.append(_EvalFrame("VISIT", child, q))
                    continue
                raise AssertionError(kind)

            if tag in ("NOT", "COPY"):
                continuation = frame.child
                if continuation is None:
                    raise AssertionError("missing continuation child")
                child, q = continuation, frame.child_position
                store(node, pos, get(child, q) ^ int(tag == "NOT"))
                continue

            if tag == "AND":
                idx = frame.index
                if idx >= len(node.args):
                    store(node, pos, 1)
                    continue
                child = node.args[idx]
                if not is_known(child, pos):
                    stack.append(_EvalFrame("AND", node, pos, index=idx))
                    stack.append(_EvalFrame("VISIT", child, pos))
                    continue
                if get(child, pos) == 0:
                    store(node, pos, 0)
                    continue
                stack.append(_EvalFrame("AND", node, pos, index=idx + 1))
                continue

            if tag == "OR":
                idx = frame.index
                if idx >= len(node.args):
                    store(node, pos, 0)
                    continue
                child = node.args[idx]
                if not is_known(child, pos):
                    stack.append(_EvalFrame("OR", node, pos, index=idx))
                    stack.append(_EvalFrame("VISIT", child, pos))
                    continue
                if get(child, pos) == 1:
                    store(node, pos, 1)
                    continue
                stack.append(_EvalFrame("OR", node, pos, index=idx + 1))
                continue

            if tag == "XOR":
                idx, acc = frame.index, frame.accumulator
                if idx >= len(node.args):
                    store(node, pos, acc)
                    continue
                child = node.args[idx]
                if not is_known(child, pos):
                    stack.append(
                        _EvalFrame("XOR", node, pos, index=idx, accumulator=acc)
                    )
                    stack.append(_EvalFrame("VISIT", child, pos))
                    continue
                stack.append(
                    _EvalFrame(
                        "XOR",
                        node,
                        pos,
                        index=idx + 1,
                        accumulator=acc ^ get(child, pos),
                    )
                )
                continue

            if tag == "ITE_SELECT":
                continuation = frame.child
                if continuation is None:
                    raise AssertionError("missing selector")
                selector = continuation
                branch = node.args[2] if get(selector, pos) else node.args[1]
                stack.append(
                    _EvalFrame("COPY", node, pos, child=branch, child_position=pos)
                )
                if not is_known(branch, pos):
                    stack.append(_EvalFrame("VISIT", branch, pos))
                continue

            if tag == "BOOLFUNC_FINISH":
                deps = frame.dependencies
                assignment = 0
                for j, (child, q) in enumerate(deps):
                    assignment |= get(child, q) << j
                store(node, pos, (int(node.param[0]) >> assignment) & 1)
                continue

            if tag == "PRED":
                idx, coeff = frame.index, frame.accumulator
                if idx >= len(node.args):
                    store(node, pos, predicate_bit(node, coeff))
                    continue
                child = node.args[idx]
                if not is_known(child, pos):
                    stack.append(
                        _EvalFrame("PRED", node, pos, index=idx, accumulator=coeff)
                    )
                    stack.append(_EvalFrame("VISIT", child, pos))
                    continue
                stack.append(
                    _EvalFrame(
                        "PRED",
                        node,
                        pos,
                        index=idx + 1,
                        accumulator=coeff | (get(child, pos) << idx),
                    )
                )
                continue

            if tag == "COEFF_FINISH":
                store(node, pos, coefficient_bit(node, pos, get))
                continue

            raise AssertionError(tag)

        return get(root, position)

    def derived_get(self, key: tuple[object, ...]) -> Expr | None:
        return self._derived.get(tuple(key))

    def metadata_get(self, key: tuple[object, ...]) -> Any:
        return self._metadata.get(tuple(key))

    def metadata_set(self, key: tuple[object, ...], value: _MetaT) -> _MetaT:
        self._metadata[tuple(key)] = value
        return value

    def metadata_increment(self, key: str, amount: int = 1) -> int:
        mkey = ("counter", str(key))
        value = int(self._metadata.get(mkey, 0)) + int(amount)
        self._metadata[mkey] = value
        return value

    def metadata_counter(self, key: str) -> int:
        return int(self._metadata.get(("counter", str(key)), 0))

    def derived_set(self, key: tuple[object, ...], value: Expr) -> Expr:
        self._derived[tuple(key)] = value
        return value

    @property
    def unique_nodes(self) -> int:
        return len(self._nodes)

    @property
    def cached_closed_bits(self) -> int:
        return self._closed_bit_count
