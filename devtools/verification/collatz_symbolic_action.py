"""Canonical symbolic affine actions and demand-driven dyadic port evaluation.

An action is ``(3**h*x+B)/2**k``.  Only the exponents and an integer-ID DAG
for B are retained.  Branch selection is separate: a bounded residue observer
cannot be assumed to be a successor-closed quotient of the Collatz map.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass

from devtools.verification.lazy_collatz import CollatzLazyView, LazyCollatzApplication
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    LoweringCapability,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicSpan,
    iter_symbols,
    source_span,
)
from number_compiler.resources.ledger import ResourceLedger


def _splice_dependency(
    stack: list[tuple[str, int, int, int]],
    results: dict[tuple[str, int, int], int | tuple[int, int]],
    key: tuple[str, int, int],
    dependency: tuple[str, int, int],
    stage: int,
    neighbor: int,
    split_first: bool,
) -> tuple[tuple[int, int], int] | None:
    if stage == 0:
        stack.extend(((*key, 1), (*dependency, 0)))
        return None
    pieces = results[dependency]
    assert isinstance(pieces, tuple)
    child = ("c", pieces[1], neighbor) if split_first else ("c", neighbor, pieces[0])
    if stage == 1:
        stack.extend(((*key, 2), (*child, 0)))
        return None
    part = results[child]
    assert isinstance(part, int)
    return pieces, part


@dataclass(frozen=True, slots=True)
class CollatzSymbolicAction:
    action_id: int
    h: int
    k: int
    left_id: int = 0
    right_id: int = 0


class CollatzSymbolicActionArena:
    """Hash-cons affine programs with a canonical, associative binary shape.

    The action domain is the valuation program's dyadic cylinder.  Canonical
    splitting by event count removes parenthesization from the action identity;
    no exact spatial occurrence participates in composition or power keys.
    """

    def __init__(self) -> None:
        self._owner = ArenaToken("collatz-affine-program")
        self._nodes = [CollatzSymbolicAction(0, 0, 0)]
        self._atoms: dict[int, int] = {}
        self._joins: dict[tuple[int, int], int] = {}
        self._compositions: dict[tuple[int, int], int] = {}
        self.compositions = 0
        self.composition_hits = 0
        self.residue_queries = 0
        self.maximum_port_bits = 0
        self.endpoint_projections = 0

    @property
    def nodes(self) -> tuple[CollatzSymbolicAction, ...]:
        """Immutable inspection snapshot; canonical identities are never recycled."""
        return tuple(self._nodes)

    @property
    def identity(self) -> ActionProgramID:
        return self._handle(0)

    def _handle(self, local_id: int) -> ActionProgramID:
        return ActionProgramID(self._owner, "collatz-affine-program", local_id)

    def validate(self, handle: ActionProgramID) -> int:
        if type(handle) is not ActionProgramID:
            raise TypeError("Collatz affine action requires a scoped program ID")
        return handle.validate(
            self._owner, "collatz-affine-program", size=len(self._nodes)
        ).local_id

    def node(self, handle: ActionProgramID) -> CollatzSymbolicAction:
        return self._nodes[self.validate(handle)]

    def atom(self, valuation: int) -> ActionProgramID:
        if type(valuation) is not int:
            raise TypeError("Collatz valuation must be an exact integer")
        if valuation < 0:
            raise ValueError(valuation)
        found = self._atoms.get(valuation)
        if found is not None:
            return self._handle(found)
        action_id = len(self._nodes)
        self._nodes.append(CollatzSymbolicAction(action_id, 1, valuation))
        self._atoms[valuation] = action_id
        return self._handle(action_id)

    def _join(self, first: int, second: int) -> int:
        key = (first, second)
        found = self._joins.get(key)
        if found is not None:
            return found
        a, b = self._nodes[first], self._nodes[second]
        action_id = len(self._nodes)
        self._nodes.append(
            CollatzSymbolicAction(action_id, a.h + b.h, a.k + b.k, first, second)
        )
        self._joins[key] = action_id
        return action_id

    def compose(
        self, first: ActionProgramID, second: ActionProgramID
    ) -> ActionProgramID:
        first_id, second_id = self.validate(first), self.validate(second)
        return self._handle(self._compose_ids(first_id, second_id))

    def _compose_ids(self, first: int, second: int) -> int:
        """Return second after first, normalized without recursive evaluation."""
        self.compositions += 1
        cached = self._compositions.get((first, second))
        if cached is not None:
            self.composition_hits += 1
            return cached
        results: dict[tuple[str, int, int], int | tuple[int, int]] = {}
        stack = [("c", first, second, 0)]
        while stack:
            kind, a, b, stage = stack.pop()
            key = (kind, a, b)
            if key in results:
                continue
            if kind == "c":
                if not a or not b:
                    results[key] = a or b
                    continue
                old = self._compositions.get((a, b))
                if old is not None:
                    results[key] = old
                    continue
                total = self._nodes[a].h + self._nodes[b].h
                split = 1 << ((total - 1).bit_length() - 1)
                if self._nodes[a].h == split:
                    out = self._join(a, b)
                    self._compositions[(a, b)] = out
                    results[key] = out
                    continue
                split_first = self._nodes[a].h > split
                dependency = (
                    ("s", a, split)
                    if split_first
                    else ("s", b, split - self._nodes[a].h)
                )
                neighbor = b if split_first else a
            else:
                node = self._nodes[a]
                if b == 0 or b == node.h:
                    results[key] = (0, a) if b == 0 else (a, 0)
                    continue
                left, right = node.left_id, node.right_id
                left_count = self._nodes[left].h
                if b == left_count:
                    results[key] = (left, right)
                    continue
                split_first = b < left_count
                dependency = (
                    ("s", left, b) if split_first else ("s", right, b - left_count)
                )
                neighbor = right if split_first else left
            resolved = _splice_dependency(
                stack, results, key, dependency, stage, neighbor, split_first
            )
            if resolved is None:
                continue
            pieces, part = resolved
            if kind == "c":
                out = (
                    self._join(pieces[0], part)
                    if split_first
                    else self._join(part, pieces[1])
                )
                self._compositions[(a, b)] = out
                results[key] = out
            else:
                results[key] = (pieces[0], part) if split_first else (part, pieces[1])
        result = results[("c", first, second)]
        assert isinstance(result, int)
        return result

    def _valuation_program(self, action_id: int) -> Iterator[int]:
        if type(action_id) is not int or not 0 <= action_id < len(self._nodes):
            raise ValueError("invalid affine action ID")
        stack = [action_id]
        while stack:
            current = stack.pop()
            if current == 0:
                continue
            node = self._nodes[current]
            if node.h == 1:
                yield node.k
            else:
                stack.extend((node.right_id, node.left_id))

    def _lazy_application(
        self, source: DyadicSpan, action_id: int
    ) -> tuple[LazyCollatzApplication, CollatzLazyView]:
        if type(source) is not DyadicSpan:
            raise TypeError("Collatz source must be an exact dyadic span")
        if type(action_id) is not int or not 0 <= action_id < len(self._nodes):
            raise ValueError("invalid affine action ID")
        bits = tuple(
            bit
            for digit in iter_symbols(source)
            for bit in (digit & 1, (digit >> 1) & 1)
        )
        # This compatibility observer has a bounded working program budget;
        # production uses the index-owned application and its shared ledger.
        application = LazyCollatzApplication(
            2, 0, bits, ResourceLedger(max_cache_entries=8192)
        )
        view = application.valuation_program(self._valuation_program(action_id))
        return application, view

    def residue(self, source: DyadicSpan, action_id: ActionProgramID, bits: int) -> int:
        """Compatibility machine-word observation; no expanded source/B prefix."""
        if type(source) is not DyadicSpan:
            raise TypeError("Collatz source must be an exact dyadic span")
        if type(bits) is not int:
            raise TypeError("numeric carry width must be an exact integer")
        if not 0 <= bits <= 64:
            raise ValueError("a numeric carry port is limited to 64 bits")
        local_id = self.validate(action_id)
        self.residue_queries += 1
        self.maximum_port_bits = max(self.maximum_port_bits, bits)
        application, view = self._lazy_application(source, local_id)
        result = 0
        for position in range(bits):
            result |= application.view_point(view, position) << position
        return result

    def project(
        self, source: DyadicSpan, action_id: ActionProgramID, bit_bound: int
    ) -> DyadicSpan:
        """Explicit endpoint lowering of a factored finite-carry program."""
        if type(source) is not DyadicSpan:
            raise TypeError("Collatz source must be an exact dyadic span")
        if type(bit_bound) is not int:
            raise TypeError("endpoint bit bound must be an exact integer")
        if bit_bound < 1:
            raise ValueError(bit_bound)
        local_id = self.validate(action_id)
        application, view = self._lazy_application(source, local_id)
        summary = application.range_summary(view)
        width = 1 if summary.last_one is None else summary.last_one + 1
        view = CollatzLazyView(view.source, view.program, width)
        bits = application.materialize_bits(view, LoweringCapability(application.token))
        digits = tuple(
            bits[i] + (2 * bits[i + 1] if i + 1 < len(bits) else 0)
            for i in range(0, len(bits), 2)
        )
        self.endpoint_projections += 1
        return source_span(digits, blank=0, logical_length=len(digits))

    @property
    def action_count(self) -> int:
        return len(self._nodes)

    @property
    def retained_entries(self) -> int:
        return (
            len(self._nodes)
            + len(self._atoms)
            + len(self._joins)
            + len(self._compositions)
        )

    @property
    def composition_cache(self) -> dict[tuple[int, int], int]:
        """The single composition interner shared with temporal powering."""
        return self._compositions
