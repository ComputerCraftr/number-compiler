"""Persistent compressed Collatz parity/carry grammar for temporal products.

A tape retains concatenation and repeat nodes rather than expanding a named
macro into occurrences. Its exact affine and mod-5 weighted actions are
obtained by binary composition. A time puncture traverses only the path of
SLP nodes needed for that time. Different guarded source fibers can reuse
the same authenticated grammar without retaining an old pointed source.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, NamedTuple, Self, TypeVar

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        UnitsCarryMatrix,
    )
    from number_compiler.sequences.collatz.parity_carry_tape_actions import (
        LedgeredParityTapeActions,
    )

_Effect = TypeVar("_Effect")


def _full_effect(
    root: ParityCarryTape,
    *,
    identity: _Effect,
    letter: Callable[[int], _Effect],
    compose: Callable[[_Effect, _Effect], _Effect],
    power: Callable[[_Effect, int], _Effect],
    memo: dict[int, _Effect] | None = None,
) -> _Effect:
    """Fold retained nodes once; a supplied memo belongs to this one fold request."""
    values: dict[int, _Effect] = {} if memo is None else memo
    pending: list[tuple[ParityCarryTape, bool]] = [(root, False)]
    result = identity
    node: ParityCarryTape | None = None
    child: ParityCarryTape | None = None
    missing: tuple[ParityCarryTape, ...] = ()
    try:
        while pending:
            node, ready = pending.pop()
            key = id(node)
            if key in values:
                continue
            if node.kind == "word":
                result = identity
                for bit in node.word:
                    result = compose(result, letter(bit))
                values[key] = result
            elif node.kind == "repeat":
                child = node.children[0]
                if not ready and id(child) not in values:
                    pending.append((node, True))
                    pending.append((child, False))
                else:
                    values[key] = power(values[id(child)], node.repetitions)
            else:
                missing = tuple(
                    child for child in node.children if id(child) not in values
                )
                if missing:
                    pending.append((node, True))
                    pending.extend((child, False) for child in reversed(missing))
                else:
                    result = identity
                    for child in node.children:
                        result = compose(result, values[id(child)])
                    values[key] = result
        result = values[id(root)]
        return result
    finally:
        pending.clear()
        if memo is None:
            values.clear()
        result = identity
        node = None
        child = None
        missing = ()


class _ParityTapePayload(NamedTuple):
    kind: str
    word: tuple[int, ...]
    children: tuple[ParityCarryTape, ...]
    repetitions: int
    steps: int
    odds: int
    concat_height: int
    traversal_depth: int


class ParityCarryTape(tuple[_ParityTapePayload, ...]):
    """Tuple-backed immutable parity SLP node with validating construction."""

    __slots__ = ()

    def __new__(
        cls: type[Self],
        kind: str,
        word: tuple[int, ...] = (),
        children: tuple[ParityCarryTape, ...] = (),
        repetitions: int = 1,
        steps: int = 0,
        odds: int = 0,
    ) -> Self:
        if (
            cls is not ParityCarryTape
            or type(kind) is not str
            or type(word) is not tuple
            or type(children) is not tuple
            or type(repetitions) is not int
            or type(steps) is not int
            or type(odds) is not int
            or any(type(child) is not ParityCarryTape for child in children)
        ):
            raise ValueError("invalid parity tape field types")
        if kind == "word":
            if (
                not 1 <= len(word) <= 64
                or children
                or repetitions != 1
                or any(type(bit) is not int or bit not in (0, 1) for bit in word)
                or steps != len(word)
                or odds != sum(word)
            ):
                raise ValueError("invalid certified parity tape word")
            height = 1
        elif kind == "concat":
            if (
                word
                or repetitions != 1
                or len(children) != 2
                or abs(children[0].height - children[1].height) > 1
                or steps != sum(child.steps for child in children)
                or odds != sum(child.odds for child in children)
            ):
                raise ValueError("invalid certified parity tape concatenation")
            height = 1 + max(child.height for child in children)
        elif kind == "repeat":
            if (
                word
                or len(children) != 1
                or repetitions < 1
                or steps != children[0].steps * repetitions
                or odds != children[0].odds * repetitions
            ):
                raise ValueError("invalid certified parity tape power")
            height = 1
        else:
            raise ValueError("unknown certified parity tape node")
        depth = 1 + max((child.traversal_depth for child in children), default=0)
        payload = _ParityTapePayload(
            kind, word, children, repetitions, steps, odds, height, depth
        )
        return super().__new__(cls, (payload,))

    def __init__(
        self,
        kind: str,
        word: tuple[int, ...] = (),
        children: tuple[ParityCarryTape, ...] = (),
        repetitions: int = 1,
        steps: int = 0,
        odds: int = 0,
    ) -> None:
        # Validation and immutable payload publication happen in __new__.
        """No additional initialization is permitted on immutable tuple nodes."""
        del self, kind, word, children, repetitions, steps, odds

    @property
    def _payload(self) -> _ParityTapePayload:
        return self[0]

    @property
    def kind(self) -> str:
        return self._payload.kind

    @property
    def word(self) -> tuple[int, ...]:
        return self._payload.word

    @property
    def children(self) -> tuple[ParityCarryTape, ...]:
        return self._payload.children

    @property
    def repetitions(self) -> int:
        return self._payload.repetitions

    @property
    def steps(self) -> int:
        return self._payload.steps

    @property
    def odds(self) -> int:
        return self._payload.odds

    @property
    def _height(self) -> int:
        return self._payload.concat_height

    @property
    def _traversal_depth(self) -> int:
        return self._payload.traversal_depth

    @property
    def height(self) -> int:
        """Return structural AVL height without exposing representation state."""
        return self._height

    @property
    def traversal_depth(self) -> int:
        """Return full grammar depth, counting through repeat children."""
        return self._traversal_depth

    def __reduce__(self) -> tuple[object, tuple[object, ...]]:
        """Serialize through the validating constructor, not raw tuple data."""
        return (
            type(self),
            (
                self.kind,
                self.word,
                self.children,
                self.repetitions,
                self.steps,
                self.odds,
            ),
        )

    def __eq__(self, other: object) -> bool:
        """Match the former dataclass's exact-class structural equality."""
        return type(other) is ParityCarryTape and super().__eq__(other) is True

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

    def __hash__(self) -> int:
        return super().__hash__()

    @classmethod
    def _node(
        cls,
        left: ParityCarryTape,
        right: ParityCarryTape,
        *,
        on_node: Callable[[ParityCarryTape, ParityCarryTape], None] | None = None,
    ) -> ParityCarryTape:
        """Create one structural parent, reserving before allocation if owned."""
        if on_node is not None:
            on_node(left, right)
        return cls(
            "concat",
            children=(left, right),
            steps=left.steps + right.steps,
            odds=left.odds + right.odds,
        )

    @classmethod
    def _rebalance(
        cls,
        left: ParityCarryTape,
        right: ParityCarryTape,
        *,
        on_node: Callable[[ParityCarryTape, ParityCarryTape], None] | None = None,
    ) -> ParityCarryTape:
        """Perform an ordered persistent AVL rotation without reading bits."""
        if left._height > right._height + 1:
            a, b = left.children
            if a._height >= b._height:
                return cls._node(
                    a, cls._node(b, right, on_node=on_node), on_node=on_node
                )
            c, d = b.children
            return cls._node(
                cls._node(a, c, on_node=on_node),
                cls._node(d, right, on_node=on_node),
                on_node=on_node,
            )
        if right._height > left._height + 1:
            b, c = right.children
            if c._height >= b._height:
                return cls._node(
                    cls._node(left, b, on_node=on_node), c, on_node=on_node
                )
            d, e = b.children
            return cls._node(
                cls._node(left, d, on_node=on_node),
                cls._node(e, c, on_node=on_node),
                on_node=on_node,
            )
        return cls._node(left, right, on_node=on_node)

    @classmethod
    def _join(
        cls,
        left: ParityCarryTape,
        right: ParityCarryTape,
        *,
        on_node: Callable[[ParityCarryTape, ParityCarryTape], None] | None = None,
    ) -> ParityCarryTape:
        """Join ordered factors with an iterative logarithmic AVL descent."""
        frames: list[tuple[ParityCarryTape, bool]] = []
        while left.height > right.height + 1 or right.height > left.height + 1:
            if left.height > right.height + 1:
                if left.kind != "concat" or len(left.children) != 2:
                    raise ArithmeticError("tall AVL left factor has no binary split")
                first, second = left.children
                frames.append((first, True))
                left = second
            else:
                if right.kind != "concat" or len(right.children) != 2:
                    raise ArithmeticError("tall AVL right factor has no binary split")
                first, second = right.children
                frames.append((second, False))
                right = first
        joined = cls._node(left, right, on_node=on_node)
        while frames:
            fixed, left_frame = frames.pop()
            joined = (
                cls._rebalance(fixed, joined, on_node=on_node)
                if left_frame
                else cls._rebalance(joined, fixed, on_node=on_node)
            )
        return joined

    @classmethod
    def letters(cls, bits: tuple[int, ...]) -> ParityCarryTape:
        return cls("word", word=bits, steps=len(bits), odds=sum(bits))

    @classmethod
    def sequence(
        cls,
        nodes: tuple[ParityCarryTape, ...],
        *,
        on_node: Callable[[ParityCarryTape, ParityCarryTape], None] | None = None,
    ) -> ParityCarryTape:
        if not nodes:
            raise ValueError("empty parity sequence has no admitted action")
        if len(nodes) == 1:
            return nodes[0]
        if len(nodes) == 2:
            return cls._join(nodes[0], nodes[1], on_node=on_node)
        layer = list(nodes)
        while len(layer) > 1:
            layer = [
                cls._join(layer[index], layer[index + 1], on_node=on_node)
                if index + 1 < len(layer)
                else layer[index]
                for index in range(0, len(layer), 2)
            ]
        return layer[0]

    @classmethod
    def repeated(cls, node: ParityCarryTape, count: int) -> ParityCarryTape:
        if count == 1:
            return node
        return cls(
            "repeat",
            children=(node,),
            repetitions=count,
            steps=node.steps * count,
            odds=node.odds * count,
        )

    @classmethod
    def factors(
        cls,
        factors: tuple[tuple[tuple[int, ...], int], ...],
        *,
        repetitions: int = 1,
    ) -> ParityCarryTape:
        return cls.repeated(
            cls.sequence(
                tuple(cls.repeated(cls.letters(bits), count) for bits, count in factors)
            ),
            repetitions,
        )

    @classmethod
    def from_named_macro(cls, macro: object) -> ParityCarryTape:
        """Retain the canonical producer-issued factor grammar of a macro."""
        from number_compiler.sequences.collatz.border_identity import (
            ENTRY_0563,
            ENTRY_89_AT_NINE,
            ENTRY_421,
            ENTRY_4721,
            PATH_305,
            PATH_630,
        )
        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
            validate_border_return_macro,
        )
        from number_compiler.sequences.collatz.boundary_macros import (
            CollatzBoundaryMacro,
            boundary_macro_26847_phase,
            validate_boundary_macro,
        )

        factors: tuple[tuple[tuple[int, ...], int], ...]
        if type(macro) is BorderReturnMacro:
            validate_border_return_macro(macro)
            factors = tuple(((bit,), count) for bit, count in macro.parts)
        elif type(macro) is CollatzBoundaryMacro:
            validate_boundary_macro(macro)
            phase = boundary_macro_26847_phase(macro.identity)
            if macro.identity == ENTRY_421:
                factors = (((0,), 2), ((1, 0), macro.repetitions - 1), ((1,), 1))
            elif macro.identity in (ENTRY_4721, ENTRY_0563):
                factors = (((0,), 1), ((1,), 2 * macro.repetitions))
            elif phase is not None:
                factors = (
                    ((0,), 4 - phase),
                    ((1, 0, 0, 0), macro.repetitions - 1),
                    ((1,), 1),
                )
            elif macro.identity == ENTRY_89_AT_NINE:
                factors = (((1,), macro.repetitions),)
            elif macro.identity == PATH_630:
                factors = (((0, 1), 1), ((0,), macro.repetitions))
            elif macro.identity == PATH_305:
                factors = (((1,), 1), ((0,), macro.repetitions))
            else:
                raise ValueError("named macro has no retained parity factor grammar")
        else:
            raise TypeError("retained parity grammar requires an issued macro")

        factors = tuple((word, count) for word, count in factors if count)
        tape = cls.factors(factors)
        action = tape.action()
        if (
            tape.steps != macro.fields.steps
            or tape.odds != macro.odd_symbols
            or action.coefficient_snapshot() != macro.fields.coefficient_snapshot()
            or not action.certifies(macro.source)
            or action.endpoint(macro.source) != macro.endpoint
        ):
            raise ArithmeticError(
                "retained parity factors differ from their issued macro"
            )
        return tape

    def _word_action(self, limit: int) -> DyadicTerminalFieldAction:
        result = DyadicTerminalFieldAction.identity()
        for bit in self.word[:limit]:
            result = result.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        return result

    def action(
        self, *, cache: LedgeredParityTapeActions | None = None
    ) -> DyadicTerminalFieldAction:
        """Fold the tape, optionally using an explicitly ledger-owned cache."""
        if cache is not None:
            from number_compiler.sequences.collatz.parity_carry_tape_actions import (
                LedgeredParityTapeActions,
            )

            if type(cache) is not LedgeredParityTapeActions:
                raise TypeError("parity action cache requires a ledger-owned store")
            return cache.action(self)
        return _full_effect(
            self,
            identity=DyadicTerminalFieldAction.identity(),
            letter=lambda bit: (
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            ),
            compose=lambda first, after: first.then(after),
            power=lambda effect, count: effect.power(count),
        )

    def _prefix_chunks(self, time: int) -> tuple[tuple[ParityCarryTape, int], ...]:
        """Return ordered full-node and partial-word chunks for one prefix."""
        if type(time) is not int or not 0 <= time <= self.steps:
            raise ValueError("parity tape prefix lies outside its certified word")
        chunks: list[tuple[ParityCarryTape, int]] = []
        pending: list[tuple[ParityCarryTape, int]] = [(self, time)]
        children: list[tuple[ParityCarryTape, int]] = []
        node: ParityCarryTape | None = None
        child: ParityCarryTape | None = None
        try:
            while pending:
                node, take = pending.pop()
                if not take:
                    continue
                if take == node.steps:
                    chunks.append((node, 1))
                elif node.kind == "word":
                    chunks.append((ParityCarryTape.letters(node.word[:take]), 1))
                elif node.kind == "repeat":
                    child = node.children[0]
                    full, remainder = divmod(take, child.steps)
                    if remainder:
                        pending.append((child, remainder))
                    if full:
                        chunks.append((child, full))
                else:
                    remaining = take
                    children.clear()
                    for child in node.children:
                        child_take = min(remaining, child.steps)
                        if child_take:
                            children.append((child, child_take))
                            remaining -= child_take
                        if not remaining:
                            break
                    pending.extend(reversed(children))
            result = tuple(chunks)
            return result
        finally:
            chunks.clear()
            pending.clear()
            children.clear()
            node = None
            child = None

    def _prefix_effect(
        self,
        time: int,
        *,
        identity: _Effect,
        letter: Callable[[int], _Effect],
        compose: Callable[[_Effect, _Effect], _Effect],
        power: Callable[[_Effect, int], _Effect],
    ) -> _Effect:
        result = identity
        values: dict[int, _Effect] = {}
        node: ParityCarryTape | None = None
        effect = identity
        # All chunks stay alive for the request, so node identities cannot be
        # recycled while this local memo is shared across overlapping subgraphs.
        chunks = self._prefix_chunks(time)
        try:
            for node, count in chunks:
                effect = _full_effect(
                    node,
                    identity=identity,
                    letter=letter,
                    compose=compose,
                    power=power,
                    memo=values,
                )
                if count != 1:
                    effect = power(effect, count)
                result = compose(result, effect)
            return result
        finally:
            values.clear()
            chunks = ()
            node = None
            effect = identity
            result = identity

    def prefix_action(self, time: int) -> DyadicTerminalFieldAction:
        return self._prefix_effect(
            time,
            identity=DyadicTerminalFieldAction.identity(),
            letter=lambda bit: (
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            ),
            compose=lambda first, after: first.then(after),
            power=lambda effect, count: effect.power(count),
        )

    def prefix_odds(self, time: int) -> int:
        return sum(count * node.odds for node, count in self._prefix_chunks(time))

    def prefix_letters(self, time: int) -> tuple[int, ...]:
        """Walk the requested grammar prefix and emit its ordered symbols.

        Nested repeat nodes may revisit a child for each requested copy.
        """
        if type(time) is not int or not 0 <= time <= self.steps:
            raise ValueError("parity tape prefix lies outside its certified word")
        result: list[int] = []
        tasks: list[tuple[str, ParityCarryTape, int, int]] = [("NODE", self, time, 0)]
        node: ParityCarryTape | None = None
        child: ParityCarryTape | None = None
        value: ParityCarryTape | None = None
        try:
            while tasks:
                tag, value, first, second = tasks.pop()
                if tag == "NODE":
                    node = value
                    take = first
                    if not take:
                        continue
                    if node.kind == "word":
                        result.extend(node.word[:take])
                    elif node.kind == "repeat":
                        child = node.children[0]
                        full, remainder = divmod(take, child.steps)
                        tasks.append(("REPEAT", child, full, remainder))
                    else:
                        tasks.append(("CONCAT", node, 0, take))
                elif tag == "REPEAT":
                    child = value
                    copies = first
                    remainder = second
                    if copies:
                        tasks.append(("REPEAT", child, copies - 1, remainder))
                        tasks.append(("NODE", child, child.steps, 0))
                    elif remainder:
                        tasks.append(("NODE", child, remainder, 0))
                elif tag == "CONCAT":
                    node = value
                    index = first
                    remaining = second
                    if remaining and index < len(node.children):
                        child = node.children[index]
                        take = min(remaining, child.steps)
                        tasks.append(("CONCAT", node, index + 1, remaining - take))
                        tasks.append(("NODE", child, take, 0))
                    elif remaining:
                        raise ArithmeticError(
                            "parity SLP prefix escaped its concatenation"
                        )
                else:
                    raise AssertionError(tag)
            if len(result) != time:
                raise ArithmeticError("parity SLP prefix has an incorrect length")
            return tuple(result)
        finally:
            tasks.clear()
            result.clear()
            node = None
            child = None
            value = None

    def prefix_units(self, time: int) -> UnitsCarryMatrix:
        from number_compiler.sequences.collatz.named_border_carry_matrix import (
            UnitsCarryMatrix,
        )

        return self._prefix_effect(
            time,
            identity=UnitsCarryMatrix(),
            letter=UnitsCarryMatrix.letter,
            compose=lambda first, after: first.then(after),
            power=lambda effect, count: effect.power(count),
        )

    def seams(self, *, max_seams: int = 12) -> tuple[int, ...]:
        """Bounded factor boundaries without expanding a repeated SLP."""
        observed: set[int] = set()
        if self.kind == "concat":
            progress = 0
            for node in self.children[:-1]:
                progress += node.steps
                if 0 < progress < self.steps:
                    observed.add(progress)
        elif self.kind == "repeat" and self.repetitions > 1:
            observed.add(self.children[0].steps)
        if len(observed) > max_seams:
            observed = set(sorted(observed)[:max_seams])
        return tuple(sorted(observed))
