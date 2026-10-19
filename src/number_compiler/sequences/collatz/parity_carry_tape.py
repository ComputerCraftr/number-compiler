"""Persistent compressed Collatz parity/carry grammar for temporal products.

A tape retains concatenation and repeat nodes rather than expanding a named
macro into occurrences. Its exact affine and mod-5 weighted actions are
obtained by binary composition. A time puncture traverses only the path of
SLP nodes needed for that time. Different guarded source fibers can reuse
the same authenticated grammar without retaining an old pointed source.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeVar

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        UnitsCarryMatrix,
    )

_Effect = TypeVar("_Effect")


def _full_effect(
    root: ParityCarryTape,
    *,
    identity: _Effect,
    letter: Callable[[int], _Effect],
    compose: Callable[[_Effect, _Effect], _Effect],
    power: Callable[[_Effect, int], _Effect],
) -> _Effect:
    """Fold an SLP iteratively, memoizing each retained node once."""
    values: dict[int, _Effect] = {}
    pending: list[tuple[ParityCarryTape, bool]] = [(root, False)]
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
                values[key] = power(values[id(child)], node.count)
        else:
            missing = tuple(child for child in node.children if id(child) not in values)
            if missing:
                pending.append((node, True))
                pending.extend((child, False) for child in reversed(missing))
            else:
                result = identity
                for child in node.children:
                    result = compose(result, values[id(child)])
                values[key] = result
    return values[id(root)]


@dataclass(frozen=True, slots=True)
class ParityCarryTape:
    kind: str
    word: tuple[int, ...] = ()
    children: tuple[ParityCarryTape, ...] = ()
    count: int = 1
    steps: int = 0
    odds: int = 0

    def __post_init__(self) -> None:
        if self.kind == "word":
            if (
                not 1 <= len(self.word) <= 64
                or self.children
                or self.count != 1
                or any(type(v) is not int or v not in (0, 1) for v in self.word)
                or self.steps != len(self.word)
                or self.odds != sum(self.word)
            ):
                raise ValueError("invalid certified parity tape word")
        elif self.kind == "concat":
            if (
                self.word
                or self.count != 1
                or len(self.children) < 1
                or self.steps != sum(child.steps for child in self.children)
                or self.odds != sum(child.odds for child in self.children)
            ):
                raise ValueError("invalid certified parity tape concatenation")
        elif self.kind == "repeat":
            if (
                self.word
                or len(self.children) != 1
                or type(self.count) is not int
                or self.count < 1
                or self.steps != self.children[0].steps * self.count
                or self.odds != self.children[0].odds * self.count
            ):
                raise ValueError("invalid certified parity tape power")
        else:
            raise ValueError("unknown certified parity tape node")

    @classmethod
    def letters(cls, bits: tuple[int, ...]) -> ParityCarryTape:
        return cls("word", word=bits, steps=len(bits), odds=sum(bits))

    @classmethod
    def sequence(cls, nodes: tuple[ParityCarryTape, ...]) -> ParityCarryTape:
        if not nodes:
            raise ValueError("empty parity sequence has no admitted action")
        if len(nodes) == 1:
            return nodes[0]
        return cls(
            "concat",
            children=nodes,
            steps=sum(n.steps for n in nodes),
            odds=sum(n.odds for n in nodes),
        )

    @classmethod
    def repeated(cls, node: ParityCarryTape, count: int) -> ParityCarryTape:
        if count == 1:
            return node
        return cls(
            "repeat",
            children=(node,),
            count=count,
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
        if (
            tape.steps != macro.fields.steps
            or tape.odds != macro.odd_symbols
            or tape.action().coefficient_snapshot()
            != macro.fields.coefficient_snapshot()
            or not tape.action().certifies(macro.source)
            or tape.action().endpoint(macro.source) != macro.endpoint
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

    def action(self) -> DyadicTerminalFieldAction:
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
                children: list[tuple[ParityCarryTape, int]] = []
                for child in node.children:
                    child_take = min(remaining, child.steps)
                    if child_take:
                        children.append((child, child_take))
                        remaining -= child_take
                    if not remaining:
                        break
                pending.extend(reversed(children))
        return tuple(chunks)

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
        for node, count in self._prefix_chunks(time):
            effect = _full_effect(
                node,
                identity=identity,
                letter=letter,
                compose=compose,
                power=power,
            )
            if count != 1:
                effect = power(effect, count)
            result = compose(result, effect)
        return result

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
        """Emit one bounded literal prefix from this retained parity SLP."""
        if type(time) is not int or not 0 <= time <= self.steps:
            raise ValueError("parity tape prefix lies outside its certified word")
        result: list[int] = []
        for index in range(time):
            node = self
            offset = index
            while node.kind != "word":
                if node.kind == "repeat":
                    child = node.children[0]
                    offset %= child.steps
                    node = child
                    continue
                for child in node.children:
                    if offset < child.steps:
                        node = child
                        break
                    offset -= child.steps
                else:
                    raise ArithmeticError("parity SLP index escaped its concatenation")
            result.append(node.word[offset])
        return tuple(result)

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
        elif self.kind == "repeat" and self.count > 1:
            observed.add(self.children[0].steps)
        if len(observed) > max_seams:
            observed = set(sorted(observed)[:max_seams])
        return tuple(sorted(observed))
