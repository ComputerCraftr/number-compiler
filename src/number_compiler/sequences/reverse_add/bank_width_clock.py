"""Finite run-length growth-control monoid for conditional reverse/add banks.

This recognizes only the *necessary* universal language (no five quiet or
four growth steps in succession).  Admitting a control is not evidence that
any actual decimal source produces that word.  The caller must separately
supply a source-authenticated border-control certificate to make whole-source
claims; otherwise bank actions remain explicitly conditional.
"""

from __future__ import annotations

from dataclasses import dataclass

# Initial, four quiet-run states, three growth-run states, rejecting sink.
_INITIAL = 0
_SINK = 8
_STATE_COUNT = 9


def _step(state: int, bit: int) -> int:
    if state == _SINK:
        return _SINK
    if bit == 0:
        if state in (1, 2, 3, 4):
            return state + 1 if state < 4 else _SINK
        return 1
    if state in (5, 6, 7):
        return state + 1 if state < 7 else _SINK
    return 5


@dataclass(frozen=True, slots=True)
class WidthMacro:
    """Exact growth word action over all possible incoming run phases."""

    steps: int
    growth_count: int
    transfer: tuple[int, ...]

    @classmethod
    def identity(cls) -> WidthMacro:
        return cls(0, 0, tuple(range(_STATE_COUNT)))

    @classmethod
    def event(cls, bit: int) -> WidthMacro:
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("growth control must be Boolean")
        return cls(1, bit, tuple(_step(i, bit) for i in range(_STATE_COUNT)))

    @classmethod
    def from_bits(cls, bits: tuple[int, ...]) -> WidthMacro:
        result = cls.identity()
        for bit in bits:
            result = result.then(cls.event(bit))
        return result

    def then(self, later: WidthMacro) -> WidthMacro:
        return WidthMacro(
            self.steps + later.steps,
            self.growth_count + later.growth_count,
            tuple(later.transfer[self.transfer[q]] for q in range(_STATE_COUNT)),
        )

    def repeat(self, count: int) -> WidthMacro:
        if type(count) is not int or count < 0:
            raise ValueError("growth-control repeat must be nonnegative")
        acc, action = self.identity(), self
        while count:
            if count & 1:
                acc = acc.then(action)
            count >>= 1
            if count:
                action = action.then(action)
        return acc

    def admitted(self) -> bool:
        return self.transfer[_INITIAL] != _SINK


__all__ = ["WidthMacro"]
