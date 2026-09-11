"""Immutable finite observers used by symbolic space-time diamonds."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BoundarySide,
    BoundaryState,
)


@dataclass(frozen=True, slots=True)
class NonblankBlockEffect:
    """Identity output with a two-state nonblank OR port in each direction.

    Its alphabet agrees with the observed operator, including that operator's
    blank symbol. State one is absorbing over the complete fixed alphabet.
    This is a source-independent kernel, never a summary of an output word.
    """

    base: int
    blank: int
    node_id: int = field(
        default_factory=lambda: next(_OPERATOR_IDS), init=False, compare=False
    )

    def __post_init__(self) -> None:
        if (
            type(self.base) is not int
            or self.base < 2
            or type(self.blank) is not int
            or self.blank < 1
        ):
            raise ValueError("invalid observer alphabet")

    @property
    def exponent(self) -> int:
        return 0

    @property
    def blank_left_tail(self) -> int:
        return 0

    @property
    def blank_right_tail(self) -> int:
        return 0

    @property
    def stable_blank_output(self) -> bool:
        return True

    @property
    def supports_predecessor_trace(self) -> bool:
        return False

    @property
    def eager_boundary_quotient(self) -> bool:
        return True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return "diamond-nonblank", self.base, self.blank

    @staticmethod
    def _side(side: BoundarySide) -> None:
        if type(side) is not BoundarySide:
            raise ValueError("invalid observer side")

    def initial(self, side: BoundarySide) -> int:
        self._side(side)
        return 0

    def boundary_universe(
        self, side: BoundarySide, *, max_states: int | None = None
    ) -> tuple[int, ...] | None:
        self._side(side)
        return None if max_states is not None and max_states < 2 else (0, 1)

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        self._side(side)
        if (
            type(state) is not int
            or state not in (0, 1)
            or type(symbol) is not int
            or not 0 <= symbol <= self.blank
        ):
            raise ValueError("observer input outside fixed interface")
        return int(bool(state) or symbol != self.blank)

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        if (
            type(left) is not int
            or left not in (0, 1)
            or type(right) is not int
            or right not in (0, 1)
            or type(symbol) is not int
            or not 0 <= symbol <= self.blank
        ):
            raise ValueError("observer output outside fixed interface")
        return symbol

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        self._side(side)
        return None

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        return {"operator_nodes": 1}
