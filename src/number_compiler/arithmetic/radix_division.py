"""Constant-size binary long-division primitive for symbolic radix ports."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect


_SYMBOLIC_DIVISION_SCHEMA = "symbolic-binary-division-v2"
_MAX_ENUMERATED_BOUNDARY_STATES = 512


@dataclass(frozen=True, slots=True)
class SymbolicBinaryDivisionEffect:
    """One MSD-normalizing division step with an implicit ``2*radix`` port.

    Right state ``2 * remainder + active`` records the bounded remainder and
    whether a nonzero quotient symbol has appeared in the higher suffix.  Its
    domain is described by cardinality; no transition table is materialized.
    """

    radix: int
    base: int = 2
    exponent: int = 1
    blank: int = 2
    blank_left_tail: int = 0
    blank_right_tail: int = 0
    stable_blank_output: bool = True
    supports_predecessor_trace: bool = False
    node_id: int = 0

    def __post_init__(self) -> None:
        if type(self.radix) is not int or not 2 <= self.radix <= 1 << 63:
            raise ValueError("symbolic division radix requires 2..2**63")

        fixed = (
            type(self.base) is int and self.base == 2,
            type(self.exponent) is int and self.exponent == 1,
            type(self.blank) is int and self.blank == 2,
            type(self.blank_left_tail) is int and self.blank_left_tail == 0,
            type(self.blank_right_tail) is int and self.blank_right_tail == 0,
            type(self.stable_blank_output) is bool and self.stable_blank_output is True,
            type(self.supports_predecessor_trace) is bool
            and self.supports_predecessor_trace is False,
            type(self.node_id) is int and self.node_id == 0,
        )
        if not all(fixed):
            raise ValueError("symbolic division has malformed fixed semantics")

    def canonical_key(self) -> tuple[object, ...]:
        """Return the complete, versioned immutable semantic identity."""
        return (
            _SYMBOLIC_DIVISION_SCHEMA,
            self.radix,
            self.base,
            self.exponent,
            self.blank,
            self.blank_left_tail,
            self.blank_right_tail,
            self.stable_blank_output,
            self.supports_predecessor_trace,
        )

    def boundary_universe(
        self,
        side: BoundarySide,
        *,
        max_states: int | None = None,
    ) -> tuple[BoundaryState, ...] | None:
        if type(side) is not BoundarySide:
            raise ValueError("invalid symbolic division side")
        if max_states is not None and type(max_states) is not int:
            raise TypeError("boundary enumeration limit requires an exact integer")
        if max_states is not None and max_states < 0:
            raise ValueError("boundary enumeration limit cannot be negative")
        count = 1 if side is BoundarySide.LEFT else 2 * self.radix
        limit = (
            _MAX_ENUMERATED_BOUNDARY_STATES
            if max_states is None
            else min(max_states, _MAX_ENUMERATED_BOUNDARY_STATES)
        )
        if count > limit:
            return None
        return tuple(range(count))

    def initial(self, side: BoundarySide) -> int:
        if type(side) is not BoundarySide:
            raise ValueError("invalid symbolic division side")
        return 0

    def _state(self, side: BoundarySide, state: BoundaryState) -> int:
        if type(side) is not BoundarySide or type(state) is not int:
            raise TypeError("symbolic division requires exact finite states")
        bound = 1 if side is BoundarySide.LEFT else 2 * self.radix
        if not 0 <= state < bound:
            raise ValueError("symbolic division state lies outside its port")
        return state

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        state = self._state(side, state)
        if type(symbol) is not int or symbol not in (0, 1, 2):
            raise ValueError("symbolic division requires a binary or blank symbol")
        if side is BoundarySide.LEFT or symbol == self.blank:
            return state
        remainder, active = divmod(state, 2)
        quotient, outgoing = divmod(2 * remainder + symbol, self.radix)
        return 2 * outgoing + int(bool(active or quotient))

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        self._state(BoundarySide.LEFT, left)
        state = self._state(BoundarySide.RIGHT, right)
        if type(symbol) is not int or symbol not in (0, 1, 2):
            raise ValueError("symbolic division requires a binary or blank symbol")
        if symbol == self.blank:
            return self.blank
        remainder, active = divmod(state, 2)
        quotient = (2 * remainder + symbol) // self.radix
        return quotient if active or quotient else self.blank

    def predecessor(
        self, side: BoundarySide, state: BoundaryState
    ) -> BoundaryState | None:
        self._state(side, state)
        return None

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        return {}


def certified_binary_division_radix(effect: object) -> int | None:
    """Return the radix only for the exact normalized division law.

    Small radices historically use a :class:`FiniteBlockEffect` so proof and
    compatibility callers can inspect its table.  Production can nevertheless
    use the same closed arithmetic interface as the symbolic wide-radix law,
    provided the complete finite behavior is checked rather than inferred from
    a kernel name.
    """
    if type(effect) is SymbolicBinaryDivisionEffect:
        try:
            effect.__post_init__()
            expected = SymbolicBinaryDivisionEffect(effect.radix)
        except (TypeError, ValueError):
            return None
        if effect != expected or effect.canonical_key() != expected.canonical_key():
            return None
        return effect.radix
    if type(effect) is not FiniteBlockEffect:
        return None
    right_count = effect.right_count
    if (
        type(right_count) is not int
        or right_count & 1
        or not 4 <= right_count <= _MAX_ENUMERATED_BOUNDARY_STATES
    ):
        return None
    radix = right_count // 2
    try:
        fixed = (
            effect.base == 2,
            effect.exponent == 1,
            effect.left_count == 1,
            effect.alphabet_size == 3,
            effect.blank == 2,
            effect.initial(BoundarySide.LEFT) == 0,
            effect.initial(BoundarySide.RIGHT) == 0,
            effect.left_transitions == (0, 0, 0),
            effect.blank_left_tail == 0,
            effect.blank_right_tail == 0,
            effect.stable_blank_output is True,
            effect.supports_predecessor_trace is False,
        )
    except (TypeError, ValueError):
        return None
    if not all(fixed):
        return None
    if (
        len(effect.right_transitions) != 3 * right_count
        or len(effect.outputs) != 3 * right_count
    ):
        return None
    for state in range(right_count):
        remainder, active = divmod(state, 2)
        for symbol in range(3):
            offset = 3 * state + symbol
            if symbol == 2:
                expected_state = state
            else:
                quotient, outgoing = divmod(2 * remainder + symbol, radix)
                expected_state = 2 * outgoing + int(bool(active or quotient))
            if effect.right_transitions[offset] != expected_state:
                return None
    for symbol in range(3):
        for state in range(right_count):
            remainder, active = divmod(state, 2)
            expected_output = 2
            if symbol != 2:
                quotient = (2 * remainder + symbol) // radix
                expected_output = quotient if active or quotient else 2
            if effect.outputs[symbol * right_count + state] != expected_output:
                return None
    return radix


__all__ = ["SymbolicBinaryDivisionEffect", "certified_binary_division_radix"]
