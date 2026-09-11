"""Finite terminal transducer from a reverse/add pair field to radix digits.

This is deliberately a *block effect* rather than a positional post-pass.  It
lets a powered pair operator be composed directly with normalization, so one
requested digit absorbs the carry prefix into the same semantic residual query
instead of scanning all earlier pair coefficients.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BoundarySide,
    BoundaryState,
)


@dataclass(frozen=True, slots=True)
class _DigitLeftState:
    carry: int
    blank_seen: bool
    sink: bool = False


class DigitNormalizeBlockEffect:
    """Exact padded pair->digit normalizer.

    Active input symbols are pair coefficients ``0..2b-2`` and ``2b-1`` is the
    shared blank.  The first blank emits a terminal carry 1 when necessary;
    every later blank stays blank.  The right boundary is irrelevant, making
    this a tiny finite terminal observer that can be composed behind ``T**n``.

    ``exponent`` is zero because this observer is not another reverse/add
    generation.  Callers provide one explicit terminal blank in the padded
    source tape so the final carry can be observed.
    """

    __slots__ = (
        "_sealed",
        "base",
        "blank",
        "exponent",
        "node_id",
        "blank_left_tail",
        "blank_right_tail",
        "stable_blank_output",
        "supports_predecessor_trace",
    )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("kernel definitions are immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("immutable definition attributes cannot be deleted")

    def __init__(self, base: int) -> None:
        base = int(base)
        if base < 2:
            raise ValueError(base)
        self.base = base
        self.blank = 2 * base - 1
        self.exponent = 0
        self.node_id = next(_OPERATOR_IDS)
        self.blank_left_tail = 1
        self.blank_right_tail = 0
        self.stable_blank_output = True
        self.supports_predecessor_trace = False
        self._sealed = True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("digit-normalize-block", self.base)

    def boundary_universe(self, side: BoundarySide) -> tuple[BoundaryState, ...]:
        if side is BoundarySide.RIGHT:
            return (0,)
        return (
            _DigitLeftState(0, False),
            _DigitLeftState(1, False),
            _DigitLeftState(0, True),
            _DigitLeftState(0, True, True),
        )

    def initial(self, side: BoundarySide) -> BoundaryState:
        if side is BoundarySide.LEFT:
            return _DigitLeftState(0, False, False)
        return 0

    def advance(
        self, side: BoundarySide, state: BoundaryState, symbol: int
    ) -> BoundaryState:
        symbol = int(symbol)
        if side is BoundarySide.RIGHT:
            return 0
        if not isinstance(state, _DigitLeftState):
            raise TypeError(type(state))
        if state.sink:
            out = state
        elif symbol == self.blank:
            # Consuming the first padding cell discharges the final carry.
            out = _DigitLeftState(0, True, False)
        elif state.blank_seen or not 0 <= symbol <= 2 * (self.base - 1):
            out = _DigitLeftState(0, True, True)
        else:
            out = _DigitLeftState(int(symbol + state.carry >= self.base), False, False)
        return out

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        del right
        if not isinstance(left, _DigitLeftState):
            raise TypeError(type(left))
        symbol = int(symbol)
        if left.sink or left.blank_seen:
            out = self.blank
        elif symbol == self.blank:
            out = 1 if left.carry else self.blank
        elif not 0 <= symbol <= 2 * (self.base - 1):
            out = self.blank
        else:
            out = (symbol + left.carry) % self.base
        return out

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        del side, state
        return None

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        transition_cache_entries = 0
        output_cache_entries = 0
        return {
            "operator_nodes": 1,
            "left_boundary_residuals": 0,
            "right_boundary_residuals": 0,
            "residual_cache_hits": 0,
            "residual_cache_misses": 0,
            "output_cache_hits": 0,
            "output_cache_misses": 0,
            "output_cache_slots": 0,
            "output_cache_occupied": 0,
            "left_transition_entries": 0,
            "right_transition_entries": 0,
            "leaf_effect_transition_cache_entries": transition_cache_entries,
            "leaf_effect_output_cache_entries": output_cache_entries,
            "leaf_effect_cache_entries": transition_cache_entries
            + output_cache_entries,
            "finite_kernel_left_states": 0,
            "finite_kernel_right_states": 0,
            "finite_kernel_storage_bytes": 0,
        }


__all__ = ["DigitNormalizeBlockEffect"]
