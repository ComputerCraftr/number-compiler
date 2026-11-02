"""Source-independent finite-tape action for one physical Collatz step."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BoundaryState,
    next_operator_id,
)
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.physical_state import (
    odd_carry_parts,
    odd_carry_state,
)

_START = 0
_EVEN = 1


class CollatzPhysicalBlockEffect:
    """One exact physical Collatz step on a padded LSD-first binary tape."""

    __slots__ = (
        "_sealed",
        "base",
        "blank",
        "blank_left_tail",
        "blank_right_tail",
        "eager_boundary_quotient",
        "exponent",
        "node_id",
        "stable_blank_output",
        "supports_predecessor_trace",
    )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("kernel definitions are immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("immutable definition attributes cannot be deleted")

    def __init__(self) -> None:
        self.base = 2
        self.blank = 2
        self.exponent = 1
        self.node_id = next_operator_id()
        self.blank_left_tail = 2
        self.blank_right_tail = 1
        self.stable_blank_output = True
        self.supports_predecessor_trace = False
        self.eager_boundary_quotient = True
        self._sealed = True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-physical-block", 1)

    def initial(self, side: BoundarySide) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        return _START if side is BoundarySide.LEFT else self.blank

    def boundary_universe(
        self,
        side: BoundarySide,
        *,
        max_states: int | None = None,
    ) -> tuple[int, ...] | None:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        states = tuple(range(6)) if side is BoundarySide.LEFT else (0, 1, self.blank)
        if max_states is not None:
            max_states = require_integer(max_states, "maximum boundary states", 0)
        if max_states is not None and len(states) > max_states:
            return None
        return states

    def diamond_boundary_state_bounds(self) -> tuple[int, int]:
        """Return the bounded state alphabet used by diamond images."""
        return 0, 64

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        state = require_integer(state, "Collatz boundary state")
        symbol = require_integer(symbol, "Collatz source symbol")
        if symbol not in (0, 1, self.blank):
            raise ValueError(symbol)
        if side is BoundarySide.RIGHT:
            return symbol

        if state == _START:
            if symbol == self.blank:
                return _START
            if symbol == 0:
                return _EVEN
            return odd_carry_state(1, 1)
        if state == _EVEN:
            return _EVEN
        previous, carry = odd_carry_parts(state)
        current = 0 if symbol == self.blank else symbol
        total = current + previous + carry
        return odd_carry_state(current, total >> 1)

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        left = require_integer(left, "Collatz left boundary")
        symbol = require_integer(symbol, "Collatz source symbol")
        right = require_integer(right, "Collatz right boundary")
        if symbol not in (0, 1, self.blank) or right not in (0, 1, self.blank):
            raise ValueError((symbol, right))

        consumes_right, local = self.output_consumer(left, symbol)
        return right if consumes_right else local

    def output_consumer(self, left: int, symbol: int) -> tuple[bool, int]:
        """Return the geometry-selected right view and left-local output."""
        left = require_integer(left, "Collatz left boundary")
        symbol = require_integer(symbol, "Collatz source symbol")
        if symbol not in (0, 1, self.blank):
            raise ValueError(symbol)

        if left == _START:
            if symbol == self.blank:
                return False, self.blank
            if symbol == 0:
                return True, 0
            return False, (symbol + 1) & 1

        if left == _EVEN:
            return True, 0

        previous, carry = odd_carry_parts(left)
        current = 0 if symbol == self.blank else symbol
        total = current + previous + carry
        if symbol == self.blank and total == 0:
            return False, self.blank
        return False, total & 1

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        return None

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        return {
            "operator_nodes": 1,
            "retained_execution_nodes": 0,
            "canonical_program_word_roots": 0,
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
            "finite_kernel_left_states": 0,
            "finite_kernel_right_states": 0,
            "finite_kernel_storage_bytes": 0,
            "leaf_effect_transition_cache_entries": 0,
            "leaf_effect_output_cache_entries": 0,
            "leaf_effect_cache_entries": 0,
        }


def power_collatz_physical_effect(
    steps: int,
    *,
    max_context_nodes: int | None = None,
    max_cache_entries: int | None = None,
) -> BlockPower:
    """Compile ``physical_collatz**steps`` by source-independent squaring."""
    steps = require_integer(steps, "Collatz physical steps", 0)
    from number_compiler.sequences.collatz.tile_family_hooks import (
        collatz_runtime_tile_hooks,
    )

    compiler = LazyCompiler(
        ResourceLedger(max_context_nodes, max_cache_entries),
        family_hooks=collatz_runtime_tile_hooks(),
    )
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    return compile_collatz_physical_power(compiler, steps)


__all__ = ["CollatzPhysicalBlockEffect", "power_collatz_physical_effect"]
