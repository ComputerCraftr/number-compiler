from __future__ import annotations

import hashlib
import json
import struct
import sys
import zlib
from array import array
from dataclasses import dataclass
from functools import lru_cache
from importlib.resources import files
from pathlib import Path

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BoundarySide,
    BoundaryState,
    _normalized_digit,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    _decimal_kernel_carry_action,
    _decimal_kernel_pair_sum,
)


def _pair_carry_action(symbol: int, base: int) -> CarryFn:
    """Return the live primitive carry action in its proved local coordinates."""
    return (
        _decimal_kernel_carry_action(symbol)
        if base == 10
        else value_carry_fn(symbol, base)
    )


def _normalized_pair_sum(
    left_symbol: int,
    left_carry: int,
    right_symbol: int,
    right_carry: int,
    base: int,
) -> int:
    """Add two normalized digits, using the decimal factored primitive law."""
    if base == 10:
        return _decimal_kernel_pair_sum(
            left_symbol,
            left_carry,
            right_symbol,
            right_carry,
        )
    return _normalized_digit(left_symbol, left_carry, base) + _normalized_digit(
        right_symbol, right_carry, base
    )


@dataclass(frozen=True, slots=True)
class _BaseLeftState:
    carry: int
    previous_pair: int
    blank_seen: bool
    sink: bool = False


@dataclass(frozen=True, slots=True)
class _BaseRightState:
    forward_suffix: CarryFn
    backward_suffix: CarryFn


def _reverse_output_operands(
    base: int, left: _BaseLeftState, symbol: int, right: _BaseRightState
) -> tuple[int, int, int, int] | None:
    """Consume producer geometry and select the two demanded digit views.

    These bounded operands are transient execution coordinates, never a
    semantic action key. Both exact output and carry-only consumers use this
    owner, including growth edges, EQ propagation, blank tails and sinks.
    """
    if left.sink:
        return None
    if symbol == 2 * base - 1:
        if not left.blank_seen and left.previous_pair >= 0 and left.carry == 1:
            return left.previous_pair, 0, 1, 0
        return None
    action = _pair_carry_action(symbol, base)
    carry_after = apply_carry_fn(action, left.carry)
    if apply_carry_fn(right.forward_suffix, carry_after) == 0:
        return symbol, left.carry, symbol, apply_carry_fn(right.backward_suffix, 0)
    if left.previous_pair < 0:
        return symbol, 0, 1, 0
    including = compose_carry_fn(action, right.backward_suffix)
    return symbol, left.carry, left.previous_pair, apply_carry_fn(including, 0)


def _reverse_output_carry(
    base: int, left: _BaseLeftState, symbol: int, right: _BaseRightState
) -> CarryFn:
    """Observe only the next carry domain, without emitting a pair symbol."""
    operands = _reverse_output_operands(base, left, symbol, right)
    if operands is None:
        return CarryFn.ID
    a, c, b, d = operands
    if base == 10:
        from number_compiler.arithmetic.formula.skew_residue_laws import (
            skew_normalized_digit,
        )

        actions = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)
        x = skew_normalized_digit(actions.index(_pair_carry_action(a, 10)), a % 9, c)
        y = skew_normalized_digit(actions.index(_pair_carry_action(b, 10)), b % 9, d)
    else:
        x, y = _normalized_digit(a, c, base), _normalized_digit(b, d, base)
    threshold = base - 1 - y
    return (
        CarryFn.ID
        if x == threshold
        else CarryFn.CONST1
        if x > threshold
        else CarryFn.CONST0
    )


class BaseBlockEffect:
    """One exact padded pair-to-pair reverse-add transition."""

    __slots__ = (
        "_initial",
        "_sealed",
        "base",
        "blank",
        "blank_left_tail",
        "blank_right_tail",
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

    def __init__(self, base: int) -> None:
        if type(base) is not int:
            raise TypeError("kernel base must be an exact integer")
        if base < 2:
            raise ValueError(base)
        self.base = base
        self.blank = 2 * base - 1  # active pair coefficients are 0..2b-2
        self.exponent = 1
        self.node_id = next(_OPERATOR_IDS)
        self._initial = (
            _BaseLeftState(0, -1, False, False),
            _BaseRightState(CarryFn.ID, CarryFn.ID),
        )
        # For the padding blank, one left transition sets blank_seen and the
        # right transition is already the identity.  Any blank-fixed left/right
        # contexts emit blank.
        self.blank_left_tail = 1
        self.blank_right_tail = 0
        self.stable_blank_output = True
        self.supports_predecessor_trace = False
        self._sealed = True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("base_block", int(self.base))

    def initial(self, side: BoundarySide) -> BoundaryState:
        if type(side) is not BoundarySide:
            raise TypeError("kernel side must be BoundarySide")
        return self._initial[side]

    def advance(
        self, side: BoundarySide, state: BoundaryState, symbol: int
    ) -> BoundaryState:
        if type(side) is not BoundarySide:
            raise TypeError("kernel side must be BoundarySide")
        require_integer(symbol, "kernel symbol", 0, self.blank)
        if side is BoundarySide.LEFT:
            if type(state) is not _BaseLeftState:
                raise TypeError("kernel state has another boundary sort")
            return self._advance_left(state, symbol)
        if type(state) is not _BaseRightState:
            raise TypeError("kernel state has another boundary sort")
        return self._advance_right(state, symbol)

    def _advance_left(self, state: _BaseLeftState, symbol: int) -> _BaseLeftState:
        if state.sink:
            out = state
        elif symbol == self.blank:
            out = _BaseLeftState(state.carry, state.previous_pair, True, False)
        elif state.blank_seen:
            out = _BaseLeftState(0, -1, True, True)
        else:
            out = _BaseLeftState(
                apply_carry_fn(_pair_carry_action(symbol, self.base), state.carry),
                symbol,
                False,
                False,
            )
        return out

    def _advance_right(self, state: _BaseRightState, symbol: int) -> _BaseRightState:
        if symbol == self.blank:
            out = state
        else:
            phi = _pair_carry_action(symbol, self.base)
            out = _BaseRightState(
                compose_carry_fn(state.forward_suffix, phi),
                compose_carry_fn(phi, state.backward_suffix),
            )
        return out

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        return None

    def boundary_universe(
        self, side: BoundarySide, *, max_states: int | None = None
    ) -> tuple[BoundaryState, ...] | None:
        """Return the primitive domain in its certified breadth-first order.

        A left state keeps one previous pair, one carry and blank/sink flags.
        The right scan has five reachable reset pairs. Their closed form avoids
        rediscovering the same immutable alphabet by O(base**2) transitions for
        each independent index; it does not cache an execution or future field.
        """
        if type(side) is not BoundarySide:
            raise TypeError("kernel side must be BoundarySide")
        count = 4 * self.base + 3 if side is BoundarySide.LEFT else 5
        if max_states is not None:
            require_integer(max_states, "max_states", 0)
            if count > max_states:
                return None
        if side is BoundarySide.RIGHT:
            return tuple(
                _BaseRightState(first, second)
                for first, second in (
                    (CarryFn.ID, CarryFn.ID),
                    (CarryFn.CONST0, CarryFn.CONST0),
                    (CarryFn.CONST1, CarryFn.CONST1),
                    (CarryFn.CONST0, CarryFn.CONST1),
                    (CarryFn.CONST1, CarryFn.CONST0),
                )
            )
        base = self.base
        return (
            _BaseLeftState(0, -1, False),
            *(_BaseLeftState(0, value, False) for value in range(base)),
            *(_BaseLeftState(1, value, False) for value in range(base, 2 * base - 1)),
            _BaseLeftState(0, -1, True),
            *(_BaseLeftState(0, value, True) for value in range(base)),
            _BaseLeftState(1, base - 1, False),
            *(_BaseLeftState(1, value, True) for value in range(base, 2 * base - 1)),
            _BaseLeftState(0, -1, True, True),
            _BaseLeftState(1, base - 1, True),
        )

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        require_integer(symbol, "kernel symbol", 0, self.blank)
        if type(left) is not _BaseLeftState or type(right) is not _BaseRightState:
            raise TypeError((type(left), type(right)))
        operands = _reverse_output_operands(self.base, left, symbol, right)
        out = (
            self.blank
            if operands is None
            else _normalized_pair_sum(*operands, self.base)
        )
        if out != self.blank and not 0 <= out <= 2 * (self.base - 1):
            raise AssertionError((out, self.base, left, symbol, right))
        return out

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        transition_cache_entries = 0 + 0
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


# ---------------------------------------------------------------------------
# Pre-minimized exact finite powered kernels
# ---------------------------------------------------------------------------


class FiniteBlockEffect:
    """Canonical finite quotient of a powered block effect.

    State integers are proved semantic equivalence classes, not construction
    histories.  The retained decimal T^2 kernel is deterministically generated
    from :class:`BaseBlockEffect` and minimized by exact output behavior plus
    transition refinement.
    """

    __slots__ = (
        "_initial",
        "_sealed",
        "_semantic_identity",
        "alphabet_size",
        "base",
        "blank",
        "blank_left_tail",
        "blank_right_tail",
        "exponent",
        "kernel_name",
        "left_count",
        "left_transitions",
        "node_id",
        "outputs",
        "right_count",
        "right_transitions",
        "semantic_digest",
        "stable_blank_output",
        "storage_bytes",
        "supports_predecessor_trace",
        "uncompressed_bytes",
    )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("finite kernels are immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("immutable definition attributes cannot be deleted")

    def __init__(
        self,
        *,
        base: int,
        exponent: int,
        left_count: int,
        right_count: int,
        alphabet_size: int,
        initial_left: int,
        initial_right: int,
        left_transitions: array[int],
        right_transitions: array[int],
        outputs: bytes,
        kernel_name: str,
        storage_bytes: int,
        uncompressed_bytes: int,
        blank_left_tail: int,
        blank_right_tail: int,
        stable_blank_output: bool,
        blank: int | None = None,
    ) -> None:
        # Admit all metadata before copying tables or issuing an identity.
        for name, value, minimum in (
            ("base", base, 2),
            ("exponent", exponent, 1),
            ("left_count", left_count, 1),
            ("right_count", right_count, 1),
            ("alphabet_size", alphabet_size, 1),
            ("initial_left", initial_left, 0),
            ("initial_right", initial_right, 0),
            ("storage_bytes", storage_bytes, 0),
            ("uncompressed_bytes", uncompressed_bytes, 0),
            ("blank_left_tail", blank_left_tail, 0),
            ("blank_right_tail", blank_right_tail, 0),
        ):
            require_integer(value, name, minimum)
        if blank is not None:
            require_integer(blank, "blank", 0)
        resolved_blank = 2 * base - 1 if blank is None else blank
        if alphabet_size != resolved_blank + 1:
            raise ValueError((alphabet_size, resolved_blank + 1))
        if type(stable_blank_output) is not bool:
            raise TypeError("stable_blank_output must be Boolean")
        if type(kernel_name) is not str:
            raise TypeError("kernel_name must be a string")
        if not isinstance(outputs, (bytes, bytearray, memoryview)):
            raise TypeError("finite outputs require a byte buffer")
        self.base = base
        self.blank = resolved_blank
        self.exponent = exponent
        self.node_id = next(_OPERATOR_IDS)
        self.left_count = left_count
        self.right_count = right_count
        self.alphabet_size = alphabet_size
        self._initial = (initial_left, initial_right)
        self.left_transitions = tuple(left_transitions)
        self.right_transitions = tuple(right_transitions)
        if any(
            type(state) is not int
            for state in (
                *self.left_transitions,
                *self.right_transitions,
            )
        ):
            raise TypeError("finite transitions require exact integer states")
        self.outputs = bytes(outputs)
        self.kernel_name = kernel_name
        self.storage_bytes = storage_bytes
        self.uncompressed_bytes = uncompressed_bytes
        self.blank_left_tail = blank_left_tail
        self.blank_right_tail = blank_right_tail
        self.stable_blank_output = stable_blank_output
        self.supports_predecessor_trace = False
        if len(self.left_transitions) != self.left_count * self.alphabet_size:
            raise ValueError("finite left transition table has wrong size")
        if len(self.right_transitions) != self.right_count * self.alphabet_size:
            raise ValueError("finite right transition table has wrong size")
        if len(self.outputs) != self.left_count * self.alphabet_size * self.right_count:
            raise ValueError("finite output table has wrong size")

        if (
            not 0 <= self._initial[0] < self.left_count
            or not 0 <= self._initial[1] < self.right_count
        ):
            raise ValueError("finite initial state outside its domain")
        if any(not 0 <= state < self.left_count for state in self.left_transitions):
            raise ValueError("finite left transition outside its domain")
        if any(not 0 <= state < self.right_count for state in self.right_transitions):
            raise ValueError("finite right transition outside its domain")
        if any(symbol >= self.alphabet_size for symbol in self.outputs):
            raise ValueError("finite output outside its alphabet")
        behavior = (
            "finite-kernel-v2",
            self.base,
            self.blank,
            self.exponent,
            self.left_count,
            self.right_count,
            self.alphabet_size,
            self._initial,
            self.blank_left_tail,
            self.blank_right_tail,
            self.stable_blank_output,
            self.left_transitions,
            self.right_transitions,
            self.outputs.hex(),
        )
        self.semantic_digest = hashlib.sha256(
            json.dumps(behavior, separators=(",", ":")).encode("ascii")
        ).hexdigest()
        self._semantic_identity = SemanticIdentity(self.semantic_digest, behavior)
        self._sealed = True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("finite-block-v3", self._semantic_identity)

    @staticmethod
    def _validate_side(side: BoundarySide) -> None:
        if type(side) is not BoundarySide:
            raise TypeError("finite kernel side must be BoundarySide")

    def initial(self, side: BoundarySide) -> int:
        self._validate_side(side)
        return self._initial[side]

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        self._validate_side(side)
        count = self.left_count if side is BoundarySide.LEFT else self.right_count
        index = require_integer(state, "finite boundary state", 0, count - 1)
        require_integer(symbol, "finite symbol", 0, self.alphabet_size - 1)
        table = (
            self.left_transitions
            if side is BoundarySide.LEFT
            else self.right_transitions
        )
        return table[index * self.alphabet_size + symbol]

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        self._validate_side(side)
        count = self.left_count if side is BoundarySide.LEFT else self.right_count
        require_integer(state, "finite boundary state", 0, count - 1)

    def boundary_universe(
        self, side: BoundarySide, *, max_states: int | None = None
    ) -> tuple[int, ...] | None:
        self._validate_side(side)
        count = self.left_count if side is BoundarySide.LEFT else self.right_count
        if max_states is not None:
            require_integer(max_states, "max_states", 0)
            if count > max_states:
                return None
        return tuple(range(count))

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        low = require_integer(left, "finite left state", 0, self.left_count - 1)
        high = require_integer(right, "finite right state", 0, self.right_count - 1)
        require_integer(symbol, "finite symbol", 0, self.alphabet_size - 1)
        return self.outputs[
            (low * self.alphabet_size + symbol) * self.right_count + high
        ]

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
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
            "finite_kernel_left_states": self.left_count,
            "finite_kernel_right_states": self.right_count,
            "finite_kernel_storage_bytes": self.storage_bytes,
            "leaf_effect_transition_cache_entries": 0,
            "leaf_effect_output_cache_entries": 0,
            "leaf_effect_cache_entries": 0,
        }


_BASE10_T2_SHA256 = "35276802973d716c642cb1e78dfa7ee395ba60798bc3014cfc57da10e1927e61"
_BASE10_T2_HEADER = struct.Struct("<6sBBHHHH")


@lru_cache(maxsize=1)
def _load_base10_t2_kernel() -> FiniteBlockEffect:
    path = Path(str(files("number_compiler"))) / "kernels" / "base10_t2_kernel.zlib"
    packed = path.read_bytes()
    digest = hashlib.sha256(packed).hexdigest()
    if digest != _BASE10_T2_SHA256:
        raise RuntimeError(f"base-10 T^2 block-effect kernel digest mismatch: {digest}")
    raw = zlib.decompress(packed)
    header_size = _BASE10_T2_HEADER.size
    magic, base, alphabet, left_count, right_count, initial_left, initial_right = (
        _BASE10_T2_HEADER.unpack_from(raw, 0)
    )
    if magic != b"RAT2K1" or base != 10 or alphabet != 20:
        raise RuntimeError("invalid base-10 T^2 block-effect kernel header")
    offset = header_size
    left_items = left_count * alphabet
    right_items = right_count * alphabet
    left_bytes = 2 * left_items
    right_bytes = 2 * right_items
    left_transitions = array("H")
    left_transitions.frombytes(raw[offset : offset + left_bytes])
    offset += left_bytes
    right_transitions = array("H")
    right_transitions.frombytes(raw[offset : offset + right_bytes])
    offset += right_bytes
    if sys.byteorder != "little":
        left_transitions.byteswap()
        right_transitions.byteswap()
    outputs = bytes(raw[offset:])
    return FiniteBlockEffect(
        base=base,
        exponent=2,
        left_count=left_count,
        right_count=right_count,
        alphabet_size=alphabet,
        initial_left=initial_left,
        initial_right=initial_right,
        left_transitions=left_transitions,
        right_transitions=right_transitions,
        outputs=outputs,
        kernel_name="base10_t2_minimized_757x179",
        storage_bytes=len(packed),
        uncompressed_bytes=len(raw),
        blank_left_tail=2,
        blank_right_tail=1,
        stable_blank_output=True,
    )


__all__ = ["BaseBlockEffect", "FiniteBlockEffect"]
