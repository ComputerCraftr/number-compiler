"""Closed bounded port functions for reverse-add pair intervals."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    _BaseLeftState,
    _BaseRightState,
    _normalized_pair_sum,
    _reverse_output_operands,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
)
from number_compiler.resources.ledger import ResourceLedger

MIN_CLOSED_REVERSE_BASE = 2
MAX_CLOSED_REVERSE_BASE = 15


@dataclass(frozen=True, slots=True)
class ReversePortCodec:
    """Canonical integer codec for the bounded BaseBlockEffect ports."""

    base: int

    def __post_init__(self) -> None:
        if (
            type(self.base) is not int
            or not MIN_CLOSED_REVERSE_BASE <= self.base <= MAX_CLOSED_REVERSE_BASE
        ):
            raise ValueError("closed reverse port functions require radix 2 through 15")

    @property
    def left_count(self) -> int:
        return 4 * self.base + 3

    @property
    def right_count(self) -> int:
        return 5

    def decode_left(self, value: int) -> _BaseLeftState:
        if type(value) is not int or not 0 <= value < self.left_count:
            raise ValueError("left reverse port lies outside its finite domain")
        base = self.base
        if value == 0:
            return _BaseLeftState(0, -1, False)
        if value <= base:
            return _BaseLeftState(0, value - 1, False)
        if value < 2 * base:
            return _BaseLeftState(1, value - 1, False)
        if value == 2 * base:
            return _BaseLeftState(0, -1, True)
        if value <= 3 * base:
            return _BaseLeftState(0, value - 2 * base - 1, True)
        if value == 3 * base + 1:
            return _BaseLeftState(1, base - 1, False)
        if value <= 4 * base:
            return _BaseLeftState(1, value - 2 * base - 2, True)
        if value == 4 * base + 1:
            return _BaseLeftState(0, -1, True, True)
        return _BaseLeftState(1, base - 1, True)

    def encode_left(self, state: _BaseLeftState) -> int:
        if type(state) is not _BaseLeftState:
            raise TypeError("left reverse port has another state sort")
        base = self.base
        if state.sink:
            if state != _BaseLeftState(0, -1, True, True):
                raise ValueError("left reverse sink is not canonical")
            return 4 * base + 1
        if not state.blank_seen:
            if state == _BaseLeftState(0, -1, False):
                return 0
            if state.carry == 0 and 0 <= state.previous_pair < base:
                return state.previous_pair + 1
            if state.carry == 1 and base <= state.previous_pair < 2 * base - 1:
                return state.previous_pair + 1
            if state == _BaseLeftState(1, base - 1, False):
                return 3 * base + 1
        else:
            if state == _BaseLeftState(0, -1, True):
                return 2 * base
            if state.carry == 0 and 0 <= state.previous_pair < base:
                return 2 * base + state.previous_pair + 1
            if state.carry == 1 and base <= state.previous_pair < 2 * base - 1:
                return 2 * base + state.previous_pair + 2
            if state == _BaseLeftState(1, base - 1, True):
                return 4 * base + 2
        raise ValueError("left reverse state is outside its reachable domain")

    def decode_right(self, value: int) -> _BaseRightState:
        states = (
            _BaseRightState(CarryFn.ID, CarryFn.ID),
            _BaseRightState(CarryFn.CONST0, CarryFn.CONST0),
            _BaseRightState(CarryFn.CONST1, CarryFn.CONST1),
            _BaseRightState(CarryFn.CONST0, CarryFn.CONST1),
            _BaseRightState(CarryFn.CONST1, CarryFn.CONST0),
        )
        if type(value) is not int or not 0 <= value < len(states):
            raise ValueError("right reverse port lies outside its finite domain")
        return states[value]

    def encode_right(self, state: _BaseRightState) -> int:
        if type(state) is not _BaseRightState:
            raise TypeError("right reverse port has another state sort")
        states = (
            (CarryFn.ID, CarryFn.ID),
            (CarryFn.CONST0, CarryFn.CONST0),
            (CarryFn.CONST1, CarryFn.CONST1),
            (CarryFn.CONST0, CarryFn.CONST1),
            (CarryFn.CONST1, CarryFn.CONST0),
        )
        try:
            return states.index((state.forward_suffix, state.backward_suffix))
        except ValueError:
            raise ValueError(
                "right reverse state is outside its reachable domain"
            ) from None

    def active_truth_bits(self, symbol: int) -> int:
        """Return the exact live-output predicate from closed port geometry.

        Every nonblank pair symbol is live for every nonsink left state.  A
        blank symbol is live only when the existing carry creates the terminal
        growth digit: the active, preblank carry-one band plus its threshold
        boundary state.  These intervals are part of this codec's canonical
        state numbering, so constructing the mask does not need to decode or
        inspect every state again.
        """
        blank = 2 * self.base - 1
        if type(symbol) is not int or not 0 <= symbol <= blank:
            raise ValueError("reverse activity symbol lies outside its alphabet")
        if symbol != blank:
            return ((1 << self.left_count) - 1) ^ (1 << (4 * self.base + 1))
        carry_one_band = ((1 << (self.base - 1)) - 1) << (self.base + 1)
        return carry_one_band | (1 << (3 * self.base + 1))


@dataclass(frozen=True, slots=True)
class ReverseLeftTransfer:
    base: int
    has_active: bool
    has_blank: bool
    sinks: bool
    carry: CarryFn
    last_symbol: int

    def __post_init__(self) -> None:
        if type(self.base) is not int or self.base < 2:
            raise ValueError("left transfer requires an exact radix")
        if any(
            type(value) is not bool
            for value in (self.has_active, self.has_blank, self.sinks)
        ):
            raise TypeError("left transfer controls require booleans")
        if type(self.carry) is not CarryFn:
            raise TypeError("left transfer requires a carry monoid action")
        if type(self.last_symbol) is not int:
            raise TypeError("left transfer edge symbol requires an exact integer")
        if self.sinks:
            if (self.has_active, self.has_blank, self.carry, self.last_symbol) != (
                True,
                True,
                CarryFn.ID,
                -1,
            ):
                raise ValueError("sink transfer is not canonical")
        elif self.has_active:
            if not 0 <= self.last_symbol <= 2 * (self.base - 1):
                raise ValueError("left transfer has another active edge symbol")
        elif self.carry is not CarryFn.ID or self.last_symbol != -1:
            raise ValueError("inactive left transfer must preserve carry and edge")

    @classmethod
    def identity(cls, base: int) -> ReverseLeftTransfer:
        return cls(base, False, False, False, CarryFn.ID, -1)

    @classmethod
    def leaf(cls, base: int, symbol: int) -> ReverseLeftTransfer:
        blank = 2 * base - 1
        if type(symbol) is not int or not 0 <= symbol <= blank:
            raise ValueError("left transfer symbol lies outside its alphabet")
        if symbol == blank:
            return cls(base, False, True, False, CarryFn.ID, -1)
        return cls(base, True, False, False, value_carry_fn(symbol, base), symbol)

    def then(
        self,
        after: ReverseLeftTransfer,
        ledger: ResourceLedger | None = None,
    ) -> ReverseLeftTransfer:
        self.__post_init__()
        after.__post_init__()
        if self.base != after.base:
            raise ValueError("left transfers use different radices")
        if self.sinks or after.sinks or (self.has_blank and after.has_active):
            return ReverseLeftTransfer(self.base, True, True, True, CarryFn.ID, -1)
        has_active = self.has_active or after.has_active
        if ledger is not None:
            ledger.bump("reverse_port_carry_compositions")
        return ReverseLeftTransfer(
            self.base,
            has_active,
            self.has_blank or after.has_blank,
            False,
            compose_carry_fn(after.carry, self.carry),
            after.last_symbol if after.has_active else self.last_symbol,
        )

    def apply(self, state: _BaseLeftState) -> _BaseLeftState:
        self.__post_init__()
        if type(state) is not _BaseLeftState:
            raise TypeError("left transfer input has another state sort")
        if state.sink:
            return state
        if self.sinks or (state.blank_seen and self.has_active):
            return _BaseLeftState(0, -1, True, True)
        if not self.has_active:
            return _BaseLeftState(
                state.carry,
                state.previous_pair,
                state.blank_seen or self.has_blank,
            )
        return _BaseLeftState(
            apply_carry_fn(self.carry, state.carry),
            self.last_symbol,
            self.has_blank,
        )

    def predicate_preimage(self, truth_bits: int) -> int:
        """Pull back a left-state predicate through this closed transfer.

        The left-state numbering consists of four carry/blank bands plus one
        sink.  A transfer either preserves those states, moves the two live
        bands into their blank copies, or collapses each carry band to one
        edge state.  Pulling a predicate back therefore needs only bounded
        mask operations and at most two representative transition checks.
        """
        self.__post_init__()
        codec = ReversePortCodec(self.base)
        limit = (1 << codec.left_count) - 1
        if type(truth_bits) is not int or truth_bits < 0 or truth_bits & ~limit:
            raise ValueError("reverse predicate exceeds its left-state domain")
        base = self.base
        nonblank_zero = (1 << (base + 1)) - 1
        nonblank_one = (
            ((1 << (base - 1)) - 1) << (base + 1)
        ) | (1 << (3 * base + 1))
        blank_zero = ((1 << (base + 1)) - 1) << (2 * base)
        blank_one = (
            ((1 << (base - 1)) - 1) << (3 * base + 2)
        ) | (1 << (4 * base + 2))
        sink = 1 << (4 * base + 1)
        sink_live = bool(truth_bits & sink)
        if self.sinks:
            return limit if sink_live else 0
        if self.has_active:
            result = (blank_zero | blank_one | sink) if sink_live else 0
            targets = (
                codec.encode_left(self.apply(codec.decode_left(0))),
                codec.encode_left(self.apply(codec.decode_left(base + 1))),
            )
            if truth_bits & (1 << targets[0]):
                result |= nonblank_zero
            if truth_bits & (1 << targets[1]):
                result |= nonblank_one
            return result
        if not self.has_blank:
            return truth_bits
        result = truth_bits & (blank_zero | blank_one | sink)
        result |= (truth_bits & blank_zero) >> (2 * base)
        regular_one = nonblank_one & ~(1 << (3 * base + 1))
        result |= ((truth_bits & blank_one) >> (2 * base + 1)) & regular_one
        if truth_bits & (1 << (4 * base + 2)):
            result |= 1 << (3 * base + 1)
        return result


@dataclass(frozen=True, slots=True)
class ReverseRightTransfer:
    base: int
    forward: CarryFn
    backward: CarryFn

    def __post_init__(self) -> None:
        if type(self.base) is not int or self.base < 2:
            raise ValueError("right transfer requires an exact radix")
        if type(self.forward) is not CarryFn or type(self.backward) is not CarryFn:
            raise TypeError("right transfer requires two carry monoid actions")

    @classmethod
    def identity(cls, base: int) -> ReverseRightTransfer:
        return cls(base, CarryFn.ID, CarryFn.ID)

    @classmethod
    def leaf(cls, base: int, symbol: int) -> ReverseRightTransfer:
        blank = 2 * base - 1
        if type(symbol) is not int or not 0 <= symbol <= blank:
            raise ValueError("right transfer symbol lies outside its alphabet")
        action = CarryFn.ID if symbol == blank else value_carry_fn(symbol, base)
        return cls(base, action, action)

    def then(
        self,
        after: ReverseRightTransfer,
        ledger: ResourceLedger | None = None,
    ) -> ReverseRightTransfer:
        self.__post_init__()
        after.__post_init__()
        if self.base != after.base:
            raise ValueError("right transfers use different radices")
        if ledger is not None:
            ledger.bump("reverse_port_carry_compositions", 2)
        return ReverseRightTransfer(
            self.base,
            compose_carry_fn(self.forward, after.forward),
            compose_carry_fn(after.backward, self.backward),
        )

    def apply(self, state: _BaseRightState) -> _BaseRightState:
        self.__post_init__()
        if type(state) is not _BaseRightState:
            raise TypeError("right transfer input has another state sort")
        return _BaseRightState(
            compose_carry_fn(state.forward_suffix, self.forward),
            compose_carry_fn(self.backward, state.backward_suffix),
        )


ReverseFunctionKind = Literal[
    "constant", "left-transfer", "right-transfer", "output", "predicate"
]


@dataclass(frozen=True, slots=True)
class ReversePortFunction:
    """One closed two-sided function with no recursive function references."""

    signature: FunctionSignature
    base: int
    kind: ReverseFunctionKind
    left: ReverseLeftTransfer | None = None
    right: ReverseRightTransfer | None = None
    symbol: int = -1
    truth_bits: int = 0
    value: int = 0

    def __post_init__(self) -> None:
        codec = ReversePortCodec(self.base)
        if type(self.signature) is not FunctionSignature:
            raise TypeError("reverse function requires a finite signature")
        self.signature.__post_init__()
        if tuple(port.cardinality for port in self.signature.inputs) != (
            codec.left_count,
            codec.right_count,
        ):
            raise ValueError("reverse function has another two-sided port domain")
        if type(self.signature.output) is not AtomSort:
            raise TypeError("reverse function requires an atomic output")
        if type(self.symbol) is not int:
            raise TypeError("reverse function edge symbol requires an exact integer")
        if (
            type(self.truth_bits) is not int
            or self.truth_bits < 0
            or type(self.value) is not int
        ):
            raise TypeError("reverse function payloads require exact integers")
        if self.kind == "constant":
            if (
                self.left is not None
                or self.right is not None
                or self.symbol != -1
                or self.truth_bits
            ):
                raise ValueError("reverse constant contains another payload")
            if not 0 <= self.value < self.signature.output.cardinality:
                raise ValueError("reverse constant lies outside its output domain")
        elif self.kind == "left-transfer":
            if type(self.left) is not ReverseLeftTransfer or any(
                (
                    self.right is not None,
                    self.symbol != -1,
                    bool(self.truth_bits),
                    bool(self.value),
                )
            ):
                raise ValueError("left transfer function contains another payload")
            self.left.__post_init__()
            if self.left.base != self.base:
                raise ValueError("left transfer function changes the radix")
            if self.signature.output.cardinality != codec.left_count:
                raise ValueError("left transfer has another output sort")
        elif self.kind == "right-transfer":
            if type(self.right) is not ReverseRightTransfer or any(
                (
                    self.left is not None,
                    self.symbol != -1,
                    bool(self.truth_bits),
                    bool(self.value),
                )
            ):
                raise ValueError("right transfer function contains another payload")
            self.right.__post_init__()
            if self.right.base != self.base:
                raise ValueError("right transfer function changes the radix")
            if self.signature.output.cardinality != codec.right_count:
                raise ValueError("right transfer has another output sort")
        elif self.kind == "output":
            if (
                type(self.left) is not ReverseLeftTransfer
                or type(self.right) is not ReverseRightTransfer
                or not 0 <= self.symbol <= 2 * self.base - 1
                or self.truth_bits
                or self.value
            ):
                raise ValueError("output function contains another payload")
            self.left.__post_init__()
            self.right.__post_init__()
            if self.left.base != self.base or self.right.base != self.base:
                raise ValueError("output function changes the radix")
            if self.signature.output.cardinality != 2 * self.base:
                raise ValueError("output function has another symbol sort")
        elif self.kind == "predicate":
            if (
                self.left is not None
                or self.right is not None
                or self.symbol != -1
                or self.value
                or self.signature.output.cardinality != 2
            ):
                raise ValueError("predicate function contains another payload")
            if self.truth_bits >> codec.left_count:
                raise ValueError("predicate exceeds its bounded port domain")
        else:
            raise ValueError("unknown reverse port function kind")

    @property
    def retained_coefficient_slots(self) -> int:
        if self.kind == "constant":
            return 1
        return (
            int(self.left is not None) * 5
            + int(self.right is not None) * 2
            + int(self.kind == "output")
        )

    @property
    def retained_limb_slots(self) -> int:
        return int(self.kind == "predicate")

    def evaluate(self, ports: tuple[int, ...], ledger: ResourceLedger) -> int:
        self.__post_init__()
        codec = ReversePortCodec(self.base)
        if type(ports) is not tuple or len(ports) != 2:
            raise ValueError("reverse observation requires two concrete ports")
        left_index, right_index = ports
        left_state = codec.decode_left(left_index)
        right_state = codec.decode_right(right_index)
        ledger.bump("reverse_port_function_observations")
        if self.kind == "constant":
            return self.value
        if self.kind == "left-transfer":
            assert self.left is not None
            return codec.encode_left(self.left.apply(left_state))
        if self.kind == "right-transfer":
            assert self.right is not None
            return codec.encode_right(self.right.apply(right_state))
        if self.kind == "predicate":
            return (self.truth_bits >> left_index) & 1
        assert self.left is not None and self.right is not None
        ledger.bump("reverse_port_primitive_output_evaluations")
        return _emit(
            self.base,
            self.left.apply(left_state),
            self.symbol,
            self.right.apply(right_state),
        )

    def through(
        self,
        left: ReverseLeftTransfer,
        right: ReverseRightTransfer,
        ledger: ResourceLedger,
    ) -> ReversePortFunction:
        """Substitute two bounded transfers and immediately close the result."""
        self.__post_init__()
        if left.base != self.base or right.base != self.base:
            raise ValueError("reverse substitution changes the radix")
        ledger.bump("reverse_port_function_compositions")
        if self.kind == "constant":
            return self
        if self.kind == "left-transfer":
            assert self.left is not None
            return ReversePortFunction(
                self.signature,
                self.base,
                self.kind,
                left=left.then(self.left, ledger),
            )
        if self.kind == "right-transfer":
            assert self.right is not None
            return ReversePortFunction(
                self.signature,
                self.base,
                self.kind,
                right=right.then(self.right, ledger),
            )
        if self.kind == "output":
            assert self.left is not None and self.right is not None
            return ReversePortFunction(
                self.signature,
                self.base,
                self.kind,
                left.then(self.left, ledger),
                right.then(self.right, ledger),
                self.symbol,
            )
        if left.has_active and not left.sinks:
            # The closed-form pullback distinguishes only the two incoming
            # carry bands.  Keep those representative state observations in
            # the existing work counter instead of making them disappear.
            ledger.bump("reverse_port_predicate_state_evaluations", 2)
        return ReversePortFunction(
            self.signature,
            self.base,
            "predicate",
            truth_bits=left.predicate_preimage(self.truth_bits),
        )

    def predicate_or(
        self, other: ReversePortFunction, ledger: ResourceLedger
    ) -> ReversePortFunction:
        self.__post_init__()
        other.__post_init__()
        if (
            self.kind != "predicate"
            or other.kind != "predicate"
            or self.signature != other.signature
            or self.base != other.base
        ):
            raise ValueError("reverse disjunction requires matching predicates")
        ledger.bump("reverse_port_function_compositions")
        return ReversePortFunction(
            self.signature,
            self.base,
            "predicate",
            truth_bits=self.truth_bits | other.truth_bits,
        )

    def predicate_not(self) -> ReversePortFunction:
        self.__post_init__()
        if self.kind != "predicate":
            raise ValueError("reverse negation requires a predicate")
        mask = (1 << ReversePortCodec(self.base).left_count) - 1
        return ReversePortFunction(
            self.signature,
            self.base,
            "predicate",
            truth_bits=(~self.truth_bits) & mask,
        )


def _emit(
    base: int,
    left: _BaseLeftState,
    symbol: int,
    right: _BaseRightState,
) -> int:
    operands = _reverse_output_operands(base, left, symbol, right)
    return 2 * base - 1 if operands is None else _normalized_pair_sum(*operands, base)


__all__ = [
    "MAX_CLOSED_REVERSE_BASE",
    "MIN_CLOSED_REVERSE_BASE",
    "ReverseLeftTransfer",
    "ReversePortCodec",
    "ReversePortFunction",
    "ReverseRightTransfer",
]
