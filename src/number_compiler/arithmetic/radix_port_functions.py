"""Closed bounded arithmetic functions for an MSD-first division carry port.

These functions summarize the input of a division cell. They retain neither a
quotient word nor a per-position function table. Composition works directly on
modular-affine coefficients and an activation threshold, without bit blasting.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
)
from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class DivisionCarry:
    """r -> (a*r+b mod radix); active -> active OR r>=threshold."""

    transfer: RadixRemainderTransfer
    threshold: int

    def __post_init__(self) -> None:
        if type(self.transfer) is not RadixRemainderTransfer:
            raise TypeError("division carry requires canonical modular coefficients")
        self.transfer.__post_init__()
        if (
            type(self.threshold) is not int
            or not 0 <= self.threshold <= self.transfer.radix
        ):
            raise ValueError(
                "division activation threshold is outside its carry domain"
            )
        # Below this threshold the underlying scan has emitted no quotient
        # bit, so its affine remainder must not have wrapped. This invariant
        # makes threshold substitution closed without a piecewise carry tape.
        if self.threshold > 1:
            multiplier = self.transfer.multiplier
            if (
                multiplier == 0
                or self.threshold
                != (self.transfer.radix - self.transfer.offset + multiplier - 1)
                // multiplier
            ):
                raise ValueError(
                    "division carry has an uncertified activation threshold"
                )

    @classmethod
    def identity(cls, radix: int) -> DivisionCarry:
        return cls(RadixRemainderTransfer(radix, 1, 0), radix)

    @classmethod
    def leaf(cls, radix: int, symbol: int) -> DivisionCarry:
        transfer = RadixRemainderTransfer.leaf(radix, symbol)
        return cls(transfer, radix if symbol == 2 else (radix - symbol + 1) // 2)

    def preimage(self, threshold: int, ledger: ResourceLedger) -> int:
        """Threshold after this scan, accounting for a prior carry reset.

        Below our activation threshold there was no modular wrap. If that
        threshold exceeds one, the multiplier itself is the unreduced power
        of two. With threshold one only incoming zero remains undecided.
        """
        if type(threshold) is not int or not 0 <= threshold <= self.transfer.radix:
            raise ValueError("division threshold input is outside its finite domain")
        if self.threshold == 0 or self.transfer.offset >= threshold:
            return 0
        if self.threshold == 1:
            return 1
        multiplier = self.transfer.multiplier
        if not multiplier:
            raise ValueError("unreachable division carry threshold/multiplier pair")
        delta = ledger.observe_arithmetic(threshold - self.transfer.offset)
        numerator = ledger.observe_arithmetic(delta + multiplier - 1)
        return min(self.threshold, ledger.observe_arithmetic(numerator // multiplier))

    def then(self, after: DivisionCarry, ledger: ResourceLedger) -> DivisionCarry:
        self.__post_init__()
        after.__post_init__()
        result = DivisionCarry(
            self.transfer.then(after.transfer, ledger),
            self.preimage(after.threshold, ledger),
        )
        ledger.bump("tile_radix_affine_compositions")
        return result

    def apply(self, state: int, ledger: ResourceLedger) -> int:
        if type(state) is not int or not 0 <= state < 2 * self.transfer.radix:
            raise ValueError("division carry input is outside its finite domain")
        remainder, active = divmod(state, 2)
        return ledger.observe_arithmetic(
            2 * self.transfer.apply(remainder, ledger)
            + int(bool(active or remainder >= self.threshold))
        )


@dataclass(frozen=True, slots=True)
class RadixPortFunction:
    """A complete typed numeric-port function, not a deferred continuation.

    Constant, activation and output functions are observations of one closed
    carry action. A spatial substitution collapses immediately to another
    fixed-size record; records cannot reference other records recursively.
    """

    signature: FunctionSignature
    radix: int
    kind: Literal["constant", "carry", "active", "inactive", "output"]
    carry: DivisionCarry | None = None
    value: int = 0
    threshold: int | None = None

    def __post_init__(self) -> None:
        if type(self.radix) is not int or not 2 <= self.radix <= 1 << 63:
            raise ValueError("radix function requires a bounded exact radix")
        if type(self.signature) is not FunctionSignature:
            raise TypeError("radix function requires a semantic signature")
        inputs = self.signature.inputs
        if len(inputs) != 2 or tuple(port.cardinality for port in inputs) != (
            1,
            2 * self.radix,
        ):
            raise ValueError("radix function has another finite input domain")
        if type(self.signature.output) is not AtomSort or type(self.value) is not int:
            raise ValueError("radix function has another result sort")
        if self.kind == "constant":
            if (
                self.carry is not None
                or self.threshold is not None
                or not 0 <= self.value < self.signature.output.cardinality
            ):
                raise ValueError("invalid constant radix function")
            return
        if self.kind in ("active", "inactive"):
            if (
                self.carry is not None
                or self.value != 0
                or type(self.threshold) is not int
                or not 0 <= self.threshold <= self.radix
                or self.signature.output.cardinality != 2
            ):
                raise ValueError("activation requires a canonical threshold predicate")
            return
        if (
            type(self.carry) is not DivisionCarry
            or self.carry.transfer.radix != self.radix
            or self.threshold is not None
        ):
            raise ValueError("radix function has another carry action")
        self.carry.__post_init__()
        expected = {"carry": 2 * self.radix, "output": 3}
        if (
            self.kind not in expected
            or self.signature.output.cardinality != expected[self.kind]
        ):
            raise ValueError("radix function observation has another output domain")
        if self.value not in ((0, 1) if self.kind == "output" else (0,)):
            raise ValueError("radix function contains a non-kernel literal")

    def evaluate(self, ports: tuple[int, ...], ledger: ResourceLedger) -> int:
        self.__post_init__()
        if (
            len(ports) != 2
            or any(type(v) is not int for v in ports)
            or ports[0] != 0
            or not 0 <= ports[1] < 2 * self.radix
        ):
            raise ValueError("invalid concrete division ports")
        ledger.bump("tile_radix_algebraic_observations")
        if self.kind == "constant":
            return self.value
        remainder, active = divmod(ports[1], 2)
        if self.kind in ("active", "inactive"):
            assert self.threshold is not None
            result = bool(active or remainder >= self.threshold)
            return int(not result if self.kind == "inactive" else result)
        assert self.carry is not None
        state = self.carry.apply(ports[1], ledger)
        if self.kind == "carry":
            return state
        remainder, active = divmod(state, 2)
        quotient = ledger.observe_arithmetic(2 * remainder + self.value) // self.radix
        return quotient if active or quotient else 2

    def through(
        self, before: DivisionCarry, ledger: ResourceLedger
    ) -> RadixPortFunction:
        """Substitute one numeric transfer without expanding its input bits."""
        if self.kind == "constant":
            return self
        if self.kind in ("active", "inactive"):
            assert self.threshold is not None
            ledger.bump("tile_radix_activation_compositions")
            return RadixPortFunction(
                self.signature,
                self.radix,
                self.kind,
                threshold=before.preimage(self.threshold, ledger),
            )
        assert self.carry is not None
        carry = before.then(self.carry, ledger)
        return RadixPortFunction(
            self.signature, self.radix, self.kind, carry, self.value
        )


__all__ = ["DivisionCarry", "RadixPortFunction"]
