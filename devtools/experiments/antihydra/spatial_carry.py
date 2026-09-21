"""Exact spatial multiplier quotients and checked repeated-block compression.

This research module concerns a fixed radix block repeated in *space*.  It is
not a temporal Mahler successor quotient and it does not discover event
exponents.  A carry action retains every incoming port.  Repetition is
compressed only after the concrete incoming carry reaches a checked fixed
point; the remaining emitted blocks are then identical by direct arithmetic.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class MultiplierCarryAction:
    """Exact quotient/remainder map on carries ``0 .. multiplier-1``."""

    multiplier: int
    block_modulus: int
    quotient: int
    remainder: int

    def __post_init__(self) -> None:
        if type(self.multiplier) is not int or self.multiplier < 1:
            raise ValueError("positive multiplier required")
        if type(self.block_modulus) is not int or self.block_modulus < 2:
            raise ValueError("block modulus must be at least two")
        if type(self.quotient) is not int or not 0 <= self.quotient < self.multiplier:
            raise ValueError("carry quotient is outside its ports")
        if (
            type(self.remainder) is not int
            or not 0 <= self.remainder < self.block_modulus
        ):
            raise ValueError("carry remainder is outside the block")
        if (
            self.quotient + (self.remainder + self.multiplier - 1) // self.block_modulus
            >= self.multiplier
        ):
            raise ValueError("carry action exceeds its output ports")

    def apply(self, incoming: int) -> int:
        if type(incoming) is not int or not 0 <= incoming < self.multiplier:
            raise ValueError("incoming carry is outside the multiplier ports")
        return self.quotient + (self.remainder + incoming) // self.block_modulus

    def emit(self, incoming: int) -> int:
        """Exact normalized output block for this incoming carry."""
        self.apply(incoming)  # Validate the port through the same contract.
        return (self.remainder + incoming) % self.block_modulus

    def then(self, high: MultiplierCarryAction) -> MultiplierCarryAction:
        """Compose adjacent low/high spatial blocks in carry order."""
        if self.multiplier != high.multiplier:
            raise ValueError("spatial carry multipliers disagree")
        low_total = self.quotient * self.block_modulus + self.remainder
        high_total = high.quotient * high.block_modulus + high.remainder
        modulus = self.block_modulus * high.block_modulus
        quotient, remainder = divmod(
            low_total + self.block_modulus * high_total, modulus
        )
        result = MultiplierCarryAction(self.multiplier, modulus, quotient, remainder)
        for incoming in (0, self.multiplier - 1):
            if result.apply(incoming) != high.apply(self.apply(incoming)):
                raise ArithmeticError("spatial carry composition lost its ports")
        return result


def block_carry_action(
    multiplier: int, block_modulus: int, block_value: int
) -> MultiplierCarryAction:
    """Return ``c -> floor((multiplier*block_value+c)/block_modulus)``."""
    if type(block_modulus) is not int or block_modulus < 2:
        raise ValueError("block modulus must be at least two")
    if type(block_value) is not int or not 0 <= block_value < block_modulus:
        raise ValueError("block value is outside its radix extent")
    if type(multiplier) is not int or multiplier < 1:
        raise ValueError("positive multiplier required")
    total = multiplier * block_value
    quotient, remainder = divmod(total, block_modulus)
    return MultiplierCarryAction(multiplier, block_modulus, quotient, remainder)


@dataclass(frozen=True, slots=True)
class CompressedSpatialRepeat:
    """Finite transient followed by an exact repeated emitted block."""

    transient: tuple[int, ...]
    repeated_block: int | None
    repeated_count: int
    outgoing_carry: int
    checked_steps: int


def _candidate_bound(multiplier: int, block_modulus: int) -> int:
    """Candidate contraction horizon; every use is checked before publication."""
    power, count = 1, 0
    while power < multiplier:
        power *= block_modulus
        count += 1
    return count + 1


def compress_repeated_block(
    multiplier: int,
    block_modulus: int,
    block_value: int,
    incoming: int,
    repetitions: int,
    ledger: ResourceLedger | None = None,
) -> CompressedSpatialRepeat:
    """Compress identical spatial blocks after a verified carry fixed point.

    The small contraction horizon is treated as a candidate and checked on the
    supplied action and incoming port.  If that check ever fails, publication
    fails rather than assuming the bound.  Work is independent of
    ``repetitions`` after the fixed point is established.
    """
    if type(repetitions) is not int or repetitions < 0:
        raise ValueError("nonnegative repetition count required")
    action = block_carry_action(multiplier, block_modulus, block_value)
    action.apply(incoming)  # Validate the incoming port even for zero repeats.
    bound = _candidate_bound(multiplier, block_modulus)
    carry, transient, remaining = incoming, [], repetitions
    checked = 0
    while remaining and action.apply(carry) != carry:
        if checked >= bound:
            raise ArithmeticError("spatial carry did not reach its checked fixed point")
        transient.append(action.emit(carry))
        carry = action.apply(carry)
        remaining -= 1
        checked += 1
        if ledger is not None:
            ledger.bump("mahler_spatial_transient_steps")
    repeated = None
    if remaining:
        if action.apply(carry) != carry:
            raise ArithmeticError("unchecked spatial repetition")
        repeated = action.emit(carry)
        total = action.quotient * block_modulus + action.remainder
        if total + carry != repeated + block_modulus * carry:
            raise ArithmeticError("fixed carry does not reproduce the emitted block")
        if ledger is not None:
            ledger.bump("mahler_spatial_fixed_repetitions", remaining)
    if ledger is not None:
        ledger.bump(
            "mahler_spatial_operand_bits",
            multiplier.bit_length()
            + block_modulus.bit_length()
            + block_value.bit_length()
            + repetitions.bit_length(),
        )
    return CompressedSpatialRepeat(
        tuple(transient), repeated, remaining, carry, checked
    )


__all__ = [
    "CompressedSpatialRepeat",
    "MultiplierCarryAction",
    "block_carry_action",
    "compress_repeated_block",
]
