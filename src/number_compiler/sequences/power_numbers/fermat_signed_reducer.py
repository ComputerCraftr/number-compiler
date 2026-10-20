"""Bounded signed end-around folding for the Fermat modulus ``2**w + 1``.

This is a spatial integer reducer. It accepts a caller-supplied integer and
does not construct a three-power source, evaluate a candidate-modulus square,
or issue primality evidence.
"""

from __future__ import annotations

from dataclasses import dataclass

MAX_FERMAT_FOLD_WIDTH = 65_536
MAX_FERMAT_FOLD_INPUT_BITS = 262_144


def validate(width: int, value: int | None = None) -> None:
    if type(width) is not int or not 1 <= width <= MAX_FERMAT_FOLD_WIDTH:
        raise ValueError(("fermat-fold-width-budget", width, MAX_FERMAT_FOLD_WIDTH))
    if value is not None and (
        type(value) is not int or value.bit_length() > MAX_FERMAT_FOLD_INPUT_BITS
    ):
        raise ValueError(("fermat-fold-input-bit-budget", MAX_FERMAT_FOLD_INPUT_BITS))


@dataclass(frozen=True, slots=True)
class FermatSignedFoldStep:
    """One exactly checkable integer fold preserving the Fermat congruence."""

    signed_input: int
    low: int
    high: int
    signed_output: int

    def verify(self, width: int) -> None:
        validate(width, self.signed_input)
        if any(
            type(value) is not int
            for value in (self.low, self.high, self.signed_output)
        ):
            raise TypeError("signed fold proof fields must be exact integers")
        block = 1 << width
        magnitude = abs(self.signed_input)
        if self.low != (magnitude & (block - 1)) or self.high != magnitude >> width:
            raise ArithmeticError("invalid signed fold decomposition")
        direction = -1 if self.signed_input < 0 else 1
        if self.signed_output != direction * (self.low - self.high):
            raise ArithmeticError("invalid signed fold output")
        if self.signed_input - self.signed_output != direction * self.high * (
            block + 1
        ):
            raise ArithmeticError("fold does not preserve the Fermat congruence")


@dataclass(frozen=True, slots=True)
class FermatSignedFoldResult:
    """Replayable arithmetic reduction certificate for an explicit integer."""

    width: int
    canonical: int
    steps: tuple[FermatSignedFoldStep, ...]
    input_value: int

    def verify(self) -> None:
        validate(self.width, self.input_value)
        if type(self.steps) is not tuple or any(
            type(step) is not FermatSignedFoldStep for step in self.steps
        ):
            raise TypeError("fold proof steps must be exact signed-fold records")
        block = 1 << self.width
        if type(self.canonical) is not int or not 0 <= self.canonical <= block:
            raise ArithmeticError("noncanonical Fermat remainder")
        current = self.input_value
        for step in self.steps:
            if step.signed_input != current:
                raise ArithmeticError("fold proof has a disconnected step")
            step.verify(self.width)
            current = step.signed_output
        if current < 0:
            current += block + 1
        if current != self.canonical:
            raise ArithmeticError("fold proof has the wrong canonical output")


def _fold(
    value: int, width: int, *, prove: bool
) -> tuple[int, tuple[FermatSignedFoldStep, ...]]:
    validate(width, value)
    block = 1 << width
    mask = block - 1
    signed = value
    steps: list[FermatSignedFoldStep] = []
    while signed < -block or signed > block:
        direction = -1 if signed < 0 else 1
        magnitude = abs(signed)
        low = magnitude & mask
        high = magnitude >> width
        folded = direction * (low - high)
        if prove:
            steps.append(FermatSignedFoldStep(signed, low, high, folded))
        signed = folded
    if signed < 0:
        signed += block + 1
    return signed, tuple(steps)


def fold_signed_fermat(value: int, width: int) -> int:
    """Return the exact canonical residue using bounded shifts and masks."""
    return _fold(value, width, prove=False)[0]


def certify_signed_fermat_fold(value: int, width: int) -> FermatSignedFoldResult:
    """Certify reduction of an explicit integer, not its source provenance."""
    canonical, steps = _fold(value, width, prove=True)
    result = FermatSignedFoldResult(width, canonical, steps, value)
    result.verify()
    return result


__all__ = [
    "MAX_FERMAT_FOLD_INPUT_BITS",
    "MAX_FERMAT_FOLD_WIDTH",
    "FermatSignedFoldResult",
    "FermatSignedFoldStep",
    "certify_signed_fermat_fold",
    "fold_signed_fermat",
]
