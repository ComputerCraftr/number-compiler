"""Explicit raw special-number specialization and bounded-jump references."""

from __future__ import annotations

from dataclasses import dataclass

from devtools.proofs.oracles.special_binary_jump import (
    SpecialBinaryJumpApplication,
    build_fermat_binary_jump,
    build_mersenne_binary_jump,
)
from devtools.proofs.special_power_monoid import SpecialPowerProgram


@dataclass(frozen=True, slots=True)
class SpecialPowerApplication:
    family: str
    parameter: int
    steps: int
    source: int
    value: int
    target: bool
    nonlinear_squarings: int

    @property
    def reference_only(self) -> bool:
        return True


def _modulus(program: SpecialPowerProgram) -> int:
    if program.family == "fermat":
        width = 1 << program.parameter
        return (1 << width) + 1
    return (1 << program.parameter) - 1


def apply_special_power_reference(
    program: SpecialPowerProgram,
    source: int | None = None,
) -> SpecialPowerApplication:
    modulus = _modulus(program)
    value = (3 if program.family == "fermat" else 4) if source is None else int(source)
    value %= modulus
    original = value
    if program.family == "fermat":
        value = program.operator.apply_multiplicative(value, modulus)
        target = value == modulus - 1
    else:
        value = program.operator.apply_trace(value, modulus)
        target = value == 0
    return SpecialPowerApplication(
        program.family,
        program.parameter,
        program.steps,
        original,
        value,
        target,
        program.steps,
    )


def bounded_binary_target_jump(
    program: SpecialPowerProgram,
) -> SpecialBinaryJumpApplication:
    jump = (
        build_fermat_binary_jump(program.parameter)
        if program.family == "fermat"
        else build_mersenne_binary_jump(program.parameter)
    )
    return jump.apply(program.steps)


__all__ = [
    "SpecialPowerApplication",
    "apply_special_power_reference",
    "bounded_binary_target_jump",
]
