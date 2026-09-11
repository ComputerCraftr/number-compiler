"""Proof views of the shared Fermat/Mersenne quadratic temporal morphism.

This proof module constructs and powers only the symbolic temporal
operator.  It deliberately has **no raw residue specialization method** and no
bounded carrier-jump method: recurrence-equivalent execution and exhaustive
finite carriers live under :mod:`devtools.proofs.oracles`.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
from number_compiler.arithmetic.fields.radix import bit_width

_FAMILIES = frozenset({"fermat", "mersenne"})


@dataclass(frozen=True, slots=True)
class SpecialPowerProgram:
    """Family metadata wrapped around one shared quadratic temporal operator."""

    family: str
    parameter: int
    operator: QuadraticPower
    construction_compositions: int

    def __post_init__(self) -> None:
        family = str(self.family)
        parameter = int(self.parameter)
        compositions = int(self.construction_compositions)
        if family not in _FAMILIES or parameter < 0 or compositions < 0:
            raise ValueError((family, parameter, compositions))
        if family == "mersenne" and parameter < 2:
            raise ValueError((family, parameter))
        if not isinstance(self.operator, QuadraticPower):
            raise TypeError(type(self.operator))
        object.__setattr__(self, "family", family)
        object.__setattr__(self, "parameter", parameter)
        object.__setattr__(self, "construction_compositions", compositions)

    @property
    def steps(self) -> int:
        return self.operator.depth

    @property
    def fast_raw_exact(self) -> bool:
        # Binary composition of the semantic operator is fast; specializing a
        # raw residue is intentionally not part of the production surface.
        return False

    @property
    def raw_specialization_lower_bound(self) -> int:
        return self.steps

    @property
    def operator_description_bits(self) -> int:
        return bit_width(self.steps) + bit_width(self.parameter) + 1

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("special-power-program", self.family, self.parameter, self.steps)

    def prime_domain_image_classes(self) -> int:
        """Closed image-rank theorem on an independently established prime domain."""
        if self.family == "fermat":
            height = 1 << self.parameter
            remaining = max(0, height - self.steps)
            return 1 + (1 << remaining)
        remaining = max(0, self.parameter - self.steps)
        if remaining == 0:
            return 1
        return (1 << (remaining - 1)) + 1

    def prime_domain_image_payload_bits(self) -> int:
        return bit_width(self.prime_domain_image_classes() - 1)


def build_special_power_program(
    family: str, parameter: int, steps: int
) -> SpecialPowerProgram:
    """Build ``T**steps`` through the repository-wide quadratic power object."""
    family = str(family)
    parameter = int(parameter)
    steps = int(steps)
    if family not in _FAMILIES or steps < 0:
        raise ValueError((family, parameter, steps))
    powered = QuadraticPower.atom().power(steps)
    if powered.value.depth != steps:
        raise AssertionError((powered.value.depth, steps))
    return SpecialPowerProgram(family, parameter, powered.value, powered.compositions)


__all__ = ["SpecialPowerProgram", "build_special_power_program"]
