"""Recurrence-equivalent Fermat/Mersenne primality reference oracles.

This module is deliberately outside the production import graph.  It exists for
bounded differential validation only.  The scalable release path must use
``special_terminal_threshold`` and must never import this module.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.proofs.oracles.special_power_reference import (
    apply_special_power_reference,
)
from devtools.proofs.special_power_monoid import (
    build_special_power_program,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    mersenne_number,
)


@dataclass(frozen=True, slots=True)
class PepinResult:
    index: int
    modulus_bits: int
    squarings: int
    residue: int
    passes: bool
    operator_compositions: int = 0
    raw_specialization_squarings: int = 0
    powered_image_classes: int = 0


def pepin_test(index: int, *, base: int = 3) -> PepinResult:
    index, base = int(index), int(base)
    if index < 1 or base <= 1:
        raise ValueError((index, base))
    spec = FermatNumberSpec(index)
    modulus = spec.materialize()
    squarings = spec.exponent - 1
    program = build_special_power_program("fermat", index, squarings)
    application = apply_special_power_reference(program, base % modulus)
    if application.nonlinear_squarings != squarings:
        raise AssertionError((application.nonlinear_squarings, squarings))
    return PepinResult(
        index,
        spec.bit_length,
        squarings,
        application.value,
        application.target,
        program.construction_compositions,
        application.nonlinear_squarings,
        program.prime_domain_image_classes(),
    )


@dataclass(frozen=True, slots=True)
class LucasLehmerResult:
    exponent: int
    modulus_bits: int
    iterations: int
    residue: int
    passes: bool
    operator_compositions: int = 0
    raw_specialization_squarings: int = 0
    powered_image_classes: int = 0


def lucas_lehmer_test(exponent: int) -> LucasLehmerResult:
    p = int(exponent)
    if p < 2:
        raise ValueError(p)
    modulus = mersenne_number(p)
    if p == 2:
        return LucasLehmerResult(p, p, 0, 0, True, 0, 0, 3)
    iterations = p - 2
    program = build_special_power_program("mersenne", p, iterations)
    application = apply_special_power_reference(program, 4 % modulus)
    return LucasLehmerResult(
        p,
        p,
        iterations,
        application.value,
        application.target,
        program.construction_compositions,
        application.nonlinear_squarings,
        program.prime_domain_image_classes(),
    )


__all__ = ["PepinResult", "pepin_test", "LucasLehmerResult", "lucas_lehmer_test"]
