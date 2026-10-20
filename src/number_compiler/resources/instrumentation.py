"""Radix/residue instrumentation for exact closed digit formulas."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump
from number_compiler.arithmetic.fields.digit_formula import DigitSpec, closed_digit_at
from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot


@dataclass(frozen=True, slots=True)
class ResidueChannel:
    evaluation_radix: int
    modulus: int

    def __post_init__(self) -> None:
        if self.modulus <= 1:
            raise ValueError(self.modulus)


def formula_radix_residue(
    arena: FormulaArena,
    root: FormulaRoot,
    spec: DigitSpec,
    evaluation_radix: int,
    modulus: int,
) -> int:
    """Evaluate ``sum d_i*z^i mod m`` directly from closed digit formulas."""
    forbid_in_powered_jump("formula_radix_residue_materialized")
    z, m = int(evaluation_radix), int(modulus)
    if m <= 1:
        raise ValueError(modulus)
    out = 0
    power = 1
    for i in range(root.width):
        out = (out + closed_digit_at(arena, root, i) * power) % m
        power = power * z % m
    return out


def residue_bundle(
    arena: FormulaArena,
    root: FormulaRoot,
    spec: DigitSpec,
    channels: Iterable[ResidueChannel],
) -> dict[tuple[int, int], int]:
    return {
        (c.evaluation_radix, c.modulus): formula_radix_residue(
            arena, root, spec, c.evaluation_radix, c.modulus
        )
        for c in channels
    }


def prime_power_moduli(primes: Iterable[int], max_power: int = 3) -> tuple[int, ...]:
    out: list[int] = []
    for p in primes:
        p = int(p)
        if p < 2:
            raise ValueError(p)
        q = 1
        for _ in range(int(max_power)):
            q *= p
            out.append(q)
    return tuple(out)


def default_radix_residue_channels(base: int) -> tuple[ResidueChannel, ...]:
    """Compact multi-view bundle: arithmetic radix, +/-1, and small prime powers."""
    b = int(base)
    mods = sorted(set(prime_power_moduli((2, 3, 5, 7, 11), 3)))
    zs = (b, 1, -1, 2, 3, 5)
    return tuple(ResidueChannel(z, m) for z in zs for m in mods)


__all__ = [
    "ResidueChannel",
    "default_radix_residue_channels",
    "formula_radix_residue",
    "prime_power_moduli",
    "residue_bundle",
]
