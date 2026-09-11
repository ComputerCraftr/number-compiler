"""Exact linear-work ceiling for demanded Fermat/Mersenne theorem queries.

The special compiler first tries compact quotient/constraint propagation.  If
that state remains unresolved, production is allowed to execute the classical
special-form recurrence directly.  This module is the hard performance ceiling:
there is no factor-slot, carrier, CRT, or tropical enumeration here.

For ``F_n`` we square the canonical base 3 exactly ``2**n - 1`` times and test
the Pépin target ``-1``.  For a prime Mersenne exponent ``p`` we execute the
Lucas--Lehmer trace recurrence exactly ``p - 2`` times and test zero.  In both
families the recurrence work is ``modulus_bits - 2`` nonlinear squarings.

The final target equation is also exposed as a candidate-ring defect.  A single
final gcd may produce a natural split/factor packet on a failing candidate, but
no gcd is needed to decide the theorem bit itself.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.polynomials.arithmetic_tile import SquareTileAction


@dataclass(frozen=True, slots=True)
class SpecialClassicalCeilingResult:
    family: str
    parameter: int
    modulus_bits: int
    steps: int
    residue: int
    defect: int
    passes: bool
    method: str
    gcd_packet: int | None = None
    factor_enumeration: int = 0
    carrier_states_enumerated: int = 0

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.parameter < 0 or self.modulus_bits <= 0 or self.steps < 0:
            raise ValueError((self.parameter, self.modulus_bits, self.steps))
        if self.steps > max(0, self.modulus_bits - 2):
            raise ValueError((self.steps, self.modulus_bits))
        if self.factor_enumeration or self.carrier_states_enumerated:
            raise ValueError("classical ceiling cannot enumerate factors/carriers")
        if self.gcd_packet is not None and self.gcd_packet <= 1:
            raise ValueError(self.gcd_packet)

    @property
    def status(self) -> str:
        return "prime" if self.passes else "composite"

    @property
    def raw_specialization_squarings(self) -> int:
        return self.steps


def _proper_gcd_packet(modulus: int, defect: int) -> int | None:
    """Return a proper nontrivial target-defect gcd, if the failure exposes one."""
    g = gcd(int(modulus), int(defect))
    return g if 1 < g < int(modulus) else None


def fermat_classical_ceiling(
    index: int, *, collect_gcd_packet: bool = False
) -> SpecialClassicalCeilingResult:
    """Exact Pépin-equivalent fallback with an explicit squaring budget."""
    n = int(index)
    if n < 1:
        raise ValueError(n)
    width = 1 << n
    modulus = (1 << width) + 1
    steps = width - 1
    value = SquareTileAction.atom("fermat").power_block(steps).apply(3, modulus)
    # Pépin target is -1.  This normalized defect is zero exactly on PASS.
    defect = (value + 1) % modulus
    passes = defect == 0
    packet = (
        None
        if passes or not collect_gcd_packet
        else _proper_gcd_packet(modulus, defect)
    )
    return SpecialClassicalCeilingResult(
        "fermat",
        n,
        width + 1,
        steps,
        value,
        defect,
        passes,
        "classical-ceiling:pepin-target-pullback",
        packet,
    )


def mersenne_classical_ceiling(
    exponent: int,
    *,
    collect_gcd_packet: bool = False,
) -> SpecialClassicalCeilingResult:
    """Exact Lucas--Lehmer fallback for an already-prime exponent candidate."""
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    modulus = (1 << p) - 1
    steps = p - 2
    value = SquareTileAction.atom("mersenne").power_block(steps).apply(4, modulus)
    defect = value
    passes = defect == 0
    packet = (
        None
        if passes or not collect_gcd_packet
        else _proper_gcd_packet(modulus, defect)
    )
    return SpecialClassicalCeilingResult(
        "mersenne",
        p,
        p,
        steps,
        value,
        defect,
        passes,
        "classical-ceiling:lucas-lehmer-target-pullback",
        packet,
    )


def special_classical_ceiling(
    family: str,
    parameter: int,
    *,
    collect_gcd_packet: bool = False,
) -> SpecialClassicalCeilingResult:
    family = str(family)
    if family == "fermat":
        return fermat_classical_ceiling(
            parameter, collect_gcd_packet=collect_gcd_packet
        )
    if family == "mersenne":
        return mersenne_classical_ceiling(
            parameter, collect_gcd_packet=collect_gcd_packet
        )
    raise ValueError(family)


__all__ = [
    "SpecialClassicalCeilingResult",
    "fermat_classical_ceiling",
    "mersenne_classical_ceiling",
    "special_classical_ceiling",
]
