"""Exact finite 2-adic forcing cylinders; clocks are projection mechanisms.

Precision is semantic for an unbound cylinder. Only consuming an actual
matching occurrence prefix removes bits and emits their valuation weight.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.morphism_core import DyadicAffineCocycle
from number_compiler.arithmetic.fields.two_adic import v2_nonzero

MAX_CYLINDER_BITS = 16384


def _natural(value: int, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


def _precision(bits: int) -> int:
    _natural(bits, "precision")
    if bits > MAX_CYLINDER_BITS:
        raise BlockContextBudgetExceeded("Hensel precision budget exceeded")
    return bits


def three_unit_phase(exponent: int, bits: int) -> int:
    """Return 3**h modulo 2**q without ever constructing 3**h."""
    _natural(exponent, "exponent")
    _precision(bits)
    if bits == 0:
        return 0
    order_bits = 0 if bits == 1 else max(1, bits - 2)
    phase = exponent & ((1 << order_bits) - 1)
    return pow(3, phase, 1 << bits)


def three_dyadic_phase(level: int, bits: int) -> int:
    """3**(2**j) at live precision, including the exceptional j=0 case."""
    _natural(level, "dyadic level")
    _precision(bits)
    if not bits:
        return 0
    if bits == 1 or level >= max(1, bits - 2):
        return 1
    return three_unit_phase(1 << level, bits)


@dataclass(frozen=True, slots=True, order=True)
class HenselCylinder:
    """C(q,r): the exact residue class r modulo 2**q; C(0,0) is universal."""

    bits: int
    residue: int

    def __post_init__(self) -> None:
        _precision(self.bits)
        if type(self.residue) is not int:
            raise TypeError("cylinder residue must be an exact integer")
        object.__setattr__(self, "residue", self.residue % (1 << self.bits))

    @classmethod
    def from_root(cls, bits: int, exponent: int, constant: int) -> HenselCylinder:
        if type(constant) is not int:
            raise TypeError("root constant must be an exact integer")
        unit = three_unit_phase(exponent, bits)
        modulus = 1 << bits
        return cls(bits, -(constant % modulus) * pow(unit, -1, modulus))

    def contains(self, value: int) -> bool:
        if type(value) is not int:
            raise TypeError("cylinder input must be an exact integer")
        return value % (1 << self.bits) == self.residue

    def covers(self, other: HenselCylinder) -> bool:
        return self.bits <= other.bits and self.contains(other.residue)

    def intersect(self, other: HenselCylinder) -> HenselCylinder | None:
        if self.covers(other):
            return other
        return self if other.covers(self) else None

    def consume(self, symbol: int, *, symbol_bits: int = 6) -> CylinderConsumption:
        """Consume one actual input chunk, emitting known valuation bits.

        If a partial final chunk matches, the result is exhausted, not an
        invented exact valuation. A mismatch dies and emits its exact local
        v2. Matching q=0 observes nothing and is already exhausted.
        """
        _natural(symbol_bits, "symbol precision")
        if not 1 <= symbol_bits <= 64:
            raise ValueError("symbol precision must lie in 1..64")
        if type(symbol) is not int or not 0 <= symbol < 1 << symbol_bits:
            raise ValueError("symbol is outside its finite radix")
        used = min(self.bits, symbol_bits)
        mask = (1 << used) - 1
        difference = (symbol & mask) - (self.residue & mask)
        if difference:
            return CylinderConsumption("mismatch", v2_nonzero(difference), None)
        if used == self.bits:
            return CylinderConsumption("exhausted", used, None)
        return CylinderConsumption(
            "match", used, HenselCylinder(self.bits - used, self.residue >> used)
        )

    def pullback(self, block: HenselAffineBlock) -> HenselCylinder:
        """Exact preimage, including the block's integrality condition."""
        precision = _precision(self.bits + block.divisions)
        return self.pullback_modular(
            multiplier=three_unit_phase(block.steps, precision),
            offset=block.offset, divisions=block.divisions,
        )

    def pullback_modular(self, *, multiplier: int, offset: int, divisions: int) -> HenselCylinder:
        """Pull back using coefficients known only at the demanded precision."""
        _natural(divisions, "divisions")
        precision = _precision(self.bits + divisions)
        modulus = 1 << precision
        if type(multiplier) is not int or type(offset) is not int:
            raise TypeError("affine coefficients must be exact integers")
        if precision and not multiplier & 1:
            raise ValueError("dyadic pullback multiplier must be a unit")
        inverse = pow(multiplier, -1, modulus)
        return HenselCylinder(
            precision, inverse * ((self.residue << divisions) - offset)
        )


@dataclass(frozen=True, slots=True)
class CylinderConsumption:
    status: str
    valuation_bits: int
    target: HenselCylinder | None


@dataclass(frozen=True, slots=True)
class HenselAffineBlock:
    """Execution transport (3**n*x+beta)/2**E, not a forcing identity.

    This algebra alone does not certify a Collatz valuation itinerary. The
    separate block domain must retain every primitive exact-valuation guard.
    """

    steps: int
    divisions: int
    offset: int

    def __post_init__(self) -> None:
        _natural(self.steps, "steps")
        _precision(self.divisions)
        _natural(self.offset, "offset")
        if (
            self.steps > MAX_CYLINDER_BITS
            or self.offset.bit_length() > 4 * MAX_CYLINDER_BITS
        ):
            raise BlockContextBudgetExceeded(
                "Hensel affine coefficient budget exceeded"
            )

    def then(self, after: HenselAffineBlock) -> HenselAffineBlock:
        # Exact affine composition has one existing owner. Complete powers of
        # three are bounded transport coefficients here, never cylinder keys.
        _precision(self.divisions + after.divisions)
        if self.steps + after.steps > MAX_CYLINDER_BITS:
            raise BlockContextBudgetExceeded("Hensel affine step budget exceeded")
        first = DyadicAffineCocycle(3**self.steps, self.offset, self.divisions)
        second = DyadicAffineCocycle(3**after.steps, after.offset, after.divisions)
        result = first.then(second)
        return HenselAffineBlock(self.steps + after.steps, result.shift, result.addend)

    def apply_exact(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("block input must be an exact integer")
        return DyadicAffineCocycle(
            3**self.steps, self.offset, self.divisions
        ).apply_exact(value)
