"""Collatz research: spatial wire responses and binary temporal jet actions.

The spatial indeterminate advances one radix-64 cell; the temporal one advances
one bit. They are deliberately separate interfaces. Neither is a temporal ID.
All polynomial arithmetic uses the existing primary-jet owner.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    carry_fn_from_outputs,
)
from number_compiler.arithmetic.carry.jet_cylinder import JetPortCylinder, JetPortRow
from number_compiler.arithmetic.carry.carry_normalization import (
    linear_normalization_fields,
)
from number_compiler.arithmetic.carry.collatz_carry_wires import (
    CollatzCarryWires,
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    PrimaryJetBlock,
    _poly_add,
    _poly_mul,
    primary_jet_from_digits,
)
from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder

Jet = tuple[int, ...]
ZERO: Jet = (0, 0, 0, 0, 0)
ONE: Jet = (1, 0, 0, 0, 0)
Y: Jet = (0, 1, 0, 0, 0)
_CELL_POWERS = tuple(
    PrimaryJetBlock.digit(0, degree=5, modulus=2).power_block(n).power for n in range(8)
)


@dataclass(frozen=True, slots=True)
class WireResponse:
    """Two extensional rows; carry and affine coefficients are derived views."""

    rows: tuple[JetPortRow, JetPortRow]

    def __post_init__(self) -> None:
        require_endpoint_construction()
        cylinder = self.cylinder
        if cylinder.degree != 5 or cylinder.outputs not in ((0, 0), (0, 1), (1, 1)):
            raise ValueError("invalid finite two-wire response")

    @property
    def cylinder(self) -> JetPortCylinder:
        return JetPortCylinder(2, self.rows)

    @property
    def fn(self) -> CarryFn:
        return carry_fn_from_outputs(self.cylinder.outputs)

    @property
    def constant(self) -> Jet:
        return self.rows[0].jet

    @property
    def linear(self) -> Jet:
        return _poly_add(self.rows[0].jet, self.rows[1].jet, 2)

    @classmethod
    def from_affine(cls, fn: CarryFn, constant: Jet, linear: Jet) -> WireResponse:
        return cls(
            (
                JetPortRow(apply_carry_fn(fn, 0), constant),
                JetPortRow(apply_carry_fn(fn, 1), _poly_add(constant, linear, 2)),
            )
        )

    def emit(self, incoming: int) -> Jet:
        apply_carry_fn(CarryFn.ID, incoming)
        return self.rows[incoming].jet

    def then(self, after: WireResponse, shift: Jet) -> WireResponse:
        result = self.cylinder.then(after.cylinder, shift)
        return WireResponse((result.rows[0], result.rows[1]))


@dataclass(frozen=True, slots=True)
class Radix64WireHarmonicAction:
    phase: int
    lower: WireResponse
    upper: WireResponse

    def __post_init__(self) -> None:
        require_endpoint_construction()
        if type(self.phase) is not int or not 0 <= self.phase < 8:
            raise ValueError("radix-64 harmonic phase must lie in Z/8")
        self.domain  # Validate the joint staircase ports.

    @classmethod
    def identity(cls) -> Radix64WireHarmonicAction:
        empty = WireResponse.from_affine(CarryFn.ID, ZERO, ZERO)
        return cls(0, empty, empty)

    @classmethod
    def digit(cls, digit: int) -> Radix64WireHarmonicAction:
        wires = collatz_digit_carry_wires(digit, base=64)
        return cls(
            1,
            WireResponse.from_affine(wires.lower, ZERO, ONE),
            WireResponse.from_affine(wires.upper, ZERO, ONE),
        )

    @property
    def domain(self) -> CollatzCarryWires:
        return CollatzCarryWires(self.lower.fn, self.upper.fn)

    @property
    def response_key(self) -> tuple[WireResponse, WireResponse]:
        """Value response alone; the periodic spatial phase is separate."""
        return self.lower, self.upper

    @property
    def canonical_key(self) -> tuple[int, WireResponse, WireResponse]:
        """Complete action identity with exact jet phase and no width copy."""
        return self.phase, self.lower, self.upper

    def then(self, after: Radix64WireHarmonicAction) -> Radix64WireHarmonicAction:
        shift = _CELL_POWERS[self.phase]
        return Radix64WireHarmonicAction(
            (self.phase + after.phase) % 8,
            self.lower.then(after.lower, shift),
            self.upper.then(after.upper, shift),
        )

    @classmethod
    def from_digits(cls, digits: Iterable[int]) -> Radix64WireHarmonicAction:
        result = cls.identity()
        for digit in digits:
            result = result.then(cls.digit(digit))
        return result


def binary_jet(value: int, modulus: int = 32) -> Jet:
    if type(value) is not int or value < 0:
        raise ValueError("binary jet source must be nonnegative and exact")
    return primary_jet_from_digits(digits_lsd(value, 2), degree=5, modulus=modulus).jet


def binary_carry_birth(value: int, modulus: int = 32, incoming: int = 1) -> Jet:
    """Independent carry forcing for 3*value+incoming, from redundant bits."""
    if type(incoming) is not int or incoming not in (0, 1, 2):
        raise ValueError("Collatz incoming carry must be 0,1,2")
    if type(value) is not int or value < 0:
        raise ValueError("binary forcing source must be nonnegative and exact")
    bits = digits_lsd(value, 2) + (0, 0)
    raw = tuple(bit + (bits[i - 1] if i else 0) for i, bit in enumerate(bits))
    _digits, carries = linear_normalization_fields(raw, base=2, boundary_in=incoming)
    assert carries[-1] == 0
    forcing = tuple(carries[i] - 2 * carries[i + 1] for i in range(len(raw)))
    return primary_jet_from_digits(forcing, degree=5, modulus=modulus).jet


def binary_temporal_action(
    valuation: int, birth: Jet, modulus: int = 32
) -> PrimaryJetAffineMorphism:
    """Known forcing event: z^{-e}(y*J+B). Valuation legality is external."""
    if type(valuation) is not int or valuation < 0:
        raise ValueError("valuation must be nonnegative and exact")
    # z=y-1, hence z^{-1}=-(1+y+...+y^4) in this quotient.
    inverse = (
        PrimaryJetAffineMorphism(5, modulus, ((modulus - 1),) * 5, ZERO)
        .power(valuation)
        .kernel
    )
    return PrimaryJetAffineMorphism(
        5,
        modulus,
        _poly_mul(inverse, Y, modulus),
        _poly_mul(inverse, birth, modulus),
        1,
    )


def binary_output_response(value: int, modulus: int = 2) -> tuple[Jet, Jet, Jet]:
    """All three unshifted multiply/add output jets, from source plus forcing."""
    transported = _poly_mul(Y, binary_jet(value, modulus), modulus)
    rows = tuple(
        _poly_add(transported, binary_carry_birth(value, modulus, c), modulus)
        for c in range(3)
    )
    return rows[0], rows[1], rows[2]


_BIT_Z = PrimaryJetBlock.digit(0, degree=5, modulus=2)
_OUTPUT_CELL_POWERS = tuple(_BIT_Z.power_block(6 * phase).power for phase in range(4))


OutputHarmonicRow = JetPortRow


@dataclass(frozen=True, slots=True)
class Radix64OutputHarmonicAction:
    """Three-port Mealy action for the low-bit output jet.

    Exact extent is occurrence geometry.  The action needs only ``L mod 4``
    because its higher block is translated by ``z_bit**(6L)`` and that unit
    has order four in ``F2[y]/y**5``.
    """

    phase: int
    rows: tuple[OutputHarmonicRow, OutputHarmonicRow, OutputHarmonicRow]

    def __post_init__(self) -> None:
        require_endpoint_construction()
        if type(self.phase) is not int or not 0 <= self.phase < 4:
            raise ValueError("output harmonic phase must lie in Z/4")
        if (
            type(self.rows) is not tuple
            or len(self.rows) != 3
            or any(type(row) is not OutputHarmonicRow for row in self.rows)
        ):
            raise ValueError("output harmonic requires exactly three carry rows")
        cylinder = JetPortCylinder(2, self.rows)
        if cylinder.degree != 5:
            raise ValueError("output harmonic requires five coefficients")

    @classmethod
    def identity(cls) -> Radix64OutputHarmonicAction:
        return cls(
            0,
            (
                OutputHarmonicRow(0, ZERO),
                OutputHarmonicRow(1, ZERO),
                OutputHarmonicRow(2, ZERO),
            ),
        )

    @classmethod
    def digit(cls, digit: int) -> Radix64OutputHarmonicAction:
        collatz_digit_carry_wires(digit, base=64)
        rows: list[OutputHarmonicRow] = []
        for incoming in range(3):
            raw = 3 * digit + incoming
            rows.append(OutputHarmonicRow(raw // 64, binary_jet(raw % 64, 2)))
        return cls(1, (rows[0], rows[1], rows[2]))

    def then(self, after: Radix64OutputHarmonicAction) -> Radix64OutputHarmonicAction:
        if type(after) is not Radix64OutputHarmonicAction:
            raise TypeError("output harmonics compose with their own action sort")
        result = JetPortCylinder(2, self.rows).then(
            JetPortCylinder(2, after.rows), _OUTPUT_CELL_POWERS[self.phase]
        )
        return Radix64OutputHarmonicAction(
            (self.phase + after.phase) % 4,
            (result.rows[0], result.rows[1], result.rows[2]),
        )

    @classmethod
    def from_digits(cls, digits: Iterable[int]) -> Radix64OutputHarmonicAction:
        result = cls.identity()
        for digit in digits:
            result = result.then(cls.digit(digit))
        return result


def radix64_phi5(digit: int) -> int:
    """y_bit^2 coefficient of the digit's binary forcing birth at carry one."""
    collatz_digit_carry_wires(digit, base=64)  # Validate the radix-64 digit.
    return binary_carry_birth(digit, modulus=5, incoming=1)[2]


def admitted_cylinder_symbols(cylinder: HenselCylinder) -> tuple[int, ...]:
    """Exactly the radix-64 first symbols with a completion in C(q,r)."""
    return tuple(
        symbol
        for symbol in range(64)
        if cylinder.intersect(HenselCylinder(6, symbol)) is not None
    )
