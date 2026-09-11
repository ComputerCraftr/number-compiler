"""Reversal-fixed frame for reverse-and-add pair fields.

A reverse-and-add pair polynomial ``S`` of width ``L`` satisfies

    S(z) = z**(L-1) S(z**-1).

The apparent extra-digit branch is therefore a change of the reflection frame,
not an independent forcing coordinate.  This module removes that frame action
before cyclotomic projection.

For odd width we center the palindrome directly.  For even width the palindrome
has the exact factor ``1+z``; removing that factor first produces an odd-width
palindrome which can be centered in the same inversion-fixed ring::

    N_L(S) = z**(-(L-1)/2) S                         (L odd)
           = z**(-(L-2)/2) S/(1+z)                  (L even).

Every ``N_L(S)`` is fixed by ``z -> z**-1``.  In this frame the homogeneous
reverse-add action becomes

* no growth: ``2``;
* odd -> even growth: ``1``;
* even -> odd growth: ``z + 2 + z**-1``.

Thus the width-growth bit acts only on a two-sector symmetry frame.  This is the
semidirect-product form of the old ``A_0=2, A_1=1+z`` transport.

The classes below are quotient/proof coordinates.  They are not promoted to a
closed orbit state unless a caller separately proves successor closure.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Mapping, Sequence

from number_compiler.arithmetic.fields.morphism_core import QuadraticPower, binary_power
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
    CyclotomicAffineMorphism,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.polynomial import (
    polynomial_divide_exact,
    trace_square_polynomial,
)


def _fixed_coordinates(residue: Sequence[int], modulus: int) -> tuple[int, ...]:
    """Canonical coordinates of the ``z -> z^-1`` fixed subring.

    In ``Z/2^w[z]/(z^m+1)``, ``z^-i=-z^(m-i)``.  A fixed residue therefore
    stores only ``a_0,a_1,...,a_(m/2-1)`` plus the one-bit middle torsion
    coefficient ``a_(m/2) in {0,2^(w-1)}`` (for even m).
    """
    values = tuple(int(v) % int(modulus) for v in residue)
    modulus = int(modulus)
    if not values or modulus <= 1 or modulus & (modulus - 1):
        raise ValueError((len(values), modulus))
    degree = len(values)
    if degree == 1:
        return values
    if degree & 1:
        raise ValueError("power-of-two cyclotomic fixed frame expects degree 1 or even")
    half = degree // 2
    for i in range(1, half):
        if values[degree - i] != (-values[i]) % modulus:
            raise ValueError(("not-inversion-fixed", i, values[i], values[degree - i]))
    middle = values[half]
    torsion = modulus // 2
    if middle not in (0, torsion):
        raise ValueError(("invalid-middle-torsion", middle, modulus))
    return values[:half] + (int(middle == torsion),)


def _fixed_description_bits(degree: int, bits: int) -> int:
    degree, bits = int(degree), int(bits)
    if degree <= 0 or bits <= 0:
        raise ValueError((degree, bits))
    if degree == 1:
        return bits
    if degree & 1:
        raise ValueError(degree)
    return (degree // 2) * bits + 1


def _palindromic_core(coefficients: Sequence[int]) -> tuple[int, ...]:
    """Return the odd-width palindrome after removing the symmetry edge factor.

    Every even-width palindrome has odd polynomial degree and hence vanishes at
    ``z=-1``.  Division by ``1+z`` is exact over the integers, including for the
    signed forcing-event coefficients used by reverse-add.
    """
    values = tuple(map(int, coefficients))
    if not values or values != values[::-1]:
        raise ValueError("symmetry-frame coefficients must be a nonempty palindrome")
    if len(values) & 1:
        return values
    if not any(values):
        # ``polynomial_divide_exact`` intentionally trims the zero polynomial;
        # preserve the physical padded width of this symmetry coordinate.
        quotient = (0,) * (len(values) - 1)
    else:
        divided = polynomial_divide_exact(values, (1, 1))
        if divided is None:
            raise AssertionError("even-width palindrome lost its exact (1+z) factor")
        quotient = tuple(map(int, divided)) + (0,) * (len(values) - 1 - len(divided))
    if len(quotient) != len(values) - 1 or quotient != quotient[::-1]:
        raise AssertionError((values, quotient))
    return quotient


@dataclass(frozen=True, slots=True)
class ReverseAddSymmetryProjection:
    """One reversal-fixed cyclotomic projection of a symmetric coefficient row."""

    order: int
    bits: int
    width: int
    residue: tuple[int, ...]

    def __post_init__(self) -> None:
        order, bits, width = int(self.order), int(self.bits), int(self.width)
        if order < 2 or order & (order - 1) or bits <= 0 or width <= 0:
            raise ValueError((order, bits, width))
        template = CyclotomicDigitBlock.identity(order, 1 << bits)
        if len(self.residue) != template.degree:
            raise ValueError((len(self.residue), template.degree))
        modulus = 1 << bits
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "bits", bits)
        object.__setattr__(self, "width", width)
        object.__setattr__(
            self, "residue", tuple(int(v) % modulus for v in self.residue)
        )

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def parity(self) -> int:
        return self.width & 1

    @property
    def removed_edge_factor(self) -> bool:
        return not self.parity

    @classmethod
    def from_coefficients(
        cls,
        coefficients: Sequence[int],
        *,
        order: int,
        bits: int,
    ) -> "ReverseAddSymmetryProjection":
        values = tuple(map(int, coefficients))
        core = _palindromic_core(values)
        center = (len(core) - 1) // 2
        block = CyclotomicDigitBlock.from_coefficients(
            core,
            order=int(order),
            modulus=1 << int(bits),
        )
        centered = block.shift_positions(-center, result_length=len(core))
        return cls(int(order), int(bits), len(values), centered.residue)

    def _template(self) -> CyclotomicDigitBlock:
        return CyclotomicDigitBlock.identity(self.order, self.modulus)

    def inversion_residue(self) -> tuple[int, ...]:
        """Apply ``z -> z^-1`` to the centered residue."""
        template = self._template()
        inv_z = template.z_power_residue(-1)
        power = (1,) + (0,) * (template.degree - 1)
        out = [0] * template.degree
        for coefficient in self.residue:
            for index, value in enumerate(power):
                out[index] = (out[index] + coefficient * value) % self.modulus
            factor = CyclotomicDigitBlock.from_coefficients(
                power,
                order=self.order,
                modulus=self.modulus,
            ).multiply(
                CyclotomicDigitBlock.from_coefficients(
                    inv_z,
                    order=self.order,
                    modulus=self.modulus,
                )
            )
            power = factor.residue
        return tuple(out)

    @property
    def inversion_fixed(self) -> bool:
        return self.inversion_residue() == self.residue

    @property
    def fixed_coordinates(self) -> tuple[int, ...]:
        return _fixed_coordinates(self.residue, self.modulus)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # Absolute width is retained only because this object is a projection
        # result.  Affine symmetry-frame blocks below retain parity instead.
        return (
            "reverse-add-symmetry-projection",
            self.order,
            self.bits,
            self.width,
            self.fixed_coordinates,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.order)
            + bit_width(self.bits)
            + bit_width(self.width)
            + _fixed_description_bits(len(self.residue), self.bits)
        )


@lru_cache(maxsize=None)
def _fixed_real_basis(order: int, bits: int) -> tuple[tuple[int, ...], ...]:
    """Triangular ``x=z+2+z^-1`` basis in one 2-power cyclotomic ring.

    Integral reversal-fixed Laurent polynomials lie in ``Z[x]``.  The extra
    middle coefficient admitted by modular inversion-fixity is pure 2-torsion
    and is not part of such an integral lift.  The basis is triangular with
    unit diagonal, so conversion to real-cyclotomic coefficients is exact over
    ``Z/2^bits`` without division.
    """
    order, bits = int(order), int(bits)
    if order < 2 or order & (order - 1) or bits <= 0:
        raise ValueError((order, bits))
    if order == 2:
        return ((1,),)
    modulus = 1 << bits
    template = CyclotomicDigitBlock.identity(order, modulus)
    real_degree = template.degree // 2
    one = CyclotomicDigitBlock.from_coefficients((1,), order=order, modulus=modulus)
    z = template.z_power_residue(1)
    inv_z = template.z_power_residue(-1)
    x = tuple(
        (2 * int(i == 0) + z[i] + inv_z[i]) % modulus for i in range(template.degree)
    )
    xb = CyclotomicDigitBlock.from_coefficients(x, order=order, modulus=modulus)
    rows: list[tuple[int, ...]] = []
    power = one
    for _ in range(real_degree):
        rows.append(tuple(power.residue[:real_degree]))
        power = power.multiply(xb)
    for k, row in enumerate(rows):
        if row[k] % modulus != 1 or any(
            row[j] % modulus for j in range(k + 1, real_degree)
        ):
            raise AssertionError((order, bits, k, row))
    return tuple(rows)


def _fixed_real_coefficients(
    order: int,
    bits: int,
    fixed_coordinates: Sequence[int],
) -> tuple[int, ...]:
    """Convert canonical inversion-fixed coordinates to an integral ``Z[x]`` lift.

    The final fixed-coordinate bit for orders >=4 is modular middle torsion.
    It must vanish for a genuine integer palindrome/symmetric forcing field.
    Rejecting it prevents a silent projection from the full fixed subring onto
    the smaller integral real-cyclotomic subring.
    """
    order, bits = int(order), int(bits)
    modulus = 1 << bits
    coords = tuple(map(int, fixed_coordinates))
    if order == 2:
        if len(coords) != 1:
            raise ValueError((order, coords))
        return (coords[0] % modulus,)
    template = CyclotomicDigitBlock.identity(order, modulus)
    real_degree = template.degree // 2
    if len(coords) != real_degree + 1:
        raise ValueError((order, len(coords), real_degree + 1))
    if coords[-1] != 0:
        raise ValueError(
            "integral fixed-ring germ cannot retain modular middle torsion"
        )
    values = [int(v) % modulus for v in coords[:real_degree]]
    basis = _fixed_real_basis(order, bits)
    out = [0] * real_degree
    for k in range(real_degree - 1, -1, -1):
        value = values[k]
        for j in range(k + 1, real_degree):
            value -= out[j] * basis[j][k]
        out[k] = value % modulus
    return tuple(out)


@dataclass(frozen=True, slots=True)
class FixedRealCyclotomicGerm:
    """Canonical joint ``Phi_2/Phi_4/Phi_8`` innovation in the real fixed ring.

    With ``x=(1+z)(1+z^-1)=z+2+z^-1`` and

        P8(x) = x^2 - 4*x + 2,

    write ``F = R8 + P8*Q`` with ``deg(R8)<2``.  The three low cyclotomic
    views are exactly equivalent to

        R8(x) = r0 + r1*x                 mod 2^w
        q0     = Q(0)                     mod 2^(w-1)
        slope  = (Q(2)-Q(0))/2            mod 2^(w-2).

    The last division is exact because an integer polynomial has
    ``Q(2)==Q(0) (mod 2)``.  This removes the redundant product-ring encoding
    while preserving every bit of the three aligned low-order projections.
    """

    bits: int
    r0: int
    r1: int
    q0: int
    q02_slope: int

    def __post_init__(self) -> None:
        bits = int(self.bits)
        if bits < 3:
            raise ValueError("real fixed-ring germ requires at least three 2-adic bits")
        modulus = 1 << bits
        qmod = 1 << (bits - 1)
        smod = 1 << (bits - 2)
        object.__setattr__(self, "bits", bits)
        object.__setattr__(self, "r0", int(self.r0) % modulus)
        object.__setattr__(self, "r1", int(self.r1) % modulus)
        object.__setattr__(self, "q0", int(self.q0) % qmod)
        object.__setattr__(self, "q02_slope", int(self.q02_slope) % smod)

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def qmodulus(self) -> int:
        return 1 << (self.bits - 1)

    @property
    def q2(self) -> int:
        return (self.q0 + 2 * self.q02_slope) % self.qmodulus

    @classmethod
    def from_fixed_views(
        cls,
        views: Mapping[int, Sequence[int]],
        *,
        bits: int,
    ) -> "FixedRealCyclotomicGerm":
        bits = int(bits)
        missing = {2, 4, 8}.difference(views)
        if missing:
            raise ValueError(("missing fixed-ring views", tuple(sorted(missing))))
        modulus = 1 << bits
        f0 = _fixed_real_coefficients(2, bits, views[2])[0]
        f2 = _fixed_real_coefficients(4, bits, views[4])[0]
        r0, r1 = _fixed_real_coefficients(8, bits, views[8])
        d0 = (f0 - r0) % modulus
        d2 = (r0 + 2 * r1 - f2) % modulus
        if d0 & 1 or d2 & 1:
            raise ValueError(
                ("unaligned/nonintegral low fixed-ring views", f0, f2, r0, r1)
            )
        q0 = d0 // 2
        q2 = d2 // 2
        delta = (q2 - q0) % (1 << (bits - 1))
        if delta & 1:
            raise ValueError(
                ("divided values violate integer-polynomial parity", q0, q2)
            )
        return cls(bits, r0, r1, q0, delta // 2)

    @property
    def fixed_views(self) -> dict[int, tuple[int, ...]]:
        modulus = self.modulus
        f0 = (self.r0 + 2 * self.q0) % modulus
        f2 = (self.r0 + 2 * self.r1 - 2 * self.q2) % modulus
        # ``r0+r1*x`` maps to z-coordinates ``(r0+2*r1,r1,0,-r1)``
        # in Phi_8.  Canonical fixed coordinates retain the first two and the
        # (zero) integral middle-torsion bit.
        phi8 = ((self.r0 + 2 * self.r1) % modulus, self.r1 % modulus, 0)
        return {2: (f0,), 4: (f2, 0), 8: phi8}

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "fixed-real-cyclotomic-germ",
            self.bits,
            self.r0,
            self.r1,
            self.q0,
            self.q02_slope,
        )

    @property
    def description_bits(self) -> int:
        return 2 * self.bits + (self.bits - 1) + (self.bits - 2)

    @staticmethod
    def trace_tower_coefficients(depth: int) -> tuple[int, ...]:
        """Return the real 2-power cyclotomic trace iterate at ``depth``.

        The seed ``x-2 = z+z^-1`` and temporal depth are represented by the
        same :class:`QuadraticPower` used by Fermat/Mersenne.  Only the
        coordinate-level one-step map is polynomial-valued here.
        """
        return QuadraticPower(int(depth)).apply_iterated(
            (-2, 1),
            step=trace_square_polynomial,
        )

    @staticmethod
    def p8_coefficients() -> tuple[int, ...]:
        return FixedRealCyclotomicGerm.trace_tower_coefficients(1)

    @staticmethod
    def p16_coefficients() -> tuple[int, ...]:
        return FixedRealCyclotomicGerm.trace_tower_coefficients(2)

    def invisible_kernel_generators(self) -> tuple[tuple[int, ...], ...]:
        """Generators inside the hidden ``P8`` cofactor.

        At precision ``w`` equality of the low germ means ``Q(0)=Q(2)=0``
        modulo ``2^(w-1)``.  The exact cofactor ideal is generated by

            2^(w-1),  2^(w-2)*x,  x*(x-2).

        The full invisible difference is ``P8`` times this ideal.  These are
        theorem generators, not additional retained coordinates.
        """
        return (
            ((1 << (self.bits - 1)),),
            (0, (1 << (self.bits - 2))),
            (0, -2, 1),
        )


@dataclass(frozen=True, slots=True)
class ReverseAddSymmetryLinearAction:
    """Homogeneous reverse-add transport after quotienting the reflection frame.

    ``start_parity`` is supplied when applying the action.  Growth toggles that
    two-state frame; every second growth contributes the inversion-fixed factor
    ``z+2+z^-1``.  No-growth steps contribute only the scalar ``2``.
    """

    order: int
    bits: int
    no_growth: int
    growth: int
    compositions: int = 0

    def __post_init__(self) -> None:
        order, bits = int(self.order), int(self.bits)
        q, r, c = int(self.no_growth), int(self.growth), int(self.compositions)
        if order < 2 or order & (order - 1) or bits <= 0 or q < 0 or r < 0 or c < 0:
            raise ValueError(self)
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "bits", bits)
        object.__setattr__(self, "no_growth", q)
        object.__setattr__(self, "growth", r)
        object.__setattr__(self, "compositions", c)

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def steps(self) -> int:
        return self.no_growth + self.growth

    @staticmethod
    def _check_parity(parity: int) -> int:
        parity = int(parity)
        if parity not in (0, 1):
            raise ValueError(parity)
        return parity

    def end_parity(self, start_parity: int) -> int:
        return self._check_parity(start_parity) ^ (self.growth & 1)

    def paired_growths(self, start_parity: int) -> int:
        """Number of even->odd growths, i.e. ``z+2+z^-1`` factors."""
        p = self._check_parity(start_parity)
        return (self.growth + int(p == 0)) // 2

    def _symmetry_pair_factor(self) -> tuple[int, ...]:
        template = CyclotomicDigitBlock.identity(self.order, self.modulus)
        one = (1,) + (0,) * (template.degree - 1)
        z = template.z_power_residue(1)
        inv_z = template.z_power_residue(-1)
        return tuple(
            (2 * one[i] + z[i] + inv_z[i]) % self.modulus
            for i in range(template.degree)
        )

    def multiplier_residue(self, start_parity: int) -> tuple[int, ...]:
        p = self._check_parity(start_parity)
        block = CyclotomicDigitBlock.from_coefficients(
            (1,),
            order=self.order,
            modulus=self.modulus,
        ).scale_coefficients(pow(2, self.no_growth, self.modulus))
        pairs = self.paired_growths(p)
        if pairs:
            block = block.multiply_polynomial_power(
                self._symmetry_pair_factor(),
                pairs,
            )
        return block.residue

    def apply_residue(
        self, residue: Sequence[int], *, start_parity: int
    ) -> tuple[int, ...]:
        template = CyclotomicDigitBlock.identity(self.order, self.modulus)
        values = tuple(int(v) % self.modulus for v in residue)
        if len(values) != template.degree:
            raise ValueError((len(values), template.degree))
        morphism = CyclotomicAffineMorphism.from_residues(
            template,
            self.multiplier_residue(start_parity),
            (0,) * template.degree,
        )
        source = CyclotomicDigitBlock(
            self.order,
            self.modulus,
            0,
            values,
            0,
        )
        return morphism.apply(source, result_length=0).residue

    def then(
        self, other: "ReverseAddSymmetryLinearAction"
    ) -> "ReverseAddSymmetryLinearAction":
        if (self.order, self.bits) != (other.order, other.bits):
            raise ValueError(((self.order, self.bits), (other.order, other.bits)))
        return ReverseAddSymmetryLinearAction(
            self.order,
            self.bits,
            self.no_growth + other.no_growth,
            self.growth + other.growth,
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> "ReverseAddSymmetryLinearAction":
        base = ReverseAddSymmetryLinearAction(
            self.order, self.bits, self.no_growth, self.growth, 0
        )
        identity = ReverseAddSymmetryLinearAction(self.order, self.bits, 0, 0, 0)
        powered = binary_power(
            base,
            exponent,
            identity=identity,
            compose=ReverseAddSymmetryLinearAction.then,
        )
        result = powered.value
        return ReverseAddSymmetryLinearAction(
            result.order,
            result.bits,
            result.no_growth,
            result.growth,
            powered.compositions,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-add-symmetry-linear",
            self.order,
            self.bits,
            self.no_growth,
            self.growth,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.order)
            + bit_width(self.bits)
            + bit_width(self.no_growth)
            + bit_width(self.growth)
        )


@dataclass(frozen=True, slots=True)
class ReverseAddSymmetryInnovationBlock:
    """Affine forcing block in the reversal-fixed two-sector frame.

    Only the starting *parity* is retained; absolute width has been quotiented by
    centering.  Composition is legal whenever the frame parity matches.  This is
    strictly smaller than carrying the old absolute reflection exponent.
    """

    order: int
    bits: int
    start_parity: int
    steps: int
    growth: int
    innovation: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        order, bits = int(self.order), int(self.bits)
        p, steps, growth = int(self.start_parity), int(self.steps), int(self.growth)
        c = int(self.compositions)
        if order < 2 or order & (order - 1) or bits <= 0 or p not in (0, 1):
            raise ValueError(self)
        if steps < 0 or not 0 <= growth <= steps or c < 0:
            raise ValueError(self)
        template = CyclotomicDigitBlock.identity(order, 1 << bits)
        if len(self.innovation) != template.degree:
            raise ValueError((len(self.innovation), template.degree))
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "bits", bits)
        object.__setattr__(self, "start_parity", p)
        object.__setattr__(self, "steps", steps)
        object.__setattr__(self, "growth", growth)
        object.__setattr__(
            self,
            "innovation",
            tuple(int(v) % (1 << bits) for v in self.innovation),
        )
        object.__setattr__(self, "compositions", c)

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def end_parity(self) -> int:
        return self.start_parity ^ (self.growth & 1)

    @property
    def no_growth(self) -> int:
        return self.steps - self.growth

    @property
    def linear(self) -> ReverseAddSymmetryLinearAction:
        return ReverseAddSymmetryLinearAction(
            self.order,
            self.bits,
            self.no_growth,
            self.growth,
        )

    @property
    def multiplier_residue(self) -> tuple[int, ...]:
        return self.linear.multiplier_residue(self.start_parity)

    @property
    def source_annihilated(self) -> bool:
        return not any(self.multiplier_residue)

    def _template(self) -> CyclotomicDigitBlock:
        return CyclotomicDigitBlock.identity(self.order, self.modulus)

    def affine_morphism(self) -> CyclotomicAffineMorphism:
        return CyclotomicAffineMorphism.from_residues(
            self._template(),
            self.multiplier_residue,
            self.innovation,
        )

    @classmethod
    def identity(
        cls,
        *,
        start_parity: int,
        order: int,
        bits: int,
    ) -> "ReverseAddSymmetryInnovationBlock":
        template = CyclotomicDigitBlock.identity(int(order), 1 << int(bits))
        return cls(
            int(order),
            int(bits),
            int(start_parity),
            0,
            0,
            (0,) * template.degree,
            0,
        )

    @classmethod
    def atom(
        cls,
        event: Sequence[int],
        growth: int,
        *,
        source_width: int,
        order: int,
        bits: int,
    ) -> "ReverseAddSymmetryInnovationBlock":
        g, width = int(growth), int(source_width)
        row = tuple(map(int, event))
        if g not in (0, 1) or width <= 0 or len(row) != width + g:
            raise ValueError((width, g, len(row)))
        projection = ReverseAddSymmetryProjection.from_coefficients(
            row,
            order=int(order),
            bits=int(bits),
        )
        return cls(
            int(order),
            int(bits),
            width & 1,
            1,
            g,
            projection.residue,
            0,
        )

    @classmethod
    def from_events(
        cls,
        events: Sequence[Sequence[int]],
        growths: Sequence[int],
        *,
        order: int,
        bits: int,
        start_width: int | None = None,
    ) -> "ReverseAddSymmetryInnovationBlock":
        rows = tuple(tuple(map(int, row)) for row in events)
        gs = tuple(map(int, growths))
        if len(rows) != len(gs):
            raise ValueError((len(rows), len(gs)))
        if not rows:
            if start_width is None or int(start_width) <= 0:
                raise ValueError("empty symmetry block requires start_width")
            return cls.identity(
                start_parity=int(start_width) & 1,
                order=int(order),
                bits=int(bits),
            )
        inferred = len(rows[0]) - gs[0]
        width = inferred if start_width is None else int(start_width)
        if width != inferred or width <= 0:
            raise ValueError((width, inferred))
        out = cls.identity(start_parity=width & 1, order=int(order), bits=int(bits))
        for event, growth in zip(rows, gs, strict=True):
            atom = cls.atom(
                event,
                growth,
                source_width=width,
                order=int(order),
                bits=int(bits),
            )
            out = out.then(atom)
            width += growth
        return out

    def then(
        self, other: "ReverseAddSymmetryInnovationBlock"
    ) -> "ReverseAddSymmetryInnovationBlock":
        if (self.order, self.bits) != (other.order, other.bits):
            raise ValueError(((self.order, self.bits), (other.order, other.bits)))
        if self.end_parity != other.start_parity:
            raise ValueError((self.end_parity, other.start_parity))
        composed = self.affine_morphism().then(other.affine_morphism())
        total = ReverseAddSymmetryInnovationBlock(
            self.order,
            self.bits,
            self.start_parity,
            self.steps + other.steps,
            self.growth + other.growth,
            composed.addend,
            self.compositions + other.compositions + 1,
        )
        if composed.multiplier != total.multiplier_residue:
            raise AssertionError(
                "symmetry-frame counts disagree with affine composition"
            )
        return total

    def power_block(self, exponent: int) -> "ReverseAddSymmetryInnovationBlock":
        """Binary-power a frame-preserving affine block.

        A block with odd growth flips the parity sector.  One sector-specific
        addend is then insufficient to define its second application, so that
        case is rejected rather than inventing an alternate-sector forcing term.
        """
        n = int(exponent)
        if n < 0:
            raise ValueError(n)
        if self.growth & 1 and n > 1:
            raise ValueError(
                "frame-flipping symmetry block needs a paired-sector addend before self-power"
            )
        identity = self.identity(
            start_parity=self.start_parity,
            order=self.order,
            bits=self.bits,
        )
        base = ReverseAddSymmetryInnovationBlock(
            self.order,
            self.bits,
            self.start_parity,
            self.steps,
            self.growth,
            self.innovation,
            0,
        )
        powered = binary_power(
            base, n, identity=identity, compose=ReverseAddSymmetryInnovationBlock.then
        )
        result = powered.value
        return ReverseAddSymmetryInnovationBlock(
            result.order,
            result.bits,
            result.start_parity,
            result.steps,
            result.growth,
            result.innovation,
            powered.compositions,
        )

    @property
    def fixed_innovation(self) -> tuple[int, ...]:
        return _fixed_coordinates(self.innovation, self.modulus)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-add-symmetry-innovation",
            self.order,
            self.bits,
            self.start_parity,
            self.linear.canonical_key,
            self.fixed_innovation,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.order)
            + bit_width(self.bits)
            + 1
            + bit_width(self.steps)
            + bit_width(self.growth)
            + _fixed_description_bits(len(self.innovation), self.bits)
        )


__all__ = [
    "ReverseAddSymmetryProjection",
    "FixedRealCyclotomicGerm",
    "ReverseAddSymmetryLinearAction",
    "ReverseAddSymmetryInnovationBlock",
]
