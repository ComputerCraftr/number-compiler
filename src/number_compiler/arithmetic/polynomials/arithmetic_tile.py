"""Canonical cyclic/negacyclic binary square-and-carry tile.

The tile owns one source digit polynomial in :class:`CyclotomicDigitBlock`.
Its boundary polynomial is ``X**width-sign``: ``sign=1`` is the cyclic
Mersenne quotient and ``sign=-1`` is the negacyclic Fermat quotient.  A step
uses the shared adaptive convolution and scalar end-around carry owners.

This is a spatial arithmetic carrier.  Repeated nonlinear squaring is still
executed one step at a time; no temporal scheduler certificate exists for
these recurrences yet, so scheduler composition is reported as zero.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.carry.carry_normalization import (
    EndAroundCarryNormalization,
    RadixCarryAction,
    RadixCarryBlock,
    normalization_digits_lsf,
    normalization_carry_boundaries,
    normalize_cyclic_block,
    normalize_negacyclic_block,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.morphism_core import (
    QuadraticPower,
    binary_power,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    ConvolutionMetrics,
    adaptive_square_convolution,
    binary_square_sign_representative,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
    CyclotomicDigitBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_carry import (
    CarryCyclotomicTransducer,
)
from number_compiler.arithmetic.polynomials.folded_square_packet import (
    FoldedSquareProjection,
    folded_square_packet as project_folded_square_packet,
)
from number_compiler.arithmetic.polynomials.radix64_mirror import (
    FoldedFifthProjection,
    folded_fifth_residue as project_folded_fifth_residue,
)


@dataclass(frozen=True, slots=True)
class SquarePrecisionMap:
    """Coefficient precision for forward squaring, unrelated to inverse 3."""

    bits: int

    def __post_init__(self) -> None:
        if (
            not isinstance(self.bits, int)
            or isinstance(self.bits, bool)
            or self.bits <= 0
        ):
            raise ValueError(self.bits)

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def canonical_key(self) -> tuple[str, int]:
        return ("square-forward-precision", self.bits)


@dataclass(frozen=True, slots=True)
class ArithmeticTileSpec:
    """Minimal family parameters; all ring data is derived."""

    family: str
    width: int

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne") or self.width < 2:
            raise ValueError((self.family, self.width))

    @classmethod
    def fermat(cls, width: int) -> "ArithmeticTileSpec":
        return cls("fermat", int(width))

    @classmethod
    def mersenne(cls, width: int) -> "ArithmeticTileSpec":
        return cls("mersenne", int(width))

    @property
    def boundary_sign(self) -> int:
        return -1 if self.family == "fermat" else 1

    @property
    def addend(self) -> int:
        return 0 if self.family == "fermat" else -2

    @property
    def modulus(self) -> int:
        return (1 << self.width) - self.boundary_sign

    @property
    def angular_order(self) -> int:
        return 2 * self.width if self.boundary_sign == -1 else self.width

    @property
    def precision(self) -> SquarePrecisionMap:
        bound = 2 * (self.width + abs(self.addend) + 1)
        return SquarePrecisionMap(bound.bit_length())

    @property
    def boundary_factor(self) -> tuple[int, ...]:
        return (-self.boundary_sign,) + (0,) * (self.width - 1) + (1,)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("arithmetic-square-spec", self.family, self.width)

    def block(self, coefficients: tuple[int, ...]) -> CyclotomicDigitBlock:
        if len(coefficients) != self.width:
            raise ValueError((len(coefficients), self.width))
        return CyclotomicDigitBlock.from_coefficients(
            coefficients,
            order=self.angular_order,
            modulus=self.precision.modulus,
            length=self.width,
            factor=self.boundary_factor,
        )


@dataclass(frozen=True, slots=True)
class ArithmeticTileStep:
    tile: "ArithmeticTile"
    normalization: EndAroundCarryNormalization
    convolution: ConvolutionMetrics
    naive_scalar_products: int
    sign_quotient_applied: bool
    nonzero_digits_saved: int

    def boundary_action(
        self, *, incoming_min: int, incoming_max: int
    ) -> RadixCarryAction:
        """Return the demanded extensional carry action of the folded product."""
        return RadixCarryAction.from_block(
            self.normalization.block,
            incoming_min=int(incoming_min),
            incoming_max=int(incoming_max),
        )


@dataclass(frozen=True, slots=True)
class ArithmeticTileMetrics:
    primitive_steps: int = 0
    scalar_multiplications: int = 0
    naive_scalar_products: int = 0
    coefficient_additions: int = 0
    recursive_nodes: int = 0
    max_boundary_bits: int = 0
    exceptional_minus_one_steps: int = 0
    karatsuba_steps: int = 0
    schoolbook_steps: int = 0
    sign_quotient_steps: int = 0
    sign_quotient_nonzero_digits_saved: int = 0
    scheduler_compositions: int = 0

    def add(self, step: ArithmeticTileStep) -> "ArithmeticTileMetrics":
        convolution = step.convolution
        return ArithmeticTileMetrics(
            self.primitive_steps + 1,
            self.scalar_multiplications + convolution.scalar_multiplications,
            self.naive_scalar_products + step.naive_scalar_products,
            self.coefficient_additions + convolution.coefficient_additions,
            self.recursive_nodes + convolution.recursive_nodes,
            max(self.max_boundary_bits, step.normalization.boundary_bits),
            self.exceptional_minus_one_steps
            + int(step.normalization.exceptional_minus_one),
            self.karatsuba_steps + int(convolution.algorithm == "karatsuba"),
            self.schoolbook_steps + int(convolution.algorithm == "schoolbook"),
            self.sign_quotient_steps + int(step.sign_quotient_applied),
            self.sign_quotient_nonzero_digits_saved + step.nonzero_digits_saved,
            0,
        )


@dataclass(frozen=True, slots=True)
class ArithmeticTileRun:
    tile: "ArithmeticTile"
    metrics: ArithmeticTileMetrics

    @property
    def residue(self) -> int:
        return self.tile.residue

    @property
    def primitive_steps(self) -> int:
        return self.metrics.primitive_steps


@dataclass(frozen=True, slots=True)
class SquareTileAction:
    """Shared composed temporal depth for square and trace-square coordinates.

    This action composes logarithmically, but applying it to the trace
    coordinate still performs ``span`` primitive trace squares.  Its
    ``compositions`` counter records only structural binary composition and
    must not be interpreted as a finite scheduler certificate.
    """

    family: str
    endpoint_power: QuadraticPower = QuadraticPower.identity()
    compositions: int = field(default=0, compare=False)

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne") or self.compositions < 0:
            raise ValueError((self.family, self.compositions))

    @classmethod
    def identity(cls, family: str) -> "SquareTileAction":
        return cls(str(family))

    @classmethod
    def atom(cls, family: str) -> "SquareTileAction":
        return cls(str(family), QuadraticPower.atom())

    @property
    def span(self) -> int:
        return self.endpoint_power.depth

    def then(self, other: "SquareTileAction") -> "SquareTileAction":
        if not isinstance(other, SquareTileAction):
            raise TypeError(type(other))
        if self.family != other.family:
            raise ValueError((self.family, other.family))
        return SquareTileAction(
            self.family,
            self.endpoint_power.then(other.endpoint_power),
            self.compositions + other.compositions + 1,
        )

    def power_block(self, exponent: int) -> "SquareTileAction":
        exponent = int(exponent)
        if exponent < 0:
            raise ValueError(exponent)
        base = SquareTileAction(self.family, self.endpoint_power)
        powered = binary_power(
            base,
            exponent,
            identity=SquareTileAction.identity(self.family),
            compose=SquareTileAction.then,
        )
        value = powered.value
        return SquareTileAction(
            value.family, value.endpoint_power, powered.compositions
        )

    def apply(self, value: int, modulus: int) -> int:
        if self.family == "fermat":
            return self.endpoint_power.apply_multiplicative(value, modulus)
        return self.endpoint_power.apply_trace(value, modulus)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # Keep the established semantic key while moving the implementation to
        # the shared arithmetic owner.
        return ("special-germ-transfer", self.family, self.span)


@dataclass(frozen=True, slots=True)
class ArithmeticTile:
    """One canonical digit block and its derived special-number ring spec."""

    spec: ArithmeticTileSpec
    block: CyclotomicDigitBlock

    def __post_init__(self) -> None:
        expected = self.spec.block((0,) * self.spec.width)
        if (
            self.block.module_key != expected.module_key
            or self.block.length != self.spec.width
        ):
            raise ValueError((self.block.module_key, expected.module_key))
        coefficients = _signed_lift(self.block.residue, self.spec.precision.modulus)
        value = (
            sum(coefficient << index for index, coefficient in enumerate(coefficients))
            % self.spec.modulus
        )
        canonical = self.spec.block(_representative_digits(value, self.spec))
        if self.block.residue != canonical.residue:
            raise ValueError("noncanonical arithmetic tile digit block")

    @classmethod
    def from_value(cls, spec: ArithmeticTileSpec, value: int) -> "ArithmeticTile":
        value = int(value) % spec.modulus
        return cls(spec, spec.block(_representative_digits(value, spec)))

    @property
    def residue(self) -> int:
        coefficients = _signed_lift(self.block.residue, self.spec.precision.modulus)
        return (
            sum(value << index for index, value in enumerate(coefficients))
            % self.spec.modulus
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("arithmetic-square-tile", self.spec.canonical_key, self.block.residue)

    def angular_view(
        self, *, modulus: int, order: int | None = None, power: int = 1
    ) -> CyclotomicDigitBlock:
        """Project canonical digits into a demanded cyclotomic observer.

        The tile's explicit factor is the full boundary polynomial, not an
        irreducible finite-field factor.  Angular and primary consumers must
        request this separate standard cyclotomic block before splitting it.
        """
        order = self.spec.angular_order if order is None else int(order)
        digits = _representative_digits(self.residue, self.spec)
        return CyclotomicDigitBlock.from_coefficients(
            digits,
            order=order,
            modulus=int(modulus),
            power=int(power),
            length=self.spec.width,
        )

    def step(self) -> ArithmeticTileStep:
        step, _field = self._step_with_field()
        return step

    def folded_square_packet(self) -> FoldedSquareProjection:
        """Read two square residues without stepping or decoding the integer.

        The coefficient precision is a multiple of eight, so the stored
        representatives give the same packet as their signed lifts. This is
        an arithmetic projection, not an admitted primality certificate.
        """
        return project_folded_square_packet(
            self.block.residue, sign=self.spec.boundary_sign
        )

    def folded_fifth_residue(self) -> FoldedFifthProjection:
        """Observe a binary tile's transient radix-64 mirror residue.

        Exceptional signed charts are outside this binary observation. Zero
        does not certify support; no temporal identity or history is refined.
        """
        return project_folded_fifth_residue(
            self.block.residue, sign=self.spec.boundary_sign
        )

    def step_with_harmonic_consumer(
        self,
        *,
        incoming_min: int,
        incoming_max: int,
        order: int,
        modulus: int,
    ) -> tuple[ArithmeticTileStep, CarryCyclotomicTransducer]:
        """Execute once and quotient its transient field into demanded actions."""
        step, field = self._step_with_field()
        harmonic = CarryCyclotomicTransducer.from_coefficients(
            field,
            base=2,
            incoming_min=int(incoming_min),
            incoming_max=int(incoming_max),
            order=int(order),
            modulus=int(modulus),
        )
        return step, harmonic

    def step_with_carry_interval(
        self,
    ) -> tuple[ArithmeticTileStep, tuple[int, int]]:
        """Execute once and derive the internal carry port only on demand."""
        step, field = self._step_with_field()
        boundaries = normalization_carry_boundaries(field, step.normalization)
        return step, (min(boundaries), max(boundaries))

    def _step_with_field(self) -> tuple[ArithmeticTileStep, tuple[int, ...]]:
        value = self.residue
        representative = binary_square_sign_representative(
            value, self.spec.width, self.spec.boundary_sign
        )
        original_digits = _representative_digits(value, self.spec)
        digits = _representative_digits(representative, self.spec)
        product, convolution = adaptive_square_convolution(digits)
        raw = list(product)
        if not raw:
            raw = [0]
        raw[0] += self.spec.addend
        folded_mod = self.block.ring.reduce(raw)
        field = _signed_lift(folded_mod, self.spec.precision.modulus)
        carry = RadixCarryBlock.from_coefficients(field, base=2)
        normalization = (
            normalize_cyclic_block(carry)
            if self.spec.boundary_sign == 1
            else normalize_negacyclic_block(carry)
        )
        next_tile = ArithmeticTile(
            self.spec,
            self.spec.block(normalization_digits_lsf(normalization)),
        )
        if next_tile.residue != normalization.residue:
            raise AssertionError((next_tile.residue, normalization.residue))
        original_weight = sum(int(digit != 0) for digit in original_digits)
        weight = sum(int(digit != 0) for digit in digits)
        return (
            ArithmeticTileStep(
                next_tile,
                normalization,
                convolution,
                weight * weight,
                representative != value,
                max(0, original_weight - weight),
            ),
            field,
        )

    def run(self, steps: int) -> ArithmeticTileRun:
        count = int(steps)
        if count < 0:
            raise ValueError(count)
        tile = self
        metrics = ArithmeticTileMetrics()
        for _ in range(count):
            result = tile.step()
            tile = result.tile
            metrics = metrics.add(result)
        return ArithmeticTileRun(tile, metrics)


def _signed_lift(values: tuple[int, ...], modulus: int) -> tuple[int, ...]:
    half = modulus // 2
    return tuple(value if value <= half else value - modulus for value in values)


def _representative_digits(value: int, spec: ArithmeticTileSpec) -> tuple[int, ...]:
    scale = 1 << spec.width
    if spec.boundary_sign == -1 and value == scale:
        return (-1,) + (0,) * (spec.width - 1)
    if not 0 <= value < scale:
        raise ValueError((value, spec.width, spec.boundary_sign))
    return tuple(digits_lsd(value, 2, spec.width))


__all__ = [
    "ArithmeticTile",
    "ArithmeticTileMetrics",
    "ArithmeticTileRun",
    "ArithmeticTileSpec",
    "ArithmeticTileStep",
    "SquareTileAction",
    "SquarePrecisionMap",
]
