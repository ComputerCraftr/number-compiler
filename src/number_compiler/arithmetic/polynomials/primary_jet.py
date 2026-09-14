"""Canonical ``(z+1)``-primary digit-field blocks.

This is a cross-family theorem interface, not a semantic integer state.  A
little-endian radix word ``d_0,d_1,...`` represents the polynomial

    D(z) = sum_i d_i z**i.

Put ``y=z+1`` and truncate modulo ``(y**degree, modulus)``.  A block retains
only

    (length, z**length, D(z))

in that quotient.  Concatenation is associative, and repeated runs are powered
by squaring, so sparse Fermat/Mersenne words and other RLE digit programs never
need one operation per represented digit merely to construct the primary jet.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.program_word import CanonicalWord, iter_runs
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.radix import bit_width


def _validate_poly(values: Sequence[int], degree: int, modulus: int) -> tuple[int, ...]:
    degree, modulus = int(degree), int(modulus)
    if degree <= 0 or modulus <= 1:
        raise ValueError((degree, modulus))
    vals = tuple(int(v) % modulus for v in values)
    if len(vals) != degree:
        raise ValueError((len(vals), degree))
    return vals


def _poly_add(a: Sequence[int], b: Sequence[int], modulus: int) -> tuple[int, ...]:
    if len(a) != len(b):
        raise ValueError((len(a), len(b)))
    m = int(modulus)
    return tuple((int(x) + int(y)) % m for x, y in zip(a, b))


def _poly_scale(a: Sequence[int], scalar: int, modulus: int) -> tuple[int, ...]:
    m = int(modulus)
    s = int(scalar) % m
    return tuple((s * int(x)) % m for x in a)


def _poly_mul(a: Sequence[int], b: Sequence[int], modulus: int) -> tuple[int, ...]:
    """Multiply modulo ``y**degree`` and coefficient ``modulus``."""
    if len(a) != len(b):
        raise ValueError((len(a), len(b)))
    degree = len(a)
    m = int(modulus)
    out = [0] * degree
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b[: degree - i]):
            if y:
                out[i + j] = (out[i + j] + int(x) * int(y)) % m
    return tuple(out)


def _one(degree: int) -> tuple[int, ...]:
    return (1,) + (0,) * (int(degree) - 1)


def _z(degree: int, modulus: int) -> tuple[int, ...]:
    """``z=y-1`` in the primary coordinate."""
    degree, modulus = int(degree), int(modulus)
    out = [0] * degree
    out[0] = (-1) % modulus
    if degree > 1:
        out[1] = 1
    return tuple(out)


@dataclass(frozen=True, slots=True)
class PrimaryJetBlock:
    """Associative primary-jet block for a little-endian digit substring."""

    degree: int
    modulus: int
    length: int
    power: tuple[int, ...]
    jet: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        if (
            self.degree <= 0
            or self.modulus <= 1
            or self.length < 0
            or self.compositions < 0
        ):
            raise ValueError(self)
        object.__setattr__(
            self, "power", _validate_poly(self.power, self.degree, self.modulus)
        )
        object.__setattr__(
            self, "jet", _validate_poly(self.jet, self.degree, self.modulus)
        )

    @classmethod
    def identity(cls, degree: int, modulus: int) -> PrimaryJetBlock:
        degree, modulus = int(degree), int(modulus)
        return cls(degree, modulus, 0, _one(degree), (0,) * degree, 0)

    @classmethod
    def digit(cls, digit: int, *, degree: int, modulus: int) -> PrimaryJetBlock:
        degree, modulus = int(degree), int(modulus)
        return cls(
            degree,
            modulus,
            1,
            _z(degree, modulus),
            (int(digit) % modulus,) + (0,) * (degree - 1),
            0,
        )

    def then(self, higher: PrimaryJetBlock) -> PrimaryJetBlock:
        """Place ``higher`` immediately above this lower-position block."""
        if (self.degree, self.modulus) != (higher.degree, higher.modulus):
            raise ValueError("incompatible primary jets")
        shifted = _poly_mul(self.power, higher.jet, self.modulus)
        return PrimaryJetBlock(
            self.degree,
            self.modulus,
            self.length + higher.length,
            _poly_mul(self.power, higher.power, self.modulus),
            _poly_add(self.jet, shifted, self.modulus),
            self.compositions + higher.compositions + 1,
        )

    def _then_raw(self, higher: PrimaryJetBlock) -> PrimaryJetBlock:
        if (self.degree, self.modulus) != (higher.degree, higher.modulus):
            raise ValueError("incompatible primary jets")
        shifted = _poly_mul(self.power, higher.jet, self.modulus)
        return PrimaryJetBlock(
            self.degree,
            self.modulus,
            self.length + higher.length,
            _poly_mul(self.power, higher.power, self.modulus),
            _poly_add(self.jet, shifted, self.modulus),
            0,
        )

    def power_block(self, exponent: int) -> PrimaryJetBlock:
        """Repeat this block through the repository-wide binary power kernel."""
        base = PrimaryJetBlock(
            self.degree, self.modulus, self.length, self.power, self.jet, 0
        )
        powered = binary_power(
            base,
            exponent,
            identity=PrimaryJetBlock.identity(self.degree, self.modulus),
            compose=PrimaryJetBlock._then_raw,
        )
        result = powered.value
        return PrimaryJetBlock(
            result.degree,
            result.modulus,
            result.length,
            result.power,
            result.jet,
            powered.compositions,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "primary_jet",
            self.degree,
            self.modulus,
            self.length,
            self.power,
            self.jet,
        )

    @property
    def description_bits(self) -> int:
        coeff_bits = max(1, (self.modulus - 1).bit_length())
        return (
            bit_width(self.degree)
            + bit_width(self.modulus)
            + bit_width(self.length)
            + 2 * self.degree * coeff_bits
        )


def primary_jet_from_digits(
    digits_lsf: Sequence[int], *, degree: int = 4, modulus: int = 32
) -> PrimaryJetBlock:
    """Exact primary jet from explicit little-endian digits."""
    out = PrimaryJetBlock.identity(degree, modulus)
    for digit in map(int, digits_lsf):
        out = out.then(PrimaryJetBlock.digit(digit, degree=degree, modulus=modulus))
    return out


def primary_jet_from_runs(
    runs_lsf: Iterable[tuple[int, int]], *, degree: int = 4, modulus: int = 32
) -> PrimaryJetBlock:
    """Exact RLE construction; run lengths are handled by binary powering."""
    out = PrimaryJetBlock.identity(degree, modulus)
    for symbol, count in runs_lsf:
        count = int(count)
        if count < 0:
            raise ValueError(count)
        if count == 0:
            continue
        atom = PrimaryJetBlock.digit(int(symbol), degree=degree, modulus=modulus)
        out = out.then(atom.power_block(count))
    return out


def primary_jet_from_word(
    word: CanonicalWord, *, degree: int = 4, modulus: int = 32
) -> PrimaryJetBlock:
    return primary_jet_from_runs(iter_runs(word), degree=degree, modulus=modulus)


@dataclass(frozen=True, slots=True)
class PrimaryJetAffineMorphism:
    """Affine action ``state -> kernel*state + offset`` in one primary jet.

    Reverse-add event transport is the important instance: no-growth has
    ``kernel=2`` while growth has ``kernel=y``.  Keeping the whole truncated
    kernel makes composition closed, so repeated theorem actions can be powered
    without expanding binomial coefficients.
    """

    degree: int
    modulus: int
    kernel: tuple[int, ...]
    offset: tuple[int, ...]
    steps: int = 0
    compositions: int = 0

    def __post_init__(self) -> None:
        if (
            self.degree <= 0
            or self.modulus <= 1
            or self.steps < 0
            or self.compositions < 0
        ):
            raise ValueError(self)
        object.__setattr__(
            self, "kernel", _validate_poly(self.kernel, self.degree, self.modulus)
        )
        object.__setattr__(
            self, "offset", _validate_poly(self.offset, self.degree, self.modulus)
        )

    @classmethod
    def identity(cls, degree: int, modulus: int) -> PrimaryJetAffineMorphism:
        return cls(
            int(degree), int(modulus), _one(int(degree)), (0,) * int(degree), 0, 0
        )

    @classmethod
    def reverse_add_event(
        cls, event: Sequence[int], growth: int, *, degree: int, modulus: int
    ) -> PrimaryJetAffineMorphism:
        growth = int(growth)
        degree = int(degree)
        modulus = int(modulus)
        if growth not in (0, 1):
            raise ValueError(growth)
        if growth:
            kernel = (0, 1) + (0,) * max(0, degree - 2)
            kernel = kernel[:degree]
        else:
            kernel = (2 % modulus,) + (0,) * (degree - 1)
        offset = primary_jet_from_digits(event, degree=degree, modulus=modulus).jet
        return cls(degree, modulus, kernel, offset, 1, 0)

    @classmethod
    def square_tangent(
        cls,
        base_germ: Sequence[int],
        birth: Sequence[int] = (),
        *,
        degree: int = 5,
        modulus: int = 32,
    ) -> PrimaryJetAffineMorphism:
        """Return the exact first-order transport ``J -> 2*X*J + B``.

        ``X`` and ``B`` are truncated primary germs.  Quadratic ``J**2`` is a
        newly evaluated birth and belongs in ``birth`` when demanded; it is not
        hidden in this linear transport.  At modulus 32, any composition of
        five such tangent maps annihilates the old source regardless of the
        intervening base germs.
        """
        degree, modulus = int(degree), int(modulus)
        base = _validate_poly(base_germ, degree, modulus)
        offset = (
            (0,) * degree if len(birth) == 0 else _validate_poly(birth, degree, modulus)
        )
        return cls(
            degree,
            modulus,
            _poly_scale(base, 2, modulus),
            offset,
            1,
            0,
        )

    def apply(self, state: Sequence[int]) -> tuple[int, ...]:
        state = _validate_poly(state, self.degree, self.modulus)
        return _poly_add(
            _poly_mul(self.kernel, state, self.modulus), self.offset, self.modulus
        )

    @property
    def cocycle(self) -> AffineCocycle[tuple[int, ...]]:
        return AffineCocycle(self.kernel, self.offset)

    @property
    def source_annihilated(self) -> bool:
        """Whether no old primary-jet source can affect this action."""
        return not any(self.kernel)

    def _then_raw(self, other: PrimaryJetAffineMorphism) -> PrimaryJetAffineMorphism:
        if (self.degree, self.modulus) != (other.degree, other.modulus):
            raise ValueError("incompatible primary affine morphisms")
        cocycle = self.cocycle.then(
            other.cocycle,
            multiply=lambda a, b: _poly_mul(a, b, self.modulus),
            add=lambda a, b: _poly_add(a, b, self.modulus),
        )
        return PrimaryJetAffineMorphism(
            self.degree,
            self.modulus,
            cocycle.multiplier,
            cocycle.addend,
            self.steps + other.steps,
            0,
        )

    def then(self, other: PrimaryJetAffineMorphism) -> PrimaryJetAffineMorphism:
        out = self._then_raw(other)
        return PrimaryJetAffineMorphism(
            out.degree,
            out.modulus,
            out.kernel,
            out.offset,
            out.steps,
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> PrimaryJetAffineMorphism:
        base = PrimaryJetAffineMorphism(
            self.degree, self.modulus, self.kernel, self.offset, self.steps, 0
        )
        powered = binary_power(
            base,
            exponent,
            identity=PrimaryJetAffineMorphism.identity(self.degree, self.modulus),
            compose=PrimaryJetAffineMorphism._then_raw,
        )
        result = powered.value
        return PrimaryJetAffineMorphism(
            result.degree,
            result.modulus,
            result.kernel,
            result.offset,
            result.steps,
            powered.compositions,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "primary_jet_affine",
            self.degree,
            self.modulus,
            self.kernel,
            self.offset,
        )


__all__ = [
    "PrimaryJetAffineMorphism",
    "PrimaryJetBlock",
    "primary_jet_from_digits",
    "primary_jet_from_runs",
    "primary_jet_from_word",
]
