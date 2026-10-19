"""Radial-mode quotients for affine sequence transports.

The sequence families in this repository often have a large predictable
multiplicative mode and a much smaller innovation term.  Retaining the large
coefficient itself is duplicate state: its valuation/exponent is enough, while
future semantics depend on the additive forcing cocycle and a bounded unit or
cyclotomic phase.

This module owns the reverse-add instance of that pattern.  Collatz already
uses the generic :mod:`number_compiler.arithmetic.fields.adic_morphism` implementation; its exact
``3**H / 2**K`` scale is exposed through ``PadicAffineMorphism.radial_quotient``.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
    CyclotomicAffineMorphism,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


@dataclass(frozen=True, slots=True)
class InnovationID(ArenaHandle):
    """Scoped arithmetic identity; source authority is deliberately absent."""

    seal: str = ""


@dataclass(frozen=True, slots=True)
class RadialMultiplier:
    """The unexpanded multiplier ``2**no_growth * (1+z)**growth``."""

    no_growth: int = 0
    growth: int = 0

    def __post_init__(self) -> None:
        if type(self.no_growth) is not int or type(self.growth) is not int:
            raise TypeError("radial exponents must be exact integers")
        if self.no_growth < 0 or self.growth < 0:
            raise ValueError("radial exponents must be nonnegative")

    @property
    def is_identity(self) -> bool:
        return self.no_growth == self.growth == 0

    def then(self, after: RadialMultiplier) -> RadialMultiplier:
        if type(after) is not RadialMultiplier:
            raise TypeError("radial composition requires a radial multiplier")
        self.__post_init__()
        after.__post_init__()
        return RadialMultiplier(
            self.no_growth + after.no_growth,
            self.growth + after.growth,
        )


@dataclass(frozen=True, slots=True)
class InnovationZero:
    pass


@dataclass(frozen=True, slots=True)
class InnovationAtom:
    semantic: SemanticIdentity


@dataclass(frozen=True, slots=True)
class InnovationInterval:
    """The exact window ``E_m = 1 + z + ... + z**(m-1)``."""

    length: int


@dataclass(frozen=True, slots=True)
class InnovationRadial:
    multiplier: RadialMultiplier
    child: InnovationID


@dataclass(frozen=True, slots=True)
class InnovationCharted:
    chart: CylinderChart
    child: InnovationID


@dataclass(frozen=True, slots=True)
class InnovationScale:
    coefficient: int
    child: InnovationID


@dataclass(frozen=True, slots=True)
class InnovationAdd:
    left: InnovationID
    right: InnovationID


InnovationNode: TypeAlias = (
    InnovationZero
    | InnovationAtom
    | InnovationInterval
    | InnovationRadial
    | InnovationCharted
    | InnovationScale
    | InnovationAdd
)


@dataclass(frozen=True, slots=True)
class SymbolicRadialInnovation:
    """One source-free affine arithmetic component ``(M, B)``."""

    multiplier: RadialMultiplier
    innovation: InnovationID


@dataclass(frozen=True, slots=True)
class ReverseWidthPhase:
    """Decimal extent observed ONLY through its F5 and parity coordinates.

    This quotient does not recover an exact width or certify a future seam.
    Exact extent and source authority belong to the admitted occurrence.
    """

    phase: int

    def __post_init__(self) -> None:
        if type(self.phase) is not int or not 0 <= self.phase < 10:
            raise ValueError("reverse width phase must lie in Z/10")

    @classmethod
    def from_extent(cls, extent: int) -> ReverseWidthPhase:
        if type(extent) is not int or extent <= 0:
            raise ValueError("reverse active extent must be a positive integer")
        return cls(extent % 10)

    @property
    def observable(self) -> tuple[int, int]:
        self.__post_init__()
        return self.phase % 5, self.phase % 2

    def apply(self, action: ReverseWidthPhaseAction) -> ReverseWidthPhase:
        self.__post_init__()
        if type(action) is not ReverseWidthPhaseAction:
            raise TypeError("reverse width phase requires a width action")
        action.__post_init__()
        return ReverseWidthPhase((self.phase + action.delta) % 10)

    def reflection_offset(self, *, terminal_growth: int = 0) -> int:
        """The reflected input chart after one admitted terminal growth bit."""
        self.__post_init__()
        if type(terminal_growth) is not int or terminal_growth not in (0, 1):
            raise ValueError("reverse terminal growth must be an exact bit")
        return (self.phase + terminal_growth - 1) % 10


@dataclass(frozen=True, slots=True)
class ReverseWidthPhaseAction:
    """Translation by an ALREADY established growth count modulo ten.

    This is a finite observer action, not an exact return or a growth-count
    constructor. Equal deltas never authorize substituting successor images.
    """

    delta: int

    def __post_init__(self) -> None:
        if type(self.delta) is not int or not 0 <= self.delta < 10:
            raise ValueError("reverse width action must lie in Z/10")

    @classmethod
    def from_growth_count(cls, growth_count: int) -> ReverseWidthPhaseAction:
        if type(growth_count) is not int or growth_count < 0:
            raise ValueError("reverse growth count must be a nonnegative integer")
        return cls(growth_count % 10)

    def then(self, after: ReverseWidthPhaseAction) -> ReverseWidthPhaseAction:
        self.__post_init__()
        if type(after) is not ReverseWidthPhaseAction:
            raise TypeError("reverse width composition requires a width action")
        after.__post_init__()
        return ReverseWidthPhaseAction((self.delta + after.delta) % 10)

    def power(self, repetitions: int) -> ReverseWidthPhaseAction:
        self.__post_init__()
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("width repetitions must be a nonnegative integer")
        return ReverseWidthPhaseAction(self.delta * (repetitions % 10) % 10)


def normalize_event_schedule(
    events: Sequence[Sequence[int]], growths: Sequence[int]
) -> tuple[tuple[tuple[int, ...], ...], tuple[int, ...]]:
    """Normalize one finite coefficient forcing schedule and preserve its pairing."""
    rows = tuple(tuple(map(int, row)) for row in events)
    gs = tuple(map(int, growths))
    if len(rows) != len(gs):
        raise ValueError((len(rows), len(gs)))
    return rows, gs


@dataclass(frozen=True, slots=True)
class ReverseAddCyclotomicInnovationBlock:
    """Exact affine reverse-add block in one power-of-two cyclotomic factor.

    For a block containing ``q`` no-growth and ``r`` growth transitions,

    ``S_out = 2**q (1+z)**r S_in + B``.

    Only ``B`` is retained as the nonlinear innovation.  The multiplier is
    reconstructed from the two scalar counts and can be split into its radial
    valuation/unit phase with :attr:`radial`.  This avoids retaining a carry
    history or a second full pair field.
    """

    order: int
    bits: int
    steps: int
    growth: int
    innovation: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        order, bits = int(self.order), int(self.bits)
        steps, growth = int(self.steps), int(self.growth)
        if order < 2 or order & (order - 1) or bits <= 0:
            raise ValueError((order, bits))
        if steps < 0 or not 0 <= growth <= steps or int(self.compositions) < 0:
            raise ValueError(self)
        template = CyclotomicDigitBlock.identity(order, 1 << bits)
        if len(self.innovation) != template.degree:
            raise ValueError((len(self.innovation), template.degree))
        modulus = 1 << bits
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "bits", bits)
        object.__setattr__(self, "steps", steps)
        object.__setattr__(self, "growth", growth)
        object.__setattr__(
            self, "innovation", tuple(int(v) % modulus for v in self.innovation)
        )
        object.__setattr__(self, "compositions", int(self.compositions))

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def classes(self) -> int:
        return self.order // 2

    @property
    def width_phase_action(self) -> ReverseWidthPhaseAction:
        """Project this block's supplied growth; grants no source admission."""
        return ReverseWidthPhaseAction.from_growth_count(self.growth)

    @property
    def no_growth(self) -> int:
        return self.steps - self.growth

    def _template(self) -> CyclotomicDigitBlock:
        return CyclotomicDigitBlock.identity(self.order, self.modulus)

    @classmethod
    def identity(cls, *, order: int, bits: int) -> ReverseAddCyclotomicInnovationBlock:
        template = CyclotomicDigitBlock.identity(int(order), 1 << int(bits))
        return cls(int(order), int(bits), 0, 0, (0,) * template.degree, 0)

    @classmethod
    def atom(
        cls,
        event: Sequence[int],
        growth: int,
        *,
        order: int,
        bits: int,
    ) -> ReverseAddCyclotomicInnovationBlock:
        g = int(growth)
        if g not in (0, 1):
            raise ValueError(g)
        block = CyclotomicDigitBlock.from_coefficients(
            tuple(map(int, event)),
            order=int(order),
            modulus=1 << int(bits),
        )
        return cls(int(order), int(bits), 1, g, block.residue, 0)

    @classmethod
    def from_events(
        cls,
        events: Sequence[Sequence[int]],
        growths: Sequence[int],
        *,
        order: int,
        bits: int,
    ) -> ReverseAddCyclotomicInnovationBlock:
        rows, gs = normalize_event_schedule(events, growths)
        out = cls.identity(order=int(order), bits=int(bits))
        for event, growth in zip(rows, gs, strict=True):
            out = out.then(cls.atom(event, growth, order=int(order), bits=int(bits)))
        return out

    @property
    def radial(self) -> PowerTwoCyclotomicRadialQuotient:
        return power_two_cyclotomic_radial_quotient(
            self.classes,
            self.no_growth,
            self.growth,
            bits=self.bits,
        )

    @property
    def source_annihilated(self) -> bool:
        return self.radial.annihilated

    def linear_morphism(self) -> CyclotomicAffineMorphism:
        template = self._template()
        multiplier = self.radial.multiplier_residue()
        return CyclotomicAffineMorphism.from_residues(
            template,
            multiplier,
            (0,) * template.degree,
        )

    def affine_morphism(self) -> CyclotomicAffineMorphism:
        template = self._template()
        return CyclotomicAffineMorphism.from_residues(
            template,
            self.radial.multiplier_residue(),
            self.innovation,
        )

    def then(
        self, other: ReverseAddCyclotomicInnovationBlock
    ) -> ReverseAddCyclotomicInnovationBlock:
        if (self.order, self.bits) != (other.order, other.bits):
            raise ValueError(((self.order, self.bits), (other.order, other.bits)))
        composed = self.affine_morphism().then(other.affine_morphism())
        total = ReverseAddCyclotomicInnovationBlock(
            self.order,
            self.bits,
            self.steps + other.steps,
            self.growth + other.growth,
            composed.addend,
            self.compositions + other.compositions + 1,
        )
        if composed.multiplier != total.radial.multiplier_residue():
            raise AssertionError("radial counts disagree with affine composition")
        return total

    def power_block(self, exponent: int) -> ReverseAddCyclotomicInnovationBlock:
        identity = ReverseAddCyclotomicInnovationBlock.identity(
            order=self.order, bits=self.bits
        )
        base = ReverseAddCyclotomicInnovationBlock(
            self.order,
            self.bits,
            self.steps,
            self.growth,
            self.innovation,
            0,
        )
        powered = binary_power(
            base,
            exponent,
            identity=identity,
            compose=ReverseAddCyclotomicInnovationBlock.then,
        )
        result = powered.value
        return ReverseAddCyclotomicInnovationBlock(
            result.order,
            result.bits,
            result.steps,
            result.growth,
            result.innovation,
            powered.compositions,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # The large radial multiplier is represented only through its exact
        # quotient key.  Construction provenance and carry/event histories are
        # deliberately absent.
        return (
            "reverse-add-cyclotomic-innovation",
            self.order,
            self.bits,
            self.radial.canonical_key,
            self.innovation,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.order)
            + bit_width(self.bits)
            + bit_width(self.steps)
            + bit_width(self.growth)
            + sum(bit_width(v) for v in self.innovation)
        )


__all__ = [
    "InnovationAdd",
    "InnovationAtom",
    "InnovationCharted",
    "InnovationID",
    "InnovationInterval",
    "InnovationNode",
    "InnovationRadial",
    "InnovationScale",
    "InnovationZero",
    "RadialMultiplier",
    "ReverseAddCyclotomicInnovationBlock",
    "ReverseWidthPhase",
    "ReverseWidthPhaseAction",
    "SymbolicRadialInnovation",
]
