"""Branch-independent source bounds for reverse/add Frobenius sectors.

The reverse/add temporal multiplier is ``2**q * (1 + z)**r`` with
``q + r = steps``.  Growth is an executed observation, so a source-independent
temporal action must not pretend to know either count.  It can nevertheless
retain the sharp lower bound ``floor(steps / m)`` in every power-of-two sector
``z**m + 1``.  Reaching the requested precision proves that the old source
coefficient is zero in that sector for every possible branch itinerary.

For the exact symmetric ``BaseBlockEffect`` law in bases at least three, the
outer coefficient also proves that four consecutive growth steps are
impossible.  That certificate supplies the independent uniform bound
``q >= floor(steps / 4)``.  It is attached explicitly; generic sector plans do
not acquire the stronger bound by matching numeric parameters.

These records describe only that source coefficient.  They deliberately have
no innovation, output, carry, digit, or source-binding field.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.polynomials.cyclotomic import is_power_of_two

MAX_REVERSE_FROBENIUS_CLASSES = 8
MAX_REVERSE_FROBENIUS_BITS = 64
_GROWTH_CERTIFICATE_VERSION = "base-block-symmetric-outer-growth-v1"
_MAX_CERTIFIED_GROWTH_BASE = 64
_DECIMAL_OUTER_SUCCESSORS = tuple(
    (symbol, 1 + symbol - 10 * int(symbol >= 10)) for symbol in range(9, 19)
)


def _valid_geometry(classes: int, bits: int, steps: int) -> bool:
    return (
        is_power_of_two(classes)
        and classes <= MAX_REVERSE_FROBENIUS_CLASSES
        and 0 < bits <= MAX_REVERSE_FROBENIUS_BITS
        and steps >= 0
    )


@dataclass(frozen=True, slots=True)
class ReverseGrowthRunCertificate:
    """Finite proof graph for the symmetric outer-coefficient growth bound."""

    base: int
    kernel_behavior: tuple[str, int]
    version: str
    maximum_consecutive_growth: int
    outer_successors: tuple[tuple[int, int], ...]
    requires_symmetric_active_prefix: bool
    initial_carry: int
    normalization_law: str

    def __post_init__(self) -> None:
        if (
            type(self.base) is not int
            or not 3 <= self.base <= _MAX_CERTIFIED_GROWTH_BASE
        ):
            raise ValueError("growth-run certificate requires a bounded exact base>=3")
        expected_edges = tuple(
            (symbol, 1 + symbol - self.base * int(symbol >= self.base))
            for symbol in range(self.base - 1, 2 * self.base - 1)
        )
        if (
            type(self.kernel_behavior) is not tuple
            or self.kernel_behavior != ("base_block", self.base)
            or type(self.kernel_behavior[0]) is not str
            or type(self.kernel_behavior[1]) is not int
            or type(self.version) is not str
            or self.version != _GROWTH_CERTIFICATE_VERSION
            or type(self.maximum_consecutive_growth) is not int
            or self.maximum_consecutive_growth != 3
            or type(self.outer_successors) is not tuple
            or any(
                type(edge) is not tuple
                or len(edge) != 2
                or type(edge[0]) is not int
                or type(edge[1]) is not int
                for edge in self.outer_successors
            )
            or self.outer_successors != expected_edges
            or self.requires_symmetric_active_prefix is not True
            or type(self.initial_carry) is not int
            or self.initial_carry != 0
            or type(self.normalization_law) is not str
            or self.normalization_law != "growth-leading-one-v1"
        ):
            raise ValueError("growth-run certificate differs from the kernel law")
        transitions = dict(expected_edges)
        for initial, _successor in expected_edges:
            state = initial
            for _ in range(self.maximum_consecutive_growth):
                if state < self.base - 1:
                    break
                state = transitions[state]
            if state >= self.base - 1:
                raise ValueError("growth-run proof graph permits four growths")

    @classmethod
    def for_base(cls, base: int) -> ReverseGrowthRunCertificate:
        if type(base) is not int or not 3 <= base <= _MAX_CERTIFIED_GROWTH_BASE:
            raise ValueError("growth-run certificate requires a bounded exact base>=3")
        return cls(
            base,
            ("base_block", base),
            _GROWTH_CERTIFICATE_VERSION,
            3,
            tuple(
                (symbol, 1 + symbol - base * int(symbol >= base))
                for symbol in range(base - 1, 2 * base - 1)
            ),
            True,
            0,
            "growth-leading-one-v1",
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-growth-run-certificate-v1",
            self.base,
            self.kernel_behavior,
            self.version,
            self.maximum_consecutive_growth,
            self.outer_successors,
            self.requires_symmetric_active_prefix,
            self.initial_carry,
            self.normalization_law,
        )


DECIMAL_REVERSE_GROWTH_CERTIFICATE = ReverseGrowthRunCertificate(
    10,
    ("base_block", 10),
    _GROWTH_CERTIFICATE_VERSION,
    3,
    _DECIMAL_OUTER_SUCCESSORS,
    True,
    0,
    "growth-leading-one-v1",
)


def validate_decimal_growth_certificate(
    certificate: object,
) -> None:
    """Validate the issued decimal proof declaration in constant time."""
    if type(certificate) is not ReverseGrowthRunCertificate:
        raise TypeError("decimal growth certificate has another sort")
    if certificate is not DECIMAL_REVERSE_GROWTH_CERTIFICATE:
        raise ValueError("decimal growth certificate was not issued by its kernel")
    if (
        type(certificate.base) is not int
        or certificate.base != 10
        or type(certificate.kernel_behavior) is not tuple
        or certificate.kernel_behavior != ("base_block", 10)
        or type(certificate.kernel_behavior[0]) is not str
        or type(certificate.kernel_behavior[1]) is not int
        or type(certificate.version) is not str
        or certificate.version != _GROWTH_CERTIFICATE_VERSION
        or type(certificate.maximum_consecutive_growth) is not int
        or certificate.maximum_consecutive_growth != 3
        or certificate.outer_successors is not _DECIMAL_OUTER_SUCCESSORS
        or certificate.requires_symmetric_active_prefix is not True
        or type(certificate.initial_carry) is not int
        or certificate.initial_carry != 0
        or type(certificate.normalization_law) is not str
        or certificate.normalization_law != "growth-leading-one-v1"
    ):
        raise ValueError("decimal growth certificate differs from its kernel proof")


@dataclass(frozen=True, slots=True)
class FrobeniusSectorSourceBound:
    """One canonical source-coefficient bound modulo ``(z**m+1, 2**bits)``."""

    classes: int
    bits: int
    steps: int
    uniform_no_growth_lower_bound: int
    valuation_lower_bound: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.classes,
                self.bits,
                self.steps,
                self.uniform_no_growth_lower_bound,
                self.valuation_lower_bound,
            )
        ):
            raise TypeError("Frobenius sector bounds require exact integers")
        if not _valid_geometry(self.classes, self.bits, self.steps):
            raise ValueError("invalid Frobenius sector geometry")
        if not 0 <= self.uniform_no_growth_lower_bound <= self.steps:
            raise ValueError("invalid uniform no-growth lower bound")
        expected = min(
            self.bits,
            max(self.steps // self.classes, self.uniform_no_growth_lower_bound),
        )
        if self.valuation_lower_bound != expected:
            raise ValueError("Frobenius valuation is not the canonical lower bound")

    @classmethod
    def for_steps(
        cls,
        classes: int,
        bits: int,
        steps: int,
        *,
        uniform_no_growth_lower_bound: int = 0,
    ) -> FrobeniusSectorSourceBound:
        if any(type(value) is not int for value in (classes, bits, steps)):
            raise TypeError("Frobenius sector bounds require exact integers")
        if not _valid_geometry(classes, bits, steps):
            raise ValueError("invalid Frobenius sector geometry")
        if (
            type(uniform_no_growth_lower_bound) is not int
            or not 0 <= uniform_no_growth_lower_bound <= steps
        ):
            raise ValueError("invalid uniform no-growth lower bound")
        return cls(
            classes,
            bits,
            steps,
            uniform_no_growth_lower_bound,
            min(bits, max(steps // classes, uniform_no_growth_lower_bound)),
        )

    @property
    def source_annihilated(self) -> bool:
        return self.valuation_lower_bound == self.bits

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-frobenius-source-bound-v2",
            self.classes,
            self.bits,
            self.steps,
            self.uniform_no_growth_lower_bound,
            self.valuation_lower_bound,
        )


@dataclass(frozen=True, slots=True)
class ReverseFrobeniusPlan:
    """Fixed-arity product of all configured power-of-two source sectors.

    ``steps`` is exact exponent metadata.  The tuple length depends only on the
    configured maximum sector and is therefore independent of temporal depth.
    A growth certificate remains conditional on the authenticated symmetric
    active-prefix, initial-carry, and normalization hypotheses recorded in it;
    this plan alone does not prove those occurrence facts.
    """

    maximum_classes: int
    bits: int
    steps: int
    sectors: tuple[FrobeniusSectorSourceBound, ...]
    growth_certificate: ReverseGrowthRunCertificate | None = None

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.maximum_classes, self.bits, self.steps)
        ):
            raise TypeError("reverse Frobenius plans require exact integers")
        if (
            not _valid_geometry(self.maximum_classes, self.bits, self.steps)
            or type(self.sectors) is not tuple
        ):
            raise ValueError("invalid reverse Frobenius plan")
        if len(self.sectors) != self.maximum_classes.bit_length():
            raise ValueError("reverse Frobenius plan has another sector count")
        uniform_bound = 0
        if self.growth_certificate is not None:
            if type(self.growth_certificate) is not ReverseGrowthRunCertificate:
                raise TypeError("reverse Frobenius plan has another certificate sort")
            if self.growth_certificate is DECIMAL_REVERSE_GROWTH_CERTIFICATE:
                validate_decimal_growth_certificate(self.growth_certificate)
            else:
                self.growth_certificate.__post_init__()
            uniform_bound = self.steps // (
                self.growth_certificate.maximum_consecutive_growth + 1
            )
        expected_classes = 1
        for sector in self.sectors:
            if type(sector) is not FrobeniusSectorSourceBound:
                raise TypeError("reverse Frobenius plan has another sector sort")
            sector.__post_init__()
            if (
                sector.classes != expected_classes
                or sector.bits != self.bits
                or sector.steps != self.steps
                or sector.uniform_no_growth_lower_bound != uniform_bound
            ):
                raise ValueError("reverse Frobenius plan is not the canonical product")
            expected_classes <<= 1

    @staticmethod
    def _sectors_for(
        maximum_classes: int,
        bits: int,
        steps: int,
        growth_certificate: ReverseGrowthRunCertificate | None,
    ) -> tuple[FrobeniusSectorSourceBound, ...]:
        sectors: list[FrobeniusSectorSourceBound] = []
        classes = 1
        while classes <= maximum_classes:
            uniform_bound = (
                0
                if growth_certificate is None
                else steps // (growth_certificate.maximum_consecutive_growth + 1)
            )
            sectors.append(
                FrobeniusSectorSourceBound.for_steps(
                    classes,
                    bits,
                    steps,
                    uniform_no_growth_lower_bound=uniform_bound,
                )
            )
            classes <<= 1
        return tuple(sectors)

    @classmethod
    def for_steps(
        cls,
        *,
        maximum_classes: int,
        bits: int,
        steps: int,
        growth_certificate: ReverseGrowthRunCertificate | None = None,
    ) -> ReverseFrobeniusPlan:
        if any(type(value) is not int for value in (maximum_classes, bits, steps)):
            raise TypeError("reverse Frobenius plans require exact integers")
        if not _valid_geometry(maximum_classes, bits, steps):
            raise ValueError("invalid reverse Frobenius plan")
        if growth_certificate is not None:
            if type(growth_certificate) is not ReverseGrowthRunCertificate:
                raise TypeError("reverse growth certificate has another sort")
            if growth_certificate is DECIMAL_REVERSE_GROWTH_CERTIFICATE:
                validate_decimal_growth_certificate(growth_certificate)
            else:
                growth_certificate.__post_init__()
        return cls(
            maximum_classes,
            bits,
            steps,
            cls._sectors_for(maximum_classes, bits, steps, growth_certificate),
            growth_certificate,
        )

    @classmethod
    def identity(
        cls,
        *,
        maximum_classes: int,
        bits: int,
        growth_certificate: ReverseGrowthRunCertificate | None = None,
    ) -> ReverseFrobeniusPlan:
        return cls.for_steps(
            maximum_classes=maximum_classes,
            bits=bits,
            steps=0,
            growth_certificate=growth_certificate,
        )

    def then(self, after: ReverseFrobeniusPlan) -> ReverseFrobeniusPlan:
        if type(after) is not ReverseFrobeniusPlan:
            raise TypeError("Frobenius composition requires another plan")
        if (self.maximum_classes, self.bits) != (
            after.maximum_classes,
            after.bits,
        ):
            raise ValueError("Frobenius plans use different sector products")
        if self.growth_certificate != after.growth_certificate:
            raise ValueError("Frobenius plans use different growth certificates")
        return ReverseFrobeniusPlan.for_steps(
            maximum_classes=self.maximum_classes,
            bits=self.bits,
            steps=self.steps + after.steps,
            growth_certificate=self.growth_certificate,
        )

    @property
    def annihilated_sectors(self) -> tuple[bool, ...]:
        return tuple(sector.source_annihilated for sector in self.sectors)

    @property
    def all_source_sectors_annihilated(self) -> bool:
        return all(self.annihilated_sectors)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-frobenius-plan-v2",
            self.maximum_classes,
            self.bits,
            self.steps,
            None
            if self.growth_certificate is None
            else self.growth_certificate.canonical_key,
            tuple(sector.canonical_key for sector in self.sectors),
        )


def decimal_reverse_plan(steps: int) -> ReverseFrobeniusPlan:
    """Build the canonical plan issued for the exact decimal pair kernel."""
    return ReverseFrobeniusPlan.for_steps(
        maximum_classes=8,
        bits=5,
        steps=steps,
        growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    )


__all__ = [
    "FrobeniusSectorSourceBound",
    "DECIMAL_REVERSE_GROWTH_CERTIFICATE",
    "MAX_REVERSE_FROBENIUS_BITS",
    "MAX_REVERSE_FROBENIUS_CLASSES",
    "ReverseFrobeniusPlan",
    "ReverseGrowthRunCertificate",
    "decimal_reverse_plan",
    "validate_decimal_growth_certificate",
]
