"""Authenticated multiplication-by-15 view of an Antihydra weighted carry.

For ``H = D + 1`` the centered carry supplies ``J`` and the physical floor
correction is ``K = 3**n - 2**n - J``.  The raw and physical decimal lifts
are deliberately kept distinct::

    15**n H                         (raw multiplication)
    15**n H - 5**n K = 10**n H_n   (iterated physical floors)

Large decimal powers are materialized only by explicit demand methods after
the caller has reserved scratch space.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer

_X15_MORPHISM_ISSUANCE_SEAL = object()

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_carry_quotient import (
        IssuedWeightedCarry,
    )
    from number_compiler.sequences.antihydra.mahler_diagonal_carry import (
        DiagonalCarryTower,
    )


@dataclass(frozen=True, slots=True)
class X15IntegerCut:
    """Raw dyadic quotient/remainder paired with the physical endpoint."""

    raw_quotient: int
    raw_remainder: int
    denominator: int
    physical_endpoint: int
    floor_correction: int


@dataclass(frozen=True, slots=True)
class X15ScaledIntegerPair:
    raw_numerator: int
    floor_numerator: int
    physical_numerator: int


@dataclass(frozen=True, slots=True)
class TwoParentX15Floor:
    future: int
    remainder_correction: int


@dataclass(frozen=True, slots=True)
class _X15IssuanceCertificate:
    issuer: object
    payload: tuple[object, ...]


@dataclass(frozen=True, slots=True, init=False)
class X15CarryMorphism:
    """A source-bound projection of one or more issued carry actions."""

    source: int
    ticks: int
    innovation: int
    gain: int
    denominator: int
    endpoint: int
    floor_correction: int
    centered_skew: SkewTransfer[int]
    _carry: IssuedWeightedCarry | None
    _parents: tuple[X15CarryMorphism, X15CarryMorphism] | None
    _owner: IssuedWeightedCarry
    _issuer: object
    _certificate: _X15IssuanceCertificate
    _snapshot: tuple[object, ...]

    @classmethod
    def from_carry(
        cls,
        carry: IssuedWeightedCarry,
        *,
        reserve_bits: Callable[[int], None],
    ) -> X15CarryMorphism:
        from number_compiler.sequences.antihydra.mahler_carry_quotient import (
            IssuedWeightedCarry,
        )

        if type(carry) is not IssuedWeightedCarry:
            raise TypeError("x15 morphism requires an issued weighted carry")
        if not callable(reserve_bits):
            raise TypeError("x15 morphism requires a scratch reservation hook")
        carry.require_issued()
        reserve_bits(
            8
            * (
                carry.width
                + carry.centered_source.bit_length()
                + carry.innovation.bit_length()
                + 64
            )
        )
        endpoint = carry.endpoint(carry.centered_source)
        return cls._issue(
            source=carry.centered_source,
            ticks=carry.width,
            skew=carry.skew,
            endpoint=endpoint,
            carry=carry,
            parents=None,
            owner=carry,
        )

    @classmethod
    def _issue(
        cls,
        *,
        source: int,
        ticks: int,
        skew: SkewTransfer[int],
        endpoint: int,
        carry: IssuedWeightedCarry | None,
        parents: tuple[X15CarryMorphism, X15CarryMorphism] | None,
        owner: IssuedWeightedCarry,
    ) -> X15CarryMorphism:
        if (
            type(source) is not int
            or source < 0
            or type(ticks) is not int
            or ticks < 0
            or type(skew) is not SkewTransfer
            or any(
                type(value) is not int
                for value in (skew.upper, skew.offset, skew.lower)
            )
            or skew.upper <= 0
            or skew.lower <= 0
            or skew.lower & (skew.lower - 1)
            or skew.lower.bit_length() - 1 != ticks
        ):
            raise ValueError("x15 morphism has incompatible exact coefficients")
        numerator = skew.upper * source + skew.offset
        if numerator & (skew.lower - 1) or endpoint != numerator >> ticks:
            raise ArithmeticError("x15 morphism lost its centered endpoint")
        correction = skew.upper - skew.lower - skew.offset
        if correction < 0:
            raise ArithmeticError("x15 morphism has a negative physical correction")
        physical_source = source + 1
        physical_endpoint = endpoint + 1
        if skew.upper * physical_source - correction != skew.lower * physical_endpoint:
            raise ArithmeticError("x15 morphism lost the physical floor identity")
        value = object.__new__(cls)
        fields: tuple[tuple[str, object], ...] = (
            ("source", source),
            ("ticks", ticks),
            ("innovation", skew.offset),
            ("gain", skew.upper),
            ("denominator", skew.lower),
            ("endpoint", endpoint),
            ("floor_correction", correction),
            ("centered_skew", skew),
            ("_carry", carry),
            ("_parents", parents),
            ("_owner", owner),
            ("_issuer", _X15_MORPHISM_ISSUANCE_SEAL),
        )
        for name, item in fields:
            object.__setattr__(value, name, item)
        snapshot = value.publication_payload()
        object.__setattr__(
            value,
            "_certificate",
            _X15IssuanceCertificate(_X15_MORPHISM_ISSUANCE_SEAL, snapshot),
        )
        object.__setattr__(value, "_snapshot", snapshot)
        value.require_issued()
        return value

    @property
    def integer_source(self) -> int:
        self.require_issued()
        return self.source + 1

    @property
    def integer_endpoint(self) -> int:
        self.require_issued()
        return self.endpoint + 1

    @property
    def affine_offset(self) -> int:
        self.require_issued()
        return -self.floor_correction

    def require_issued(self) -> None:
        pending: list[X15CarryMorphism] = [self]
        visited: set[int] = set()
        while pending:
            current = pending.pop()
            identity = id(current)
            if identity in visited:
                continue
            visited.add(identity)
            carry = current._carry
            parents = current._parents
            certificate = getattr(current, "_certificate", None)
            if (
                getattr(current, "_issuer", None) is not _X15_MORPHISM_ISSUANCE_SEAL
                or type(certificate) is not _X15IssuanceCertificate
                or certificate.issuer is not _X15_MORPHISM_ISSUANCE_SEAL
                or certificate.payload != current.publication_payload()
            ):
                raise ValueError("x15 morphism was not issued by its source owner")
            if current.publication_payload() != current._snapshot:
                raise ValueError("x15 morphism publication was altered")
            if (carry is None) == (parents is None):
                raise ValueError("x15 morphism lost its unique authority")
            if carry is not None:
                carry.require_issued()
                if (
                    current._owner is not carry
                    or carry.centered_source != current.source
                    or carry.width != current.ticks
                    or carry.skew != current.centered_skew
                    or carry.endpoint(current.source) != current.endpoint
                ):
                    raise ValueError("x15 morphism has another issued carry")
                continue
            assert parents is not None
            before, after = parents
            if (
                current._owner is not before._owner
                or after.source != before.endpoint
                or current.source != before.source
                or current.endpoint != after.endpoint
                or current.ticks != before.ticks + after.ticks
            ):
                raise ValueError("x15 morphism lost its chronological source seam")
            pending.append(after)
            pending.append(before)

    def coupled_integer_cut(self) -> X15IntegerCut:
        """Return the raw single-floor cut without decimal-power expansion."""
        self.require_issued()
        raw_numerator = self.gain * self.integer_source
        raw_quotient = raw_numerator >> self.ticks
        raw_remainder = raw_numerator & (self.denominator - 1)
        physical = self.integer_endpoint
        if (
            raw_remainder + self.denominator * (raw_quotient - physical)
            != self.floor_correction
        ):
            raise ArithmeticError("raw and physical cuts lost their floor correction")
        return X15IntegerCut(
            raw_quotient,
            raw_remainder,
            self.denominator,
            physical,
            self.floor_correction,
        )

    def scaled_integer_pair(
        self, *, reserve_bits: Callable[[int], None]
    ) -> X15ScaledIntegerPair:
        """Materialize the exact x15/5/10 identity only on explicit demand."""
        self.require_issued()
        if not callable(reserve_bits):
            raise TypeError("scaled x15 pair requires scratch reservation")
        reserve_bits(
            24
            * (
                self.ticks
                + self.integer_source.bit_length()
                + self.floor_correction.bit_length()
                + 64
            )
        )
        five = 5**self.ticks
        raw = self.gain * five * self.integer_source
        floor = five * self.floor_correction
        physical = 10**self.ticks * self.integer_endpoint
        if raw - floor != physical:
            raise ArithmeticError("scaled x15 pair lost its physical correction")
        return X15ScaledIntegerPair(raw, floor, physical)

    def then(
        self,
        after: X15CarryMorphism,
        *,
        reserve_bits: Callable[[int], None],
    ) -> X15CarryMorphism:
        """Compose compatible complete-source morphisms chronologically."""
        self.require_issued()
        if type(after) is not X15CarryMorphism:
            raise TypeError("x15 composition requires a typed morphism")
        after.require_issued()
        if after.source != self.endpoint:
            raise ValueError("x15 morphism has an incompatible source seam")
        if not self._owner.has_same_resource_owner(after._owner):
            raise ValueError("x15 composition spans foreign resource owners")
        if not callable(reserve_bits):
            raise TypeError("x15 composition requires scratch reservation")
        reserve_bits(
            12
            * (
                self.ticks
                + after.ticks
                + self.innovation.bit_length()
                + after.innovation.bit_length()
                + 64
            )
        )
        skew = self.centered_skew.then(after.centered_skew, multiply=mul, add=add)
        result = X15CarryMorphism._issue(
            source=self.source,
            ticks=self.ticks + after.ticks,
            skew=skew,
            endpoint=after.endpoint,
            carry=None,
            parents=(self, after),
            owner=self._owner,
        )
        expected_correction = (
            after.gain * self.floor_correction
            + self.denominator * after.floor_correction
        )
        if result.floor_correction != expected_correction:
            raise ArithmeticError("x15 floor cocycle broke under composition")
        return result

    def diagonal_tower(self) -> DiagonalCarryTower:
        """Create a lazy spatial projection; allocate no decimal field yet."""
        self.require_issued()
        from number_compiler.sequences.antihydra.mahler_diagonal_carry import (
            DiagonalCarryTower,
        )

        return DiagonalCarryTower.from_morphism(self)

    def charge_projection_metrics(self, entries: tuple[tuple[str, int], ...]) -> None:
        """Validate once, then charge a bounded projection work batch."""
        self.require_issued()
        self._owner.charge_projection_metrics(entries)

    def publication_payload(self) -> tuple[object, ...]:
        """Return the immutable semantic value authenticated at publication."""
        return (
            self.source,
            self.ticks,
            self.innovation,
            self.gain,
            self.denominator,
            self.endpoint,
            self.floor_correction,
            self.centered_skew,
            self._carry,
            self._parents,
            self._owner,
            self._issuer,
        )


def two_parent_x15_floor(
    previous: int,
    current: int,
    previous_carry: int,
    current_carry: int,
) -> TwoParentX15Floor:
    """Check the multiplication recurrence and its exact 57/4 correction."""
    values = previous, current, previous_carry, current_carry
    if any(type(value) is not int for value in values):
        raise TypeError("two-parent x15 recurrence requires exact integers")
    if (
        previous < 0
        or current < 0
        or not 0 <= previous_carry < 15
        or not 0 <= current_carry < 15
    ):
        raise ValueError("two-parent x15 ports are outside their finite domains")
    if current != 15 * previous + previous_carry:
        raise ArithmeticError("successive x15 ports have different sources")
    correction, remainder = divmod(
        3 * previous_carry + current % 4 + previous % 4,
        4,
    )
    if remainder:
        raise ArithmeticError("57/4 complementary correction is not integral")
    future = 15 * current + current_carry
    multiplication = 10 * current + 75 * previous + 5 * previous_carry + current_carry
    floor_form = 57 * current // 4 + 45 * previous // 4 + current_carry + correction
    if future != multiplication or future != floor_form:
        raise ArithmeticError("two-parent x15 recurrence lost its carry")
    return TwoParentX15Floor(future, correction)


__all__ = [
    "TwoParentX15Floor",
    "X15CarryMorphism",
    "X15IntegerCut",
    "X15ScaledIntegerPair",
    "two_parent_x15_floor",
]
