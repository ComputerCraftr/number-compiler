"""Canonical scalar-boundary carry monoid for radix coefficient fields.

A raw coefficient block ``s_0,...,s_(m-1)`` in radix ``b`` represents

    A = sum_i s_i b**i.

Ordinary carry propagation with incoming carry ``c`` satisfies

    A + c = D + b**m * c_out,

where ``D`` is the normalized ``m``-digit value.  Consequently the complete
*boundary* behavior of the whole block is the one-dimensional floor-affine map

    c -> floor((A+c)/b**m).

The internal carry vector is therefore derived execution history, not semantic
state.  For the two special cyclotomic moduli this yields exact boundary laws:

* cyclic / Mersenne ``b**m-1``:     ``c_out = c_in``;
* negacyclic / Fermat ``b**m+1``:   ``c_out = -c_in``.

The block monoid composes by positional concatenation and can power repeated
blocks by binary composition without expanding their coefficients.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import balanced_fold, binary_power
from number_compiler.arithmetic.fields.radix import bit_width


@dataclass(frozen=True, slots=True)
class RadixCarryBlock:
    """Exact raw coefficient block modulo no quotient.

    ``raw_value`` may be signed; coefficients themselves are intentionally not
    retained after they have been folded into the canonical positional value.
    ``then`` appends a more-significant block.
    """

    base: int
    length: int
    raw_value: int
    compositions: int = 0

    def __post_init__(self) -> None:
        if self.base < 2 or self.length < 0 or self.compositions < 0:
            raise ValueError(self)
        if self.length == 0 and self.raw_value:
            raise ValueError("empty carry block must have zero raw value")

    @classmethod
    def identity(cls, base: int) -> RadixCarryBlock:
        return cls(int(base), 0, 0, 0)

    @classmethod
    def coefficient(cls, coefficient: int, *, base: int = 2) -> RadixCarryBlock:
        return cls(int(base), 1, int(coefficient), 0)

    @classmethod
    def from_coefficients(
        cls, coefficients: Iterable[int], *, base: int = 2
    ) -> RadixCarryBlock:
        base = int(base)
        return balanced_fold(
            (cls.coefficient(int(value), base=base) for value in coefficients),
            identity=cls.identity(base),
            compose=RadixCarryBlock.then,
        )

    @property
    def scale(self) -> int:
        return int(self.base**self.length)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("radix-carry-block", self.base, self.length, self.raw_value)

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.base)
            + bit_width(self.length)
            + bit_width(abs(self.raw_value))
            + int(self.raw_value < 0)
        )

    def outgoing_carry(self, incoming: int) -> int:
        return (self.raw_value + int(incoming)) // self.scale

    def normalized_payload(self, incoming: int) -> int:
        """Ordinary ``length``-digit payload for a supplied boundary carry."""
        return (self.raw_value + int(incoming)) % self.scale

    def then(self, other: RadixCarryBlock) -> RadixCarryBlock:
        """Append ``other`` as the more-significant coefficient block."""
        if self.base != other.base:
            raise ValueError("incompatible radix carry blocks")
        return RadixCarryBlock(
            self.base,
            self.length + other.length,
            self.raw_value + self.scale * other.raw_value,
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> RadixCarryBlock:
        base = RadixCarryBlock(self.base, self.length, self.raw_value, 0)
        powered = binary_power(
            base,
            exponent,
            identity=RadixCarryBlock.identity(self.base),
            compose=RadixCarryBlock.then,
        )
        result = powered.value
        return RadixCarryBlock(
            result.base, result.length, result.raw_value, powered.compositions
        )


@dataclass(frozen=True, slots=True)
class RadixCarryAction:
    """Extensional multi-valued carry action on one reachable carry interval.

    ``RadixCarryBlock`` is the algebraic floor-affine representation

        ``c -> floor((raw_value + c) / base**length)``.

    For quotienting we often do *not* want ``raw_value`` because it can retain
    nearly the whole coefficient field.  ``RadixCarryAction`` forgets that
    provenance and keeps only the exact function on one contiguous carry
    interval.  Equal actions are therefore behaviorally identical even when
    they came from different raw coefficient blocks.

    The object is deliberately a transient theorem/action coordinate.  It is
    closed under spatial concatenation whenever the intermediate carries stay
    inside the declared interval, which is exactly the contract needed by the
    carry/cyclotomic transducer below.
    """

    base: int
    length: int
    incoming_min: int
    outgoing: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        if (
            self.base < 2
            or self.length < 0
            or not self.outgoing
            or self.compositions < 0
        ):
            raise ValueError(self)

    @classmethod
    def from_block(
        cls,
        block: RadixCarryBlock,
        *,
        incoming_min: int,
        incoming_max: int,
    ) -> RadixCarryAction:
        lo, hi = int(incoming_min), int(incoming_max)
        if hi < lo:
            raise ValueError((lo, hi))
        return cls(
            block.base,
            block.length,
            lo,
            tuple(block.outgoing_carry(carry) for carry in range(lo, hi + 1)),
            block.compositions,
        )

    @property
    def incoming_max(self) -> int:
        return self.incoming_min + len(self.outgoing) - 1

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "radix-carry-action",
            self.base,
            self.length,
            self.incoming_min,
            self.outgoing,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.base)
            + bit_width(self.length)
            + bit_width(abs(self.incoming_min))
            + int(self.incoming_min < 0)
            + bit_width(len(self.outgoing))
            + sum(bit_width(abs(value)) + int(value < 0) for value in self.outgoing)
        )

    def apply(self, incoming: int) -> int:
        incoming = int(incoming)
        if not self.incoming_min <= incoming <= self.incoming_max:
            raise ValueError((incoming, self.incoming_min, self.incoming_max))
        return self.outgoing[incoming - self.incoming_min]

    def then(self, other: RadixCarryAction) -> RadixCarryAction:
        """Append ``other`` as the more-significant spatial action."""
        if (
            self.base != other.base
            or self.incoming_min != other.incoming_min
            or self.incoming_max != other.incoming_max
        ):
            raise ValueError("incompatible carry-action domains")
        out: list[int] = []
        for incoming in range(self.incoming_min, self.incoming_max + 1):
            middle = self.apply(incoming)
            if not other.incoming_min <= middle <= other.incoming_max:
                raise ValueError(
                    (
                        "carry-action-domain-escape",
                        middle,
                        other.incoming_min,
                        other.incoming_max,
                    )
                )
            out.append(other.apply(middle))
        return RadixCarryAction(
            self.base,
            self.length + other.length,
            self.incoming_min,
            tuple(out),
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> RadixCarryAction:
        """Repeat one spatial action by the repository-wide binary power kernel."""
        identity = RadixCarryAction(
            self.base,
            0,
            self.incoming_min,
            tuple(range(self.incoming_min, self.incoming_max + 1)),
            0,
        )
        base = RadixCarryAction(
            self.base,
            self.length,
            self.incoming_min,
            self.outgoing,
            0,
        )
        powered = binary_power(
            base, exponent, identity=identity, compose=RadixCarryAction.then
        )
        result = powered.value
        return RadixCarryAction(
            result.base,
            result.length,
            result.incoming_min,
            result.outgoing,
            powered.compositions,
        )


@dataclass(frozen=True, slots=True)
class EndAroundCarryNormalization:
    """Exact cyclic/negacyclic normalization result.

    ``sign=+1`` denotes modulus ``b**m-1`` and a fixed boundary carry.
    ``sign=-1`` denotes modulus ``b**m+1`` and an anti-fixed boundary carry.
    For the latter, ``exceptional_minus_one`` represents the unique canonical
    residue ``b**m == -1`` using the signed one-digit value ``-1`` rather than
    duplicating it as an impossible ordinary ``m``-digit payload.
    """

    block: RadixCarryBlock
    sign: int
    modulus: int
    boundary_in: int
    boundary_out: int
    residue: int
    exceptional_minus_one: bool = False

    def __post_init__(self) -> None:
        if self.sign not in (-1, 1):
            raise ValueError(self.sign)
        want = self.block.scale - self.sign
        if self.modulus != want or not 0 <= self.residue <= self.block.scale:
            raise ValueError(self)
        if self.sign == 1:
            if self.boundary_in != self.boundary_out:
                raise ValueError("cyclic normalization requires a fixed carry")
        else:
            if self.boundary_out != -self.boundary_in:
                raise ValueError(
                    "negacyclic normalization requires an anti-fixed carry"
                )
        if self.exceptional_minus_one != (
            self.sign == -1 and self.residue == self.block.scale
        ):
            raise ValueError("noncanonical exceptional residue flag")

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "end-around-carry",
            self.block.canonical_key,
            self.sign,
            self.boundary_in,
            self.boundary_out,
            self.residue,
        )

    @property
    def boundary_bits(self) -> int:
        return bit_width(abs(self.boundary_in)) + int(self.boundary_in < 0)


@dataclass(frozen=True, slots=True)
class EndAroundCarryMarker:
    """Compact spatial marker summary of an end-around normalization.

    This is a *derived* view of the internal carry trajectory, not retained
    semantic carry state.  It records only a constant number of positional and
    moment statistics while one pass over the raw coefficient field verifies
    the fixed/anti-fixed boundary law.  Each scalar therefore needs only
    logarithmic description size in the represented width/carry magnitude.

    Cyclic (Mersenne) callers interpret positions modulo ``length``.
    Negacyclic (Fermat) callers additionally retain ``sign=-1`` so a wrap has
    the correct orientation.  The marker is intended for exact quotient
    synthesis: it must never be promoted to an order-depth state unless target
    separation and successor closure are proved independently.
    """

    base: int
    length: int
    sign: int
    boundary_in: int
    change_count: int
    first_change: int
    last_change: int
    nonzero_count: int
    first_nonzero: int
    max_abs_carry: int
    first_max_abs: int
    carry_sum: int
    carry_moment: int

    def __post_init__(self) -> None:
        if self.base < 2 or self.length <= 0 or self.sign not in (-1, 1):
            raise ValueError(self)
        for value in (self.change_count, self.nonzero_count, self.max_abs_carry):
            if int(value) < 0:
                raise ValueError(self)
        for position in (
            self.first_change,
            self.last_change,
            self.first_nonzero,
            self.first_max_abs,
        ):
            if not 0 <= int(position) <= self.length:
                raise ValueError(self)

    def phase(self, order: int, *, source: str = "first_change") -> int | None:
        """Return one exact spatial marker phase modulo ``order``.

        ``None`` denotes an absent event.  Absence is deliberately not mapped
        into a residue class because doing so could alias a real position.
        """
        order = int(order)
        if order <= 0:
            raise ValueError(order)
        if source not in {
            "first_change",
            "last_change",
            "first_nonzero",
            "first_max_abs",
        }:
            raise ValueError(source)
        position = int(getattr(self, source))
        return None if position == self.length else position % order

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "end-around-carry-marker",
            self.base,
            self.length,
            self.sign,
            self.boundary_in,
            self.change_count,
            self.first_change,
            self.last_change,
            self.nonzero_count,
            self.first_nonzero,
            self.max_abs_carry,
            self.first_max_abs,
            self.carry_sum,
            self.carry_moment,
        )

    @property
    def description_bits(self) -> int:
        return (
            sum(
                bit_width(abs(int(value))) + int(int(value) < 0)
                for value in (
                    self.base,
                    self.length,
                    self.boundary_in,
                    self.change_count,
                    self.first_change,
                    self.last_change,
                    self.nonzero_count,
                    self.first_nonzero,
                    self.max_abs_carry,
                    self.first_max_abs,
                    self.carry_sum,
                    self.carry_moment,
                )
            )
            + 1
        )


@dataclass(frozen=True, slots=True)
class NormalizationDefect:
    """Exact polynomial certificate for one finite radix normalization.

    For raw coefficients ``a_i``, normalized digits ``d_i`` and carry
    boundaries ``c_0..c_L`` satisfying

        ``a_i + c_i = d_i + base*c_(i+1)``,

    define ``Q(z)=sum_i c_(i+1) z**i``.  Then the finite-block identity is

        ``A(z)-D(z) = (base-z)Q(z) - c_0 + c_L z**L``.

    The boundary term is essential.  It disappears literally for zero-ended
    ordinary normalization, and disappears *in the quotient ring* modulo
    ``z**L-1`` / ``z**L+1`` for cyclic / negacyclic end-around carries.

    This certificate stores only the algebraic difference and outgoing-carry
    polynomial required by the theorem; it is not a second semantic digit
    state.
    """

    base: int
    length: int
    boundary_in: int
    boundary_out: int
    difference_lsf: tuple[int, ...]
    carry_quotient_lsf: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.base < 2 or self.length < 0:
            raise ValueError(self)
        if len(self.difference_lsf) != self.length:
            raise ValueError((len(self.difference_lsf), self.length))
        if len(self.carry_quotient_lsf) != self.length:
            raise ValueError((len(self.carry_quotient_lsf), self.length))
        if not self.identity_holds:
            raise ValueError("invalid normalization-defect identity")

    @property
    def boundary_term_lsf(self) -> tuple[int, ...]:
        if not self.length:
            return (self.boundary_out - self.boundary_in,)
        return (-self.boundary_in,) + (0,) * (self.length - 1) + (self.boundary_out,)

    @property
    def rhs_lsf(self) -> tuple[int, ...]:
        out = [0] * (self.length + 1)
        for index, carry in enumerate(self.carry_quotient_lsf):
            out[index] += self.base * carry
            out[index + 1] -= carry
        out[0] -= self.boundary_in
        out[self.length] += self.boundary_out
        return tuple(out)

    @property
    def identity_holds(self) -> bool:
        lhs = self.difference_lsf + (0,)
        return lhs == self.rhs_lsf

    def boundary_vanishes_mod_end_around(self, sign: int) -> bool:
        """Whether the boundary term is a multiple of ``z**L-sign``."""
        sign = int(sign)
        if sign not in (-1, 1):
            raise ValueError(sign)
        return self.boundary_out == sign * self.boundary_in

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "normalization-defect",
            self.base,
            self.length,
            self.boundary_in,
            self.boundary_out,
            self.difference_lsf,
            self.carry_quotient_lsf,
        )


def linear_normalization_fields(
    coefficients: Iterable[int], *, base: int, boundary_in: int = 0
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Return ordinary digits and all carry boundaries for a finite field."""
    coeffs = tuple(map(int, coefficients))
    base, carry = int(base), int(boundary_in)
    if base < 2:
        raise ValueError(base)
    digits: list[int] = []
    carries = [carry]
    for coefficient in coeffs:
        carry, digit = divmod(coefficient + carry, base)
        digits.append(digit)
        carries.append(carry)
    return tuple(digits), tuple(carries)


def normalization_defect(
    coefficients: Iterable[int],
    digits: Iterable[int],
    carries: Iterable[int],
    *,
    base: int,
) -> NormalizationDefect:
    """Build and verify the exact finite-block normalization identity."""
    coeffs = tuple(map(int, coefficients))
    ds = tuple(map(int, digits))
    cs = tuple(map(int, carries))
    base = int(base)
    if len(ds) != len(coeffs) or len(cs) != len(coeffs) + 1:
        raise ValueError((len(coeffs), len(ds), len(cs)))
    if base < 2:
        raise ValueError(base)
    for index, (coefficient, digit) in enumerate(zip(coeffs, ds, strict=True)):
        if coefficient + cs[index] != digit + base * cs[index + 1]:
            raise ValueError((index, coefficient, cs[index], digit, cs[index + 1]))
    return NormalizationDefect(
        base,
        len(coeffs),
        cs[0],
        cs[-1],
        tuple(a - d for a, d in zip(coeffs, ds, strict=True)),
        tuple(cs[1:]),
    )


def linear_normalization_defect(
    coefficients: Iterable[int], *, base: int, boundary_in: int = 0
) -> NormalizationDefect:
    coeffs = tuple(coefficients)
    digits, carries = linear_normalization_fields(
        coeffs,
        base=base,
        boundary_in=boundary_in,
    )
    return normalization_defect(coeffs, digits, carries, base=base)


def normalize_cyclic_block(block: RadixCarryBlock) -> EndAroundCarryNormalization:
    """Normalize modulo ``base**length-1`` with one scalar fixed carry."""
    if block.length <= 0:
        raise ValueError("cyclic block must be nonempty")
    modulus = block.scale - 1
    boundary, residue = divmod(block.raw_value, modulus)
    # A cyclic residue always fits in the ordinary m-digit payload.
    if block.outgoing_carry(boundary) != boundary:
        raise AssertionError((block, boundary))
    if block.normalized_payload(boundary) % modulus != residue:
        raise AssertionError((block, boundary, residue))
    return EndAroundCarryNormalization(
        block, 1, modulus, boundary, boundary, residue, False
    )


def normalize_negacyclic_block(block: RadixCarryBlock) -> EndAroundCarryNormalization:
    """Normalize modulo ``base**length+1`` with one scalar anti-fixed carry."""
    if block.length <= 0:
        raise ValueError("negacyclic block must be nonempty")
    modulus = block.scale + 1
    quotient, residue = divmod(block.raw_value, modulus)
    if residue == block.scale:
        # ``base**m`` is the canonical -1 residue.  Represent it by signed
        # payload -1 at the LSD.  Then A+c = -1 + base**m*(-c).
        incoming = -(quotient + 1)
        outgoing = -incoming
        exceptional = True
    else:
        incoming = -quotient
        outgoing = quotient
        exceptional = False
        if block.outgoing_carry(incoming) != outgoing:
            raise AssertionError((block, incoming, outgoing, residue))
        if block.normalized_payload(incoming) != residue:
            raise AssertionError((block, incoming, residue))
    return EndAroundCarryNormalization(
        block, -1, modulus, incoming, outgoing, residue, exceptional
    )


def normalization_digits_lsf(
    normalization: EndAroundCarryNormalization,
) -> tuple[int, ...]:
    """Return the canonical signed/ordinary digit field of an end-around result."""
    block = normalization.block
    if normalization.exceptional_minus_one:
        return (-1,) + (0,) * (block.length - 1)
    payload = normalization.residue
    out_digits: list[int] = []
    for _ in range(block.length):
        payload, digit = divmod(payload, block.base)
        out_digits.append(digit)
    if payload:
        raise AssertionError((normalization, payload))
    return tuple(out_digits)


def _admit_normalization_coefficients(
    coefficients: Iterable[int], normalization: EndAroundCarryNormalization
) -> tuple[tuple[int, ...], RadixCarryBlock]:
    coeffs = tuple(map(int, coefficients))
    block = normalization.block
    if len(coeffs) != block.length:
        raise ValueError((len(coeffs), block.length))
    return coeffs, block


def normalization_carry_boundaries(
    coefficients: Iterable[int], normalization: EndAroundCarryNormalization
) -> tuple[int, ...]:
    """Derive the complete internal carry history for one normalization.

    Production retains only the scalar fixed/anti-fixed boundary carry.  This
    helper reconstructs internal carries *on demand* for theorem/research
    instrumentation from the already-available raw coefficient field.  The
    exceptional negacyclic ``-1`` residue uses its canonical signed payload
    ``(-1,0,...,0)`` rather than silently switching to an ordinary all-ones
    digit representation.
    """
    coeffs, block = _admit_normalization_coefficients(coefficients, normalization)
    digits = normalization_digits_lsf(normalization)

    carry = normalization.boundary_in
    out = [carry]
    for coefficient, digit in zip(coeffs, digits, strict=True):
        numerator = coefficient + carry - digit
        if numerator % block.base:
            raise AssertionError((coefficient, carry, digit, block.base))
        carry = numerator // block.base
        out.append(carry)
    if carry != normalization.boundary_out:
        raise AssertionError((normalization.boundary_out, carry, tuple(out)))
    return tuple(out)


def end_around_carry_marker(
    coefficients: Iterable[int], normalization: EndAroundCarryNormalization
) -> EndAroundCarryMarker:
    """Stream a compact exact marker summary without retaining carry history."""
    coeffs, block = _admit_normalization_coefficients(coefficients, normalization)

    # Stream canonical digits from the scalar residue.  The exceptional
    # negacyclic -1 residue is represented by (-1,0,...,0), matching the
    # normalization theorem rather than an alternate all-ones payload.
    payload = normalization.residue
    carry = normalization.boundary_in
    previous = carry
    change_count = nonzero_count = 0
    first_change = last_change = block.length
    first_nonzero = block.length
    max_abs = 0
    first_max = block.length
    carry_sum = carry_moment = 0

    for index, coefficient in enumerate(coeffs):
        if normalization.exceptional_minus_one:
            digit = -1 if index == 0 else 0
        else:
            payload, digit = divmod(payload, block.base)
        numerator = coefficient + carry - digit
        if numerator % block.base:
            raise AssertionError((index, coefficient, carry, digit, block.base))
        next_carry = numerator // block.base

        # Marker coefficients are outgoing carries Q_i=c_(i+1), matching the
        # normalization-defect polynomial convention.
        qcarry = next_carry
        carry_sum += qcarry
        carry_moment += (index + 1) * qcarry
        if qcarry:
            nonzero_count += 1
            if first_nonzero == block.length:
                first_nonzero = index
        magnitude = abs(qcarry)
        if magnitude > max_abs:
            max_abs = magnitude
            first_max = index
        if next_carry != previous:
            change_count += 1
            if first_change == block.length:
                first_change = index
            last_change = index
        previous = next_carry
        carry = next_carry

    if not normalization.exceptional_minus_one and payload:
        raise AssertionError((normalization, payload))
    if carry != normalization.boundary_out:
        raise AssertionError((normalization.boundary_out, carry))
    return EndAroundCarryMarker(
        block.base,
        block.length,
        normalization.sign,
        normalization.boundary_in,
        change_count,
        first_change,
        last_change,
        nonzero_count,
        first_nonzero,
        max_abs,
        first_max,
        carry_sum,
        carry_moment,
    )


def end_around_normalization_defect(
    coefficients: Iterable[int], normalization: EndAroundCarryNormalization
) -> NormalizationDefect:
    """Return the boundary-aware defect certificate for one cyclic normalization."""
    coeffs = tuple(coefficients)
    digits = normalization_digits_lsf(normalization)
    carries = normalization_carry_boundaries(coeffs, normalization)
    defect = normalization_defect(
        coeffs,
        digits,
        carries,
        base=normalization.block.base,
    )
    if not defect.boundary_vanishes_mod_end_around(normalization.sign):
        raise AssertionError((normalization, defect))
    return defect


__all__ = [
    "EndAroundCarryMarker",
    "EndAroundCarryNormalization",
    "NormalizationDefect",
    "RadixCarryAction",
    "RadixCarryBlock",
    "end_around_carry_marker",
    "end_around_normalization_defect",
    "linear_normalization_defect",
    "linear_normalization_fields",
    "normalization_carry_boundaries",
    "normalization_defect",
    "normalization_digits_lsf",
    "normalize_cyclic_block",
    "normalize_negacyclic_block",
]
