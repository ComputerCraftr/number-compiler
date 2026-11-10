"""Exact multi-digit 3^n / 3^(2^t) carry and borrow orbit actions.

This reuses the same synthesized multiplication-by-3 transition monoid
as the Collatz digit compiler.  Unlike the last-digit / moving 2-adic
pivot observations, its source consists of *all demanded low radix digits*.
The clocks are the exact multiplicative orders of 3 in each prime-power
radix, with the 2-adic and 5-adic factors combined for decimal digits.

Every source residue comes from a modulus b**j, never from reducing against
a Fermat candidate.  These observations must NOT be used alone to issue a
Pépin PASS/FAIL certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from number_compiler.arithmetic.fields.digit_formula import (
    synthesize_multiply_add,
)


class ThreePowerClock(StrEnum):
    ORDINARY = "ordinary"
    DYADIC = "dyadic"


RADICES = (2, 3, 5, 6, 7, 10, 11, 13, 27, 64)


def _require_base_places(base: int, places: int) -> None:
    if type(base) is not int or base not in RADICES:
        raise ValueError("radix must be one of 2,3,5,6,7,10,11,13,27,64")
    if type(places) is not int or not 1 <= places <= 64:
        raise ValueError("radix places must be in 1..64")


def decimal_tripling_order(places: int) -> int:
    """Exact order of three modulo a bounded decimal source window."""
    if type(places) is not int or not 1 <= places <= 512:
        raise ValueError("decimal source places must be in 1..512")
    return (1 << max(2, places - 2)) * int(5 ** (places - 1))


def order_three(base: int, places: int) -> int | None:
    """Exact ord_{base**places}(3); None when the modulus contains 3.

    Decimal order includes the 2-power component, which first increases
    beyond the ordinary four-cycle at j=5:
      ord_(10**j)(3) = 2**max(2,j-2) * 5**(j-1).
    The base-11 order has a 3-Wieferich lift at 11**2: 3**5 == 1 mod121.
    """
    _require_base_places(base, places)
    if base in (3, 6, 27):
        return None
    if base in (2, 64):
        power = places * (6 if base == 64 else 1)
        return 1 if power == 1 else 2 if power == 2 else 1 << (power - 2)
    if base == 5:
        return 4 * int(5 ** (places - 1))
    if base == 7:
        return 6 * int(7 ** (places - 1))
    if base == 10:
        return decimal_tripling_order(places)
    if base == 11:
        return 5 * int(11 ** max(0, places - 2))
    return 3 * int(13 ** (places - 1))


def _known_factors(n: int) -> tuple[tuple[int, int], ...]:
    pairs: list[tuple[int, int]] = []
    for prime in (2, 3, 5, 7, 11, 13):
        exp = 0
        while n % prime == 0:
            n //= prime
            exp += 1
        if exp:
            pairs.append((prime, exp))
    if n != 1:
        raise AssertionError("orbit period factorization contains an unsupported prime")
    return tuple(pairs)


def dyadic_clock(base: int, places: int) -> tuple[int, int]:
    """(preperiod, exact period) for t -> 3**(2**t) mod base**places.

    For units, write ord(3)=2**a * odd.  The 2-adic part dies at t=a,
    and the eventual period is ord_odd(2).  Base 3/27 has an eventual
    constant-zero orbit once 2**t reaches the radix's 3-adic valuation.
    """
    order = order_three(base, places)
    if base == 6:
        # The 3-primary coordinate dies, while the binary unit rotates.
        # Their joint eventual period is one, but only after BOTH settle.
        return max((places - 1).bit_length(), max(0, places - 2)), 1
    if order is None:
        v3 = places * (3 if base == 27 else 1)
        return (v3 - 1).bit_length(), 1
    a = (order & -order).bit_length() - 1
    odd = order >> a
    if odd == 1:
        return a, 1
    factors = _known_factors(odd)
    phi = 1
    for prime, exp in factors:
        phi *= (prime - 1) * prime ** (exp - 1)
    period = phi
    for prime, _exp in _known_factors(phi):
        while period % prime == 0 and pow(2, period // prime, odd) == 1:
            period //= prime
    return a, period


def triple_residue(
    clock: ThreePowerClock | str, level: int, base: int, places: int
) -> int:
    """Low `places` digits of 3**n or 3**(2**t), no large source integer."""
    _require_base_places(base, places)
    if clock not in ("ordinary", "dyadic") or type(level) is not int or level < 0:
        raise ValueError("clock must be ordinary or dyadic with nonnegative index")
    clock = ThreePowerClock(clock)
    modulus = int(base**places)
    order = order_three(base, places)
    if base == 6:
        # 6**places = 2**places * 3**places. The non-unit 3-adic
        # source eventually vanishes, but the 2-adic factor never does.
        modulus2, modulus3 = 1 << places, int(3**places)
        r2 = _unit_residue(clock, level, 2, places)
        if clock == "ordinary":
            r3 = 0 if level >= places else pow(3, level, modulus3)
        else:
            r3 = (
                0
                if level >= (places - 1).bit_length()
                else pow(3, 1 << level, modulus3)
            )
        lift = ((r2 - r3) * pow(modulus3, -1, modulus2)) % modulus2
        return r3 + modulus3 * lift
    if order is None:
        threshold = places * (3 if base == 27 else 1)
        if clock == "ordinary":
            if level >= threshold:
                return 0
            exponent = level
        else:
            if level >= (threshold - 1).bit_length():
                return 0
            exponent = 1 << level
        return pow(3, exponent, modulus)
    if base == 10:
        # The decimal cylinder is the CRT join of genuinely different
        # binary and 5-adic exponent clocks, not a last-digit cycle.
        m2, m5 = 1 << places, int(5**places)
        r2 = _unit_residue(clock, level, 2, places)
        r5 = _unit_residue(clock, level, 5, places)
        join = ((r2 - r5) * pow(m5, -1, m2)) % m2
        return r5 + m5 * join
    return _unit_residue(clock, level, base, places)


def _unit_residue(
    clock: ThreePowerClock | str, level: int, base: int, places: int
) -> int:
    order = order_three(base, places)
    assert order is not None
    exponent = (
        level % order if clock == ThreePowerClock.ORDINARY else pow(2, level, order)
    )
    return pow(3, exponent, int(base**places))


@dataclass(frozen=True, slots=True)
class TripleRadixBoundary:
    """One exact physical digit boundary, with distinct carry/borrow sources.

    c3 = floor(3 * (X mod m)/m) is in {0,1,2}.  q2 is the carry of 2X;
    c3-q2 is the Boolean carry of X+(2X mod m), exactly the borrow of
    3X-X.  The innovation ports refer to *temporal* X_next-X, which is
    2X for ordinary powers but X**2-X for dyadic powers.
    """

    position: int
    source_digit: int
    source_remainder: int
    tripling_carry: int
    doubling_carry: int
    tripling_add_carry: int
    tripling_sub_borrow: int
    innovation_carry: int
    innovation_borrow: int
    difference_borrow: int

    @property
    def tripling_high(self) -> int:
        return int(self.tripling_carry >= 2)

    @property
    def tripling_low(self) -> int:
        return int(self.tripling_carry >= 1)

    @property
    def innovation_xor(self) -> int:
        return self.innovation_carry ^ self.innovation_borrow

    @property
    def difference_xor(self) -> int:
        return self.innovation_carry ^ self.difference_borrow


@dataclass(frozen=True, slots=True)
class OrdinaryRadixPorts:
    """Demand-local projections of one authenticated ordinary-power tape."""

    tape: tuple[TripleRadixBoundary, ...]
    carry_word: str
    add_borrow_mask: int
    forward_borrow_mask: int
    difference_xor_mask: int
    high_mask: int
    low_mask: int


@dataclass(frozen=True, slots=True)
class CompactOrdinaryRadixPorts:
    """Aggregated ordinary-power ports without per-position boundary rows."""

    source_residue: int
    source_boundaries: tuple[int, ...] | None
    carry_word: str
    add_borrow_mask: int
    forward_borrow_mask: int
    difference_xor_mask: int
    high_mask: int
    low_mask: int


def _ordinary_port_summary(
    source: int,
    base: int,
    places: int,
    *,
    include_source_boundaries: bool,
    boundary_rows: tuple[TripleRadixBoundary, ...] | None = None,
) -> CompactOrdinaryRadixPorts:
    """Fold one resolved ordinary source into demanded aggregate ports."""
    _require_base_places(base, places)
    if type(include_source_boundaries) is not bool:
        raise TypeError("source-boundary demand must be Boolean")
    if type(source) is not int or not 0 <= source < base**places:
        raise ValueError("ordinary port source is outside its radix window")
    source_boundaries: list[int] | None = [] if include_source_boundaries else None
    carry_digits: list[str] = []
    add = forward = high = low = 0
    modulus = 1
    for position in range(places):
        modulus *= base
        if boundary_rows is None:
            remainder = source % modulus
            tripling, _doubling, add_borrow, _subtraction = _tripling_prefix_components(
                modulus, remainder
            )
        else:
            row = boundary_rows[position]
            remainder = row.source_remainder
            tripling = row.tripling_carry
            add_borrow = row.tripling_sub_borrow
        forward_borrow = int((6 * remainder) % modulus < (2 * remainder) % modulus)
        add |= add_borrow << position
        forward |= forward_borrow << position
        high |= int(tripling >= 2) << position
        low |= int(tripling >= 1) << position
        carry_digits.append(str(tripling))
        if source_boundaries is not None:
            source_boundaries.append(remainder)
    return CompactOrdinaryRadixPorts(
        source,
        None if source_boundaries is None else tuple(source_boundaries),
        "".join(reversed(carry_digits)),
        add,
        forward,
        add ^ forward,
        high,
        low,
    )


@dataclass(frozen=True, slots=True)
class ThreePowerRadixOrbit:
    """Compact, source-authenticated ordinary/dyadic low-radix action."""

    clock: ThreePowerClock | str
    level: int
    base: int

    def __post_init__(self) -> None:
        if self.clock not in ("ordinary", "dyadic"):
            raise ValueError("clock must be ordinary or dyadic")
        if type(self.level) is not int or self.level < 1:
            raise ValueError("difference-sequence observations need an index >= 1")
        _require_base_places(self.base, 1)
        object.__setattr__(self, "clock", ThreePowerClock(self.clock))

    def advance(self, steps: int) -> ThreePowerRadixOrbit:
        if type(steps) is not int or steps < 0:
            raise ValueError("advance requires a nonnegative integer")
        return ThreePowerRadixOrbit(self.clock, self.level + steps, self.base)

    def cycle(self, places: int) -> tuple[int, int]:
        if self.clock == "dyadic":
            return dyadic_clock(self.base, places)
        if self.base == 6:
            # After the 3-primary source vanishes, the binary unit continues.
            return places, max(1, 1 << max(0, places - 2)) if places != 2 else 2
        order = order_three(self.base, places)
        return (
            (0, order)
            if order is not None
            else (places * (3 if self.base == 27 else 1), 1)
        )

    def decimal_crt_coordinates(self, places: int) -> tuple[int, int, int]:
        """Recover low decimal digits from their separate 2/5-adic clocks."""
        if self.base != 10:
            raise ValueError("CRT decimal coordinates require base 10")
        return (
            triple_residue(self.clock, self.level, 2, places),
            triple_residue(self.clock, self.level, 5, places),
            self.residue(places),
        )

    def residue(self, places: int, offset: int = 0) -> int:
        if type(offset) is not int or self.level + offset < 0:
            raise ValueError("requested source index is negative")
        return triple_residue(self.clock, self.level + offset, self.base, places)

    def boundary(self, places: int) -> TripleRadixBoundary:
        _require_base_places(self.base, places)
        modulus = self.base**places
        previous = self.residue(places, -1)
        x = self.residue(places)
        future = self.residue(places, 1)
        return _boundary_from_residues(places, self.base, modulus, previous, x, future)

    def forward_innovation_borrow(self, places: int) -> int:
        """Borrow between 2*3**(q+1) and 2*3**q (ordinary clock).

        This forward borrow is distinct from the backward innovation-difference
        borrow in ``boundary`` and is what a future-seam XOR needs.
        """
        if self.clock != "ordinary":
            raise ValueError("forward innovation identity requires ordinary powers")
        modulus = self.base**places
        residue = self.residue(places)
        return int((6 * residue) % modulus < (2 * residue) % modulus)

    def forward_difference_xor(self, places: int) -> int:
        return self.boundary(
            places
        ).tripling_sub_borrow ^ self.forward_innovation_borrow(places)

    def forward_mask(self, places: int, field: str) -> int:
        """Pack demanded, forward differences; do not enumerate full powers."""
        _require_base_places(self.base, places)
        if field not in ("forward_innovation_borrow", "forward_difference_xor"):
            raise ValueError("unsupported forward difference mask")
        if self.clock != ThreePowerClock.ORDINARY:
            raise ValueError("forward innovation identity requires ordinary powers")
        source = self.residue(places)
        mask = 0
        modulus = 1
        for position in range(places):
            modulus *= self.base
            residue = source % modulus
            bit = int((6 * residue) % modulus < (2 * residue) % modulus)
            if field == "forward_difference_xor":
                bit ^= int((3 * residue) % modulus < residue)
            mask |= bit << position
        return mask

    def tape(self, places: int) -> tuple[TripleRadixBoundary, ...]:
        _require_base_places(self.base, places)
        previous = self.residue(places, -1)
        modulus = self.base**places
        source = (
            previous * previous
            if self.clock == ThreePowerClock.DYADIC
            else 3 * previous
        ) % modulus
        following = (
            source * source if self.clock == ThreePowerClock.DYADIC else 3 * source
        ) % modulus
        rows: list[TripleRadixBoundary] = []
        prefix_modulus = 1
        for position in range(1, places + 1):
            prefix_modulus *= self.base
            rows.append(
                _boundary_from_residues(
                    position,
                    self.base,
                    prefix_modulus,
                    previous % prefix_modulus,
                    source % prefix_modulus,
                    following % prefix_modulus,
                )
            )
        return tuple(rows)

    def ordinary_ports(self, places: int) -> OrdinaryRadixPorts:
        """Share source resolution across all demanded carry/borrow channels."""
        if self.clock != ThreePowerClock.ORDINARY:
            raise ValueError("forward innovation identity requires ordinary powers")
        tape = self.tape(places)
        summary = _ordinary_port_summary(
            tape[-1].source_remainder,
            self.base,
            places,
            include_source_boundaries=False,
            boundary_rows=tape,
        )
        return OrdinaryRadixPorts(
            tape,
            summary.carry_word,
            summary.add_borrow_mask,
            summary.forward_borrow_mask,
            summary.difference_xor_mask,
            summary.high_mask,
            summary.low_mask,
        )

    def compact_ordinary_ports(
        self, places: int, *, include_source_boundaries: bool = False
    ) -> CompactOrdinaryRadixPorts:
        """Aggregate ordinary ports without constructing boundary dataclasses.

        ``source_boundaries`` is retained only for callers that publish the
        per-position source remainders.  The detailed ``tape`` API remains
        available when callers need the full physical boundary records.
        """
        if self.clock != ThreePowerClock.ORDINARY:
            raise ValueError("forward innovation identity requires ordinary powers")
        _require_base_places(self.base, places)
        source = self.residue(places)
        return _ordinary_port_summary(
            source,
            self.base,
            places,
            include_source_boundaries=include_source_boundaries,
        )

    def conditional_digit_mask(self, places: int) -> int:
        """Positions whose 3d+carry rule depends on the incoming trit.

        These source-sensitive domain cells have the same finite-function
        semantics as the Collatz digit transducer.  A constant transfer is
        not an EQ/propagate cell; a nonconstant transfer may have a 0/1 or
        a 1/2 threshold, depending on radix.
        """
        machine = synthesize_multiply_add(self.base, 3, 0)
        mask = 0
        for i, row in enumerate(self.tape(places)):
            effects = {machine.step(cin, row.source_digit)[0] for cin in (0, 1, 2)}
            if len(effects) != 1:
                mask |= 1 << i
        return mask

    def mask(self, places: int, field: str) -> int:
        allowed = {
            "tripling_high",
            "tripling_low",
            "tripling_add_carry",
            "tripling_sub_borrow",
            "innovation_carry",
            "innovation_borrow",
            "difference_borrow",
            "innovation_xor",
            "difference_xor",
        }
        if field not in allowed:
            raise ValueError("unsupported Boolean carry mask")
        return sum(getattr(row, field) << i for i, row in enumerate(self.tape(places)))

    def carry_word(self, places: int) -> str:
        """All base-b multiplication carries MSB-first, retaining 0/1/2."""
        return "".join(str(row.tripling_carry) for row in reversed(self.tape(places)))

    def mask_word(self, places: int, field: str) -> str:
        return format(self.mask(places, field), f"0{places}b")


def difference_power_block(
    exponent: int, gap: int, modulus: int
) -> tuple[int, int, int]:
    """(raw difference, exact v2, normalized difference) modulo ``modulus``.

    The normalized field (3**(q+gap)-3**q)/2**v is computed by lifting
    only the demanded modulus, not by constructing either large power.
    No Collatz affine denominator is cancelled by this observation alone.
    """
    if (
        any(type(x) is not int for x in (exponent, gap, modulus))
        or exponent < 0
        or gap < 1
        or modulus < 2
    ):
        raise ValueError("difference field needs q>=0, gap>=1, modulus>=2")
    valuation = 1 if gap & 1 else 2 + ((gap & -gap).bit_length() - 1)
    if valuation + modulus.bit_length() > 8192:
        raise ValueError("difference-field 2-adic lift exceeds the bit budget")
    lifted = modulus << valuation
    reduced = (pow(3, exponent, lifted) * (pow(3, gap, lifted) - 1)) % lifted
    if reduced % (1 << valuation):
        raise AssertionError("difference-field dyadic cancellation failed")
    return reduced % modulus, valuation, (reduced >> valuation) % modulus


def _boundary_from_residues(
    places: int, base: int, modulus: int, previous: int, x: int, future: int
) -> TripleRadixBoundary:
    c3, c2, add_carry, subtraction = _tripling_prefix_components(modulus, x)
    innovation = (future - x) % modulus
    previous_innovation = (x - previous) % modulus
    innovation_carry = int(x + innovation >= modulus)
    innovation_borrow = int(future < x)
    if innovation_carry != innovation_borrow:
        raise AssertionError("carry/borrow duality failed")
    return TripleRadixBoundary(
        places,
        x // (modulus // base),
        x,
        c3,
        c2,
        add_carry,
        subtraction,
        innovation_carry,
        innovation_borrow,
        int(innovation < previous_innovation),
    )


def _tripling_prefix_components(
    modulus: int, remainder: int
) -> tuple[int, int, int, int]:
    """Return tripling/doubling carries and their exact borrow duals."""
    tripling = 3 * remainder // modulus
    doubling = 2 * remainder // modulus
    add_carry = tripling - doubling
    subtraction_borrow = int((3 * remainder) % modulus < remainder)
    if add_carry != subtraction_borrow:
        raise AssertionError("tripling carry and subtraction borrow disagree")
    return tripling, doubling, add_carry, subtraction_borrow
