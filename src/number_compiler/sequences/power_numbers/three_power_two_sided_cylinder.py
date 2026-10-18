"""Source-owned Fermat binary/decimal CRT + radial intervals + signed phase fibers.

This ports the *conditional* interval/coset idea of NC17 Mahler without
pretending that a periodic low residue or a leading carry RESET fixes an
unobserved middle.  The cyclotomic low residues and the independently
certified leading digits are intersected on ONE integer source.  A bounded
fiber may produce exact, correlated signed 2w phase/carry histories; a large
fiber remains an open source inlet, never a synthetic phase histogram.

There is no modular squaring, enormous source creation, or prime lookup here.
A transported cylinder retains the full multiplied CRT stride (including its
factor 3); replacing it by the original 2/5 CRT projection is unsound.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.carry.signed_phase import (
    BinaryPhaseCarryAction,
    signed_phase_fold,
)
from number_compiler.arithmetic.fields.integer_congruence import join_congruences
from number_compiler.arithmetic.fields.integer_cylinder import IntegerCylinder
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
        FermatOuterCyclotomicClock,
    )
    from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
        SourceWeightedTriplingAction,
    )

MAX_EXPLICIT_SOURCE_BITS = 65_536
MAX_EXPLICIT_DECIMAL_DIGITS = 19_730  # > 65536 * log10(2)
MAX_EXPLICIT_PHASE_FOLD_WIDTH = 8_192
MAX_PHASE_FIBER_BIT_WORK = 4_194_304
MAX_FIBER_LIMIT = 4_096


def _terminal_status_from_signed_folds(
    source_level: int, fold_width: int, signed_folds: tuple[int, ...]
) -> str:
    """Classify only a complete finite source fiber at the terminal level."""
    if source_level != fold_width - 1 or not signed_folds:
        return "UNKNOWN"
    terminal_residue = 1 << fold_width
    if all(value == terminal_residue for value in signed_folds):
        return "PRIME"
    if all(value != terminal_residue for value in signed_folds):
        return "COMPOSITE"
    return "UNKNOWN"


def _validate_fiber_limit(limit: int) -> None:
    if type(limit) is not int or not 1 <= limit <= MAX_FIBER_LIMIT:
        raise ValueError(f"source fiber limit must be in 1..{MAX_FIBER_LIMIT}")


@dataclass(frozen=True, slots=True)
class ExactAffineSourceCylinder(IntegerCylinder):
    """Family name for shared interval/coset geometry plus 3X transport."""

    def multiply_three(self) -> Self:
        return self.affine_image(3)


def crt_join(a: int, m: int, b: int, n: int) -> tuple[int, int]:
    """Join source projections through the shared generalized CRT owner."""
    if any(type(v) is not int for v in (a, m, b, n)) or m < 1 or n < 1:
        raise ValueError("invalid CRT source projections")
    joined = join_congruences((a % m, m), (b % n, n))
    if joined is None:
        raise ArithmeticError("binary and decimal source residues disagree")
    return joined


@dataclass(frozen=True, slots=True)
class SignedCylinderFiber:
    """One possible complete source history, not an imported prime verdict."""

    source_phase_counts: tuple[int, ...]
    output_phase_counts: tuple[int, ...]
    carry_phase_counts: tuple[int, ...]
    signed_source: int
    signed_output: int
    boundary_edges: tuple[tuple[int, int], ...]


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatTwoSidedSourceCylinder:
    """Issuer-bound joint binary/decimal high/low source-language cylinder.

    For sources with billions of digits, ``exact_interval=None`` indicates
    that the exact interval exists mathematically but cannot be represented
    under the explicit resource limit. Low residues and high guards remain
    authoritative; no global phase-count claim follows from them.
    """

    source: SourceWeightedTriplingAction
    combined_residue: int
    combined_modulus: int
    binary_low_bits: int
    decimal_low_digits: int
    source_high_bits: int
    source_high_prefix: int
    exact_interval: ExactAffineSourceCylinder | None
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    @property
    def producer_verified(self) -> bool:
        return self.source.producer_verified and harmonic_verified(
            self, self._payload(), issuer=_CYLINDER_ISSUER
        )

    def _payload(self) -> tuple[object, ...]:
        return (
            self.source._payload(),
            self.combined_residue,
            self.combined_modulus,
            self.binary_low_bits,
            self.decimal_low_digits,
            self.source_high_bits,
            self.source_high_prefix,
            self.exact_interval,
        )

    @property
    def full_interval_available(self) -> bool:
        return self.producer_verified and self.exact_interval is not None

    @property
    def candidate_count(self) -> int | None:
        if not self.producer_verified:
            raise ValueError("unissued/modified Fermat source cylinder")
        return None if self.exact_interval is None else self.exact_interval.count

    @property
    def outer_clock(self) -> FermatOuterCyclotomicClock:
        """Exact mod-9900 source clock, separate from ordinary tripling offset."""
        from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
            FermatOuterCyclotomicClock,
        )

        return FermatOuterCyclotomicClock.from_level(self.source.level)

    def _admitted(self, x: int) -> tuple[tuple[int, int], ...] | None:
        """Validate ONE entire correlated source/carry path and decimal guards."""
        s = self.source
        if x.bit_length() != s.origin.bilateral.binary.source_digits:
            return None
        decimal = s.origin.bilateral.decimal
        suffix = 10**decimal.low_places
        if x % suffix != decimal.low_source:
            return None
        for window in s.origin.decimal_middle.windows:
            if (x // 10**window.start) % (10**window.width) != window.radix_value:
                return None
        decimal_shift = decimal.source_digits - decimal.high_places
        if x // 10**decimal_shift != decimal.source_top:
            return None
        y = 3 * x
        if y % suffix != decimal.low_product:
            return None
        if (
            y // 10 ** (decimal.target_digits - decimal.high_places)
            != decimal.target_top
        ):
            return None
        carry = 0
        edges: list[tuple[int, int]] = []
        for block, allowed in zip(s.blocks, s.admissible_edges, strict=True):
            part = (x >> block.start) & ((1 << block.width) - 1)
            if block.source_value is not None and part != block.source_value:
                return None
            outgoing = (3 * part + carry) >> block.width
            if (carry, outgoing) not in allowed:
                return None
            edges.append((carry, outgoing))
            carry = outgoing
        return tuple(edges)

    def bounded_phase_fibers(
        self, limit: int = 64
    ) -> tuple[SignedCylinderFiber, ...] | None:
        """Carry and signed 2w histories for *all* members of a small cylinder.

        ``None`` means proof precision is insufficient. No source history is
        guessed. No candidate-modulus square is performed.
        """
        if not self.producer_verified:
            raise ValueError("unissued/modified Fermat source cylinder")
        _validate_fiber_limit(limit)
        interval = self.exact_interval
        width = self.source.fold_width
        length = self.source.origin.bilateral.binary.source_digits
        if (
            interval is None
            or width > MAX_EXPLICIT_PHASE_FOLD_WIDTH
            or interval.count > limit
            or interval.count * length > MAX_PHASE_FIBER_BIT_WORK
        ):
            return None
        candidates = interval.enumerated(limit)
        if candidates is None:
            return None
        fibers: list[SignedCylinderFiber] = []
        for x in candidates:
            edges = self._admitted(x)
            if edges is None:
                continue
            action = BinaryPhaseCarryAction.from_word(x, length, width)
            out = action.carry_out[0]
            signed_x = signed_phase_fold(action.source_counts, width)
            signed_y = signed_phase_fold(action.output_counts[0], width)
            source_mod = (1 << width) + 1
            signed_y = (signed_y + (out << length) % source_mod) % source_mod
            if signed_y != 3 * signed_x % source_mod:
                raise ArithmeticError("correlated cylinder lost signed carry seam")
            if out != edges[-1][1]:
                raise ArithmeticError("correlated cylinder lost high carry guard")
            fibers.append(
                SignedCylinderFiber(
                    action.source_counts,
                    action.output_counts[0],
                    action.ingress_counts[0],
                    signed_x,
                    signed_y,
                    edges,
                )
            )
        if not fibers:
            raise ArithmeticError("source cylinder has no valid carry/decimal fiber")
        return tuple(fibers)

    def signed_fold_if_forced(self, limit: int = 64) -> int | None:
        """Only certify a signed fold if *every* admitted source agrees."""
        fibers = self.bounded_phase_fibers(limit)
        if fibers is None:
            return None
        values = {f.signed_source for f in fibers}
        return next(iter(values)) if len(values) == 1 else None

    def _binary_coset_ingress_options(self, boundary: int) -> tuple[int, ...]:
        """All ordinary-tripling carries allowed by the *complete low coset*.

        For j>B, x mod 2**j ranges through r+2**B*t for
        0<=t<2**(j-B), because the odd part of the CRT stride is a unit
        modulo 2**(j-B). Each possible carry c is determined by a short
        linear inequality in t. This is a finite symbolic calculation, not
        enumeration of the orbit or the source. Upper guards can only remove
        possibilities, so this domain is a certified safe superset.
        """
        j = boundary
        b = self.binary_low_bits
        if j <= b:
            return ((3 * (self.combined_residue % (1 << j))) >> j,)
        if j > 8192:
            return (0, 1, 2)  # refuse excessive precision, never guess
        r = self.combined_residue % (1 << b)
        high = (1 << (j - b)) - 1
        base = 3 << b
        denom = 1 << j
        possible = []
        for carry in (0, 1, 2):
            # carry*2**j <= 3*(r+2**b*t) < (carry+1)*2**j
            lo = -((3 * r - carry * denom) // base)
            hi = ((carry + 1) * denom - 1 - 3 * r) // base
            if max(0, lo) <= min(high, hi):
                possible.append(carry)
        return tuple(possible)

    def ingress_options(self, boundary: int, limit: int = 64) -> tuple[int, ...]:
        """Safe exact forced-carry query; if unresolved keep ALL possible ports."""
        if not self.producer_verified:
            raise ValueError("unissued/modified Fermat source cylinder")
        _validate_fiber_limit(limit)
        if (
            type(boundary) is not int
            or not 0 <= boundary <= self.source.origin.bilateral.binary.source_digits
        ):
            raise ValueError("carry boundary lies outside source")
        domain = set(self._binary_coset_ingress_options(boundary))
        if len(domain) == 1:
            return tuple(domain)
        interval = self.exact_interval
        source_length = self.source.origin.bilateral.binary.source_digits
        candidates = None
        if (
            interval is not None
            and interval.count <= limit
            and interval.count * source_length <= MAX_PHASE_FIBER_BIT_WORK
        ):
            candidates = interval.enumerated(limit)
        if candidates is not None:
            # Carry projection needs exact admitted source words, not their
            # signed phase histories. Keep that work out of each boundary
            # query; the relation builds those histories once for all ports.
            carry_options: set[int] = set()
            boundary_modulus = 1 << boundary
            for x in candidates:
                if self._admitted(x) is not None:
                    carry_options.add((3 * (x % boundary_modulus)) >> boundary)
            if not carry_options:
                raise ArithmeticError(
                    "source cylinder has no valid carry/decimal fiber"
                )
            return tuple(sorted(carry_options))
        for block, edges in zip(
            self.source.blocks, self.source.admissible_edges, strict=True
        ):
            if block.start == boundary:
                domain.intersection_update(ci for ci, _ in edges)
            if block.start + block.width == boundary:
                domain.intersection_update(co for _, co in edges)
        if not domain:
            raise ArithmeticError("low coset and high carry constraints contradict")
        return tuple(sorted(domain))

    def terminal_predicate(self, limit: int = 64) -> str:
        """Certify Pépin's terminal predicate only if *all* fibers agree.

        A complete small cylinder gives an ordinary exact arithmetic proof,
        not a generic fast-prime quotient. An unenumerated middle is UNKNOWN.
        Never use an untrusted local carry RESET as a primality decision.
        """
        if not self.producer_verified:
            raise ValueError("unissued/modified Fermat source cylinder")
        w = self.source.fold_width
        fibers = self.bounded_phase_fibers(limit)
        if fibers is None:
            return "UNKNOWN"
        return _terminal_status_from_signed_folds(
            self.source.level, w, tuple(fiber.signed_source for fiber in fibers)
        )

    def transported_target(self) -> ExactAffineSourceCylinder | None:
        """One guarded *ordinary tripling* step, retaining the ENTIRE 3*M stride.

        This is not a dyadic jump or a global temporal period theorem.
        For a huge fiber, refuse a synthetic target-cylinder certificate.
        """
        if not self.producer_verified:
            raise ValueError("unissued/modified Fermat source cylinder")
        if self.exact_interval is None:
            return None
        result = self.exact_interval.affine_image(3)
        binary = self.source.origin.bilateral.binary
        decimal = self.source.origin.bilateral.decimal
        bshift = binary.target_digits - binary.high_places
        low = binary.target_top << bshift
        high = ((binary.target_top + 1) << bshift) - 1
        binary_target = result.intersect_interval(low, high)
        if binary_target is None:
            raise ArithmeticError("binary target Sturmian guard excludes all sources")
        result = binary_target
        dshift = decimal.target_digits - decimal.high_places
        decimal_target = result.intersect_interval(
            decimal.target_top * 10**dshift, (decimal.target_top + 1) * 10**dshift - 1
        )
        if decimal_target is None:
            raise ArithmeticError("decimal target Sturmian guard excludes all sources")
        result = decimal_target
        if result.modulus != 3 * self.combined_modulus:
            raise ArithmeticError("tripling lost a factor of 3 from exact CRT stride")
        if result.first % 9_900 != self.outer_clock.advance(1).residue9900:
            raise ArithmeticError(
                "tripling target disagrees with the outer source clock"
            )
        return result


_CYLINDER_ISSUER = new_harmonic_issuer(FermatTwoSidedSourceCylinder)


def demand_two_sided_source_cylinder(
    source: SourceWeightedTriplingAction,
) -> FermatTwoSidedSourceCylinder:
    """Join independently certified source orbits and radial leading guards."""
    from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
        OUTER_MODULUS,
        FermatOuterCyclotomicClock,
    )

    if not source.producer_verified:
        raise ValueError("two-sided cylinder requires an issued source occurrence")
    binary = source.origin.bilateral.binary
    decimal = source.origin.bilateral.decimal
    bbank = source.origin.binary_phase_bank
    dbank = source.origin.decimal_phase_bank
    if (
        bbank is None
        or dbank is None
        or not bbank.producer_verified
        or not dbank.producer_verified
    ):
        raise ValueError("source cylinder requires both exact phase banks")
    # Both residue channels refer to the SAME integer X_t. Join their complete
    # source residues (not carry observations) with generalized CRT.
    residue, modulus = crt_join(
        bbank.source_prefix,
        1 << bbank.depth,
        dbank.source_prefix,
        10**dbank.depth,
    )
    outer_clock = FermatOuterCyclotomicClock.from_level(source.level)
    residue, modulus = crt_join(
        residue, modulus, outer_clock.residue9900, OUTER_MODULUS
    )
    if residue % (1 << binary.low_places) != binary.low_source:
        raise ArithmeticError("joined CRT contradicts certified low binary border")
    if residue % (10**decimal.low_places) != decimal.low_source:
        raise ArithmeticError("joined CRT contradicts certified low decimal border")
    interval = None
    total_bits = binary.source_digits
    if (
        total_bits <= MAX_EXPLICIT_SOURCE_BITS
        and decimal.source_digits <= MAX_EXPLICIT_DECIMAL_DIGITS
    ):
        shift = total_bits - binary.high_places
        low = binary.source_top << shift
        high = ((binary.source_top + 1) << shift) - 1
        cylinder = ExactAffineSourceCylinder(low, high, residue, modulus)
        decimal_shift = decimal.source_digits - decimal.high_places
        bounded_cylinder = cylinder.intersect_interval(
            decimal.source_top * 10**decimal_shift,
            (decimal.source_top + 1) * 10**decimal_shift - 1,
        )
        if bounded_cylinder is None:
            raise ArithmeticError(
                "decimal high digits disagree with binary source cylinder"
            )
        interval = bounded_cylinder
    result = FermatTwoSidedSourceCylinder(
        source,
        residue,
        modulus,
        bbank.depth,
        dbank.depth,
        binary.high_places,
        binary.source_top,
        interval,
    )
    issue_harmonic(result, result._payload(), issuer=_CYLINDER_ISSUER)
    return result


__all__ = [
    "ExactAffineSourceCylinder",
    "FermatTwoSidedSourceCylinder",
    "SignedCylinderFiber",
    "crt_join",
    "demand_two_sided_source_cylinder",
]
