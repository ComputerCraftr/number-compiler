"""Source-root temporal squares for the Fermat 3**(2**t) family.

Port of the *source-identity/adjacency* rule of 2rev10's
``CertifiedSeedOrbitMorphism``, NOT a port of its digit-reversal stencil.
A root here is the exact exponent-circuit expression 3**(2**level), not an
SLP supporting arbitrary binary-digit reads.  All observed low cyclotomic,
high radial, signed 2w and carry packets are reissued at the actual second
half's exponent level; no temporal repetition of an unknown middle is assumed.

The finite source-root square is mathematically certified for any permitted
levels, but the *interior-normalized* phase action remains open until its
cyclic-convolution carry histogram is source-certified.  In particular this
module does not evaluate a Fermat-candidate modulus or prove the prime bit.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, TypedDict, Unpack

from number_compiler.arithmetic.carry.carry_normalization import (
    linear_normalization_fields,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    ConvolutionMetrics,
    fold_cyclic,
    karatsuba_square,
)
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)

MAX_EXACT_PHASE_SQUARE_PERIOD = 512
MAX_EXACT_SQUARE_SOURCE_BITS = 256
MAX_EXACT_SQUARE_PRODUCTS = 36 * 3**5
MAX_SOURCE_LEVEL = 65_535
MAX_SOURCE_INDEX = 8


class FermatSourceOptions(TypedDict, total=False):
    """Bounded options accepted by a source action constructor."""

    phase_binary_places: int
    phase_decimal_places: int
    binary_windows: tuple[tuple[int, int], ...]
    decimal_windows: tuple[tuple[int, int], ...]
    low_binary_places: int
    low_decimal_places: int
    high_binary_places: int
    high_decimal_places: int


class FermatSourceDemandOptions(FermatSourceOptions, total=False):
    """Source options plus limits for the source-restricted observation."""

    max_fibers: int
    inward_boundaries: int


if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
    from number_compiler.sequences.power_numbers.three_power_signed_phase import (
        SourceRestrictedPhaseRelation,
    )
    from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
        FermatTwoSidedSourceCylinder,
    )


def cyclic_square_coefficients(counts: tuple[int, ...]) -> tuple[int, ...]:
    """Exact unnormalized 2w-phase coefficient convolution.

    This is a *spatial* polynomial operation for an already authenticated
    histogram, not a Fermat-prime shortcut or a temporal driver-period proof.
    It does not produce the normalized binary output histogram by itself.
    """
    length = len(counts)
    if (
        length == 0
        or length % 2
        or length > MAX_EXACT_PHASE_SQUARE_PERIOD
        or any(type(v) is not int or v < 0 for v in counts)
    ):
        raise ValueError("invalid exact source 2w phase histogram")
    ordinary, _metrics = karatsuba_square(counts, threshold=8)
    return fold_cyclic(ordinary, length)


def certify_phase_square_carries(
    source: tuple[int, ...],
    target: tuple[int, ...],
    ingresses: tuple[int, ...],
) -> None:
    """Check ALL normalized inner carry emissions for a dyadic square.

    Define z_j = sum_(a+b=j) d_a d_b, and c_j the carry *entering* bit j
    when normalizing z.  Then d'_j = z_j + c_j - 2*c_(j+1).
    Summing over j modulo 2w gives the identity checked here.  Unlike an H5
    summary it keeps unbounded integer carries and the exact wrap phase.

    These values must come from an independently authenticated complete source
    grammar; this checker never invents them from border RESET actions.
    """
    period = len(source)
    if (
        period == 0
        or period % 2
        or period > MAX_EXACT_PHASE_SQUARE_PERIOD
        or len(target) != period
        or len(ingresses) != period
    ):
        raise ValueError("incompatible signed phase-square dimensions")
    if any(type(v) is not int or v < 0 for v in (*source, *target, *ingresses)):
        raise ValueError("invalid phase/carry histogram entries")
    raw = cyclic_square_coefficients(source)
    for r in range(period):
        if target[r] != raw[r] + ingresses[r] - 2 * ingresses[(r + 1) % period]:
            raise ArithmeticError(
                f"source square's signed carry relation fails at phase {r}"
            )


def _integer_phase_counts(value: int, period: int) -> tuple[int, ...]:
    counts = [0] * period
    position = 0
    while value:
        counts[position % period] += value & 1
        value >>= 1
        position += 1
    return tuple(counts)


def _square_product_upper_bound(bit_length: int) -> int:
    padded = 1 << (bit_length - 1).bit_length()
    if padded <= 8:
        return padded * (padded + 1) // 2
    levels = (padded // 8).bit_length() - 1
    bound = 36
    for _ in range(levels):
        bound *= 3
    return bound


@dataclass(frozen=True, slots=True, weakref_slot=True)
class ExactNormalizedSquareResponse:
    """One authenticated source-cylinder member and its exact binary square.

    The bounded convolution and subsequent carry normalization are computed
    from the selected source word.  The result is a one-step observation; it
    does not establish a reusable future quotient or a primality result.
    """

    index: int
    source_level: int
    target_level: int
    source: int
    target: int
    fold_width: int
    source_counts: tuple[int, ...]
    target_counts: tuple[int, ...]
    ingress_counts: tuple[int, ...]
    source_edges: tuple[tuple[int, int], ...]
    target_edges: tuple[tuple[int, int], ...] | None
    convolution: ConvolutionMetrics
    _temporal_payload: tuple[object, ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def _payload(self) -> tuple[object, ...]:
        return (
            self.index,
            self.source_level,
            self.target_level,
            self.source,
            self.target,
            self.fold_width,
            self.source_counts,
            self.target_counts,
            self.ingress_counts,
            self.source_edges,
            self.target_edges,
            self.convolution,
            self._temporal_payload,
        )

    @property
    def producer_verified(self) -> bool:
        return harmonic_verified(self, self._payload(), issuer=_SQUARE_RESPONSE_ISSUER)

    @property
    def next_source_admitted(self) -> bool:
        if not self.producer_verified:
            raise ValueError("unissued or modified normalized-square response")
        return self.target_edges is not None

    @property
    def scalar_products(self) -> int:
        if not self.producer_verified:
            raise ValueError("unissued or modified normalized-square response")
        return self.convolution.scalar_multiplications


_SQUARE_RESPONSE_ISSUER = new_harmonic_issuer(ExactNormalizedSquareResponse)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class CertifiedFermatRootTemporalMorphism:
    """Authentic Fermat exponent-circuit root-to-root temporal action.

    This is the sound part of the 2rev10 temporal-square architecture:
    issue the second half from the true first-half endpoint, and refuse
    nonadjacent/foreign/mutated records.  It does NOT possess 2rev10's full
    digit-addressable Hashlife SLP root; unknown phase-count emissions are
    retained instead of being filled by an unproved orbit.
    """

    index: int
    source_level: int
    dyadic_steps: int
    first: SourceRestrictedPhaseRelation = field(repr=False)
    last: SourceRestrictedPhaseRelation = field(repr=False)
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def _payload(self) -> tuple[object, ...]:
        return (
            self.index,
            self.source_level,
            self.dyadic_steps,
            self.first._payload(),
            self.last._payload(),
        )

    @property
    def target_level(self) -> int:
        return self.source_level + self.dyadic_steps

    @property
    def root_expression(self) -> str:
        return f"3**(2**{self.source_level})"

    @property
    def target_root_expression(self) -> str:
        return f"3**(2**{self.target_level})"

    @property
    def producer_verified(self) -> bool:
        if not harmonic_verified(self, self._payload(), issuer=_TEMPORAL_ISSUER):
            return False
        if not self.first.producer_verified or not self.last.producer_verified:
            return False
        if (
            type(self.index) is not int
            or not 1 <= self.index <= MAX_SOURCE_INDEX
            or type(self.dyadic_steps) is not int
            or self.dyadic_steps <= 0
            or self.source_level < 1
            or self.target_level > MAX_SOURCE_LEVEL
        ):
            return False
        w = 1 << self.index
        left = self.first.outer_inner.clock
        right = self.last.outer_inner.clock
        if (
            self.source_level != left.level
            or self.target_level != right.level
            or self.first.phase.source_index != self.index
            or self.last.phase.source_index != self.index
            or self.first.phase.fold_width != w
            or self.last.phase.fold_width != w
            or left.physical_offset != 0
            or right.physical_offset != 0
        ):
            return False
        # Exact dyadic level-to-level source clock, not a repeated carry word.
        return (
            right.physical_phase
            == (left.physical_phase * pow(2, self.dyadic_steps, 20)) % 20
        )

    @property
    def signed_phase_histograms_complete(self) -> bool:
        if not self.producer_verified:
            raise ValueError("unissued Fermat source-temporal morphism")
        return (
            not self.first.phase.unknown_intervals
            and not self.last.phase.unknown_intervals
        )

    @property
    def all_inner_carries_certified(self) -> bool:
        """No arbitrary-depth normalized carry witness is issued here.

        Complete endpoint histograms do not by themselves validate a claimed
        normalization history.  A separately certified *complete* source/carry
        program can be checked with ``certify_phase_square_carries``.
        """
        if not self.producer_verified:
            raise ValueError("unissued Fermat source-temporal morphism")
        return False

    @property
    def signed_phase_status(self) -> str:
        if not self.producer_verified:
            raise ValueError("unissued Fermat source-temporal morphism")
        return (
            "COMPLETE_ENDPOINTS_UNCERTIFIED_CARRIES"
            if self.signed_phase_histograms_complete
            else "OPEN_CARRY_HISTOGRAM"
        )

    @property
    def terminal_status(self) -> str:
        """A temporal root identity is never silently a Fermat prime bit."""
        if not self.producer_verified:
            raise ValueError("unissued Fermat source-temporal morphism")
        return "UNKNOWN"

    @property
    def exact_signed_root(self) -> int | None:
        """Never infer the global signed fold from a physical border reset."""
        if not self.producer_verified:
            raise ValueError("unissued Fermat source-temporal morphism")
        return self.last.complete_signed_fold

    def then(
        self, later: CertifiedFermatRootTemporalMorphism
    ) -> CertifiedFermatRootTemporalMorphism:
        """Compose only the actual, authenticated shared exponent root."""
        if not self.producer_verified or not later.producer_verified:
            raise ValueError("unissued Fermat source-temporal action")
        if (
            self.index != later.index
            or self.target_level != later.source_level
            or self.last is not later.first
        ):
            raise ValueError("temporal square needs the actual previous endpoint root")
        return _issue(
            self.index,
            self.source_level,
            self.dyadic_steps + later.dyadic_steps,
            self.first,
            later.last,
        )

    def square(
        self,
        spec: FermatNumberSpec,
        **demand_kwargs: Unpack[FermatSourceDemandOptions],
    ) -> CertifiedFermatRootTemporalMorphism:
        """Reissue the second temporal half from the exact first-half root.

        ``square`` denotes doubling the temporal *duration*, not assuming
        repeatability of a driver and not squaring modulo F_n.  Source-level
        dyadic squaring is the algebraic successor X_(t+1)=X_t**2.
        """
        if not self.producer_verified or spec.index != self.index:
            raise ValueError("foreign/unissued Fermat temporal source")
        later = demand_fermat_source_temporal_morphism(
            spec,
            self.target_level,
            self.dyadic_steps,
            known_first=self.last,
            **demand_kwargs,
        )
        return self.then(later)

    def power_of_two(
        self,
        spec: FermatNumberSpec,
        exponent: int,
        **demand_kwargs: Unpack[FermatSourceDemandOptions],
    ) -> CertifiedFermatRootTemporalMorphism:
        """Repeated genuine source-root temporal squares; no guessed period."""
        if type(exponent) is not int or not 0 <= exponent <= 32:
            raise ValueError("invalid temporal squaring power")
        current = self
        for _ in range(exponent):
            current = current.square(spec, **demand_kwargs)
        return current

    def normalized_square_response(
        self,
        source: int,
        *,
        max_source_bits: int = MAX_EXACT_SQUARE_SOURCE_BITS,
        max_products: int = MAX_EXACT_SQUARE_PRODUCTS,
    ) -> ExactNormalizedSquareResponse:
        """Demand the exact normalized square for one admitted source point.

        This bounded one-step consumer uses both endpoint cylinders already
        carried by a root morphism.  It never enumerates a cylinder, and a
        failed next-level guard is represented explicitly as ``False`` rather
        than being filled by a guessed carry orbit.  Multi-step morphisms are
        refused because an endpoint pair alone does not supply the intervening
        carry responses.
        """
        if not self.producer_verified:
            raise ValueError("unissued Fermat source-temporal morphism")
        if self.dyadic_steps != 1:
            raise ValueError("normalized square response requires one temporal step")
        if type(source) is not int or source <= 0:
            raise ValueError(
                "normalized square source must be a positive exact integer"
            )
        if (
            type(max_source_bits) is not int
            or not 1 <= max_source_bits <= MAX_EXACT_SQUARE_SOURCE_BITS
            or type(max_products) is not int
            or not 1 <= max_products <= MAX_EXACT_SQUARE_PRODUCTS
        ):
            raise ValueError("invalid normalized square work budget")

        source_bits = source.bit_length()
        if source_bits > max_source_bits:
            raise ValueError("source square exceeds the exact carry-convolution budget")
        first_cylinder = self.first.cylinder
        source_edges = _admitted_cylinder_point(first_cylinder, source)
        if source_edges is None:
            raise ValueError(
                "square source is outside the authenticated source cylinder"
            )
        if _square_product_upper_bound(source_bits) > max_products:
            raise ValueError("source square exceeds the exact cross-term budget")

        fold_width = self.first.phase.fold_width
        period = 2 * fold_width
        if period > MAX_EXACT_PHASE_SQUARE_PERIOD:
            raise ValueError(
                "source square phase period exceeds the exact response budget"
            )
        bits = tuple((source >> position) & 1 for position in range(source_bits))
        coefficients, convolution = karatsuba_square(bits, threshold=8)
        if convolution.scalar_multiplications > max_products:
            raise ArithmeticError(
                "shared square convolution exceeded its admitted budget"
            )
        output_bits, carries = linear_normalization_fields(coefficients, base=2)

        target = 0
        target_counts = [0] * period
        ingress_counts = [0] * period
        for position, (digit, ingress) in enumerate(
            zip(output_bits, carries[:-1], strict=True)
        ):
            if digit not in (0, 1) or ingress < 0:
                raise ArithmeticError(
                    "binary square normalization produced an invalid digit"
                )
            ingress_counts[position % period] += ingress
            if digit:
                target |= 1 << position
                target_counts[position % period] += 1

        position = len(output_bits)
        carry = carries[-1]
        while carry:
            ingress_counts[position % period] += carry
            digit = carry & 1
            if digit:
                target |= 1 << position
                target_counts[position % period] += 1
            carry >>= 1
            position += 1
        if target != source * source:
            raise ArithmeticError(
                "normalized square disagrees with the exact integer product"
            )

        source_counts = _integer_phase_counts(source, period)
        target_count_tuple = tuple(target_counts)
        ingress_count_tuple = tuple(ingress_counts)
        certify_phase_square_carries(
            source_counts, target_count_tuple, ingress_count_tuple
        )
        target_edges = _admitted_cylinder_point(self.last.cylinder, target)
        response = ExactNormalizedSquareResponse(
            self.index,
            self.source_level,
            self.target_level,
            source,
            target,
            fold_width,
            source_counts,
            target_count_tuple,
            ingress_count_tuple,
            source_edges,
            target_edges,
            convolution,
            self._payload(),
        )
        issue_harmonic(response, response._payload(), issuer=_SQUARE_RESPONSE_ISSUER)
        if not response.producer_verified:
            raise ArithmeticError("normalized square response publication failed")
        return response


def _admitted_cylinder_point(
    cylinder: FermatTwoSidedSourceCylinder, value: int
) -> tuple[tuple[int, int], ...] | None:
    """Check exact coset membership and the producer's full source guards."""
    if not cylinder.producer_verified:
        raise ValueError("unissued or modified Fermat source cylinder")
    if (
        type(value) is not int
        or value <= 0
        or value % cylinder.combined_modulus != cylinder.combined_residue
    ):
        return None
    interval = cylinder.exact_interval
    if interval is not None and not interval.contains(value):
        return None
    return cylinder._admitted(value)


_TEMPORAL_ISSUER = new_harmonic_issuer(CertifiedFermatRootTemporalMorphism)


def _issue(
    index: int,
    level: int,
    steps: int,
    first: SourceRestrictedPhaseRelation,
    last: SourceRestrictedPhaseRelation,
) -> CertifiedFermatRootTemporalMorphism:
    result = CertifiedFermatRootTemporalMorphism(index, level, steps, first, last)
    issue_harmonic(result, result._payload(), issuer=_TEMPORAL_ISSUER)
    if not result.producer_verified:
        raise ArithmeticError("dyadic source clock or source owner was not preserved")
    return result


def demand_fermat_source_temporal_morphism(
    spec: FermatNumberSpec,
    source_level: int,
    dyadic_steps: int = 1,
    *,
    known_first: SourceRestrictedPhaseRelation | None = None,
    **demand_kwargs: Unpack[FermatSourceDemandOptions],
) -> CertifiedFermatRootTemporalMorphism:
    """Issue exact source roots and independently bound outer/inner endpoints.

    An explicit ``known_first`` can only be an existing producer-authenticated
    *same family/level* endpoint.  The end packet is always reissued from the
    actual dyadic family source, not a repeated driver motif or a square of
    the first packet's unknown phase capacities.
    """
    if (
        type(spec.index) is not int
        or not 1 <= spec.index <= MAX_SOURCE_INDEX
        or type(source_level) is not int
        or not 1 <= source_level <= MAX_SOURCE_LEVEL
        or type(dyadic_steps) is not int
        or not 1 <= dyadic_steps <= MAX_SOURCE_LEVEL
    ):
        raise ValueError("invalid Fermat temporal exponent interval")
    target_level = source_level + dyadic_steps
    if target_level > MAX_SOURCE_LEVEL or not spec.exponent_extent.contains_index(
        target_level
    ):
        raise ValueError(
            "dyadic action exceeds the candidate's signed terminal horizon"
        )
    first = known_first
    if first is None:
        first = spec.demand_three_power_source_restricted_phase(
            source_level, **demand_kwargs
        )
    if (
        not first.producer_verified
        or first.phase.source_index != spec.index
        or first.outer_inner.clock.level != source_level
    ):
        raise ValueError("unissued/foreign earlier Fermat source root")
    last = spec.demand_three_power_source_restricted_phase(
        target_level, **demand_kwargs
    )
    return _issue(spec.index, source_level, dyadic_steps, first, last)


__all__ = (
    "CertifiedFermatRootTemporalMorphism",
    "ExactNormalizedSquareResponse",
    "FermatSourceDemandOptions",
    "FermatSourceOptions",
    "certify_phase_square_carries",
    "cyclic_square_coefficients",
    "demand_fermat_source_temporal_morphism",
)
