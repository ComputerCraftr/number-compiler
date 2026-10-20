"""Exact two-sided radix-6/carry witness on an already-issued Collatz word.

This module is a *dependent port*, never a successor oracle.  An authentic
source cylinder and an issued affine action determine the endpoint cylinder.
The proven initial base-6 5 bands propagate through arbitrary mixed parity
words as [a+odd_events, b-normalized_steps).  For a word centered at -1,
there is an additional 3-primary *birth* of low 5 digits, established from
source-wide 2/3-adic divisibility, not from a sampled phase.

The upper bands come from exact endpoint bounds.  The centered homogeneous
factor is retained separately: it cannot certify endpoint leading digits
without the affine correction.  Local 100x100 inlet/carry rows always retain
the ORIGINAL source congruence, including the upper parity inlet.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
    WeightedPairMatrix,
)
from number_compiler.sequences.collatz.collatz_digit_coverage import (
    Radix6DigitCoverage,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceCongruence,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.homogeneous_growth import (
        GrowthArithmeticEvaluator,
    )
    from number_compiler.arithmetic.fields.radial_sturmian import (
        RadialSturmianClock,
        RadialSturmianPacket,
    )
    from number_compiler.resources.ledger import ResourceLedger


_CARRY_COUNTS_ISSUER = object()


@dataclass(frozen=True, slots=True, order=True)
class FiveBand:
    """Source-wide closed-open interval of proven radix-6 digit fives."""

    lower: int
    upper: int

    def __post_init__(self) -> None:
        if (
            type(self.lower) is not int
            or type(self.upper) is not int
            or self.lower < 0
            or self.upper <= self.lower
        ):
            raise ValueError("invalid forced base-6 five interval")

    def through(self, odds: int, halvings: int) -> FiveBand | None:
        if (
            type(odds) is not int
            or type(halvings) is not int
            or not 0 <= odds <= halvings
        ):
            raise ValueError("invalid Collatz physical word event counts")
        lower, upper = self.lower + odds, self.upper - halvings
        return FiveBand(lower, upper) if lower < upper else None


def merge_bands(bands: tuple[FiveBand, ...]) -> tuple[FiveBand, ...]:
    if not bands:
        return ()
    result: list[FiveBand] = []
    for band in sorted(bands):
        if result and band.lower <= result[-1].upper:
            prior = result[-1]
            result[-1] = FiveBand(prior.lower, max(prior.upper, band.upper))
        else:
            result.append(band)
    return tuple(result)


def transport_bands(
    bands: tuple[FiveBand, ...], odds: int, halvings: int
) -> tuple[FiveBand, ...]:
    transported: list[FiveBand] = []
    for band in bands:
        value = band.through(odds, halvings)
        if value is not None:
            transported.append(value)
    return tuple(transported)


def _coverage_fives(coverage: Radix6DigitCoverage | None) -> tuple[FiveBand, ...]:
    if coverage is None:
        return ()
    seen = set(range(coverage.low_digits))
    seen.update(range(coverage.width - coverage.high_digits, coverage.width))
    consecutive: list[FiveBand] = []
    start: int | None = None
    previous = -2
    for position in sorted(seen):
        if coverage.digit_at(position) == 5:
            if start is None or position != previous + 1:
                if start is not None:
                    consecutive.append(FiveBand(start, previous + 1))
                start = position
            previous = position
        elif start is not None:
            consecutive.append(FiveBand(start, previous + 1))
            start = None
    if start is not None:
        consecutive.append(FiveBand(start, previous + 1))
    return tuple(consecutive)


def _vp(value: int, prime: int) -> int:
    """Finite valuation of a strictly positive integer (at most 2k-bit budget)."""
    if value <= 0:
        raise ValueError("valuation needs a positive argument")
    if prime == 2:
        return (value & -value).bit_length() - 1
    count = 0
    while value % prime == 0:
        value //= prime
        count += 1
    return count


def common_plus_one_valuation(cylinder: CollatzTwoSidedCylinder, prime: int) -> int:
    """Exact *lower bound* on v_p(x+1) for every x in the cylinder.

    When more than one source is present, no source witness can replace the
    v_p of the stride; for one source the pointed valuation is exact.
    """
    if cylinder.count == 1:
        return _vp(cylinder.first + 1, prime)
    return min(_vp(cylinder.residue + 1, prime), _vp(cylinder.modulus, prime))


def trace_is_zero_tail(trace: MacroTraceGrammar) -> bool:
    """Check the existing trace grammar without materializing its word."""
    if type(trace) is not MacroTraceGrammar:
        return False
    pending = [trace]
    while pending:
        node = pending.pop()
        if node.left is None:
            if any(tail != 0 for tail in node.letters):
                return False
        else:
            assert node.right is not None
            pending.extend((node.left, node.right))
    return True


@dataclass(frozen=True, slots=True)
class CertifiedPairCarryInlet:
    """One original-source guard for the first local 100x100 weighted row."""

    guard: SourceCongruence
    pair: int
    upper_parity: int
    successor_pair: int
    carry_tens: int
    carry_hundreds: int


@dataclass(frozen=True, slots=True, init=False)
class GuardedTemporalCarryCounts:
    """Exact 100x100 weighted rows for a *guard-fixed* normalized program.

    The certificate covers all translated roots in ``guard``: after any
    k<=steps normalized divisions, their differences remain multiples of
    200. This yields the same 100-state pair, upper inlet parity, and carry
    arrivals. This finite evaluator is deliberately not an unrestricted
    matrix-power claim for unproved future inlet programs.
    """

    guard: SourceCongruence
    steps: int
    odds: int
    carry_tens: int
    carry_hundreds: int
    last_pair: int
    matrix_power_period: int | None = None
    forced_six_reset_events: int = 0
    forced_six_div_remainders: int = 0
    port_punctures: int = 0
    matrix_compositions: int = 0
    matrix_squarings: int = 0
    scalar_steps: int = 0
    _issuer: object = field(init=False, repr=False, compare=False)
    _issued_snapshot: tuple[object, ...] = field(init=False, repr=False, compare=False)

    def __init__(
        self,
        guard: SourceCongruence,
        steps: int,
        odds: int,
        carry_tens: int,
        carry_hundreds: int,
        last_pair: int,
        matrix_power_period: int | None = None,
        forced_six_reset_events: int = 0,
        forced_six_div_remainders: int = 0,
        port_punctures: int = 0,
        matrix_compositions: int = 0,
        matrix_squarings: int = 0,
        scalar_steps: int = 0,
        *,
        _issuer: object | None = None,
    ) -> None:
        if _issuer is not _CARRY_COUNTS_ISSUER:
            raise TypeError("guarded carry counts require their checked producer")
        for name, value in (
            ("guard", guard),
            ("steps", steps),
            ("odds", odds),
            ("carry_tens", carry_tens),
            ("carry_hundreds", carry_hundreds),
            ("last_pair", last_pair),
            ("matrix_power_period", matrix_power_period),
            ("forced_six_reset_events", forced_six_reset_events),
            ("forced_six_div_remainders", forced_six_div_remainders),
            ("port_punctures", port_punctures),
            ("matrix_compositions", matrix_compositions),
            ("matrix_squarings", matrix_squarings),
            ("scalar_steps", scalar_steps),
        ):
            object.__setattr__(self, name, value)
        self.__post_init__()
        object.__setattr__(self, "_issuer", _CARRY_COUNTS_ISSUER)
        object.__setattr__(self, "_issued_snapshot", self._snapshot())

    @classmethod
    def create_checked(
        cls,
        guard: SourceCongruence,
        steps: int,
        odds: int,
        carry_tens: int,
        carry_hundreds: int,
        last_pair: int,
        matrix_power_period: int | None = None,
        forced_six_reset_events: int = 0,
        forced_six_div_remainders: int = 0,
        port_punctures: int = 0,
        matrix_compositions: int = 0,
        matrix_squarings: int = 0,
        scalar_steps: int = 0,
    ) -> GuardedTemporalCarryCounts:
        """Issue counts only after a producer checked the complete program."""
        return cls(
            guard,
            steps,
            odds,
            carry_tens,
            carry_hundreds,
            last_pair,
            matrix_power_period,
            forced_six_reset_events,
            forced_six_div_remainders,
            port_punctures,
            matrix_compositions,
            matrix_squarings,
            scalar_steps,
            _issuer=_CARRY_COUNTS_ISSUER,
        )

    def _snapshot(self) -> tuple[object, ...]:
        guard = object.__getattribute__(self, "guard")

        def tagged(value: object) -> tuple[object, object]:
            return (type(value), value)

        return (
            id(self),
            id(guard),
            tagged(guard.residue),
            tagged(guard.modulus),
            tagged(guard.minimum_source),
            tagged(self.steps),
            tagged(self.odds),
            tagged(self.carry_tens),
            tagged(self.carry_hundreds),
            tagged(self.last_pair),
            tagged(self.matrix_power_period),
            tagged(self.forced_six_reset_events),
            tagged(self.forced_six_div_remainders),
            tagged(self.port_punctures),
            tagged(self.matrix_compositions),
            tagged(self.matrix_squarings),
            tagged(self.scalar_steps),
        )

    def verify_issued(self) -> None:
        try:
            valid = (
                object.__getattribute__(self, "_issuer") is _CARRY_COUNTS_ISSUER
                and object.__getattribute__(self, "_issued_snapshot")
                == self._snapshot()
            )
        except (AttributeError, TypeError, ValueError):
            valid = False
        if not valid:
            raise ValueError("guarded carry count issuance seal is invalid")

    def audit_snapshot(self) -> tuple[object, ...]:
        """Return immutable validated fields for external candidate auditing."""
        self.verify_issued()
        return self._snapshot()

    def __post_init__(self) -> None:
        if (
            type(self.guard) is not SourceCongruence
            or type(self.steps) is not int
            or self.steps < 0
            or type(self.odds) is not int
            or not 0 <= self.odds <= self.steps
            or type(self.carry_tens) is not int
            or self.carry_tens < 0
            or type(self.carry_hundreds) is not int
            or self.carry_hundreds < 0
            or type(self.last_pair) is not int
            or not 0 <= self.last_pair < 100
            or (
                self.matrix_power_period is not None
                and (
                    type(self.matrix_power_period) is not int
                    or self.matrix_power_period < 1
                )
            )
            or type(self.forced_six_reset_events) is not int
            or self.forced_six_reset_events < 0
            or type(self.forced_six_div_remainders) is not int
            or self.forced_six_div_remainders < 0
            or type(self.port_punctures) is not int
            or self.port_punctures < 0
            or type(self.matrix_compositions) is not int
            or self.matrix_compositions < 0
            or type(self.matrix_squarings) is not int
            or self.matrix_squarings < 0
            or self.matrix_squarings > self.matrix_compositions
            or type(self.scalar_steps) is not int
            or self.scalar_steps < 0
            or self.scalar_steps > self.steps
        ):
            raise ValueError("invalid guarded temporal carry certificate")


@dataclass(frozen=True, slots=True)
class GuardedRadix6Bridge:
    """Proof-scoped upper and interior port of an already authorized action.

    Even if the source class is nonsingleton, all reported bands are valid
    for *every* source alternative. The centered factor is algebraic, while
    actual upper digit words are independently interval-certified.
    """

    inlet: CollatzTwoSidedCylinder
    target: CollatzTwoSidedCylinder
    action: DyadicTerminalFieldAction
    odd_events: int
    source_coverage: Radix6DigitCoverage | None
    target_coverage: Radix6DigitCoverage | None
    source_fives: tuple[FiveBand, ...]
    inherited_fives: tuple[FiveBand, ...]
    born_fives: tuple[FiveBand, ...]
    target_fives: tuple[FiveBand, ...]
    centered_at_minus_one: bool
    # K*x - offset, K=2**steps-gain, is the exact centered numerator.
    centered_defect_range: tuple[int, int]

    @property
    def radial_clock(self) -> RadialSturmianClock:
        """NC17's existing exact 3**H/2**D Sturmian clock, not a new oracle."""
        from number_compiler.arithmetic.fields.homogeneous_growth import (
            HomogeneousGrowthScale,
        )
        from number_compiler.arithmetic.fields.radial_sturmian import (
            RadialSturmianClock,
        )

        return RadialSturmianClock(
            HomogeneousGrowthScale(self.odd_events, self.action.steps)
        )

    def demanded_radial_binary(
        self, evaluator: GrowthArithmeticEvaluator, *, width: int = 8
    ) -> RadialSturmianPacket:
        """Read the homogeneous upper Sturmian factor with NC17's evaluator.

        No endpoint prefix is inferred; target_coverage gives the separate
        exact affine endpoint upper digits.
        """
        return self.radial_clock.leading_binary(evaluator, width)

    def restrict_to(self, inlet: CollatzTwoSidedCylinder) -> GuardedRadix6Bridge:
        """Transport an existing proof to a certified source *subset*.

        An upper-digit word or forced base-6 band true for the larger
        cylinder remains true for its subset. Rebuilding that coverage at
        each matrix seam was the main overhead of temporal composition.
        Narrowing can additionally force a 6-adic suffix/birth; those are
        computed algebraically without revisiting the interior.
        """
        if type(inlet) is not CollatzTwoSidedCylinder:
            raise TypeError("restricted bridge requires an exact source cylinder")
        if (
            inlet.first < self.inlet.first
            or inlet.last > self.inlet.last
            or (
                self.inlet.count > 1
                and inlet.count > 1
                and (
                    inlet.modulus % self.inlet.modulus
                    or inlet.residue % self.inlet.modulus != self.inlet.residue
                )
            )
            or not self.inlet.contains(inlet.first)
            or not self.inlet.contains(inlet.last)
        ):
            raise ValueError(
                "bridge restriction is not a subset of its certified source"
            )
        if inlet == self.inlet:
            return self
        target = inlet.transport(self.action)
        # Reuse formerly proved upper/lower digits; adjust only their
        # cardinality metadata, never fabricate new uncovered digits.
        src_cover = (
            replace(self.source_coverage, alternatives=inlet.count)
            if self.source_coverage is not None
            else None
        )
        dst_cover = (
            replace(self.target_coverage, alternatives=target.count)
            if self.target_coverage is not None
            else None
        )
        v2 = common_plus_one_valuation(inlet, 2)
        v3 = common_plus_one_valuation(inlet, 3)
        low = min(v2, v3)
        source_fives = merge_bands(
            self.source_fives + ((FiveBand(0, low),) if low else ())
        )
        inherited = merge_bands(
            self.inherited_fives
            + transport_bands(source_fives, self.odd_events, self.action.steps)
        )
        born = self.born_fives
        if self.centered_at_minus_one:
            if v2 < self.action.steps:
                raise ArithmeticError(
                    "narrowed centered action lacks its division guard"
                )
            digits = min(v2 - self.action.steps, v3 + self.odd_events)
            if digits:
                born = merge_bands(born + (FiveBand(0, digits),))
        bands = merge_bands(self.target_fives + inherited + born)
        k = (1 << self.action.steps) - self.action.gain
        d1 = k * inlet.first - self.action.offset
        d2 = k * inlet.last - self.action.offset
        return GuardedRadix6Bridge(
            inlet,
            target,
            self.action,
            self.odd_events,
            src_cover,
            dst_cover,
            source_fives,
            inherited,
            born,
            bands,
            self.centered_at_minus_one,
            (min(d1, d2), max(d1, d2)),
        )

    def then(self, after: GuardedRadix6Bridge) -> GuardedRadix6Bridge:
        """Fuse compatible certified macros, retaining *intermediate births*.

        Source and destination cosets must match exactly. A mere endpoint
        collision cannot join two different source cylinders. This operation
        preserves a base-6 5 region born in the first action even if the
        composite affine action is not centered at -1, and does not visit
        any of its interior digits. It is associative on compatible chains.
        """
        if type(after) is not GuardedRadix6Bridge or self.target != after.inlet:
            raise ValueError("two-sided join needs the identical guarded seam cylinder")
        action = self.action.then(after.action)
        target = self.inlet.transport(action)
        if target != after.target:
            raise ArithmeticError("composed radix-6 bridge lost its exact source image")
        joined_clock = self.radial_clock.then(after.radial_clock)
        if joined_clock.scale.growths != self.odd_events + after.odd_events or (
            joined_clock.scale.halvings != action.steps
        ):
            raise ArithmeticError("joined upper Sturmian factor lost event clock")
        inherited = merge_bands(
            transport_bands(self.inherited_fives, after.odd_events, after.action.steps)
            + after.inherited_fives
        )
        born = merge_bands(
            transport_bands(self.born_fives, after.odd_events, after.action.steps)
            + after.born_fives
        )
        outputs = merge_bands(
            transport_bands(self.target_fives, after.odd_events, after.action.steps)
            + after.target_fives
        )
        denominator = 1 << action.steps
        k = denominator - action.gain
        defects = (
            k * self.inlet.first - action.offset,
            k * self.inlet.last - action.offset,
        )
        return GuardedRadix6Bridge(
            self.inlet,
            after.target,
            action,
            self.odd_events + after.odd_events,
            self.source_coverage,
            after.target_coverage,
            self.source_fives,
            inherited,
            born,
            outputs,
            action.offset + denominator == action.gain,
            (min(defects), max(defects)),
        )

    def first_pair_carry(self, source: int) -> CertifiedPairCarryInlet:
        """Demand a source-qualified weighted 100x100 inlet, not a naked row.

        The necessary original-source precision is x mod 200: low two
        decimal digits plus parity of the next hundred block.  A translated
        source passing this guard has exactly the same inlet and spatial
        carry outputs.  The macro's original guard must *also* be kept.
        """
        if not self.inlet.contains(source):
            raise ValueError("decimal carry source is outside the certified cylinder")
        # The first Collatz step may be even. A zero row has no mul3 carry.
        pair, parity = source % 100, (source // 100) & 1
        step = (
            WeightedPairMatrix.odd_half(parity)
            if source & 1
            else WeightedPairMatrix.even(parity)
        )
        row = step.successors(pair)
        if len(row) != 1:
            raise ArithmeticError("certified decimal carry input has no successor")
        output, tens, hundreds = row[0]
        guard = SourceCongruence(source % 200, 200)
        part = self.inlet.intersect_congruence(guard.residue, guard.modulus)
        if part is None or not part.contains(source):
            raise ArithmeticError("decimal carry inlet lost its exact source guard")
        return CertifiedPairCarryInlet(guard, pair, parity, output, tens, hundreds)

    def demanded_weighted_carry_counts(
        self,
        source: int,
        *,
        max_steps: int = 512,
    ) -> GuardedTemporalCarryCounts:
        """Count temporal carry arrivals on the authenticated 100-state path.

        A bounded linear walk is required unless a *separate* certified
        repeating inlet word licenses weighted matrix squaring. This walk
        never authorizes a Collatz successor and never changes source guards.
        """
        if type(max_steps) is not int or not 0 <= max_steps <= 4096:
            raise ValueError("weighted matrix temporal budget is invalid")
        if self.action.steps > max_steps:
            raise BlockContextBudgetExceeded(
                "unpowered weighted carry inlet program exceeds its budget"
            )
        if not self.inlet.contains(source):
            raise ValueError("weighted matrix source is outside its certified cylinder")
        # A 200*2**d source stride implies identical low 200 residues at
        # every normalized prefix, even though the upper integer changes.
        modulus = 200 << self.action.steps
        guard = SourceCongruence(source % modulus, modulus)
        if self.inlet.intersect_congruence(guard.residue, guard.modulus) is None:
            raise ArithmeticError("weighted matrix guard has no source fiber")
        matrices = (
            (WeightedPairMatrix.even(0), WeightedPairMatrix.even(1)),
            (WeightedPairMatrix.odd_half(0), WeightedPairMatrix.odd_half(1)),
        )
        current, odds, tens, hundreds = source, 0, 0, 0
        for _ in range(self.action.steps):
            odd, parity, pair = current & 1, (current // 100) & 1, current % 100
            row = matrices[odd][parity].successors(pair)
            if len(row) != 1:
                raise ArithmeticError("weighted 100x100 inlet lacks exact successor")
            output, c1, c2 = row[0]
            next_value = (3 * current + 1) // 2 if odd else current // 2
            if output != next_value % 100:
                raise ArithmeticError(
                    "weighted matrix row disagrees with Collatz arithmetic"
                )
            odds += odd
            tens += c1
            hundreds += c2
            current = next_value
        if odds != self.odd_events or current != self.action.endpoint(source):
            raise ArithmeticError(
                "weighted carry program disagrees with the issued macro"
            )
        return GuardedTemporalCarryCounts.create_checked(
            guard, self.action.steps, odds, tens, hundreds, current % 100
        )

    def demanded_zero_tail_sturmian_factor(
        self, source: int, trace: MacroTraceGrammar
    ) -> tuple[int, int, int] | None:
        """Reuse NC17's exact centered Sturmian orbit, not a guessed clock.

        Its odd mantissa is pointed-source data. Upper *endpoint* digit
        assertions continue to use the independently certified interval.
        """
        if not self.inlet.contains(source) or type(trace) is not MacroTraceGrammar:
            raise ValueError("upper Sturmian request lacks source/trace authority")
        if not trace_is_zero_tail(trace):
            return None
        if source % 10 != 3 or trace.length == 0:
            return None
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            ZeroTailFree6305Orbit,
        )

        orbit = ZeroTailFree6305Orbit(source, trace.length)
        if orbit.word.power(trace.length).endpoint(source) != self.action.endpoint(
            source
        ):
            raise ArithmeticError("centered upper orbit disagrees with powered action")
        return orbit.upper_sturmian_source

    def observation(self) -> dict[str, object]:
        """Authenticated, compact port suitable for a conditional Moore key."""
        source_high = None
        if self.source_coverage is not None:
            c = self.source_coverage
            source_high = (c.width, c.high_digits, c.high_word)
        target_high = None
        if self.target_coverage is not None:
            c = self.target_coverage
            target_high = (c.width, c.high_digits, c.high_word)
        return {
            "source_guard": (
                self.inlet.residue,
                self.inlet.modulus,
                self.inlet.first,
                self.inlet.last,
            ),
            "source_upper_base6": source_high,
            "target_upper_base6": target_high,
            "upper_centered_defect_interval": self.centered_defect_range,
            "upper_scale": (self.odd_events, self.action.steps),
            "source_five_intervals": tuple(
                (b.lower, b.upper) for b in self.source_fives
            ),
            "carried_five_intervals": tuple(
                (b.lower, b.upper) for b in self.inherited_fives
            ),
            "born_five_intervals": tuple((b.lower, b.upper) for b in self.born_fives),
            "certified_target_five_intervals": tuple(
                (b.lower, b.upper) for b in self.target_fives
            ),
            "base6_mul3_carry_after_five": 2 if self.target_fives else None,
            "base6_div2_remainder_below_five": 1 if self.target_fives else None,
            "centered_minus_one_birth": self.centered_at_minus_one,
            "future_inlet_authority": "source-bound physical word only",
        }


def certify_guarded_radix6_bridge(
    inlet: CollatzTwoSidedCylinder,
    action: DyadicTerminalFieldAction,
    odd_events: int,
    *,
    max_upper_digits: int = 12,
    max_lower_digits: int = 24,
    ledger: ResourceLedger | None = None,
) -> GuardedRadix6Bridge:
    """Join exact upper intervals, affine radial factor, and forced 5 runs.

    No parity/width/carry program is invented.  ``inlet.transport`` refuses
    if the action isn't valid over the entire source cylinder.  The birth
    condition is an integer identity, *not* a presumed Sturmian cycle.
    """
    if type(inlet) is not CollatzTwoSidedCylinder:
        raise TypeError("bridge requires an exact two-sided source cylinder")
    if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
        raise TypeError("bridge requires producer-issued normalized action")
    if type(odd_events) is not int or not 0 <= odd_events <= action.steps:
        raise ValueError("bridge requires authentic odd-event count")
    if 3**odd_events != action.gain:
        raise ValueError("bridge odd-event count disagrees with source action")
    if any(
        type(x) is not int or not 0 <= x <= 64
        for x in (max_upper_digits, max_lower_digits)
    ):
        raise ValueError("radix-6 bridge band budget exceeds 64 cells")
    target = inlet.transport(action)
    # Very large admitted actions may be published without building a huge
    # positional radix conversion. This loses only optional upper/low digit
    # observations, never the exact affine action or analytic 3-primary birth.
    source_cover = (
        inlet.radix6_coverage(
            max_leading_digits=max_upper_digits,
            max_trailing_digits=max_lower_digits,
            ledger=ledger,
        )
        if inlet.last.bit_length() <= 8192
        else None
    )
    target_cover = (
        target.radix6_coverage(
            max_leading_digits=max_upper_digits,
            max_trailing_digits=max_lower_digits,
            ledger=ledger,
        )
        if target.last.bit_length() <= 8192
        else None
    )
    starts = _coverage_fives(source_cover)
    inherited = merge_bands(
        tuple(
            survived
            for band in starts
            if (survived := band.through(odd_events, action.steps)) is not None
        )
    )
    centered = action.offset + (1 << action.steps) == action.gain
    born: tuple[FiveBand, ...] = ()
    if centered:
        v2 = common_plus_one_valuation(inlet, 2)
        v3 = common_plus_one_valuation(inlet, 3)
        if v2 < action.steps:
            raise ArithmeticError(
                "centered Collatz cylinder has incomplete division guard"
            )
        digits = min(v2 - action.steps, v3 + odd_events)
        if digits:
            born = (FiveBand(0, digits),)
    covered = _coverage_fives(target_cover)
    joined = merge_bands(inherited + born + covered)
    # A true band must fit the actual target width for *all* source values.
    if target_cover is not None and any(b.upper > target_cover.width for b in joined):
        raise ArithmeticError("forced five interval extends beyond certified width")
    denominator = 1 << action.steps
    k = denominator - action.gain
    defects = (k * inlet.first - action.offset, k * inlet.last - action.offset)
    return GuardedRadix6Bridge(
        inlet,
        target,
        action,
        odd_events,
        source_cover,
        target_cover,
        starts,
        inherited,
        born,
        joined,
        centered,
        (min(defects), max(defects)),
    )


def certify_return_trace_radix6_bridge(
    inlet: CollatzTwoSidedCylinder,
    trace: MacroTraceGrammar,
    action: DyadicTerminalFieldAction,
    *,
    max_returns: int = 256,
    ledger: ResourceLedger | None = None,
) -> GuardedRadix6Bridge:
    """Fused upper/inner matrix port for a fully certified 6305 return SLP.

    On a bounded trace, compose *all* intermediate source-bound births with
    the physical 3-border return transitions. This specifically preserves a
    born interior run across subsequent mixed 6305 tail lengths. For a longer
    trace, use only the certified aggregate endpoint and inherited initial
    bands; it deliberately makes no claim about missing intermediate births.
    Neither case expands the 100x100 relation or performs successor search.
    """
    if type(trace) is not MacroTraceGrammar:
        raise TypeError("return-trace bridge requires an issued SLP")
    if type(max_returns) is not int or not 1 <= max_returns <= 4096:
        raise ValueError("return-trace work budget is outside 1..4096")
    total_odds = 2 * trace.length
    if trace.length > max_returns:
        return certify_guarded_radix6_bridge(inlet, action, total_odds, ledger=ledger)
    if trace.length == 0:
        return certify_guarded_radix6_bridge(inlet, action, 0, ledger=ledger)
    if inlet.forced_residue(10) != 3:
        raise ValueError("6305 trace has no certified 3-border inlet")
    from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
        DyadicTerminalFieldAction as Action,
    )

    current = inlet
    composed: GuardedRadix6Bridge | None = None
    for tail in trace.materialize(max_labels=max_returns):
        step = Action.one_run(1).then(Action.zero_run(tail)).then(Action.one_run(1))
        partial = certify_guarded_radix6_bridge(current, step, 2, ledger=ledger)
        if partial.target.forced_residue(10) != 3:
            raise ValueError("authenticated return trace exits the 3-border")
        composed = partial if composed is None else composed.then(partial)
        current = partial.target
    if (
        composed is None
        or composed.action.coefficient_snapshot() != action.coefficient_snapshot()
    ):
        raise ArithmeticError("radix-6 return trace lost its powered affine action")
    return composed


__all__ = (
    "CertifiedPairCarryInlet",
    "FiveBand",
    "GuardedRadix6Bridge",
    "GuardedTemporalCarryCounts",
    "certify_guarded_radix6_bridge",
    "certify_return_trace_radix6_bridge",
)
