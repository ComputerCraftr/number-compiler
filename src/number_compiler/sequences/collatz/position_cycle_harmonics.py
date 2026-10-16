"""Demanded, exact spatial/temporal harmonics of certified Collatz words.

A zero-tail-free 6305 return has x' + 1 = 9*(x+1)/4.  The odd
3-primary source valuation grows by two per return, while the 2-primary
valuation decreases by two.  At a fixed radix-6 position the overlapping
valuation cones force a digit of 5 without visiting the intervening returns.

For a general *already issued* Collatz word, the finite odd-radix spatial
quotient is a genuine Moore machine for the conditional repeated word. It
is NOT a future-selector for unknown parity words, nor is the symbolic
Sturmian multiplier a guarantee about the affine endpoint's leading bits.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.homogeneous_growth import HomogeneousGrowthScale
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.arithmetic.functions.finite_observer import (
    MAX_FINITE_ORBIT_STATES,
    minimize_finite_orbit,
    partition_representatives,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.homogeneous_growth import (
        GrowthArithmeticEvaluator,
    )


def _valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("zero has unbounded prime valuation")
    value = abs(value)
    if prime == 2:
        # Avoid thousands of eager divisions on a long admitted 2-adic ray.
        return (value & -value).bit_length() - 1
    if value % prime:
        return 0
    powers = [prime]
    # Exponential search followed by descending exact divisions, rather
    # than a linear chain of large-integer divisions for each zero digit.
    while value % powers[-1] == 0:
        powers.append(powers[-1] * powers[-1])
    count = 0
    for index in range(len(powers) - 2, -1, -1):
        power = powers[index]
        # A valuation can contain the same largest binary chunk more than
        # once (for example v_3(3**4) = 4). Consume every available copy at
        # this level before descending to smaller chunks.
        while value % power == 0:
            value //= power
            count += 1 << index
    return count


def _power_of_three_matches(exponent: int, target: int) -> bool:
    """Compare a bounded power without allocating past an issued coefficient."""
    if exponent >= target.bit_length():
        return False
    return _integer_power(3, exponent) == target


def _integer_power(base: int, exponent: int) -> int:
    """Compute an exact natural power with an explicitly typed accumulator."""
    if type(base) is not int or base < 0:
        raise ValueError("integer power base must be a natural number")
    if type(exponent) is not int or exponent < 0:
        raise ValueError("integer power exponent must be a natural number")
    value: int = base**exponent
    return value


def _centered_prefix_observation(
    tick: int,
    width: int,
    prefix: int,
    sign: int,
    binary_order: int,
    precision_bits: int,
    radial_growths: int,
    normalized_steps: int,
) -> dict[str, object]:
    """Publish the common fields for either exact or interval prefix proof."""
    return {
        "tick": tick,
        "width": width,
        "prefix": prefix,
        "sign": sign,
        "binary_order": binary_order,
        "precision_bits": precision_bits,
        "scale": (radial_growths, normalized_steps),
        "scope": "centered multiplier D_t/K; affine B/K endpoint correction remains demanded",
    }


@dataclass(frozen=True, slots=True)
class PositionHarmonicSpectrum:
    """Complete count of a demanded digit across admitted return *sources*.

    All counts describe t=0..repetitions-1, before each 6305 return.
    ``odd_period`` is the period of the odd-modulus residue, not an
    assertion that the whole even-radix digit stream is periodic.
    """

    radix: int
    position: int
    repetitions: int
    counts: tuple[int, ...]
    forced_position_interval: tuple[int, int] | None
    forced_position_digit: int | None
    two_adic_forced_through: int | None
    ternary_forced_from: int | None
    odd_preperiod: int | None
    odd_period: int | None
    evaluated_cells: int
    radial_scale: HomogeneousGrowthScale
    walsh64_change_mod5: tuple[int, ...] | None

    def observation(self) -> dict[str, object]:
        return {
            "radix": self.radix,
            "position_lsd_zero_indexed": self.position,
            "completed_return_sources": self.repetitions,
            "digit_frequencies": self.counts,
            "forced_position_interval_inclusive": self.forced_position_interval,
            "forced_position_digit": self.forced_position_digit,
            "forced_all_max_digit_interval_inclusive": (
                self.forced_position_interval
                if self.forced_position_digit == self.radix - 1
                else None
            ),
            "two_adic_forced_through": self.two_adic_forced_through,
            "ternary_forced_from": self.ternary_forced_from,
            "odd_modulus_preperiod": self.odd_preperiod,
            "odd_modulus_period": self.odd_period,
            "modular_cell_evaluations": self.evaluated_cells,
            "homogeneous_radial_exponents": (
                self.radial_scale.growths,
                self.radial_scale.halvings,
            ),
            "walsh64_digit_change_mod5": self.walsh64_change_mod5,
            "scope": (
                "source-certified fixed parity motif; digit harmonics "
                "do not authorize its next repetition"
            ),
        }


@dataclass(frozen=True, slots=True)
class CenteredMotifPositionOrbit:
    """An issued fixed Collatz parity-word repeated on an exact source cylinder.

    C = (2**d-a)*x-B, C_t = a**t*C/2**(d*t). This holds for all
    admitted macro motifs, including 421 (fixed point 1), 26847
    (fixed point 1/13), and odd-pair returns (fixed point -1).
    """

    source: int
    repetitions: int
    word: DyadicTerminalFieldAction
    odd_events: int
    _defect: int = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0:
            raise ValueError("motif orbit requires a positive source")
        if (
            type(self.word) is not DyadicTerminalFieldAction
            or not self.word.producer_issued
        ):
            raise ValueError("motif orbit requires a producer-issued parity word")
        if type(self.odd_events) is not int or self.odd_events < 0:
            raise ValueError("motif requires an exact nonnegative odd-event count")
        if type(self.repetitions) is not int or self.repetitions < 0:
            raise ValueError("motif repetitions must be nonnegative")
        if self.odd_events > self.word.steps or not _power_of_three_matches(
            self.odd_events, self.word.gain
        ):
            raise ValueError("motif event count differs from its issued affine gain")
        if self.repetitions and self.word.steps == 0:
            raise ValueError("nonempty motif repetition needs a temporal action")
        if self.repetitions and not self.word.certifies(self.source):
            raise ValueError("motif source does not admit the first parity word")
        object.__setattr__(
            self,
            "_defect",
            ((1 << self.word.steps) - self.word.gain) * self.source - self.word.offset,
        )
        defect = self.centered_defect
        if defect and _valuation(defect, 2) < self.word.steps * self.repetitions:
            raise ValueError("motif repeats exceed the exact 2-adic source cylinder")

    @property
    def centered_defect(self) -> int:
        return self._defect

    @property
    def radial_scale(self) -> HomogeneousGrowthScale:
        return HomogeneousGrowthScale(
            self.odd_events * self.repetitions,
            self.word.steps * self.repetitions,
        )

    @property
    def upper_sturmian_source(self) -> tuple[int, int, int]:
        """Signed centered odd mantissa, exponent of 3, remaining 2-adic shift."""
        defect = self.centered_defect
        if defect == 0:
            return (0, self.odd_events * self.repetitions, 0)
        exponent = _valuation(defect, 2)
        return (
            defect >> exponent,
            self.odd_events * self.repetitions,
            exponent - self.word.steps * self.repetitions,
        )

    def centered_leading_binary(
        self, tick: int, width: int, evaluator: GrowthArithmeticEvaluator
    ) -> dict[str, object]:
        """Certified upper prefix of the *centered homogeneous* endpoint.

        The full positive magnitude is |D_t/K| where
        D_t = 3**(odd_events*t) * (D_0 // 2**(steps*t)),
        K = 2**steps - 3**odd_events. This readout never constructs a
        large power; the separate affine +B/K correction is NOT discarded.
        """
        from number_compiler.arithmetic.fields.homogeneous_growth import (
            GrowthArithmeticEvaluator,
        )

        if type(evaluator) is not GrowthArithmeticEvaluator:
            raise TypeError("leading border port requires an owned growth evaluator")
        if type(tick) is not int or not 0 <= tick <= self.repetitions:
            raise ValueError("leading port tick outside authenticated repeat")
        if type(width) is not int or not 1 <= width <= evaluator.max_precision_bits:
            raise ValueError("leading port width outside precision budget")
        defect = self.centered_defect
        if defect == 0:
            raise ValueError("zero centered coordinate has no leading digit")
        e = _valuation(defect, 2)
        numerator = abs(defect) >> e
        denominator = abs((1 << self.word.steps) - self.word.gain)
        dyadic_shift = e - self.word.steps * tick
        order_offset = dyadic_shift
        # Normalize the rational odd mantissa into [1,2); only a bounded
        # number of shifts is needed from its two operand bit lengths.
        shift = numerator.bit_length() - denominator.bit_length()
        if shift >= 0:
            denominator <<= shift
        else:
            numerator <<= -shift
        order_offset += shift
        if numerator < denominator:
            numerator <<= 1
            order_offset -= 1
        elif numerator >= 2 * denominator:
            denominator <<= 1
            order_offset += 1
        if not denominator <= numerator < 2 * denominator:
            raise AssertionError("upper mantissa normalization failed")
        scale = HomogeneousGrowthScale(self.odd_events * tick, 0)
        # Exact finite-width equality fallback. Some small rational mantissas
        # land *exactly* on a binary prefix threshold, which interval-only
        # comparisons cannot separate at any precision. It is allowed only
        # when the entire comparison numerator has an explicit small bound.
        if scale.growths <= 512 and (
            numerator.bit_length() + 2 * scale.growths <= 2048
        ):
            with evaluator._charge_work(
                max(1, width + scale.growths),
                0,
                numerator.bit_length() + denominator.bit_length() + 2 * scale.growths,
            ):
                exact_n = numerator * _integer_power(3, scale.growths)
                exact_d = denominator
                exact_order = exact_n.bit_length() - exact_d.bit_length()
                if exact_order >= 0:
                    if exact_n < exact_d << exact_order:
                        exact_order -= 1
                elif (exact_n << (-exact_order)) < exact_d:
                    exact_order -= 1
                shift_for_prefix = width - 1 - exact_order
                prefix = (
                    (exact_n << shift_for_prefix) // exact_d
                    if shift_for_prefix >= 0
                    else exact_n // (exact_d << -shift_for_prefix)
                )
                if not (1 << (width - 1)) <= prefix < (1 << width):
                    raise AssertionError("finite centered readout lost normalization")
                sign = (
                    -1 if defect * ((1 << self.word.steps) - self.word.gain) < 0 else 1
                )
                return _centered_prefix_observation(
                    tick,
                    width,
                    prefix,
                    sign,
                    exact_order + order_offset,
                    0,
                    scale.growths,
                    self.word.steps * tick,
                )
        precision = min(32, evaluator.max_precision_bits)

        def centered_log_bounds(
            precision_bits: int,
        ) -> tuple[Fraction, Fraction]:
            order_low, order_high = evaluator.order_bounds(
                scale, 2, precision_bits=precision_bits
            )
            ratio_low, ratio_high = evaluator.binary_log_ratio_bounds(
                numerator, denominator, precision_bits=precision_bits
            )
            return order_low + ratio_low, order_high + ratio_high

        while True:
            lower, upper = centered_log_bounds(precision)
            if (
                lower.numerator // lower.denominator
                == upper.numerator // upper.denominator
            ):
                order = lower.numerator // lower.denominator
                break
            if precision >= evaluator.max_precision_bits:
                raise BlockContextBudgetExceeded(
                    "centered upper width threshold unresolved"
                )
            precision = min(2 * precision, evaluator.max_precision_bits)
        lo = 1 << (width - 1)
        hi = 1 << width
        while hi - lo > 1:
            middle = (lo + hi) // 2
            threshold_low, threshold_high = evaluator.binary_log_ratio_bounds(
                middle, 1 << (width - 1), precision_bits=precision
            )
            phase_low, phase_high = lower - order, upper - order
            if phase_low >= threshold_high:
                lo = middle
            elif phase_high < threshold_low:
                hi = middle
            else:
                if precision >= evaluator.max_precision_bits:
                    raise BlockContextBudgetExceeded(
                        "centered leading binary prefix unresolved"
                    )
                precision = min(2 * precision, evaluator.max_precision_bits)
                lower, upper = centered_log_bounds(precision)
        sign = -1 if defect * ((1 << self.word.steps) - self.word.gain) < 0 else 1
        return _centered_prefix_observation(
            tick,
            width,
            lo,
            sign,
            order + order_offset,
            precision,
            self.odd_events * tick,
            self.word.steps * tick,
        )

    def digit(self, tick: int, radix: int, position: int) -> int:
        """Random access to any admitted return source via modular powering."""
        if type(tick) is not int or not 0 <= tick <= self.repetitions:
            raise ValueError("6305 observation tick is outside the admitted orbit")
        if type(radix) is not int or not 2 <= radix <= 64:
            raise ValueError("digit radix must be in 2..64")
        if type(position) is not int or position < 0:
            raise ValueError("digit position must be nonnegative")
        if (position + 1) * radix.bit_length() > 4096:
            raise BlockContextBudgetExceeded(
                "position modulus exceeds precision budget"
            )
        if self.word.steps == 0:
            return (self.source // _integer_power(radix, position)) % radix
        modulus = _integer_power(radix, position + 1)
        # Cancel the exact source-cylinder divisor *before* reducing at an
        # even-radix modulus. The integer fixed-point denominator can be
        # nonunit (e.g. 5 for the odd-pair word), so retain it in the CRT
        # modulus rather than inventing an inverse.
        denominator = (1 << self.word.steps) - self.word.gain
        lift = abs(denominator) * modulus
        shifted = self.centered_defect >> (self.word.steps * tick)
        c = (shifted % lift) * pow(self.word.gain, tick, lift) % lift
        numerator = c + self.word.offset
        if numerator % denominator:
            raise AssertionError("centered spatial source lost its exact divide")
        return ((numerator // denominator) % modulus) // (modulus // radix)

    def spectrum(
        self,
        radix: int,
        position: int,
        *,
        walsh64: bool = False,
        walsh_start: int = 0,
        max_states: int = 4096,
        max_modulus_bits: int = 4096,
    ) -> PositionHarmonicSpectrum:
        """Full frequencies without stepping across forced/periodic interiors.

        The odd CRT coordinate of the affine action has a finite orbit.  The
        binary coordinate is forced to -1 while v2(x_t+1) exceeds the
        demanded position.  Split the timeline at that exact dyadic threshold,
        fold complete odd-component periods, and directly inspect only the
        exceptional suffix. No unobserved borrow or phase is guessed.
        """
        if type(radix) is not int or not 2 <= radix <= 64:
            raise ValueError("position spectrum requires radix 2..64")
        if type(position) is not int or position < 0:
            raise ValueError("position must be nonnegative")
        if (
            type(max_states) is not int
            or not 1 <= max_states <= MAX_FINITE_ORBIT_STATES
        ):
            raise ValueError("odd orbit state budget must be positive")
        if type(max_modulus_bits) is not int or max_modulus_bits < 1:
            raise ValueError("modulus bit budget must be positive")
        if max_modulus_bits > 4096:
            raise ValueError("modulus bit budget exceeds the supported 4096-bit cap")
        if type(walsh64) is not bool or type(walsh_start) is not int or walsh_start < 0:
            raise ValueError("Walsh demand requires a valid Boolean and start")
        if walsh64 and walsh_start + 64 > self.repetitions:
            raise ValueError(
                "complete 64-transition Walsh request exceeds return count"
            )
        if self.repetitions == 0:
            return PositionHarmonicSpectrum(
                radix,
                position,
                0,
                (0,) * radix,
                None,
                None,
                None,
                None,
                None,
                None,
                0,
                self.radial_scale,
                None,
            )
        # Bound allocation *before* exponentiating a radix to a massive power.
        if (position + 1) * radix.bit_length() > max_modulus_bits:
            raise BlockContextBudgetExceeded(
                "position modulus exceeds precision budget"
            )
        modulus = _integer_power(radix, position + 1)
        two_bits = _valuation(radix, 2) * (position + 1)
        three_bits = _valuation(radix, 3) * (position + 1)
        two_modulus = 1 << two_bits
        odd_modulus = modulus // two_modulus
        defect = self.centered_defect
        # The zero-defect fixed point has all valuations infinite.
        e2 = (
            _valuation(defect, 2)
            if defect
            else self.word.steps * (self.repetitions + 1) + two_bits
        )
        e3 = (
            _valuation(defect, 3)
            if defect
            else (self.odd_events or 1) * (self.repetitions + 1) + three_bits
        )
        power = self.word.steps
        odds = self.odd_events
        binary_end = (e2 - two_bits) // power if two_bits else self.repetitions - 1
        ternary_start = (
            max(0, (three_bits - e3 + odds - 1) // odds)
            if three_bits and odds
            else None
        )
        # Only radices consisting of powers of two and three can have
        # their whole low word forced to b**(p+1)-1 by these two valuations.
        only_two_three = modulus == (1 << two_bits) * _integer_power(
            3, three_bits
        ) and (not three_bits or ternary_start is not None)
        forced = None
        forced_digit = None
        if only_two_three:
            start = ternary_start or 0
            stop = min(self.repetitions - 1, binary_end)
            if start <= stop:
                forced = (start, stop)
                denominator = (1 << self.word.steps) - self.word.gain
                forced_residue = (
                    self.word.offset * pow(denominator, -1, modulus)
                ) % modulus
                forced_digit = forced_residue // (modulus // radix)
        counts = [0] * radix
        evaluated = 0
        if self.repetitions <= 48:
            # Small-run observations do not pay for orbit discovery at all.
            for t in range(self.repetitions):
                counts[self.digit(t, radix, position)] += 1
                evaluated += 1
            transient = period = None
        else:
            prefix_end = min(self.repetitions, max(0, binary_end + 1))
            # For odd radices the complete timeline uses the periodic
            # coordinate. For even radices this applies only to the prefix
            # whose 2-adic residue is certified -1.
            start_residue = self.source % odd_modulus if odd_modulus > 1 else 0
            seen: dict[int, int] = {}
            orbit: list[int] = []
            residue = start_residue
            inverse_denominator = (
                pow(2, -self.word.steps, odd_modulus) if odd_modulus > 1 else 0
            )
            needed = prefix_end
            transient = period = None
            while len(orbit) < needed and residue not in seen:
                if len(orbit) >= max_states:
                    raise BlockContextBudgetExceeded(
                        "odd-radix harmonic orbit exceeds its state budget"
                    )
                seen[residue] = len(orbit)
                orbit.append(residue)
                residue = (
                    (
                        (self.word.gain * residue + self.word.offset)
                        * inverse_denominator
                    )
                    % odd_modulus
                    if odd_modulus > 1
                    else 0
                )
            if residue in seen:
                transient = seen[residue]
                period = len(orbit) - transient
            # Assemble the radix digit from the forced binary residue and
            # the periodic odd coordinate, using exact CRT.
            fixed_binary = (
                (
                    self.word.offset
                    * pow((1 << self.word.steps) - self.word.gain, -1, two_modulus)
                )
                % two_modulus
                if two_modulus > 1
                else 0
            )
            crt_inverse = pow(two_modulus, -1, odd_modulus) if odd_modulus > 1 else 0

            def digit_from_odd(odd_residue: int) -> int:
                if odd_modulus == 1:
                    reconstructed = fixed_binary
                elif two_modulus == 1:
                    reconstructed = odd_residue
                else:
                    low = fixed_binary
                    reconstructed = low + two_modulus * (
                        ((odd_residue - low) * crt_inverse) % odd_modulus
                    )
                return reconstructed // (modulus // radix)

            # One prefix position per orbit residue, followed by whole
            # periodic blocks and a final partial block. Never enumerate
            # each return inside a very long period.
            if period is None:
                if len(orbit) != prefix_end:
                    raise AssertionError("incomplete odd-coordinate orbit")
                for odd in orbit:
                    counts[digit_from_odd(odd)] += 1
                    evaluated += 1
            else:
                assert transient is not None
                for odd in orbit[:transient]:
                    counts[digit_from_odd(odd)] += 1
                    evaluated += 1
                complete, extra = divmod(prefix_end - transient, period)
                for phase, odd in enumerate(orbit[transient:]):
                    counts[digit_from_odd(odd)] += complete + int(phase < extra)
                    evaluated += 1
            for tick in range(prefix_end, self.repetitions):
                counts[self.digit(tick, radix, position)] += 1
                evaluated += 1
        if sum(counts) != self.repetitions:
            raise AssertionError("position count differs from source cylinder length")
        walsh = None
        if walsh64:
            mask = 0
            for phase in range(64):
                tick = walsh_start + phase
                if self.digit(tick, radix, position) != self.digit(
                    tick + 1, radix, position
                ):
                    mask |= 1 << phase
            walsh = walsh64_mod5(mask)
        return PositionHarmonicSpectrum(
            radix,
            position,
            self.repetitions,
            tuple(counts),
            forced,
            forced_digit,
            min(binary_end, self.repetitions - 1) if two_bits else None,
            ternary_start,
            transient,
            period,
            evaluated,
            self.radial_scale,
            walsh,
        )


class ZeroTailFree6305Orbit(CenteredMotifPositionOrbit):
    """Strict zero-tail-free 3->3/8 run, using the shared centered grammar."""

    def __init__(self, source: int, repetitions: int) -> None:
        from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
            DyadicTerminalFieldAction,
        )

        if type(source) is not int or source <= 0 or source % 10 != 3:
            raise ValueError("6305 orbit requires a positive 3-ending source")
        odd_pair = DyadicTerminalFieldAction.one_run(2)
        super().__init__(source, repetitions, odd_pair, 2)


def issued_boundary_motif_orbit(macro: object) -> CenteredMotifPositionOrbit:
    """Adapt *every* authenticated named Collatz cycle's repeated motif.

    The prelude and final suffix are those in the existing issued action's
    compact parity grammar. Frequencies are sampled at motif boundaries,
    not at each physical digit tick. This does not infer a successor beyond
    the macro's authenticated repeated parity word.
    """
    from number_compiler.sequences.collatz.border_identity import (
        ENTRY_0563,
        ENTRY_89_AT_NINE,
        ENTRY_421,
        ENTRY_4721,
        ENTRY_26847_PHASES,
        PATH_305,
        PATH_630,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
        validate_boundary_macro,
    )

    if type(macro) is not CollatzBoundaryMacro:
        raise TypeError("motif harmonic requires an issued named boundary macro")
    validate_boundary_macro(macro)
    identity = macro.identity
    repetitions = macro.repetitions
    one = DyadicTerminalFieldAction.one_run
    zero = DyadicTerminalFieldAction.zero_run
    if identity == ENTRY_421:
        prefix, word, count = zero(2), one(1).then(zero(1)), repetitions - 1
    elif identity in (ENTRY_4721, ENTRY_0563):
        prefix, word, count = zero(1), one(2), repetitions
    elif identity in ENTRY_26847_PHASES:
        phase = ENTRY_26847_PHASES.index(identity)
        prefix, word, count = zero(4 - phase), one(1).then(zero(3)), repetitions - 1
    elif identity == PATH_630:
        prefix, word, count = zero(1).then(one(1)), zero(1), repetitions
    elif identity == PATH_305:
        prefix, word, count = one(1), zero(1), repetitions
    elif identity == ENTRY_89_AT_NINE:
        prefix, word, count = DyadicTerminalFieldAction.identity(), one(1), repetitions
    else:
        raise ValueError("unsupported named cycle harmonic")
    if not prefix.certifies(macro.source):
        raise AssertionError("source-bound motif prelude lost its parity guard")
    source = prefix.endpoint(macro.source)
    return CenteredMotifPositionOrbit(
        source,
        count,
        word,
        0 if word.gain == 1 else (2 if word.gain == 9 else 1),
    )


@dataclass(frozen=True, slots=True)
class OddPositionMoore:
    """Minimal odd-residue future observer for a *fixed admitted word*."""

    radix: int
    position: int
    states: int
    classes: int
    rounds: int
    class_ids: tuple[int, ...]
    outputs: tuple[int, ...]
    transitions: tuple[tuple[int, ...], ...]

    def class_for_source(self, source: int) -> int:
        if type(source) is not int or source <= 0:
            raise ValueError("source must be positive")
        return self.class_ids[source % self.states]

    def walsh64_future_digit_changes(self, source: int) -> tuple[int, ...]:
        """Use only minimized future classes to publish a 64-lane F5 pivot.

        This Walsh mask observes change of the requested digit, not the
        independent homogeneous 3-power difference/borrow stencil.
        The fixed parity word remains a conditional action at every step.
        """
        state = self.class_for_source(source)
        mask = 0
        for index in range(64):
            following = self.transitions[state][0]
            if self.outputs[state] != self.outputs[following]:
                mask |= 1 << index
            state = following
        return walsh64_mod5(mask)

    def observation(self, source: int) -> dict[str, object]:
        return {
            "radix": self.radix,
            "position_lsd_zero_indexed": self.position,
            "residue_states": self.states,
            "future_moore_classes": self.classes,
            "refinement_rounds": self.rounds,
            "source_class": self.class_for_source(source),
            "scope": (
                "odd-radix conditional fixed-word outputs; exact parity "
                "and named-family guards remain separate"
            ),
        }


def minimize_fixed_word_odd_position(
    word: DyadicTerminalFieldAction,
    radix: int,
    position: int,
    *,
    max_states: int = 4096,
) -> OddPositionMoore:
    """Full Moore minimization of one requested digit's future residue stream.

    Every residue has a deterministic next residue because division by 2
    is invertible in an odd radix. The source word must already be issued;
    this machine does NOT assert the same Collatz parity word is legal on
    every residue or that all later named-family guards remain admitted.
    """
    if type(word) is not DyadicTerminalFieldAction or not word.producer_issued:
        raise ValueError("Moore word must be issued by the Collatz source owner")
    if type(radix) is not int or radix < 3 or radix % 2 == 0:
        raise ValueError("finite position Moore requires an odd radix")
    if type(position) is not int or position < 0:
        raise ValueError("Moore digit position must be nonnegative")
    if type(max_states) is not int or not 1 <= max_states <= MAX_FINITE_ORBIT_STATES:
        raise ValueError("Moore state budget is outside the supported range")
    modulus = 1
    for _ in range(position + 1):
        if modulus > max_states // radix:
            raise BlockContextBudgetExceeded(
                "odd-digit observer exceeds finite state budget"
            )
        modulus *= radix
    gain = word.gain % modulus
    offset = word.offset % modulus
    denominator_inverse = pow(2, -word.steps, modulus)
    rows = tuple(
        ((gain * residue + offset) * denominator_inverse) % modulus
        for residue in range(modulus)
    )
    place = _integer_power(radix, position)
    labels = tuple(residue // place for residue in range(modulus))
    result = minimize_finite_orbit(rows, labels, max_states=max_states)
    representatives = partition_representatives(result.class_ids, result.class_count)
    class_outputs = tuple(state // place for state in representatives)
    if len(result.class_outputs) != len(class_outputs) or any(
        type(output) is not int or output != class_outputs[class_id]
        for class_id, output in enumerate(result.class_outputs)
    ):
        raise AssertionError("minimized class output differs from its canonical state")
    return OddPositionMoore(
        radix,
        position,
        result.source_state_count,
        result.class_count,
        result.refinement_rounds,
        result.class_ids,
        class_outputs,
        tuple((target,) for target in result.class_successors),
    )


__all__ = [
    "CenteredMotifPositionOrbit",
    "OddPositionMoore",
    "PositionHarmonicSpectrum",
    "ZeroTailFree6305Orbit",
    "issued_boundary_motif_orbit",
    "minimize_fixed_word_odd_position",
]
