"""Exact exponent arithmetic and budgeted radix-order readout.

``HomogeneousGrowthScale(H, D)`` denotes the positive rational scale
``3**H / 2**D``.  The descriptor is deliberately only homogeneous arithmetic:
it carries no source state or source-action identity.  Radix orders are
computed from certified rational logarithm intervals, so a symbolic exponent
never requires constructing either exponential numerator or denominator.
"""

from __future__ import annotations

from collections.abc import Generator
from contextlib import AbstractContextManager, contextmanager
from dataclasses import dataclass
from fractions import Fraction
from typing import Self

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys


@dataclass(frozen=True, slots=True)
class HomogeneousGrowthScale:
    """Canonical ``3**growths / 2**halvings`` exponent descriptor."""

    growths: int = 0
    halvings: int = 0

    def __post_init__(self) -> None:
        require_integer(self.growths, "growth exponent", 0)
        require_integer(self.halvings, "halving exponent", 0)

    @classmethod
    def identity(cls) -> HomogeneousGrowthScale:
        """Return the multiplicative identity scale."""
        return cls()

    @property
    def is_identity(self) -> bool:
        return self.growths == 0 and self.halvings == 0

    @property
    def canonical_key(self) -> tuple[str, int, int]:
        return ("homogeneous-growth-scale", self.growths, self.halvings)

    def then(self, after: HomogeneousGrowthScale) -> HomogeneousGrowthScale:
        """Compose commuting homogeneous scales in chronological order."""
        if type(after) is not HomogeneousGrowthScale:
            raise TypeError("growth scale composition requires the same descriptor")
        return HomogeneousGrowthScale(
            self.growths + after.growths,
            self.halvings + after.halvings,
        )

    def power(self, exponent: int) -> HomogeneousGrowthScale:
        """Raise this scale to a nonnegative integer power symbolically."""
        require_integer(exponent, "growth scale power", 0)
        return HomogeneousGrowthScale(
            self.growths * exponent,
            self.halvings * exponent,
        )


@dataclass(frozen=True, slots=True)
class _LogConstants:
    ln_two: tuple[int, int]
    ln_three: tuple[int, int]
    ln_radix: tuple[int, int]
    series_terms: int


@dataclass(frozen=True, slots=True)
class ContinuedFractionPrefix:
    """Certified finite prefix of a homogeneous radix logarithm's CF."""

    scale: HomogeneousGrowthScale
    radix: int
    terms: tuple[int, ...]
    exact_value: Fraction | None
    complete: bool
    budget_limited: bool
    precision_bits: int

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "homogeneous-growth-cf-prefix",
            self.scale.canonical_key,
            self.radix,
            self.terms,
            self.exact_value,
            self.complete,
            self.budget_limited,
            self.precision_bits,
        )


def _ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def _logarithm_interval_scaled(
    numerator: int, denominator: int, precision_bits: int
) -> tuple[int, int, int]:
    """Enclose ln(numerator/denominator) in dyadic fixed point.

    Inputs are rational values in ``[1, 2]``.  The atanh series uses
    ``ln(x) = 2 * sum(z**(2k+1)/(2k+1))`` with ``z=(x-1)/(x+1)``.  Here
    ``0 <= z <= 1/3``.  Every term is rounded down into the lower endpoint;
    the number of terms bounds accumulated rounding, and a geometric tail
    bound closes the upper endpoint.
    """
    if numerator < denominator or numerator > 2 * denominator:
        raise ValueError("logarithm interval input must lie in [1, 2]")
    if numerator == denominator:
        return 0, 0, 0

    scale = 1 << precision_bits
    z_numerator = numerator - denominator
    z_denominator = numerator + denominator
    z_square_numerator = z_numerator * z_numerator
    z_square_denominator = z_denominator * z_denominator
    term_numerator = z_numerator
    term_denominator = z_denominator
    lower = 0
    terms = 0

    while True:
        odd = 2 * terms + 1
        term = (2 * term_numerator * scale) // (term_denominator * odd)
        lower += term
        terms += 1

        next_numerator = term_numerator * z_square_numerator
        next_denominator = term_denominator * z_square_denominator
        next_odd = 2 * terms + 1
        tail_numerator = 2 * next_numerator * z_denominator * z_denominator * scale
        tail_denominator = (
            next_denominator
            * next_odd
            * (z_denominator * z_denominator - z_numerator * z_numerator)
        )
        tail_units = _ceil_div(tail_numerator, tail_denominator)
        if tail_units <= 1:
            return lower, lower + terms + tail_units, terms
        term_numerator = next_numerator
        term_denominator = next_denominator


def _ln_constants(radix: int, precision_bits: int) -> _LogConstants:
    """Return scaled intervals for ln(2), ln(3), ln(radix), and term count."""
    ln_two = _logarithm_interval_scaled(2, 1, precision_bits)
    ln_three_remainder = _logarithm_interval_scaled(3, 2, precision_bits)
    ln_three = (
        ln_two[0] + ln_three_remainder[0],
        ln_two[1] + ln_three_remainder[1],
    )
    power_two = 1 << (radix.bit_length() - 1)
    radix_exponent = radix.bit_length() - 1
    ln_remainder = _logarithm_interval_scaled(radix, power_two, precision_bits)
    ln_radix = (
        radix_exponent * ln_two[0] + ln_remainder[0],
        radix_exponent * ln_two[1] + ln_remainder[1],
    )
    if ln_radix[0] <= 0:
        raise BlockContextBudgetExceeded(
            "precision did not enclose a positive radix logarithm"
        )
    return _LogConstants(
        (ln_two[0], ln_two[1]),
        ln_three,
        ln_radix,
        ln_two[2] + ln_three_remainder[2] + ln_remainder[2],
    )


def _order_interval(
    scale: HomogeneousGrowthScale, constants: _LogConstants
) -> tuple[Fraction, Fraction]:
    lower = Fraction(
        scale.growths * constants.ln_three[0], constants.ln_radix[1]
    ) - Fraction(scale.halvings * constants.ln_two[1], constants.ln_radix[0])
    upper = Fraction(
        scale.growths * constants.ln_three[1], constants.ln_radix[0]
    ) - Fraction(scale.halvings * constants.ln_two[0], constants.ln_radix[1])
    return lower, upper


def _prime_power_exponent(value: int, prime: int) -> int | None:
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent if value == 1 else None


def _exact_rational_radix_order(
    scale: HomogeneousGrowthScale, radix: int
) -> Fraction | None:
    """Return an exact rational order when prime valuations prove one."""
    if scale.is_identity:
        return Fraction(0)
    if scale.halvings == 0:
        exponent = _prime_power_exponent(radix, 3)
        if exponent is not None:
            return Fraction(scale.growths, exponent)
    if scale.growths == 0:
        exponent = _prime_power_exponent(radix, 2)
        if exponent is not None:
            return Fraction(-scale.halvings, exponent)
    return None


def _bounded_ratio_bit_estimate(scale: HomogeneousGrowthScale) -> int:
    """Upper-bound bits in both exact powers without constructing either one."""
    return 2 * scale.growths + scale.halvings + 1


def _floor_radix_order_ratio(numerator: int, denominator: int, radix: int) -> int:
    """Compare bounded integer powers to find an exact logarithmic floor."""
    if numerator >= denominator:
        quotient = numerator // denominator
        power = 1
        order = 0
        while power <= quotient // radix:
            power *= radix
            order += 1
        return order

    reciprocal_ceiling = _ceil_div(denominator, numerator)
    power = 1
    magnitude = 0
    while power < reciprocal_ceiling:
        if power > (reciprocal_ceiling - 1) // radix:
            power = reciprocal_ceiling
        else:
            power *= radix
        magnitude += 1
    return -magnitude


class GrowthArithmeticEvaluator:
    """Ledger-owned certified radix-order and continued-fraction evaluator."""

    def __init__(
        self,
        ledger: ResourceLedger,
        *,
        name: str | None = None,
        max_precision_bits: int = 1_000_000,
        max_work_units: int = 1_000_000,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("growth arithmetic requires a ResourceLedger")
        require_integer(max_precision_bits, "growth precision budget", 1)
        require_integer(max_work_units, "growth work budget", 0)
        if name is not None and (type(name) is not str or not name):
            raise ValueError("growth arithmetic name must be nonempty")
        self.ledger = ledger
        self.max_precision_bits = max_precision_bits
        self.max_work_units = max_work_units
        self._work_used = 0
        prefix = f"{name or 'homogeneous-growth'}-{ledger.owner_count}"
        self._order_owner = ledger.register(prefix + "-radix-orders", "query_memo")
        self._log_owner = ledger.register(prefix + "-log-constants", "query_memo")
        self._scratch_owner = ledger.register(prefix + "-scratch", "execution_stack")
        self._orders: OwnedMemo[tuple[HomogeneousGrowthScale, int], int] = OwnedMemo(
            ledger, self._order_owner, nodes_per_entry=1, evictable=True
        )
        self._logs: OwnedMemo[tuple[int, int], _LogConstants] = OwnedMemo(
            ledger, self._log_owner, nodes_per_entry=1, evictable=True
        )
        self._closed = False
        self._initialize_order_counters()

    def _initialize_order_counters(self) -> None:
        """Publish measured zeroes for an observed order-evaluation owner."""
        for counter in (
            _fields_keys.GROWTH_ARITHMETIC_OPERAND_BITS,
            _fields_keys.GROWTH_ARITHMETIC_WORK,
            _fields_keys.GROWTH_ARITHMETIC_PRECISION_BITS,
            _shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS,
            _fields_keys.GROWTH_CACHE_ADMISSION_CHECKS,
            _fields_keys.GROWTH_ORDER_IDENTITY_SHORTCUTS,
            _fields_keys.GROWTH_ORDER_KEY_LOOKUPS,
            _fields_keys.GROWTH_ORDER_CACHE_HITS,
            _fields_keys.GROWTH_ORDER_EQUALITY_CHECKS,
            _fields_keys.GROWTH_ORDER_EXACT_RATIONAL_CASES,
            _fields_keys.GROWTH_ORDER_BOUNDED_EXACT_RATIO_CASES,
            _fields_keys.GROWTH_ORDER_CACHE_BYPASSES,
            _fields_keys.GROWTH_ORDER_REFINEMENTS,
            _fields_keys.GROWTH_LOG_CONSTANT_LOOKUPS,
            _fields_keys.GROWTH_LOG_CONSTANT_CACHE_HITS,
        ):
            self.ledger.bump(counter, 0)

    def __enter__(self) -> Self:
        self.ensure_open()
        return self

    def __exit__(self, exc_type: object, exc_value: object, traceback: object) -> None:
        self.close()

    def close(self) -> None:
        """Release memo payloads and close the evaluator's ledger owners."""
        if self._closed:
            return
        self._logs.dispose()
        self._orders.dispose()
        self.ledger.mark_disposed(self._scratch_owner)
        self._closed = True

    def ensure_open(self) -> None:
        """Validate that public arithmetic work may use this live evaluator."""
        if self._closed:
            raise RuntimeError("growth arithmetic evaluator has been closed")

    @property
    def work_used(self) -> int:
        return self._work_used

    @property
    def is_closed(self) -> bool:
        """Whether this evaluator's ledger-backed owners have been released."""
        return self._closed

    @contextmanager
    def charge_work(
        self,
        units: int,
        precision_bits: int,
        operand_bits: int = 0,
        *,
        storage_bits: int | None = None,
    ) -> Generator[None, None, None]:
        self.ensure_open()
        self.ledger.bump(_fields_keys.GROWTH_ARITHMETIC_OPERAND_BITS, operand_bits)
        if self._work_used + units > self.max_work_units:
            self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise BlockContextBudgetExceeded("growth arithmetic work budget exceeded")
        retained_bits = (
            precision_bits + operand_bits if storage_bits is None else storage_bits
        )
        limbs = max(1, (retained_bits + 63) // 64)
        scratch_nodes = limbs * 6
        try:
            with self.ledger.reservation(self._scratch_owner, nodes=scratch_nodes):
                self._work_used += units
                self.ledger.bump(_fields_keys.GROWTH_ARITHMETIC_WORK, units)
                self.ledger.bump(
                    _fields_keys.GROWTH_ARITHMETIC_PRECISION_BITS,
                    precision_bits,
                )
                yield
        except BlockContextBudgetExceeded:
            self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise

    def _ensure_cache_slot(self, entries: int = 1) -> None:
        self.ledger.bump(_fields_keys.GROWTH_CACHE_ADMISSION_CHECKS)
        try:
            self.ledger.check_capacity(entries=entries, nodes=entries)
        except BlockContextBudgetExceeded:
            self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise

    def order_bounds(
        self,
        scale: HomogeneousGrowthScale,
        radix: int = 10,
        *,
        precision_bits: int = 64,
    ) -> tuple[Fraction, Fraction]:
        """Return certified rational bounds for ``H log_b(3)-D log_b(2)``."""
        self.ensure_open()
        self._validate_order_request(scale, radix)
        require_integer(precision_bits, "logarithm precision", 1)
        if precision_bits > self.max_precision_bits:
            self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise BlockContextBudgetExceeded("logarithm precision budget exceeded")
        return self._charged_order_interval(scale, radix, precision_bits)

    def binary_log_ratio_bounds(
        self, numerator: int, denominator: int, *, precision_bits: int = 64
    ) -> tuple[Fraction, Fraction]:
        """Certify ``log_2(numerator/denominator)`` for ratios in [1,2].

        Reuse the owned ln(2) intervals and the same charged, finite atanh
        series as the existing radix-order evaluator. Ambiguous comparisons
        are the caller's responsibility to refine, never guessed here.
        """
        return self.radix_log_ratio_bounds(
            numerator, denominator, 2, precision_bits=precision_bits
        )

    def radix_log_ratio_bounds(
        self,
        numerator: int,
        denominator: int,
        radix: int,
        *,
        precision_bits: int = 64,
    ) -> tuple[Fraction, Fraction]:
        """Certified ``log_radix(numerator/denominator)`` for ``1<=ratio<=radix``.

        The same ledger-owned rational logarithm intervals used by the
        Sturmian width oracle authenticate decimal leading-digit thresholds.
        No floating logarithms, source powers, or digit vectors are formed.
        """
        self.ensure_open()
        require_integer(numerator, "threshold numerator", 1)
        require_integer(denominator, "threshold denominator", 1)
        require_integer(radix, "threshold radix", 2)
        require_integer(precision_bits, "logarithm precision", 1)
        if precision_bits > self.max_precision_bits:
            self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise BlockContextBudgetExceeded("radix logarithm precision budget")
        operand_bits = (
            numerator.bit_length() + denominator.bit_length() + radix.bit_length()
        )
        with self.charge_work(max(1, operand_bits), 0, operand_bits):
            if not denominator <= numerator <= radix * denominator:
                raise ValueError("radix logarithm ratio must be in [1, radix]")
            if numerator == denominator:
                return Fraction(0), Fraction(0)
            if numerator == radix * denominator:
                return Fraction(1), Fraction(1)
        # Populate the same memoized interval constants as radix_order().
        self._charged_order_interval(
            HomogeneousGrowthScale.identity(), radix, precision_bits
        )
        constants = self._logs.get((radix, precision_bits))
        if constants is None:
            raise BlockContextBudgetExceeded("owned logarithm constants were evicted")
        power = 0
        scaled_denominator = denominator
        while numerator >= 2 * scaled_denominator:
            scaled_denominator <<= 1
            power += 1
        operand_bits = numerator.bit_length() + denominator.bit_length()
        with self._charge_log_work(radix, precision_bits, operand_bits):
            low, high, _ = _logarithm_interval_scaled(
                numerator, scaled_denominator, precision_bits
            )
            return (
                Fraction(power * constants.ln_two[0] + low, constants.ln_radix[1]),
                Fraction(power * constants.ln_two[1] + high, constants.ln_radix[0]),
            )

    def continued_fraction_prefix(
        self,
        scale: HomogeneousGrowthScale,
        radix: int = 10,
        *,
        max_terms: int = 16,
    ) -> ContinuedFractionPrefix:
        """Return only CF quotients proved common to the certified log interval.

        Multiplicatively dependent cases (pure powers of two or three) are
        rational and terminate explicitly.  Other cases refine the rational
        enclosure until both endpoints prove the same next quotient.  A
        precision or work refusal returns the already certified prefix with
        ``budget_limited=True``; it never guesses the unresolved quotient.
        """
        self.ensure_open()
        self._validate_order_request(scale, radix)
        require_integer(max_terms, "continued fraction term limit", 0)
        for counter in (
            _fields_keys.GROWTH_CF_KEY_LOOKUPS,
            _fields_keys.GROWTH_CF_BUDGET_REFUSALS,
            _fields_keys.GROWTH_CF_PREFIX_RESERVATIONS,
        ):
            self.ledger.bump(counter, 0)
        if max_terms == 0:
            return ContinuedFractionPrefix(scale, radix, (), None, False, False, 0)
        if max_terms > self.max_work_units:
            return self._continued_fraction_budget_refusal(scale, radix)
        try:
            with self.ledger.reservation(
                self._scratch_owner, entries=max_terms, nodes=max_terms
            ):
                self.ledger.bump(_fields_keys.GROWTH_CF_PREFIX_RESERVATIONS)
                return self._continued_fraction_prefix_admitted(scale, radix, max_terms)
        except BlockContextBudgetExceeded:
            return self._continued_fraction_budget_refusal(scale, radix)

    def _continued_fraction_budget_refusal(
        self, scale: HomogeneousGrowthScale, radix: int
    ) -> ContinuedFractionPrefix:
        self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
        self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
        return ContinuedFractionPrefix(scale, radix, (), None, False, True, 0)

    def _continued_fraction_prefix_admitted(
        self, scale: HomogeneousGrowthScale, radix: int, max_terms: int
    ) -> ContinuedFractionPrefix:
        self.ledger.bump(_fields_keys.GROWTH_CF_KEY_LOOKUPS)
        operand_bits = self._scale_operand_bits(scale, radix)
        try:
            with self.charge_work(max(1, operand_bits), 1, operand_bits):
                exact_value = _exact_rational_radix_order(scale, radix)
        except BlockContextBudgetExceeded:
            self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
            return ContinuedFractionPrefix(scale, radix, (), None, False, True, 0)

        if exact_value is not None:
            terms: list[int] = []
            numerator, denominator = exact_value.numerator, exact_value.denominator
            while denominator and len(terms) < max_terms:
                operand_work = numerator.bit_length() + denominator.bit_length()
                try:
                    with self.charge_work(
                        max(1, operand_work),
                        1,
                        operand_work,
                        storage_bits=4 * operand_work,
                    ):
                        partial_quotient = numerator // denominator
                        remainder = numerator - partial_quotient * denominator
                except BlockContextBudgetExceeded:
                    self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
                    return ContinuedFractionPrefix(
                        scale,
                        radix,
                        tuple(terms),
                        exact_value,
                        False,
                        True,
                        0,
                    )
                terms.append(partial_quotient)
                numerator, denominator = denominator, remainder
            complete = denominator == 0
            return ContinuedFractionPrefix(
                scale,
                radix,
                tuple(terms),
                exact_value,
                complete,
                False,
                0,
            )

        terms = []
        precision = min(32, self.max_precision_bits)
        while len(terms) < max_terms:
            try:
                lower, upper = self._charged_order_interval(scale, radix, precision)
            except BlockContextBudgetExceeded:
                self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
                return ContinuedFractionPrefix(
                    scale, radix, tuple(terms), None, False, True, precision
                )

            prefix_resolved = True
            for expected_term in terms:
                lower_floor = lower.numerator // lower.denominator
                upper_floor = upper.numerator // upper.denominator
                if (
                    lower_floor != expected_term
                    or upper_floor != expected_term
                    or lower <= expected_term
                    or upper >= expected_term + 1
                ):
                    prefix_resolved = False
                    break
                try:
                    lower, upper = self._advance_cf_interval(
                        lower, upper, expected_term, precision
                    )
                except BlockContextBudgetExceeded:
                    self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
                    return ContinuedFractionPrefix(
                        scale, radix, tuple(terms), None, False, True, precision
                    )

            if not prefix_resolved:
                if precision >= self.max_precision_bits:
                    self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
                    return ContinuedFractionPrefix(
                        scale, radix, tuple(terms), None, False, True, precision
                    )
                precision = min(precision * 2, self.max_precision_bits)
                continue

            resolved = True
            while len(terms) < max_terms:
                lower_floor = lower.numerator // lower.denominator
                upper_floor = upper.numerator // upper.denominator
                if (
                    lower_floor != upper_floor
                    or lower <= lower_floor
                    or upper >= lower_floor + 1
                ):
                    resolved = False
                    break

                try:
                    next_lower, next_upper = self._advance_cf_interval(
                        lower, upper, lower_floor, precision
                    )
                except BlockContextBudgetExceeded:
                    self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
                    return ContinuedFractionPrefix(
                        scale, radix, tuple(terms), None, False, True, precision
                    )
                terms.append(lower_floor)
                lower, upper = next_lower, next_upper

            if resolved or len(terms) >= max_terms:
                return ContinuedFractionPrefix(
                    scale, radix, tuple(terms), None, False, False, precision
                )
            if precision >= self.max_precision_bits:
                self.ledger.bump(_fields_keys.GROWTH_CF_BUDGET_REFUSALS)
                return ContinuedFractionPrefix(
                    scale, radix, tuple(terms), None, False, True, precision
                )
            precision = min(precision * 2, self.max_precision_bits)

        return ContinuedFractionPrefix(
            scale, radix, tuple(terms), None, False, False, precision
        )

    def _advance_cf_interval(
        self, lower: Fraction, upper: Fraction, partial_quotient: int, precision: int
    ) -> tuple[Fraction, Fraction]:
        operand_work = (
            lower.numerator.bit_length()
            + lower.denominator.bit_length()
            + upper.numerator.bit_length()
            + upper.denominator.bit_length()
            + partial_quotient.bit_length()
        )
        with self.charge_work(
            max(1, 2 * operand_work),
            precision,
            operand_work,
            storage_bits=8 * (precision + operand_work),
        ):
            remainder_low = lower - partial_quotient
            remainder_high = upper - partial_quotient
            return 1 / remainder_high, 1 / remainder_low

    def radix_order(self, scale: HomogeneousGrowthScale, radix: int = 10) -> int:
        """Return ``floor(H*log_radix(3) - D*log_radix(2))`` exactly."""
        self.ensure_open()
        self._validate_order_request(scale, radix)
        if scale.is_identity:
            self.ledger.bump(_fields_keys.GROWTH_ORDER_IDENTITY_SHORTCUTS)
            return 0
        self.ledger.bump(_fields_keys.GROWTH_ORDER_KEY_LOOKUPS)
        key = (scale, radix)
        operand_bits = self._scale_operand_bits(scale, radix)
        with self.charge_work(max(1, operand_bits), 1, operand_bits):
            found = self._orders.get(key)
        if found is not None:
            self.ledger.bump(_fields_keys.GROWTH_ORDER_CACHE_HITS)
            return found

        with self.charge_work(max(1, operand_bits), 1, operand_bits):
            self.ledger.bump(_fields_keys.GROWTH_ORDER_EQUALITY_CHECKS)
            exact_value = _exact_rational_radix_order(scale, radix)
        if exact_value is not None:
            exact = exact_value.numerator // exact_value.denominator
            self.ledger.bump(_fields_keys.GROWTH_ORDER_EXACT_RATIONAL_CASES)
            try:
                self._publish_order(key, exact)
            except BlockContextBudgetExceeded:
                self.ledger.bump(_fields_keys.GROWTH_ORDER_CACHE_BYPASSES)
            return exact

        ratio_bit_estimate = _bounded_ratio_bit_estimate(scale)
        if ratio_bit_estimate <= 64:
            scale_bits = scale.growths.bit_length() + scale.halvings.bit_length()
            radix_bits = radix.bit_length()
            operand_bits = ratio_bit_estimate + scale_bits + radix_bits
            work_units = (
                8
                * (ratio_bit_estimate + 1)
                * (min(ratio_bit_estimate + 1, radix_bits) + 1)
                + radix_bits
            )
            storage_bits = 8 * ratio_bit_estimate + 2 * scale_bits + 32
            with self.charge_work(
                work_units,
                0,
                operand_bits,
                storage_bits=storage_bits,
            ):
                numerator = 3**scale.growths
                denominator = 1 << scale.halvings
                exact = _floor_radix_order_ratio(numerator, denominator, radix)
            self.ledger.bump(_fields_keys.GROWTH_ORDER_BOUNDED_EXACT_RATIO_CASES)
            try:
                self._publish_order(key, exact)
            except BlockContextBudgetExceeded:
                self.ledger.bump(_fields_keys.GROWTH_ORDER_CACHE_BYPASSES)
            return exact

        self._ensure_cache_slot()
        precision = min(32, self.max_precision_bits)
        while True:
            self._ensure_order_readout_capacity(radix, precision)
            lower, upper = self._charged_order_interval(scale, radix, precision)
            lower_floor = lower.numerator // lower.denominator
            upper_floor = upper.numerator // upper.denominator
            if lower_floor == upper_floor:
                self._publish_order(key, lower_floor)
                self.ledger.bump(_fields_keys.GROWTH_ORDER_REFINEMENTS)
                return lower_floor
            if precision >= self.max_precision_bits:
                self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
                raise BlockContextBudgetExceeded(
                    "radix order remains unresolved at the precision budget"
                )
            precision = min(precision * 2, self.max_precision_bits)

    def _ensure_order_readout_capacity(self, radix: int, precision_bits: int) -> None:
        constants_key = (radix, precision_bits)
        entries = 1 + int(constants_key not in self._logs)
        self._ensure_cache_slot(entries)

    def _charged_order_interval(
        self, scale: HomogeneousGrowthScale, radix: int, precision_bits: int
    ) -> tuple[Fraction, Fraction]:
        constants_key = (radix, precision_bits)
        self.ledger.bump(_fields_keys.GROWTH_LOG_CONSTANT_LOOKUPS)
        with self.charge_work(
            max(1, radix.bit_length()),
            1,
            radix.bit_length(),
            storage_bits=4 * radix.bit_length(),
        ):
            constants = self._logs.get(constants_key)
        if constants is None:
            self._ensure_cache_slot()
            with self._charge_log_work(radix, precision_bits, radix.bit_length()):
                constants = _ln_constants(radix, precision_bits)
            try:
                self._logs[constants_key] = constants
            except BlockContextBudgetExceeded:
                self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
                raise
        else:
            self.ledger.bump(_fields_keys.GROWTH_LOG_CONSTANT_CACHE_HITS)

        operand_bits = self._scale_operand_bits(scale, radix)
        units = max(1, precision_bits + operand_bits)
        with self.charge_work(
            units,
            precision_bits,
            operand_bits,
            storage_bits=8 * (precision_bits + operand_bits + 1),
        ):
            return _order_interval(scale, constants)

    def _publish_order(
        self, key: tuple[HomogeneousGrowthScale, int], value: int
    ) -> None:
        try:
            self._orders[key] = value
        except BlockContextBudgetExceeded:
            self.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise

    def _charge_log_work(
        self, radix: int, precision_bits: int, operand_bits: int
    ) -> AbstractContextManager[None]:
        # There are at most O(precision) terms. Their rational powers grow to
        # O(precision*radix_bits), so the aggregate operand work is quadratic
        # in precision and linear in the input radix width.
        input_bits = radix.bit_length() + operand_bits + 2
        units = 4 * (precision_bits + 1) ** 2 * input_bits
        storage_bits = 16 * (precision_bits + 1) * (radix.bit_length() + 2)
        return self.charge_work(
            units,
            precision_bits,
            operand_bits,
            storage_bits=storage_bits,
        )

    @staticmethod
    def _scale_operand_bits(scale: HomogeneousGrowthScale, radix: int) -> int:
        return (
            scale.growths.bit_length()
            + scale.halvings.bit_length()
            + radix.bit_length()
        )

    @staticmethod
    def _validate_order_request(scale: HomogeneousGrowthScale, radix: int) -> None:
        if type(scale) is not HomogeneousGrowthScale:
            raise TypeError("radix order requires a homogeneous growth scale")
        require_integer(radix, "radix", 2)


__all__ = [
    "ContinuedFractionPrefix",
    "GrowthArithmeticEvaluator",
    "HomogeneousGrowthScale",
]
