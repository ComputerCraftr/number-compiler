"""Symbolic raw-15 radial periods and carry totals.

This module describes the exact fixed-depth raw sequence
``15**tick * source mod 10**depth`` after its 5-primary transient.  It is a
pure arithmetic projection: constructing a descriptor does not authenticate
an occurrence, admit a repeated source action, or produce the ordered carry
word needed to evaluate digits.  Family owners must bind these values to their
own source, phase, generation, and horizon authority.

The period is stored as a power-of-two exponent.  The full period and carry
total are materialized only through explicit bounded methods.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.adic_morphism import bounded_prime_valuation


def _clock_components(
    source: int, decimal_depth: int
) -> tuple[int, int, int, int | None, PowerOfTwoAffineTotal]:
    valuation_bound = source.bit_length()
    valuation_two = bounded_prime_valuation(source, 2, valuation_bound)
    valuation_five = bounded_prime_valuation(source, 5, valuation_bound)
    effective_depth = decimal_depth - valuation_two
    first_stable = max(0, decimal_depth - valuation_five)

    if effective_depth <= 1:
        period_exponent = 0
    elif effective_depth <= 5:
        period_exponent = 1
    else:
        period_exponent = effective_depth - 4

    phase: int | None = None
    if effective_depth <= 0:
        total = PowerOfTwoAffineTotal(0, 0, 0)
    elif effective_depth == 1:
        total = PowerOfTwoAffineTotal(0, 0, 7)
    elif effective_depth <= 4:
        total = PowerOfTwoAffineTotal(0, 0, 14)
    else:
        odd_core = source // ((1 << valuation_two) * (5**valuation_five))
        residual_five_exponent = max(0, valuation_five - decimal_depth)
        phase_residue = (
            pow(3, first_stable, 32)
            * pow(5, residual_five_exponent, 32)
            * (odd_core % 32)
        ) % 32
        phase = phase_residue
        total = PowerOfTwoAffineTotal(
            7,
            period_exponent,
            7 if phase_residue >= 16 else -7,
        )

    return first_stable, period_exponent, effective_depth, phase, total


@dataclass(frozen=True, slots=True)
class PowerOfTwoAffineTotal:
    """An exact integer represented as ``coefficient * 2**exponent + offset``."""

    coefficient: int
    exponent: int
    offset: int

    def __post_init__(self) -> None:
        require_integer(self.coefficient, "symbolic carry coefficient", 0)
        require_integer(self.exponent, "symbolic carry exponent", 0)
        require_integer(self.offset, "symbolic carry offset")

    @property
    def parity(self) -> int:
        """Return the exact parity without constructing the represented power."""
        self.__post_init__()
        power_parity = self.coefficient if self.exponent == 0 else 0
        return (power_parity + self.offset) & 1

    def modulo(self, modulus: int) -> int:
        """Evaluate the represented integer modulo a positive exact modulus."""
        require_integer(modulus, "carry-total modulus", 1)
        self.__post_init__()
        return (
            self.coefficient * pow(2, self.exponent, modulus) + self.offset
        ) % modulus

    def materialize(self, *, maximum_bits: int) -> int:
        """Materialize the total after bounding both shift and result size."""
        budget = require_integer(maximum_bits, "carry-total bit budget", 1)
        self.__post_init__()
        shifted_bits = (
            0
            if self.coefficient == 0
            else self.coefficient.bit_length() + self.exponent
        )
        # This conservative preflight prevents a large shift even when the
        # subsequent signed offset might cancel some of its leading bits.
        if shifted_bits > budget + 1:
            raise ValueError("carry total requires symbolic representation")
        shifted = 0 if self.coefficient == 0 else self.coefficient << self.exponent
        result = shifted + self.offset
        if result < 0 or result.bit_length() > budget:
            raise ValueError("carry total exceeds its integer bit budget")
        return result


@dataclass(frozen=True, slots=True)
class FifteenRawPowerClock:
    """Pure fixed-depth clock for ``15**tick * source mod 10**depth``.

    ``period_power_of_two_exponent`` describes both the eventual residue and
    emitted-carry periods only after ``first_stable_exponent``.  The descriptor
    carries no issuer token and is not evidence that a family source follows
    this raw multiplication law.
    """

    source: int
    decimal_depth: int
    first_stable_exponent: int
    period_power_of_two_exponent: int
    effective_binary_depth: int
    phase_residue_mod32: int | None
    carry_total: PowerOfTwoAffineTotal

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        """Recompute every derived field before a family consumes this view."""
        require_integer(self.source, "raw-15 source", 1)
        require_integer(self.decimal_depth, "decimal depth", 1)
        expected = _clock_components(self.source, self.decimal_depth)
        actual = (
            self.first_stable_exponent,
            self.period_power_of_two_exponent,
            self.effective_binary_depth,
            self.phase_residue_mod32,
            self.carry_total,
        )
        for value in actual[:2]:
            require_integer(value, "raw-15 clock exponent", 0)
        require_integer(actual[2], "raw-15 effective depth")
        if actual[3] is not None:
            require_integer(actual[3], "raw-15 phase residue", 0, 31)
        if type(actual[4]) is not PowerOfTwoAffineTotal:
            raise TypeError("raw-15 carry total requires its symbolic value type")
        actual[4].__post_init__()
        if actual != expected:
            raise ValueError("raw-15 clock descriptor is inconsistent with its source")

    @property
    def settled(self) -> bool:
        """Whether the first stable exponent is zero."""
        self.validate()
        return self.first_stable_exponent == 0

    def settled_at(self, exponent: int) -> bool:
        """Whether a nonnegative raw-power exponent has passed the transient."""
        require_integer(exponent, "raw-15 exponent", 0)
        self.validate()
        return exponent >= self.first_stable_exponent

    @property
    def carry_total_parity(self) -> int:
        self.validate()
        return self.carry_total.parity

    @property
    def next_depth_period_exponent(self) -> int:
        """Use the complete period's carry parity for the next digit layer."""
        self.validate()
        return self.period_power_of_two_exponent + self.carry_total_parity

    def period(self, *, maximum_bits: int) -> int:
        """Materialize ``2**period_power_of_two_exponent`` under a hard cap."""
        budget = require_integer(maximum_bits, "period bit budget", 1)
        self.validate()
        if self.period_power_of_two_exponent + 1 > budget:
            raise ValueError("raw-15 period requires symbolic representation")
        return 1 << self.period_power_of_two_exponent

    def packet(self) -> dict[str, int | bool | None]:
        """Return scalar descriptor metadata without expanding a period word."""
        self.validate()
        return {
            "source": self.source,
            "decimal_depth": self.decimal_depth,
            "first_stable_exponent": self.first_stable_exponent,
            "period_power_of_two_exponent": self.period_power_of_two_exponent,
            "effective_binary_depth": self.effective_binary_depth,
            "source_phase_mod32": self.phase_residue_mod32,
            "carry_total_coefficient": self.carry_total.coefficient,
            "carry_total_power_of_two_exponent": self.carry_total.exponent,
            "carry_total_offset": self.carry_total.offset,
            "carry_total_parity": self.carry_total_parity,
            "next_depth_period_power_of_two_exponent": (
                self.next_depth_period_exponent
            ),
            "period_word_materialized": False,
        }


def fifteen_raw_power_clock(source: int, decimal_depth: int) -> FifteenRawPowerClock:
    """Construct the exact symbolic fixed-depth raw-15 period descriptor.

    The carry total is the closed form over the *complete* primitive period.
    For effective binary depth ``d >= 5``, its sign is selected from the odd
    source residue at the first stable phase modulo 32. This routine is pure;
    callers must retain and validate their own source-period authority.
    """
    require_integer(source, "raw-15 source", 1)
    require_integer(decimal_depth, "decimal depth", 1)
    first_stable, period_exponent, effective_depth, phase, total = _clock_components(
        source, decimal_depth
    )
    return FifteenRawPowerClock(
        source=source,
        decimal_depth=decimal_depth,
        first_stable_exponent=first_stable,
        period_power_of_two_exponent=period_exponent,
        effective_binary_depth=effective_depth,
        phase_residue_mod32=phase,
        carry_total=total,
    )


__all__ = [
    "FifteenRawPowerClock",
    "PowerOfTwoAffineTotal",
    "fifteen_raw_power_clock",
]
