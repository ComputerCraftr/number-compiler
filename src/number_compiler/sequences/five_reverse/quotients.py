"""Source-free 5rev10 digit-field and renormalized-H projections.

The mod-225 digit field is a universal autonomous quotient. The H action is
an unnormalized auxiliary quotient at fixed precision. Normalized physical
low bands require the separate, explicitly bounded moving cut below.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import digits_lsd, reverse_radix_integer

MAX_MOVING_CUT_DIGIT_ACTIONS = 500_000


class MovingCutBudgetExceeded(ValueError):
    """The exact physical band needs more modular digit work than admitted."""


@dataclass(frozen=True, slots=True)
class DigitField225State:
    """The universal concatenated ``decimal(5*d)`` field modulo 225."""

    residue: int

    def __post_init__(self) -> None:
        require_integer(self.residue, "mod-225 digit-field residue", 0, 224)

    def successor(self) -> DigitField225State:
        return DigitField225State((5 * self.residue) % 225)

    def power(self, generations: int) -> DigitField225State:
        generations = require_integer(generations, "digit-field generation", 0)
        return DigitField225State((pow(5, generations, 225) * self.residue) % 225)

    def next_mod1125(self, *, leading_source_digit: int) -> int:
        """Lift one successor using an independently issued leading digit."""
        digit = require_integer(leading_source_digit, "leading source digit", 0, 9)
        parent = self.successor().residue
        low = 25 if digit % 2 else 25 * digit % 125
        return parent + 225 * ((parent // 25 - low // 25) % 5)


def _digit_field225_initial(seed: int) -> int:
    tail = 5 * (seed % 10) % 25
    return tail + 25 * (4 * (5 * (seed % 9) - tail) % 9)


def digit_field225(seed: int, generation: int) -> DigitField225State:
    """Return the exact all-source mod-225 field without building terms."""
    seed = require_integer(seed, "five-reversal seed", 0)
    generation = require_integer(generation, "digit-field generation", 0)
    return DigitField225State(_digit_field225_initial(seed)).power(generation)


def _h_step_mod(value: int, modulus: int) -> int:
    """Apply H=E∘(5*) using only the requested low decimal digits."""
    source = (5 * value) % modulus
    previous_parity = 0
    result = 0
    place = 1
    while source:
        source, digit = divmod(source, 10)
        half, parity = divmod(digit, 2)
        result += (half + 5 * previous_parity) * place
        previous_parity = parity
        place *= 10
    if place < modulus:
        result += 5 * previous_parity * place
    return result


def h_power_mod(source: int, exponent: int, places: int) -> int:
    """Compute H^exponent(source) mod 10^places via its finite quotient.

    H is 1-Lipschitz across decimal precision and H^(2k) vanishes modulo
    10^k, so this runs fewer than 2k modular transitions.
    """
    source = require_integer(source, "H source", 0)
    exponent = require_integer(exponent, "H exponent", 0)
    places = require_integer(places, "H decimal places", 1, 4096)
    if exponent >= 2 * places:
        return 0
    modulus: int = 10**places
    value = source % modulus
    for _ in range(exponent):
        value = _h_step_mod(value, modulus)
    return value


@dataclass(frozen=True, slots=True)
class ReflectedHSource:
    """An exact auxiliary H source before final decimal normalization."""

    source: int
    exponent: int


def reflected_h_source(seed: int, generation: int) -> ReflectedHSource:
    """Resolve the odd/even source of the all-future symbolic expression."""
    require_integer(seed, "five-reversal seed", 0)
    require_integer(generation, "physical generation", 1)
    if generation % 2:
        return ReflectedHSource(reverse_radix_integer(seed, 10), generation // 2)
    parity_mask = 0
    for digit in reversed(digits_lsd(seed, 10)):
        parity_mask = 10 * parity_mask + digit % 2
    return ReflectedHSource((seed + 99 * parity_mask) // 2, generation // 2 - 1)


def digit_field_residue(
    physical_suffix: int,
    source_mod9: int,
    places: int,
) -> int:
    """Recover the variable-width field at 9*5^places from its physical suffix."""
    require_integer(places, "base-five digit-field places", 3, 128)
    require_integer(
        physical_suffix, "decimal digit-field suffix", 0, 10 ** (places - 1) - 1
    )
    require_integer(source_mod9, "physical residue mod 9", 0, 8)
    modulus: int = 5**places
    tail = 0
    for digit in reversed(digits_lsd(physical_suffix, 10)):
        code = 5 * digit
        tail = (tail * (10 if code < 10 else 100) + code) % modulus
    return tail + modulus * ((5 * source_mod9 - tail) * pow(modulus, -1, 9) % 9)


def physical_low_band_from_h(
    seed: int,
    generation: int,
    digits: int,
    *,
    max_places: int = 4096,
    max_digit_actions: int = MAX_MOVING_CUT_DIGIT_ACTIONS,
) -> int:
    """Return an exact normalized physical low band by the bounded moving cut."""
    seed = require_integer(seed, "five-reversal seed", 0)
    generation = require_integer(generation, "physical generation", 0)
    digits = require_integer(digits, "physical band digits", 1, 128)
    max_places = require_integer(max_places, "maximum H places", 1, 4096)
    max_digit_actions = require_integer(max_digit_actions, "H digit-action budget", 1)
    if digits > max_places:
        raise MovingCutBudgetExceeded("physical band exceeds the precision budget")
    band_modulus: int = 10**digits
    if generation == 0 or seed == 0:
        return seed % band_modulus
    source = reflected_h_source(seed, generation)

    def evaluate(places: int) -> int:
        nonlocal max_digit_actions
        actions = source.exponent * places if source.exponent < 2 * places else 0
        if actions > max_digit_actions:
            raise MovingCutBudgetExceeded(
                "moving-cut digit actions exceed their budget"
            )
        max_digit_actions -= actions
        return h_power_mod(source.source, source.exponent, places)

    places = min(digits, max_places)
    while True:
        residue = evaluate(places)
        if residue:
            selected = residue
            valuation = 0
            while residue % 10 == 0:
                residue //= 10
                valuation += 1
            needed_places = valuation + digits
            if needed_places > max_places:
                raise MovingCutBudgetExceeded("moving-cut precision exceeds its budget")
            lifted = selected if needed_places <= places else evaluate(needed_places)
            cut: int = 10**valuation
            return (5 * (lifted // cut)) % band_modulus
        if places == max_places:
            raise MovingCutBudgetExceeded(
                "moving-cut valuation exceeds its precision budget"
            )
        places = min(max_places, places * 2)
