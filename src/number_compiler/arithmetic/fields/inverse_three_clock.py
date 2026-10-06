"""Exact inverse-three unit clocks shared by admitted dyadic occurrences.

This arithmetic owner does not select a recurrence or admit a source cylinder.
The canonical-key label is preserved for existing consumers across relocation.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded

MAX_DYADIC_CLOCK_BITS = 16384


def validate_clock_natural(value: int, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


def validate_clock_precision(bits: int) -> int:
    validate_clock_natural(bits, "precision")
    if bits > MAX_DYADIC_CLOCK_BITS:
        raise BlockContextBudgetExceeded("Hensel precision budget exceeded")
    return bits


def three_unit_phase(exponent: int, bits: int) -> int:
    """Return 3**h modulo 2**q without ever constructing 3**h."""
    validate_clock_natural(exponent, "exponent")
    validate_clock_precision(bits)
    if bits == 0:
        return 0
    order_bits = 0 if bits == 1 else max(1, bits - 2)
    phase = exponent & ((1 << order_bits) - 1)
    return pow(3, phase, 1 << bits)


def three_dyadic_phase(level: int, bits: int) -> int:
    """3**(2**j) at live precision, including the exceptional j=0 case."""
    validate_clock_natural(level, "dyadic level")
    validate_clock_precision(bits)
    if not bits:
        return 0
    if bits == 1 or level >= max(1, bits - 2):
        return 1
    return three_unit_phase(1 << level, bits)


_ROOT_DIGITS_MOD64 = tuple(
    -pow(three_unit_phase(phase, 6), -1, 64) % 64 for phase in range(16)
)


def _root_digit_mod64(phase: int) -> int:
    return _ROOT_DIGITS_MOD64[phase & 15]


@dataclass(frozen=True, slots=True)
class InverseThreeClock:
    """Canonical temporal phase at one demanded spatial precision."""

    precision: int
    phase: int
    _lift_base: int | None = field(default=None, init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.precision, self.phase)):
            raise TypeError("inverse-three clock fields require exact integers")
        if not 3 <= self.precision <= MAX_DYADIC_CLOCK_BITS or self.phase < 0:
            raise ValueError(self)
        object.__setattr__(self, "phase", self.phase % self.period)

    @property
    def period(self) -> int:
        return 1 << (self.precision - 2)

    @property
    def unit(self) -> int:
        return three_unit_phase(self.phase, self.precision)

    @property
    def inverse_unit(self) -> int:
        return pow(self.unit, -1, 1 << self.precision)

    @property
    def root(self) -> int:
        """The exact finite root ``-3**(-phase) mod 2**precision``."""
        return (-self.inverse_unit) % (1 << self.precision)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-inverse-three-clock", self.precision, self.phase)

    def normalized_prefix(self, source_prefix: int) -> int:
        """Evaluate W lazily from the caller's demanded exact q-bit prefix."""
        if type(source_prefix) is not int or source_prefix < 0:
            raise ValueError("source prefix must be a nonnegative exact integer")
        mask = (1 << self.precision) - 1
        return ((source_prefix & mask) * self.inverse_unit) & mask

    def recover_prefix(self, normalized: int) -> int:
        if type(normalized) is not int or not 0 <= normalized < 1 << self.precision:
            raise ValueError("normalized prefix is outside clock precision")
        return normalized * self.unit % (1 << self.precision)

    def advance(self, steps: int = 1) -> InverseThreeClock:
        if type(steps) is not int or steps < 0:
            raise ValueError("clock advance must be nonnegative")
        return InverseThreeClock(self.precision, self.phase + steps)

    def lift_phase_digit(self, digit: int) -> InverseThreeClock:
        """Add the next six temporal phase bits while lifting q to q+6."""
        if type(digit) is not int or not 0 <= digit < 64:
            raise ValueError("temporal radix-64 phase digit is outside 0..63")
        if self.precision + 6 > MAX_DYADIC_CLOCK_BITS:
            raise ValueError("lifted inverse-three precision exceeds its bound")
        return InverseThreeClock(self.precision + 6, self.phase + digit * self.period)

    @property
    def lift_coefficient(self) -> int:
        """Coefficient of the next temporal phase digit in the root lift."""
        if self.precision < 6:
            raise ValueError("radix-64 root lift requires at least six low bits")
        return 35 if self.precision == 6 else 3

    def lifted_root_digit(self, phase_digit: int) -> int:
        """Return the next six root bits without recomputing a wide power."""
        if type(phase_digit) is not int or not 0 <= phase_digit < 64:
            raise ValueError("temporal radix-64 phase digit is outside 0..63")
        base = self._lift_base
        if base is None:
            base = InverseThreeClock(self.precision + 6, self.phase).root
            object.__setattr__(self, "_lift_base", base)
        base_digit = (base >> self.precision) & 63
        return (base_digit + self.centered_lift_digit(phase_digit)) & 63

    def centered_lift_digit(self, phase_digit: int) -> int:
        """Hasse tangent: a clock revolution shifts only the next six bits.

        Requires neither a full root nor a spatial occurrence. At q=6 the
        bootstrap coefficient is 35; at every q>=7 it is 3.
        """
        if type(phase_digit) is not int or not 0 <= phase_digit < 64:
            raise ValueError("temporal radix-64 phase digit is outside 0..63")
        return (
            self.lift_coefficient * _root_digit_mod64(self.phase) * phase_digit
        ) & 63
