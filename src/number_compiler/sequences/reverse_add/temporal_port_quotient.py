"""Exact run-level symmetric coefficient and carry-port dynamics.

The quotient stored here is a pure finite spatial representation: a decimal
width, center parity, and the canonical first half of the symmetric pair-sum
word. It has no source authority and cannot issue a Q19 occurrence. The term
owner supplies its exact starting source and owns any admitted result cache.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from decimal import Context, Decimal, Inexact, Rounded, localcontext

from number_compiler.arithmetic.fields.run_pairing import (
    append_run,
    pair_normalized_mirror_digit_runs,
)
from number_compiler.sequences.reverse_add.temporal_matrix7_port import (
    aligned_difference_mod7_from_switches,
)

DigitRun = tuple[int, int]
DigitRuns = tuple[DigitRun, ...]

MAX_EXACT_DECIMAL_BLOCK_WIDTH = 20_000


def decimal_width_upper_bound(value: int) -> int:
    """Return an integer-only upper bound before decimal digit expansion."""
    if type(value) is not int or value < 0:
        raise ValueError("decimal width bound requires a nonnegative exact integer")
    bits = value.bit_length()
    return max(1, (302 * bits + 999) // 1000)


def q19_transition_scratch_nodes(max_width: int) -> int:
    """Reserve the established temporary node bound for one Q19 transition."""
    if type(max_width) is not int or max_width < 1:
        raise ValueError("Q19 maximum width must be a positive exact integer")
    return 24 * max_width + 64


class NativeTransportWidthExceeded(ValueError):
    """A finite native decimal action exceeded its explicit width budget."""


def native_decimal_string_transport(
    source_text: str,
    steps: int,
    *,
    max_width: int = MAX_EXACT_DECIMAL_BLOCK_WIDTH,
    on_tick_start: Callable[[int], None] | None = None,
    on_tick_complete: Callable[[str, Decimal, Decimal], None] | None = None,
) -> tuple[str, int]:
    """Apply a bounded exact reverse/add block without integer conversion.

    Each physical transition is evaluated. A local Decimal context traps
    rounding and inexact operations; keeping endpoints as decimal strings
    avoids changing or depending on Python's process-wide int-string limit.
    """
    if (
        type(source_text) is not str
        or not source_text
        or (len(source_text) > 1 and source_text[0] == "0")
        or not source_text.isascii()
        or not source_text.isdecimal()
    ):
        raise ValueError("native temporal source must be canonical decimal digits")
    if type(steps) is not int or steps < 0:
        raise ValueError("native reverse/add duration must be nonnegative")
    if type(max_width) is not int or max_width < 1:
        raise ValueError("native temporal width guard must be positive")
    if len(source_text) + steps > max_width:
        raise NativeTransportWidthExceeded(
            "finite native decimal block exceeds width guard"
        )
    if steps == 0:
        return source_text, 0

    visits = 0
    value: Decimal | None = None
    reverse: Decimal | None = None
    try:
        with localcontext(
            Context(
                prec=len(source_text) + steps + 2,
                traps=[Inexact, Rounded],
            )
        ):
            value = Decimal(source_text)
            reverse = Decimal(source_text[::-1])
            for tick in range(steps):
                if on_tick_start is not None:
                    on_tick_start(len(source_text))
                visits += len(source_text)
                value += reverse
                source_text = str(value)
                if not source_text.isdecimal() or (
                    len(source_text) > 1 and source_text[0] == "0"
                ):
                    raise AssertionError(
                        "decimal transport lost canonical integer representation"
                    )
                if tick + 1 < steps or on_tick_complete is not None:
                    reverse = Decimal(source_text[::-1])
                if on_tick_complete is not None:
                    # The callback sees the *same exact physical endpoint* used
                    # by the next tick. No independently guessed port sequence.
                    on_tick_complete(source_text, value, reverse)
        return source_text, visits + len(source_text)
    except BaseException:
        # Callers may retain this exception's traceback. Do not let it keep
        # source-sized strings or Decimal coefficients after scratch release.
        source_text = ""
        value = None
        reverse = None
        raise


def _append_issued_run(runs: list[DigitRun], symbol: int, count: int) -> None:
    """Coalesce one already-validated internally issued run."""
    if count < 1:
        return
    if runs and runs[-1][0] == symbol:
        runs[-1] = symbol, runs[-1][1] + count
    else:
        runs.append((symbol, count))


@dataclass(frozen=True, slots=True)
class DecimalRunProjection:
    integer_residue: int
    reverse_residue: int
    run_records_visited: int
    operand_bits: int


def _validated_runs(runs: Sequence[DigitRun], upper: int) -> DigitRuns:
    canonical: list[DigitRun] = []
    for symbol, count in runs:
        if type(symbol) is not int or not 0 <= symbol <= upper:
            raise ValueError("run symbol is outside its alphabet")
        if type(count) is not int or count < 1:
            raise ValueError("run length must be a positive exact integer")
        append_run(canonical, symbol, count)
    return tuple(canonical)


def decimal_run_residues(runs_lsd: DigitRuns, modulus: int) -> DecimalRunProjection:
    """Return exact integer and reversed-integer residues from an LSD run tape.

    Repeated-digit runs use a repunit computed modulo ``9 * modulus`` before
    exact division by nine. This remains valid when nine is not invertible in
    the target ring, and leading zeroes in the reversed word are harmless.
    """
    if type(modulus) is not int or modulus < 2:
        raise ValueError("decimal residue modulus must be at least two")
    runs = _validated_runs(runs_lsd, 9)
    if not runs:
        raise ValueError("decimal residue projection requires a nonempty tape")

    factors: list[tuple[int, int]] = []
    operand_bits = 0
    extended_modulus = 9 * modulus
    for _, length in runs:
        power = pow(10, length, extended_modulus)
        power_residue = power % modulus
        repunit_numerator = (power - 1) // 9
        repunit = repunit_numerator % modulus
        factors.append((power_residue, repunit))
        operand_bits += (
            (10).bit_length()
            + length.bit_length()
            + extended_modulus.bit_length()
            + power.bit_length()
            + modulus.bit_length()
            + repunit_numerator.bit_length()
            + repunit.bit_length()
        )

    def fold(indices: range) -> int:
        nonlocal operand_bits
        residue = 0
        for index in indices:
            digit, _ = runs[index]
            power, repunit = factors[index]
            first_product = residue * power
            second_product = digit * repunit
            total = first_product + second_product
            operand_bits += (
                residue.bit_length()
                + power.bit_length()
                + digit.bit_length()
                + repunit.bit_length()
                + first_product.bit_length()
                + second_product.bit_length()
                + total.bit_length()
                + modulus.bit_length()
            )
            residue = total % modulus
        return residue

    forward = fold(range(len(runs) - 1, -1, -1))
    backward = fold(range(len(runs)))
    return DecimalRunProjection(forward, backward, 4 * len(runs), operand_bits)


@dataclass(frozen=True, slots=True)
class AlignedCarryPort:
    """Exact outgoing decimal carry transitions for one physical normalization."""

    source_width: int
    switches: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.source_width) is not int or self.source_width < 1:
            raise ValueError("carry port source width must be positive")
        if type(self.switches) is not tuple:
            raise TypeError("carry switches must be an immutable tuple")
        previous = 0
        for switch in self.switches:
            if type(switch) is not int or not previous < switch <= self.source_width:
                raise ValueError("carry switches must be ordered within source width")
            previous = switch

    @classmethod
    def from_switches(
        cls, source_width: int, switches: Sequence[int]
    ) -> AlignedCarryPort:
        canonical = tuple(switches)
        return cls(source_width, canonical)

    @property
    def growth(self) -> int:
        return len(self.switches) & 1

    @property
    def difference_mod7(self) -> int:
        return aligned_difference_mod7_from_switches(self.source_width, self.switches)

    @property
    def target_width(self) -> int:
        return self.source_width + self.growth

    def internal_carry_mask_mod(self, modulus: int) -> tuple[int, int, int]:
        """Project the internal binary carry word without a decimal tape."""
        if type(modulus) is not int or modulus < 2:
            raise ValueError("carry-mask modulus must be at least two")
        internal_width = self.source_width - 1
        residue = 0
        operand_bits = 0
        extended_modulus = 9 * modulus
        switches = self.switches
        for index in range(0, len(switches), 2):
            first = switches[index]
            last = min(
                internal_width,
                switches[index + 1] - 1
                if index + 1 < len(switches)
                else internal_width,
            )
            if first > last:
                continue
            length = last - first + 1
            power: int = pow(10, length, extended_modulus)
            repunit = (power - 1) // 9 % modulus
            shift: int = pow(10, internal_width - last, modulus)
            product = shift * repunit
            residue = (residue + product) % modulus
            operand_bits += (
                length.bit_length()
                + extended_modulus.bit_length()
                + power.bit_length()
                + repunit.bit_length()
                + shift.bit_length()
                + product.bit_length()
                + residue.bit_length()
                + modulus.bit_length()
            )
        return residue, len(switches), operand_bits


@dataclass(frozen=True, slots=True)
class SymmetricPortStep:
    """One exact successor transform and its normalized digit/carry output."""

    target: SymmetricCoefficientPort
    carry: AlignedCarryPort
    normalized_digits_lsd: DigitRuns
    run_records_visited: int


@dataclass(frozen=True, slots=True)
class SymmetricCoefficientPort:
    """Canonical half-tape for an exact width-indexed symmetric pair word.

    ``half_runs`` stores the first ``ceil(width / 2)`` pair coefficients in
    least-significant-first order. The full symmetric word is recovered by
    reflection. This is a pure representation law, not a semantic source ID.
    """

    width: int
    half_runs: DigitRuns

    def __post_init__(self) -> None:
        if type(self.width) is not int or self.width < 1:
            raise ValueError("symmetric coefficient width must be positive")
        if type(self.half_runs) is not tuple:
            raise TypeError("symmetric coefficient runs must be an immutable tuple")
        previous = -1
        extent = 0
        for symbol, count in self.half_runs:
            if type(symbol) is not int or not 0 <= symbol <= 18:
                raise ValueError("run symbol is outside its alphabet")
            if type(count) is not int or count < 1:
                raise ValueError("run length must be a positive exact integer")
            if symbol == previous:
                raise ValueError("symmetric coefficient runs must be canonical")
            previous = symbol
            extent += count
        if extent != (self.width + 1) // 2:
            raise ValueError("half-tape extent disagrees with width and center parity")

    @classmethod
    def from_half_runs(
        cls, half_runs: Sequence[DigitRun], *, odd: bool
    ) -> SymmetricCoefficientPort:
        if type(odd) is not bool:
            raise TypeError("center parity must be Boolean")
        half = _validated_runs(half_runs, 18)
        if not half:
            raise ValueError("symmetric pair word must be nonempty")
        half_width = sum(count for _, count in half)
        return cls(2 * half_width - int(odd), half)

    @classmethod
    def from_source_digits(cls, digits_lsd: Sequence[int]) -> SymmetricCoefficientPort:
        if not digits_lsd:
            raise ValueError("symmetric source digits must be nonempty")
        width = len(digits_lsd)
        half: list[DigitRun] = []
        for index in range((width + 1) // 2):
            low, high = digits_lsd[index], digits_lsd[width - index - 1]
            if (
                type(low) is not int
                or type(high) is not int
                or not 0 <= low <= 9
                or not 0 <= high <= 9
            ):
                raise ValueError("source digit lies outside decimal alphabet")
            append_run(half, low + high, 1)
        return cls(width, tuple(half))

    @property
    def half_width(self) -> int:
        return (self.width + 1) // 2

    def full_runs(self) -> DigitRuns:
        full = list(self.half_runs)
        last = len(self.half_runs) - 1
        for index in range(last, -1, -1):
            symbol, count = self.half_runs[index]
            if self.width & 1 and index == last:
                count -= 1
            append_run(full, symbol, count)
        return tuple(full)

    def normalize_with_carry(self) -> tuple[DigitRuns, AlignedCarryPort, int]:
        """Return the exact normalized digits, outgoing carry port and work."""
        source_runs = self.full_runs()
        digits: list[DigitRun] = []
        switches: list[int] = []
        carry = 0
        position = 0
        for coefficient, extent in source_runs:
            following = carry if coefficient == 9 else int(coefficient >= 10)
            if following != carry:
                switches.append(position + 1)
            first = coefficient + carry - 10 * following
            if not 0 <= first <= 9:
                raise AssertionError("symmetric carry emitted a non-digit")
            _append_issued_run(digits, first, 1)
            if extent > 1:
                steady = coefficient + following - 10 * following
                if not 0 <= steady <= 9:
                    raise AssertionError("steady symmetric carry emitted a non-digit")
                _append_issued_run(digits, steady, extent - 1)
            position += extent
            carry = following
        port = AlignedCarryPort.from_switches(self.width, switches)
        if carry:
            _append_issued_run(digits, 1, 1)
        if not digits or (position > 1 and digits[-1][0] == 0):
            raise ValueError("normalized symmetric output is not canonical")
        visited = 2 * len(self.half_runs) + len(source_runs)
        return tuple(digits), port, visited

    @staticmethod
    def _successor_half(
        normalized_digits_lsd: DigitRuns,
        *,
        width: int | None = None,
    ) -> tuple[DigitRuns, int]:
        """Pair one internally normalized canonical tape without copying it."""
        runs = normalized_digits_lsd
        if not runs:
            raise ValueError("normalization produced an empty decimal word")
        if width is None:
            width = sum(length for _, length in runs)
        paired, _odd, visits = pair_normalized_mirror_digit_runs(
            runs,
            width=width,
            half_only=True,
        )
        return paired, visits + 2 * len(runs)

    def successor_with_carry(self) -> SymmetricPortStep:
        normalized, carry, normalize_visits = self.normalize_with_carry()
        normalized_width = carry.target_width
        half, pairing_visits = self._successor_half(normalized, width=normalized_width)
        target = SymmetricCoefficientPort(
            normalized_width,
            half,
        )
        if target.width != carry.target_width:
            raise AssertionError("half-tape successor lost the carry width port")
        return SymmetricPortStep(
            target,
            carry,
            normalized,
            normalize_visits + pairing_visits + len(normalized) + 3 * len(half),
        )

    def successor(self) -> SymmetricCoefficientPort:
        return self.successor_with_carry().target


__all__ = [
    "MAX_EXACT_DECIMAL_BLOCK_WIDTH",
    "decimal_width_upper_bound",
    "q19_transition_scratch_nodes",
    "NativeTransportWidthExceeded",
    "AlignedCarryPort",
    "DigitRun",
    "DigitRuns",
    "SymmetricCoefficientPort",
    "SymmetricPortStep",
    "DecimalRunProjection",
    "decimal_run_residues",
    "native_decimal_string_transport",
]
