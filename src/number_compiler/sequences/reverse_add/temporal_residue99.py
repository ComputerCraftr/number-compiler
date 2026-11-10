"""Exact, predictive decimal reverse/add temporal congruence modulo 99.

This quotient is an output observer, not a full Q19/GT-bank successor oracle.
Unlike ``2rev10``, the physical reverse/add multiplier is 2 at odd width
and 11 at even width. Every positive decimal source undergoes growth within
five steps (there cannot be five consecutive nongrowth steps), so its width
becomes even within five ticks and the next result is divisible by 11.
Consequently, at every depth >= 6, the residue is independent of ALL future
width controls:

    X_n = 55 * (X_0 % 9) * 2**n  (mod 99).

An issued Q19 *pair-sum* SLP suffices to recover X_0 mod 9 without decoding X:
S(10) = X_0 + reverse10(X_0) = 2*X_0 (mod 9).
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


@dataclass(frozen=True, slots=True)
class ReverseAddResidue99:
    """Predictive scalar output. A conditional control is NOT a physical proof."""

    duration: int
    target_mod99: int
    source_mod9: int
    source_mod99: int | None
    source_width_parity: int | None
    control_needed: bool
    source_certified: bool
    proof: str
    complete_integer_certified: Literal[False] = False

    @property
    def target_mod9(self) -> int:
        return self.target_mod99 % 9

    @property
    def target_mod11(self) -> int:
        return self.target_mod99 % 11

    @property
    def binary_harmonic_phi3(self) -> tuple[int, int]:
        """Exact F2 third-cyclotomic *output* of the physical mod-99 clock.

        The physical reverse/add modulus-99 value doubles after the universal
        six-tick 11-divisibility collapse.  Its six phase values are encoded
        as seven-bit vectors, NOT as decimal addition-carry bits.  Writing
        S for one physical time shift and XOR for F2 addition, this returns
        the first two values of Z=(S+1)(S**3+1)R, so the next pair is
        (Z[n+1], Z[n] XOR Z[n+1]); the matrix [[0,1],[1,1]] has order 3.

        This is a certified *output projection*, not a Moore state for
        future source digits, growth or the independent carry/F5 ports.
        """
        if self.duration < 6 or not self.source_certified or self.control_needed:
            raise ValueError("binary harmonic needs the certified six-tick mod-99 ray")
        phases = [self.target_mod99]
        for _ in range(5):
            phases.append(2 * phases[-1] % 99)
        a, b, c, d, e, f = phases
        return (a ^ b ^ d ^ e, b ^ c ^ e ^ f)


def _check_duration(duration: int) -> None:
    if type(duration) is not int or duration < 0:
        raise ValueError("temporal duration must be a nonnegative integer")


def reverse_decimal_and_width(
    value: int, *, before_digit: Callable[[int, int], None] | None = None
) -> tuple[int, int]:
    """Return exact decimal reversal and width without string conversion.

    An optional callback runs before each digit operation with the current
    input and accumulated output bit lengths. Production bounded observers
    use it to account for operand work; ordinary arithmetic callers stay pure.
    """
    if type(value) is not int or value < 0:
        raise ValueError("decimal source must be a nonnegative exact integer")
    if value == 0:
        return 0, 1
    reversed_value, width = 0, 0
    while value:
        if before_digit is not None:
            before_digit(value.bit_length(), reversed_value.bit_length())
        value, digit = divmod(value, 10)
        reversed_value = reversed_value * 10 + digit
        width += 1
    return reversed_value, width


def from_seed(seed: int, duration: int) -> ReverseAddResidue99:
    """Cold source predictor, with no Q19 publisher or future-width oracle.

    The <=5-tick prefix uses independent literal arithmetic; all deeper
    queries are constant-size modular exponentiations regardless of duration.
    """
    if type(seed) is not int or seed < 0:
        raise ValueError("decimal reverse/add source must be nonnegative")
    _check_duration(duration)
    if duration >= 6:
        result = 55 * (seed % 9) * pow(2, duration, 99) % 99
        return ReverseAddResidue99(
            duration,
            result,
            seed % 9,
            seed % 99,
            None,
            False,
            True,
            "universal six-tick mod-11 collapse and mod-9 doubling",
        )
    current = seed
    _, width = reverse_decimal_and_width(seed)
    for _ in range(duration):
        reverse, _ = reverse_decimal_and_width(current)
        current += reverse
    return ReverseAddResidue99(
        duration,
        current % 99,
        seed % 9,
        seed % 99,
        width % 2,
        False,
        True,
        "bounded exact prefix (at most five additions)",
    )


def input_step(residue: int, width_parity: int, growth: int) -> tuple[int, int]:
    """Source-independent input-driven Moore transition (output, next parity)."""
    if type(residue) is not int or not 0 <= residue < 99:
        raise ValueError("residue must be in 0..98")
    if type(width_parity) is not int or width_parity not in (0, 1):
        raise ValueError("width parity must be 0 or 1")
    if type(growth) is not int or growth not in (0, 1):
        raise ValueError("growth must be a Boolean bit")
    return (residue * (2 if width_parity else 11)) % 99, width_parity ^ growth


def future_moore_class(width_parity: int, residue: int) -> int:
    """189 output-future classes over *all* possible growth input words.

    The two width-parity states merge iff 11 divides the residue. Remaining
    states are distinguished by the next output. The resulting 9+2*90=189
    state IDs are dense and independent of an observed growth itinerary.
    """
    input_step(residue, width_parity, 0)
    if residue % 11 == 0:
        return residue // 11
    nonmultiple_rank = residue - (residue + 10) // 11
    return 9 + 2 * nonmultiple_rank + width_parity


def from_issued_pair(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    duration: int,
    *,
    growth_word: tuple[int, ...] = (),
    border_certificate: CertifiedBorderGrowth | None = None,
) -> ReverseAddResidue99:
    """Project an authenticated source Q19 pair SLP without future Q19 work.

    The symmetric pair polynomial is S(10)=X+reverse(X). At even source
    width, S alone cannot recover X mod99 (11 is not invertible), but the
    *next* value S(10) is unambiguous and thereafter doubles modulo99.

    Before the universal six-step collapse, an odd-width source may need an
    independently certified growth word. An unproved supplied word produces
    only a *conditional* result: ``source_certified=False``.
    """
    _check_duration(duration)
    owner.validate_issued_occurrence(source)
    if type(growth_word) is not tuple or any(
        type(bit) is not int or bit not in (0, 1) for bit in growth_word
    ):
        raise ValueError("growth control must be a tuple of Boolean bits")
    if border_certificate is not None:
        border_certificate.validate(owner, source)
        if border_certificate.growth_word != growth_word:
            raise ValueError("border certificate and growth control disagree")
    pair_mod99 = owner.radix19_cochain(source, z=10, modulus=99).pairs
    source_mod9 = 5 * pair_mod99 % 9
    width_parity = source.pair_width % 2
    if duration >= 6:
        target = 55 * source_mod9 * pow(2, duration, 99) % 99
        return ReverseAddResidue99(
            duration,
            target,
            source_mod9,
            50 * pair_mod99 % 99 if width_parity else None,
            width_parity,
            False,
            True,
            "issued pair SLP plus universal six-tick collapse",
        )
    if width_parity == 0:
        if duration < 1:
            raise ValueError("even-width pair sum cannot recover current mod99")
        return ReverseAddResidue99(
            duration,
            pair_mod99 * pow(2, duration - 1, 99) % 99,
            source_mod9,
            None,
            width_parity,
            False,
            True,
            "even-width source gives mod-11 zero in its next output",
        )
    source_mod99 = 50 * pair_mod99 % 99
    if source_mod99 % 11 == 0:
        return ReverseAddResidue99(
            duration,
            source_mod99 * pow(2, duration, 99) % 99,
            source_mod9,
            source_mod99,
            width_parity,
            False,
            True,
            "source is already on the width-independent mod-11-zero ray",
        )
    if duration <= 1:
        return ReverseAddResidue99(
            duration,
            source_mod99 * pow(2, duration, 99) % 99,
            source_mod9,
            source_mod99,
            width_parity,
            False,
            True,
            "odd-width source with no future parity dependency",
        )
    if len(growth_word) != duration:
        raise ValueError("odd-width short power requires a full growth word")
    current, parity = source_mod99, width_parity
    for growth in growth_word:
        current, parity = input_step(current, parity, growth)
    certified = border_certificate is not None
    return ReverseAddResidue99(
        duration,
        current,
        source_mod9,
        source_mod99,
        width_parity,
        True,
        certified,
        "source-issued border-controlled scalar action"
        if certified
        else "conditional growth-input scalar action (not authorized)",
    )
