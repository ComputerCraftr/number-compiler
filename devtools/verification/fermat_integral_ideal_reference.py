"""Validation-only bounded integral Fermat/Pépin reference checker.

For ``w = 2**n`` and ``k = 2**level``, this module builds the exact
negacyclic integer fold of ``(1+z)**k`` modulo ``z**w + 1``. It authenticates
that fold by recomputing integer binomial coefficients, then checks its signed
binary carry cochain. At the terminal level ``level = w-1``, the canonical
signed output ``(-1, 0, ..., 0)`` proves the sufficient Pépin congruence and
therefore primality.

This reconstructive source checker is deliberately kept under ``devtools``;
it is not a production primality route. Its source term budget admits F4 and
refuses F5. Failure to meet the sufficient criterion is ``UNKNOWN``; this
reference does not use the converse of Pépin's theorem to issue compositeness.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.signed_weighted_carry import (
    MAX_SIGNED_WEIGHTED_BITS,
    SignedCarryBudgetExceeded,
    WideSignedCarryAction,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_transport,
)

MAX_FERMAT_SOURCE_TERMS = 65_536
MAX_FERMAT_SOURCE_WIDTH = 64
DEFAULT_FERMAT_WEIGHTED_BITS = 262_144
_DERIVATION = "exact-integer-binomial-negacyclic-fold-v1"


class SourceCoefficientBudgetExceeded(ValueError):
    """The requested integral source exceeds the explicit term/size budget."""


def _limit(value: int, name: str, maximum: int, minimum: int = 1) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise SourceCoefficientBudgetExceeded((name, value, minimum, maximum))
    return value


def _fold_binomial_source(
    width: int, exponent: int, max_terms: int, max_weighted_bits: int
) -> tuple[int, ...]:
    """Stream an exact alternating fold of integer binomial coefficients."""
    if type(width) is not int or not 1 <= width <= MAX_FERMAT_SOURCE_WIDTH:
        raise SourceCoefficientBudgetExceeded("source width exceeds budget")
    if type(exponent) is not int or exponent < 0:
        raise ValueError(exponent)
    if exponent + 1 > max_terms:
        raise SourceCoefficientBudgetExceeded(
            "integral binomial source exceeds the declared term budget; "
            "no hidden modular-squaring fallback"
        )
    # Since C(k,j) <= 2**k, this conservative bound rejects before any large
    # coefficient is formed. A few extra bits cover the exact ratio update.
    if exponent + exponent.bit_length() + 2 > max_weighted_bits:
        raise SourceCoefficientBudgetExceeded(
            "integer binomial coefficient exceeds the weighted-bit budget"
        )

    folded = [0] * width
    coefficient = 1
    for index in range(exponent + 1):
        wrap, position = divmod(index, width)
        folded[position] += -coefficient if wrap & 1 else coefficient
        if index != exponent:
            numerator = coefficient * (exponent - index)
            coefficient, remainder = divmod(numerator, index + 1)
            if remainder:
                raise ArithmeticError("integer binomial recurrence was inexact")
            if coefficient.bit_length() > max_weighted_bits:
                raise SourceCoefficientBudgetExceeded(
                    "integer binomial coefficient exceeds the weighted-bit budget"
                )
    if any(value.bit_length() > max_weighted_bits for value in folded):
        raise SourceCoefficientBudgetExceeded(
            "folded integer coefficient exceeds the weighted-bit budget"
        )
    return tuple(folded)


@dataclass(frozen=True, slots=True)
class FermatIntegralIdealWitness:
    """Finite integer research witness whose source and cochain are rechecked."""

    index: int
    level: int
    folded: tuple[int, ...]
    carries: tuple[int, ...]
    signed_digits: tuple[int, ...]
    derivation: str = _DERIVATION

    def __post_init__(self) -> None:
        if type(self.index) is not int or not 1 <= self.index <= 6:
            raise ValueError("bounded Fermat witness requires index 1 through 6")
        if type(self.level) is not int or not 0 <= self.level <= 15:
            raise ValueError("bounded source level requires 0 through 15")
        if (
            type(self.folded) is not tuple
            or type(self.carries) is not tuple
            or type(self.signed_digits) is not tuple
        ):
            raise TypeError("witness vectors must be exact tuples")
        width = 1 << self.index
        if (
            len(self.folded) != width
            or len(self.carries) != width + 1
            or len(self.signed_digits) != width
        ):
            raise ValueError("witness vector lengths do not match the Fermat width")
        if type(self.derivation) is not str:
            raise TypeError("source derivation must be an exact string")
        if any(type(value) is not int for value in self.folded):
            raise TypeError("folded coefficients must be an exact integer tuple")
        if any(type(value) is not int for value in self.carries):
            raise TypeError("signed carries must be an exact integer tuple")
        if any(
            type(value) is not int or value not in (-1, 0, 1)
            for value in self.signed_digits
        ):
            raise TypeError("signed output digits must be exact -1/0/1 integers")

    @property
    def width(self) -> int:
        return 1 << self.index

    @property
    def exponent(self) -> int:
        return 1 << self.level

    @property
    def terminal(self) -> bool:
        return self.level == self.width - 1

    @classmethod
    def from_source(
        cls,
        index: int,
        *,
        level: int | None = None,
        max_terms: int = MAX_FERMAT_SOURCE_TERMS,
        max_width: int = MAX_FERMAT_SOURCE_WIDTH,
        max_weighted_bits: int = DEFAULT_FERMAT_WEIGHTED_BITS,
    ) -> FermatIntegralIdealWitness:
        terms = _limit(max_terms, "source-term-budget", MAX_FERMAT_SOURCE_TERMS)
        width_budget = _limit(
            max_width, "source-width-budget", MAX_FERMAT_SOURCE_WIDTH, minimum=2
        )
        bits_budget = _limit(
            max_weighted_bits,
            "weighted-integer-budget",
            MAX_SIGNED_WEIGHTED_BITS,
            minimum=8,
        )
        if type(index) is not int or index < 1:
            raise ValueError("Pépin criterion requires Fermat index >= 1")
        # Bound the shift count before lowering the width.
        if index >= width_budget.bit_length():
            raise SourceCoefficientBudgetExceeded("Fermat width exceeds source budget")
        width = 1 << index
        if width > width_budget:
            raise SourceCoefficientBudgetExceeded("Fermat width exceeds source budget")
        if level is None:
            level = width - 1
        if type(level) is not int or level < 0:
            raise ValueError(level)
        # 2**level+1 is the number of binomial terms. Check its bit length
        # before constructing this exponent.
        if level >= terms.bit_length():
            raise SourceCoefficientBudgetExceeded(
                "dyadic source level exceeds term budget"
            )
        exponent = 1 << level
        if exponent + 1 > terms:
            raise SourceCoefficientBudgetExceeded("dyadic source exceeds term budget")

        folded = _fold_binomial_source(width, exponent, terms, bits_budget)
        arena = SLPArena()
        root = arena.word(folded)
        carry_action = WideSignedCarryAction(
            arena,
            root,
            sign=-1,
            max_width=width_budget,
            max_weighted_bits=bits_budget,
        )
        if not carry_action.verify_cochain():
            raise ArithmeticError("source-derived signed carry relation failed")
        witness = cls(
            index,
            level,
            folded,
            tuple(carry_action.carry_at(i) for i in range(width + 1)),
            tuple(carry_action.digit_at(i) for i in range(width)),
        )
        return witness

    def verify(
        self,
        *,
        max_terms: int = MAX_FERMAT_SOURCE_TERMS,
        max_width: int = MAX_FERMAT_SOURCE_WIDTH,
        max_weighted_bits: int = DEFAULT_FERMAT_WEIGHTED_BITS,
    ) -> bool:
        """Re-authenticate the binomial source, every carry, digit, and seam."""
        try:
            terms = _limit(max_terms, "source-term-budget", MAX_FERMAT_SOURCE_TERMS)
            width_budget = _limit(
                max_width,
                "source-width-budget",
                MAX_FERMAT_SOURCE_WIDTH,
                minimum=2,
            )
            bits_budget = _limit(
                max_weighted_bits,
                "weighted-integer-budget",
                MAX_SIGNED_WEIGHTED_BITS,
                minimum=8,
            )
            if (
                type(self.index) is not int
                or not 1 <= self.index <= 6
                or type(self.level) is not int
                or not 0 <= self.level <= 15
                or type(self.derivation) is not str
                or self.derivation != _DERIVATION
                or type(self.folded) is not tuple
                or type(self.carries) is not tuple
                or type(self.signed_digits) is not tuple
            ):
                return False
            if self.index >= width_budget.bit_length():
                return False
            width = 1 << self.index
            if (
                width > width_budget
                or self.level >= terms.bit_length()
                or len(self.folded) != width
                or len(self.carries) != width + 1
                or len(self.signed_digits) != width
                or any(type(value) is not int for value in self.folded)
                or any(type(value) is not int for value in self.carries)
                or any(
                    type(value) is not int or value not in (-1, 0, 1)
                    for value in self.signed_digits
                )
            ):
                return False
            exponent = 1 << self.level
            if exponent + 1 > terms:
                return False
            expected = _fold_binomial_source(width, exponent, terms, bits_budget)
            if self.folded != expected:
                return False
            arena = SLPArena()
            root = arena.word(self.folded)
            carry_action = WideSignedCarryAction(
                arena,
                root,
                sign=-1,
                max_width=width_budget,
                max_weighted_bits=bits_budget,
            )
            return (
                carry_action.verify_cochain()
                and self.carries
                == tuple(carry_action.carry_at(i) for i in range(width + 1))
                and self.signed_digits
                == tuple(carry_action.digit_at(i) for i in range(width))
            )
        except (
            ArithmeticError,
            IndexError,
            OverflowError,
            SignedCarryBudgetExceeded,
            SourceCoefficientBudgetExceeded,
            TypeError,
            ValueError,
        ):
            return False

    def terminal_result(self, *, max_terms: int = MAX_FERMAT_SOURCE_TERMS) -> str:
        """Return PRIME only for this validation-only sufficient Pépin witness."""
        if not self.verify(max_terms=max_terms):
            raise ValueError("unauthenticated Fermat integral ideal witness")
        if not self.terminal:
            raise ValueError("only a terminal witness can establish primality")
        return (
            "PRIME"
            if self.signed_digits == (-1,) + (0,) * (self.width - 1)
            else "UNKNOWN"
        )

    def terminal_ideal_member(
        self, *, max_terms: int = MAX_FERMAT_SOURCE_TERMS
    ) -> bool:
        """Whether the authenticated source proves ``(1+z)^k+1`` in the ideal."""
        return self.terminal_result(max_terms=max_terms) == "PRIME"

    def integral_cochain(self) -> tuple[int, ...]:
        """Coefficients ``C_i=c_(i+1)`` of the checked integer cochain."""
        return self.carries[1:]

    def cyclotomic_radial_shadow(self, *, bits: int = 16) -> tuple[int, bool]:
        """Return only the radial valuation and nilpotence, never primality."""
        if type(bits) is not int or bits <= 0:
            raise ValueError(bits)
        transport = power_two_cyclotomic_transport(self.width, 0, self.exponent)
        return transport.scalar_v2, transport.annihilated(bits)


__all__ = [
    "DEFAULT_FERMAT_WEIGHTED_BITS",
    "MAX_FERMAT_SOURCE_TERMS",
    "MAX_FERMAT_SOURCE_WIDTH",
    "FermatIntegralIdealWitness",
    "SourceCoefficientBudgetExceeded",
]
