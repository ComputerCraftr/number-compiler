"""Composable positional Pascal moments for finite words.

The record is a spatial word summary only.  Its marker stream is supplied by
the caller, and its formal powers do not certify that a sequence source
repeats the represented word or marker program.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.fields.morphism_core import binary_power


def _binomial_mod11(n: int, k: int) -> int:
    """Evaluate ``choose(n, k)`` in F11 with bounded Lucas digits."""
    if k < 0 or k > n:
        return 0
    result = 1
    while k:
        high_digit, low_digit = n % 11, k % 11
        if low_digit > high_digit:
            return 0
        # Each exact binomial call is bounded by ten; the source width never
        # becomes a large intermediate coefficient.
        result = result * comb(high_digit, low_digit) % 11
        n //= 11
        k //= 11
    return result


def pascal_cyclotomic_repeat_period(order: int) -> int:
    """Universal spatial moment period for F11 and Pascal order K."""
    if type(order) is not int or order < 0:
        raise ValueError("Pascal order must be nonnegative")
    frobenius = 1
    while frobenius <= order:
        frobenius *= 11
    return 22 * frobenius


@dataclass(frozen=True, slots=True)
class PascalWordMoments:
    """Digit and Boolean-marker binomial moments modulo ``modulus``.

    For either component ``x`` the coordinate at order ``r`` is
    ``sum_i (-1)**i * binom(i, r) * x_i``.  Exact length is retained as part
    of the structural word carrier; callers must establish any shorter phase
    quotient they use separately.
    """

    length: int
    modulus: int
    digit_moments: tuple[int, ...]
    marker_moments: tuple[int, ...]
    first_marker: int | None
    last_marker: int | None

    def __post_init__(self) -> None:
        if type(self.length) is not int or self.length < 0:
            raise ValueError("Pascal word length must be nonnegative")
        if type(self.modulus) is not int or self.modulus < 2:
            raise ValueError("Pascal coefficient modulus must exceed one")
        if (
            type(self.digit_moments) is not tuple
            or type(self.marker_moments) is not tuple
            or not self.digit_moments
            or len(self.digit_moments) > 33
            or len(self.digit_moments) != len(self.marker_moments)
            or any(
                type(value) is not int or not 0 <= value < self.modulus
                for value in self.digit_moments + self.marker_moments
            )
        ):
            raise ValueError("Pascal moment vectors must be normalized and aligned")
        if any(self.digit_moments[self.length :] + self.marker_moments[self.length :]):
            raise ValueError("Pascal orders outside the finite word must be zero")
        if self.length == 0:
            if (
                self.first_marker is not None
                or self.last_marker is not None
                or any(self.digit_moments + self.marker_moments)
            ):
                raise ValueError("empty Pascal word must have zero moments")
        elif (
            type(self.first_marker) is not int
            or self.first_marker not in (0, 1)
            or type(self.last_marker) is not int
            or self.last_marker not in (0, 1)
        ):
            raise ValueError("nonempty Pascal word needs Boolean endpoint markers")
        elif self.length == 1 and (
            self.first_marker != self.last_marker
            or self.marker_moments[0] != self.first_marker
        ):
            raise ValueError("a one-symbol Pascal word has one marker")

    @property
    def order(self) -> int:
        return len(self.digit_moments) - 1

    @property
    def cyclotomic_repeat_period(self) -> int | None:
        """Proved spatial period of both moment rows when coefficients are F11.

        This describes the source-free moment quotient. It is not a physical
        repetition claim, and exact word length and endpoint markers remain
        attached to every powered result.
        """
        return (
            pascal_cyclotomic_repeat_period(self.order) if self.modulus == 11 else None
        )

    @classmethod
    def empty(cls, order: int, modulus: int) -> PascalWordMoments:
        _validate_parameters(order, modulus)
        zero = (0,) * (order + 1)
        return cls(0, modulus, zero, zero, None, None)

    @classmethod
    def symbol(
        cls, value: int, marker: int, *, order: int, modulus: int
    ) -> PascalWordMoments:
        _validate_parameters(order, modulus)
        if type(value) is not int:
            raise TypeError("Pascal word symbols must be exact integers")
        if type(marker) is not int or marker not in (0, 1):
            raise ValueError("Pascal marker must be a Boolean integer")
        zero = (0,) * order
        return cls(
            1,
            modulus,
            (value % modulus,) + zero,
            (marker,) + zero,
            marker,
            marker,
        )

    def then(self, later: PascalWordMoments) -> PascalWordMoments:
        """Concatenate with the exact Vandermonde translation law."""
        if (
            type(later) is not PascalWordMoments
            or later.order != self.order
            or later.modulus != self.modulus
        ):
            raise ValueError("Pascal word join needs matching order and modulus")
        if self.length == 0:
            return later
        if later.length == 0:
            return self
        sign = -1 if self.length & 1 else 1

        def joined(first: tuple[int, ...], second: tuple[int, ...]) -> tuple[int, ...]:
            choose = _binomial_mod11 if self.modulus == 11 else comb
            return tuple(
                (
                    first[degree]
                    + sign
                    * sum(
                        choose(self.length, degree - right_degree)
                        * second[right_degree]
                        for right_degree in range(degree + 1)
                    )
                )
                % self.modulus
                for degree in range(self.order + 1)
            )

        return PascalWordMoments(
            self.length + later.length,
            self.modulus,
            joined(self.digit_moments, later.digit_moments),
            joined(self.marker_moments, later.marker_moments),
            self.first_marker,
            later.last_marker,
        )

    def reflected(self) -> PascalWordMoments:
        """Return moments for the reversed finite word."""
        if self.length == 0:
            return self
        last_index = self.length - 1

        def reflected_moments(values: tuple[int, ...]) -> tuple[int, ...]:
            choose = _binomial_mod11 if self.modulus == 11 else comb
            return tuple(
                (
                    (-1 if last_index & 1 else 1)
                    * sum(
                        (-1 if source_degree & 1 else 1)
                        * choose(last_index - source_degree, degree - source_degree)
                        * values[source_degree]
                        for source_degree in range(min(degree, last_index) + 1)
                    )
                )
                % self.modulus
                for degree in range(self.order + 1)
            )

        return PascalWordMoments(
            self.length,
            self.modulus,
            reflected_moments(self.digit_moments),
            reflected_moments(self.marker_moments),
            self.last_marker,
            self.first_marker,
        )

    def power(self, count: int) -> PascalWordMoments:
        """Repeat this spatial word, reducing only the F11 moment quotient.

        For modulus 11, Lucas/Frobenius gives a universal repeat period for
        these two moment rows. The exact represented length and first/last
        markers are restored from the requested count. Other moduli retain
        the exact binary-composition path.
        """
        if type(count) is not int or count < 0:
            raise ValueError("Pascal word repeat count must be nonnegative")
        if count == 0 or self.length == 0:
            return self.empty(self.order, self.modulus)
        if self.modulus == 11:
            reduced_count = count % pascal_cyclotomic_repeat_period(self.order)
            powered = binary_power(
                self,
                reduced_count,
                identity=self.empty(self.order, self.modulus),
                compose=PascalWordMoments.then,
            ).value
            return PascalWordMoments(
                self.length * count,
                self.modulus,
                powered.digit_moments,
                powered.marker_moments,
                self.first_marker,
                self.last_marker,
            )
        return binary_power(
            self,
            count,
            identity=self.empty(self.order, self.modulus),
            compose=PascalWordMoments.then,
        ).value


def _validate_parameters(order: int, modulus: int) -> None:
    if type(order) is not int or not 0 <= order <= 32:
        raise ValueError("Pascal moment order is outside the supported bound")
    if type(modulus) is not int or modulus < 2:
        raise ValueError("Pascal coefficient modulus must exceed one")


__all__ = ["PascalWordMoments", "pascal_cyclotomic_repeat_period"]
