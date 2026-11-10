"""Finite decimal word summaries for oriented mod-70 and Phi6 projections.

The summary composes in word order, reflects source digits, and powers a
repeated word without expanding it. It carries no source or orbit authority.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
    crt_mod70_from_residues,
    phi6_coefficients_from_root_values_mod7,
)


@dataclass(frozen=True, slots=True)
class DecimalMod70WordSummary:
    """One finite decimal word's oriented Phi6, mask, and raw-glyph data.

    The field called ``glyph_of_reversed_source_mod7`` means applying the
    digitwise ``d -> str(2*d)`` morphism after reversing source digits.  It
    does not reverse the characters inside each two-character glyph.
    """

    length: int
    threshold_count_mod6: int
    word_mod7: int
    reversed_source_word_mod7: int
    threshold_mask_mod7: int
    reversed_source_mask_mod7: int
    digitwise_glyph_mod7: int
    glyph_of_reversed_source_mod7: int
    prefix_digits: tuple[int, ...]
    suffix_digits: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.length) is not int or self.length < 0:
            raise ValueError("mod-70 word length must be nonnegative")
        if (
            type(self.threshold_count_mod6) is not int
            or not 0 <= self.threshold_count_mod6 < 6
        ):
            raise ValueError("threshold count must be normalized modulo six")
        for value in (
            self.word_mod7,
            self.reversed_source_word_mod7,
            self.threshold_mask_mod7,
            self.reversed_source_mask_mod7,
            self.digitwise_glyph_mod7,
            self.glyph_of_reversed_source_mod7,
        ):
            if type(value) is not int or not 0 <= value < 7:
                raise ValueError("word projection must be normalized modulo seven")
        if (
            type(self.prefix_digits) is not tuple
            or type(self.suffix_digits) is not tuple
        ):
            raise TypeError("word boundary ports must be immutable tuples")
        boundary_width = min(2, self.length)
        if (
            len(self.prefix_digits) != boundary_width
            or len(self.suffix_digits) != boundary_width
        ):
            raise ValueError("word boundary ports do not match the finite width")
        if any(
            type(digit) is not int or not 0 <= digit <= 9
            for digit in self.prefix_digits + self.suffix_digits
        ):
            raise ValueError("word boundary ports must be decimal digits")
        if self.length == 0 and (
            self.threshold_count_mod6
            or any(
                (
                    self.word_mod7,
                    self.reversed_source_word_mod7,
                    self.threshold_mask_mod7,
                    self.reversed_source_mask_mod7,
                    self.digitwise_glyph_mod7,
                    self.glyph_of_reversed_source_mod7,
                )
            )
        ):
            raise ValueError("empty word projection must be the identity")

    @classmethod
    def identity(cls) -> DecimalMod70WordSummary:
        return cls(0, 0, 0, 0, 0, 0, 0, 0, (), ())

    @classmethod
    def digit(cls, value: int) -> DecimalMod70WordSummary:
        if type(value) is not int or not 0 <= value <= 9:
            raise ValueError("mod-70 source words contain decimal digits")
        threshold = int(value >= 5)
        glyph = 2 * value
        residue = value % 7
        return cls(
            1,
            threshold,
            residue,
            residue,
            threshold,
            threshold,
            glyph % 7,
            glyph % 7,
            (value,),
            (value,),
        )

    @property
    def glyph_length_mod6(self) -> int:
        return (self.length + self.threshold_count_mod6) % 6

    @property
    def word_mod70(self) -> int:
        units = 0 if not self.length else self.suffix_digits[-1]
        return crt_mod70_from_residues(self.word_mod7, units)

    @property
    def reversed_source_word_mod70(self) -> int:
        units = 0 if not self.length else self.prefix_digits[0]
        return crt_mod70_from_residues(self.reversed_source_word_mod7, units)

    @property
    def threshold_mask_mod70(self) -> int:
        units = int(bool(self.length) and self.suffix_digits[-1] >= 5)
        return crt_mod70_from_residues(self.threshold_mask_mod7, units)

    @property
    def reversed_source_mask_mod70(self) -> int:
        units = int(bool(self.length) and self.prefix_digits[0] >= 5)
        return crt_mod70_from_residues(self.reversed_source_mask_mod7, units)

    @property
    def digitwise_glyph_mod70(self) -> int:
        units = 0 if not self.length else (2 * self.suffix_digits[-1]) % 10
        return crt_mod70_from_residues(self.digitwise_glyph_mod7, units)

    @property
    def glyph_of_reversed_source_mod70(self) -> int:
        units = 0 if not self.length else (2 * self.prefix_digits[0]) % 10
        return crt_mod70_from_residues(self.glyph_of_reversed_source_mod7, units)

    @property
    def word_phi6_coefficients_mod7(self) -> tuple[int, int]:
        at_five = (
            self.reversed_source_word_mod7 * pow(5, max(0, self.length - 1) % 6, 7) % 7
        )
        return phi6_coefficients_from_root_values_mod7(self.word_mod7, at_five)

    @property
    def threshold_phi6_coefficients_mod7(self) -> tuple[int, int]:
        at_five = (
            self.reversed_source_mask_mod7 * pow(5, max(0, self.length - 1) % 6, 7) % 7
        )
        return phi6_coefficients_from_root_values_mod7(
            self.threshold_mask_mod7, at_five
        )

    def then(self, later: DecimalMod70WordSummary) -> DecimalMod70WordSummary:
        if type(later) is not DecimalMod70WordSummary:
            raise TypeError("mod-70 word composition requires another summary")
        if self.length == 0:
            return later
        if later.length == 0:
            return self
        source_phase = pow(3, later.length % 6, 7)
        reverse_phase = pow(3, self.length % 6, 7)
        glyph_phase = pow(3, later.glyph_length_mod6, 7)
        reverse_glyph_phase = pow(3, self.glyph_length_mod6, 7)
        return DecimalMod70WordSummary(
            self.length + later.length,
            (self.threshold_count_mod6 + later.threshold_count_mod6) % 6,
            (self.word_mod7 * source_phase + later.word_mod7) % 7,
            (
                later.reversed_source_word_mod7 * reverse_phase
                + self.reversed_source_word_mod7
            )
            % 7,
            (self.threshold_mask_mod7 * source_phase + later.threshold_mask_mod7) % 7,
            (
                later.reversed_source_mask_mod7 * reverse_phase
                + self.reversed_source_mask_mod7
            )
            % 7,
            (self.digitwise_glyph_mod7 * glyph_phase + later.digitwise_glyph_mod7) % 7,
            (
                later.glyph_of_reversed_source_mod7 * reverse_glyph_phase
                + self.glyph_of_reversed_source_mod7
            )
            % 7,
            (self.prefix_digits + later.prefix_digits)[:2],
            (self.suffix_digits + later.suffix_digits)[-2:],
        )

    def reflected(self) -> DecimalMod70WordSummary:
        return DecimalMod70WordSummary(
            self.length,
            self.threshold_count_mod6,
            self.reversed_source_word_mod7,
            self.word_mod7,
            self.reversed_source_mask_mod7,
            self.threshold_mask_mod7,
            self.glyph_of_reversed_source_mod7,
            self.digitwise_glyph_mod7,
            tuple(reversed(self.suffix_digits)),
            tuple(reversed(self.prefix_digits)),
        )

    def power(self, count: int) -> DecimalMod70WordSummary:
        if type(count) is not int or count < 0:
            raise ValueError("mod-70 spatial repeat count must be nonnegative")
        return binary_power(
            self,
            count,
            identity=DecimalMod70WordSummary.identity(),
            compose=DecimalMod70WordSummary.then,
        ).value

    def packet(self) -> dict[str, object]:
        return {
            "source_word_mod70": self.word_mod70,
            "reversed_source_word_mod70": self.reversed_source_word_mod70,
            "threshold_mask_mod70": self.threshold_mask_mod70,
            "reversed_source_threshold_mask_mod70": self.reversed_source_mask_mod70,
            "digitwise_double_glyph_mod70": self.digitwise_glyph_mod70,
            "glyph_of_reversed_source_mod70": self.glyph_of_reversed_source_mod70,
            "word_phi6_coefficients_mod7": list(self.word_phi6_coefficients_mod7),
            "threshold_phi6_coefficients_mod7": list(
                self.threshold_phi6_coefficients_mod7
            ),
            "source_width_mod6": self.length % 6,
            "threshold_count_mod6": self.threshold_count_mod6,
            "raw_glyph_length_mod6": self.glyph_length_mod6,
        }
