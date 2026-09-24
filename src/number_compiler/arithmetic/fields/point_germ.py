"""Extensional normal form of an affine binary point/blank consumer.

The function is blank for Y < blank_prefix and, afterwards, is the top bit
of (a*Y+c) mod 2**width. This is a *spatial high-fiber* function, not an
autonomous Collatz temporal state. Equality is exact for every Y >= 0.

After powers of two in a are removed, two odd-affine square waves agree iff
(a,c) agrees or is (-a, 2**(width-1)-1-c). The blank prefix remains independently
observable. This is a consumer normal form; it is never a source admission or
temporal action ID. No truth table is needed at construction time.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class AffinePointGerm:
    width: int
    multiplier: int
    offset: int
    blank_prefix: int

    def __post_init__(self) -> None:
        values = (self.width, self.multiplier, self.offset, self.blank_prefix)
        if any(type(x) is not int for x in values):
            raise TypeError("point germ parameters must be exact integers")
        if self.width < 0 or self.blank_prefix < 0:
            raise ValueError("negative point germ width or blank prefix")
        if self.width == 0:
            if self.multiplier or self.offset not in (0, 1):
                raise ValueError("noncanonical constant point germ")
            return
        modulus = 1 << self.width
        if not (
            0 < self.multiplier < modulus
            and self.multiplier & 1
            and 0 <= self.offset < modulus
        ):
            raise ValueError("point germ multiplier must be a normalized odd unit")
        reflected = (
            (-self.multiplier) % modulus,
            ((modulus >> 1) - 1 - self.offset) % modulus,
        )
        if (self.multiplier, self.offset) > reflected:
            raise ValueError("point germ must use its canonical reflection")

    @classmethod
    def normal_form(
        cls, width: int, multiplier: int, offset: int, blank_prefix: int
    ) -> AffinePointGerm:
        if any(type(x) is not int for x in (width, multiplier, offset, blank_prefix)):
            raise TypeError("point germ parameters must be exact integers")
        if width < 0 or blank_prefix < 0:
            raise ValueError("point germ width/blank prefix must be nonnegative")
        if width == 0:
            return cls(0, 0, offset & 1, blank_prefix)
        mask = (1 << width) - 1
        a, c = multiplier & mask, offset & mask
        if not a:
            return cls(0, 0, c >> (width - 1), blank_prefix)
        zeros = (a & -a).bit_length() - 1
        a >>= zeros
        c >>= zeros
        width -= zeros
        modulus = 1 << width
        reflected = ((-a) % modulus, ((modulus >> 1) - 1 - c) % modulus)
        a, c = min((a, c), reflected)
        return cls(width, a, c, blank_prefix)

    def at(self, high: int) -> int:
        if type(high) is not int or high < 0:
            raise ValueError("high-fiber input must be a nonnegative integer")
        if high < self.blank_prefix:
            return 2
        if not self.width:
            return self.offset
        low = high & ((1 << self.width) - 1)
        return ((self.multiplier * low + self.offset) >> (self.width - 1)) & 1

    def restrict_digit(self, digit: int, radix: int = 2) -> AffinePointGerm:
        """Exact residual under Y=digit+radix*Z; no time or path is stored."""
        if (
            type(radix) is not int
            or radix < 2
            or type(digit) is not int
            or not 0 <= digit < radix
        ):
            raise ValueError("invalid spatial digit restriction")
        return self.pullback(radix, digit)

    def pullback(self, multiplier: int, offset: int) -> AffinePointGerm:
        """Precompose a nonnegative affine spatial lens, not a time step.

        Includes the future-demand lenses 2Y, 2Y+1 and 6Y+3 without
        enumerating an alphabet or constructing a source-reading DFA.
        """
        if type(multiplier) is not int or multiplier <= 0:
            raise ValueError("spatial multiplier must be a positive integer")
        if type(offset) is not int or offset < 0:
            raise ValueError("spatial offset must be a nonnegative integer")
        cutoff = max(0, -((offset - self.blank_prefix) // multiplier))
        if not self.width:
            return self.normal_form(0, 0, self.offset, cutoff)
        mask = (1 << self.width) - 1
        return self.normal_form(
            self.width,
            self.multiplier * (multiplier & mask),
            self.multiplier * (offset & mask) + self.offset,
            cutoff,
        )

    @property
    def descriptor_bits(self) -> int:
        return sum(
            max(1, x.bit_length())
            for x in (
                self.width,
                self.multiplier,
                self.offset,
                self.blank_prefix,
            )
        )


__all__ = ["AffinePointGerm"]
