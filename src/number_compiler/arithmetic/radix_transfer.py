"""Complete affine remainder transfers with bounded arithmetic payloads.

These are functions on one division port, not quotient words. Temporal powers
continue to use action references; the modulus never grows with their exponent.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger


def _multiply(left: int, right: int, modulus: int, ledger: ResourceLedger) -> int:
    """Multiply bounded residues without forming a double-width product."""
    if left.bit_length() + right.bit_length() <= 64:
        ledger.bump("radix_limb_operations")
        return ledger.observe_arithmetic(left * right) % modulus
    result = 0
    while right:
        if right & 1:
            result = ledger.observe_arithmetic(result + left) % modulus
            ledger.bump("radix_limb_operations")
        right >>= 1
        if right:
            left = ledger.observe_arithmetic(left + left) % modulus
            ledger.bump("radix_limb_operations")
    return result


@dataclass(frozen=True, slots=True)
class RadixRemainderTransfer:
    """Canonical function ``carry -> multiplier*carry + offset (mod radix)``."""

    radix: int
    multiplier: int
    offset: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.radix,
                self.multiplier,
                self.offset,
            )
        ):
            raise TypeError("radix transfer requires exact integer port values")
        if not 2 <= self.radix <= 1 << 63:
            raise ValueError("radix transfer modulus exceeds its bounded port")
        if not 0 <= self.multiplier < self.radix or not 0 <= self.offset < self.radix:
            raise ValueError("radix transfer coefficients must be reduced")

    @classmethod
    def leaf(cls, radix: int, symbol: int) -> RadixRemainderTransfer:
        if type(symbol) is not int or symbol not in (0, 1, 2):
            raise ValueError("division provider symbol must be binary or blank")
        # Blank padding has no numerical effect. A binary zero still doubles
        # the incoming remainder, including at the low end of a cell.
        return cls(radix, 1 if symbol == 2 else 2 % radix, 0 if symbol == 2 else symbol)

    def then(
        self,
        after: RadixRemainderTransfer,
        ledger: ResourceLedger,
    ) -> RadixRemainderTransfer:
        self.__post_init__()
        if type(after) is not RadixRemainderTransfer:
            raise TypeError("radix composition requires a remainder transfer")
        after.__post_init__()
        if self.radix != after.radix:
            raise ValueError("radix transfers have different port signatures")
        multiplier = _multiply(after.multiplier, self.multiplier, self.radix, ledger)
        transported = _multiply(after.multiplier, self.offset, self.radix, ledger)
        offset = ledger.observe_arithmetic(transported + after.offset) % self.radix
        ledger.bump("radix_limb_operations")
        ledger.bump("radix_recursive_transfer_evaluations")
        return RadixRemainderTransfer(self.radix, multiplier, offset)

    def apply(self, state: int, ledger: ResourceLedger) -> int:
        self.__post_init__()
        if type(state) is not int:
            raise TypeError("radix remainder must be an exact integer")
        if not 0 <= state < self.radix:
            raise ValueError("radix remainder lies outside its port")
        product = _multiply(self.multiplier, state, self.radix, ledger)
        ledger.bump("radix_limb_operations")
        return ledger.observe_arithmetic(product + self.offset) % self.radix


__all__ = ["RadixRemainderTransfer"]
