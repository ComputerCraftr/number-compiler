"""Exact shared Walsh and cyclotomic projections of bounded Boolean words."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power

LOW_WALSH_WIDTH = 64


@dataclass(frozen=True, slots=True)
class WalshH5:
    """Six-phase F5=(Phi_2, Phi_3) of a low-to-high binary word.

    The length phase is retained, so composition applies the correct sign
    and cube-root shift to the second word.  It is not the full Walsh64 matrix.
    """

    length_mod6: int
    phi2: int
    phi3_a: int
    phi3_b: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.length_mod6, self.phi2, self.phi3_a, self.phi3_b)
        ):
            raise TypeError("H5 coordinates must be integers")
        if not 0 <= self.length_mod6 < 6 or any(
            not 0 <= value < 5 for value in (self.phi2, self.phi3_a, self.phi3_b)
        ):
            raise ValueError("H5 coordinates outside their fields")

    @staticmethod
    def empty() -> WalshH5:
        return WalshH5(0, 0, 0, 0)

    @classmethod
    def from_mask(cls, mask: int, width: int) -> WalshH5:
        if type(mask) is not int or type(width) is not int or width < 0:
            raise ValueError((mask, width))
        if mask < 0 or mask.bit_length() > width:
            raise ValueError("mask exceeds H5 word width")
        alternate = a = b = 0
        # Six-phase packet can be computed from sparse 1-bit positions.
        while mask:
            least = mask & -mask
            position = least.bit_length() - 1
            alternate += -1 if position & 1 else 1
            phase = position % 3
            if phase == 0:
                a += 1
            elif phase == 1:
                b += 1
            else:
                a -= 1
                b -= 1
            mask ^= least
        return cls(width % 6, alternate % 5, a % 5, b % 5)

    def then(self, upper: WalshH5) -> WalshH5:
        if type(upper) is not WalshH5:
            raise TypeError("H5 composition requires H5 actions")
        a, b = upper.phi3_a, upper.phi3_b
        for _ in range(self.length_mod6 % 3):
            a, b = -b, a - b
        signed = -upper.phi2 if self.length_mod6 & 1 else upper.phi2
        return WalshH5(
            (self.length_mod6 + upper.length_mod6) % 6,
            (self.phi2 + signed) % 5,
            (self.phi3_a + a) % 5,
            (self.phi3_b + b) % 5,
        )

    def repeat(self, copies: int) -> WalshH5:
        if type(copies) is not int or copies < 0:
            raise ValueError("H5 repeat count must be nonnegative")
        return binary_power(
            self, copies, identity=self.empty(), compose=WalshH5.then
        ).value


def walsh64(mask: int) -> tuple[int, ...]:
    if type(mask) is not int or not 0 <= mask < 1 << LOW_WALSH_WIDTH:
        raise ValueError("Walsh64 requires an exact 64-bit window")
    values = [(mask >> i) & 1 for i in range(64)]
    block = 1
    while block < 64:
        for start in range(0, 64, block * 2):
            for offset in range(block):
                left = values[start + offset]
                right = values[start + offset + block]
                values[start + offset] = left + right
                values[start + offset + block] = left - right
        block *= 2
    return tuple(values)


def walsh64_mod5(mask: int) -> tuple[int, ...]:
    """Project the shared integer transform to the invertible F5 transform."""
    return tuple(value % 5 for value in walsh64(mask))


def walsh64_signed(mask: int) -> tuple[int, ...]:
    """Transform the signed word ``1 - 2*bit`` using the common butterfly.

    The constant word contributes only to the zero-frequency coefficient.
    Input admission is identical to the Boolean-word transform.
    """
    return tuple(
        (LOW_WALSH_WIDTH if frequency == 0 else 0) - 2 * coefficient
        for frequency, coefficient in enumerate(walsh64(mask))
    )


def walsh_h5_at_offset(mask: int, width: int, offset: int) -> WalshH5:
    """Observe an H5 mask at an absolute bit offset, without its length phase."""
    if type(offset) is not int or offset < 0:
        raise ValueError("H5 offset must be a nonnegative exact integer")
    relative = WalshH5.from_mask(mask, width)
    shifted = WalshH5(offset % 6, 0, 0, 0).then(relative)
    return WalshH5(0, shifted.phi2, shifted.phi3_a, shifted.phi3_b)
