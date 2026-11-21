"""Four-state inverse for the ordinary and XOR outputs of one operand pair."""

from __future__ import annotations


def recover_joint_operands(ordinary: int, xor: int) -> tuple[int, int]:
    """Recover ordered operands from ``x+y`` and ``x+(x xor y)``.

    Both outputs must describe the same finite operand pair. An unfinished
    outgoing carry or an inconsistent pair is rejected.
    """
    if type(ordinary) is not int or type(xor) is not int or ordinary < 0 or xor < 0:
        raise ValueError("joint outputs must be nonnegative exact integers")
    plus_carry = xor_carry = 0
    source = reflected = 0
    for bit in range(max(ordinary.bit_length(), xor.bit_length())):
        plus_bit = (ordinary >> bit) & 1
        xor_bit = (xor >> bit) & 1
        pair_xor = plus_bit ^ plus_carry
        reflected_bit = xor_bit ^ xor_carry
        source_bit = pair_xor ^ reflected_bit
        source |= source_bit << bit
        reflected |= reflected_bit << bit
        plus_carry = (source_bit & reflected_bit) | (pair_xor & plus_carry)
        xor_carry = (source_bit & pair_xor) | (reflected_bit & xor_carry)
    if plus_carry or xor_carry:
        raise ValueError("joint outputs leave an unfinished carry")
    if source + reflected != ordinary or source + (source ^ reflected) != xor:
        raise ValueError("joint outputs are not an exact operand pair")
    return source, reflected
