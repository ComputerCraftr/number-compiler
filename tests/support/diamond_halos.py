"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from array import array

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect


def suffix_parity() -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=2,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0, 1, 0, 0, 1, 0, 1, 1]),
        outputs=bytes([0, 1, 1, 0, 2, 2, 3, 3]),
        kernel_name="suffix-parity",
        storage_bytes=56,
        uncompressed_bytes=56,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
