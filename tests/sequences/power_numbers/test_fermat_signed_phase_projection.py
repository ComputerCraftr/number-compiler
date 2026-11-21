"""Signed spatial joins preserve the complete canonical Fermat residue."""

from number_compiler.sequences.power_numbers.fermat_binary_pair_fold import (
    FermatBinaryFoldAction,
)


def test_signed_phase_projection_matches_literal_modulus() -> None:
    for width in range(1, 5):
        modulus = (1 << width) + 1
        for phase in range(2 * width):
            for low in range(modulus):
                for high in range(modulus):
                    first = FermatBinaryFoldAction(width, phase, low)
                    later = FermatBinaryFoldAction(width, 1, high)
                    result = first.then(later)
                    assert result.residue == (low + (1 << phase) * high) % modulus
                    assert result.length == phase + 1
