"""Literal decimal reference packet for independent mod-70 word checks."""

from __future__ import annotations


def literal_mod70_packet(word: str) -> dict[str, object]:
    lsd = tuple(map(int, reversed(word)))
    mask = tuple(int(digit >= 5) for digit in lsd)
    glyph = "".join(str(2 * int(digit)) for digit in word)
    reverse_glyph = "".join(str(2 * int(digit)) for digit in reversed(word))
    at_three = sum(digit * pow(3, i, 7) for i, digit in enumerate(lsd)) % 7
    at_five = sum(digit * pow(5, i, 7) for i, digit in enumerate(lsd)) % 7
    mask_three = sum(digit * pow(3, i, 7) for i, digit in enumerate(mask)) % 7
    mask_five = sum(digit * pow(5, i, 7) for i, digit in enumerate(mask)) % 7

    def coefficients(at3: int, at5: int) -> tuple[int, int]:
        c1 = 4 * (at5 - at3) % 7
        return (at3 - 3 * c1) % 7, c1

    return {
        "source_word_mod70": int(word or "0") % 70,
        "reversed_source_word_mod70": int(word[::-1] or "0") % 70,
        "threshold_mask_mod70": int("".join(map(str, reversed(mask))) or "0") % 70,
        "reversed_source_threshold_mask_mod70": int("".join(map(str, mask)) or "0")
        % 70,
        "digitwise_double_glyph_mod70": int(glyph or "0") % 70,
        "glyph_of_reversed_source_mod70": int(reverse_glyph or "0") % 70,
        "word_phi6_coefficients_mod7": list(coefficients(at_three, at_five)),
        "threshold_phi6_coefficients_mod7": list(coefficients(mask_three, mask_five)),
        "source_width_mod6": len(word) % 6,
        "threshold_count_mod6": sum(mask) % 6,
        "raw_glyph_length_mod6": len(glyph) % 6,
    }
