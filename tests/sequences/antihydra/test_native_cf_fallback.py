"""The optional native terminal respects width and admission boundaries."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    append_decimal_value,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tile
from number_compiler.sequences.antihydra.mahler_continued_fraction_cylinder import (
    continued_fraction_cylinder,
)


def test_native_terminal_skips_unadmitted_widths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_CONTINUANT", "1")

    def reject() -> None:
        raise AssertionError("native import on a refused width")

    monkeypatch.setattr(tile, "_native_continuant", reject)
    for width in (1, 2, 3, 17, 18):
        value = 10 ** (width - 1) + 2 if width > 1 else 2
        result = tile.ReciprocalTile(value, (width,), 0, width)
        expected = Matrix2(append_decimal_value(value, 10 ** (width - 1), (1, 0, 0, 1)))
        assert result.product == expected


def test_native_terminal_skips_tight_ledger(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", "1")
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_CONTINUANT", "1")

    def reject() -> None:
        raise AssertionError("native import before source admission")

    monkeypatch.setattr(tile, "_native_continuant", reject)
    result = continued_fraction_cylinder(20, 64, ledger=ResourceLedger(max_nodes=512))
    assert result["status"] == "available"


def test_missing_native_extension_keeps_exact_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_CONTINUANT", "1")
    monkeypatch.setattr(tile, "_native_continuant", lambda: None)
    result = tile.ReciprocalTile(10005, (5,), 0, 5)
    assert result.product == Matrix2(append_decimal_value(10005, 10000, (1, 0, 0, 1)))
