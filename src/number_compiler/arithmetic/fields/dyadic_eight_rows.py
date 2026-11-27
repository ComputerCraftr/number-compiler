"""Fixed exact alphabet for eight chronological one-column dyadic rows."""

from struct import Struct

from number_compiler.arithmetic.fields.ordered_matrix import (
    DYADIC_FOUR_ROW,
    Matrix2,
    MatrixEntries,
    fold_dyadic_leaf,
)


def _core_product(q: int) -> MatrixEntries:
    a, b, c, d = DYADIC_FOUR_ROW[q % 80]
    e, f, g, h = DYADIC_FOUR_ROW[q >> 4]
    return a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h


# Even eight maximal coefficients (all 10) give entries below 2**32.
_ROW = Struct("<4I")


def _build_alphabet() -> bytes:
    workspace = bytearray(640 * _ROW.size)
    for q in range(640):
        _ROW.pack_into(workspace, q * _ROW.size, *_core_product(q))
    return bytes(workspace)


_CORE = _build_alphabet()


def eight_row_interval(q: int, start: int = 0, stop: int = 8) -> Matrix2:
    """Return the ordered product of rows [start, stop) of an issued lift."""
    if not 0 <= start <= stop <= 8:
        raise ValueError("eight-row interval lies outside the issued band")
    normalized = q % 1280
    core = normalized % 640
    if start == stop:
        return Matrix2.identity()
    if start == 0 and stop == 8:
        a, b, c, d = _ROW.unpack_from(_CORE, core * _ROW.size)
        entries = (a, b, c, d)
    else:
        entries = fold_dyadic_leaf(core >> start, stop - start, 1, 10).entries
    if normalized < 640 or stop < 8:
        return Matrix2(entries)
    a, b, c, d = entries
    return Matrix2((a + 5 * b, b, c + 5 * d, d))
