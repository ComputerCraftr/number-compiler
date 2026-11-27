"""Fixed five- and six-column actions built from settled lower operators."""

from number_compiler.arithmetic.fields.ordered_matrix import MatrixEntries
from number_compiler.sequences.antihydra.mahler_cf_low_period import settled_low_action


def _prepend(digit: int, suffix: MatrixEntries) -> MatrixEntries:
    a, b, c, d = suffix
    coefficient = digit + 1
    return coefficient * a + c, coefficient * b + d, a, b


_FIVE_LEADING = (0, 1, 7, 9, 5, 6, 2, 4)
_SIX_LEADING = (0, 0, 3, 9, 7, 8, 1, 7, 5, 5, 8, 4, 2, 3, 6, 2)
_FIVE = tuple(
    _prepend(digit, settled_low_action(5 + phase, 4))
    for phase, digit in enumerate(_FIVE_LEADING)
)
_SIX = tuple(
    _prepend(digit, _FIVE[(phase + 1) % 8]) for phase, digit in enumerate(_SIX_LEADING)
)
ACTIONS = (_FIVE, _SIX)
