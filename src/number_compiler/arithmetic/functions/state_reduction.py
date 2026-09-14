"""Exact target/action state reductions shared by sequence families.

A *state reduction* in this module is admitted only when the represented
observation/action is exactly recoverable from the reduced object.  The module
keeps an explicit distinction between:

* local/action reductions, which may not determine their own next reduced
  state (reverse-add growth and one accelerated Collatz action); and
Bounded special-number carrier proofs live under ``devtools.proofs``; this module
contains only the two production local/action reductions that remain useful to
reverse-add and Collatz.

This prevents a compact projection coordinate from being silently promoted to
a semantic successor state without a closure theorem.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.fields.two_adic import v2_positive as v2
from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.sequences.collatz.pair import CollatzValuationProjectionBlock


@dataclass(frozen=True, slots=True)
class ReverseAddGrowthState:
    """Exact logarithmic-size observer for the *current* growth decision.

    For a symmetric pair field ``P`` in radix ``b``, ``b-1`` is the carry
    identity symbol.  Let ``r`` be the first position from the low edge where
    ``P[r] != b-1``.  Symmetry makes the final non-identity symbol the mirror
    of the same coefficient, hence the terminal carry (incoming carry zero) is
    one iff that coefficient is above ``b-1``.  If every coefficient is
    neutral the carry remains zero.

    ``boundary_offset`` is therefore a polynomial ``z``-adic valuation of
    ``P-(b-1)(1+z+...+z^(L-1))`` and ``boundary_relation`` is only its
    first nonzero coefficient sign; no carry row or coefficient magnitude is
    required for this target.
    The object is deliberately not given a successor method: it is an exact
    growth observer, not by itself a closed reverse-add state.
    """

    base: int
    width: int
    boundary_offset: int
    boundary_relation: int

    def __post_init__(self) -> None:
        base = int(self.base)
        width = int(self.width)
        offset = int(self.boundary_offset)
        relation = int(self.boundary_relation)
        if base < 2 or width <= 0 or not 0 <= offset <= width:
            raise ValueError(self)
        if relation not in (-1, 0, 1):
            raise ValueError(self)
        if offset == width:
            if relation != 0:
                raise ValueError("all-neutral boundary state must have relation zero")
        elif relation == 0:
            raise ValueError(self)
        object.__setattr__(self, "base", base)
        object.__setattr__(self, "width", width)
        object.__setattr__(self, "boundary_offset", offset)
        object.__setattr__(self, "boundary_relation", relation)

    @classmethod
    def from_summary(cls, summary: BlockSummary, *, base: int) -> ReverseAddGrowthState:
        """Project the already-canonical pair summary without scanning digits."""
        if summary.all_threshold:
            return cls(int(base), summary.length, summary.length, 0)
        if summary.first_reset is None or summary.first_reset_sign not in (-1, 1):
            raise ValueError(summary)
        return cls(
            int(base),
            summary.length,
            int(summary.first_reset),
            int(summary.first_reset_sign),
        )

    @classmethod
    def from_pair(cls, pair: Sequence[int], *, base: int) -> ReverseAddGrowthState:
        """Project the radial boundary order/sign without building carry state.

        Reverse-add pair fields are symmetric.  The first non-neutral symbol on
        the low half is therefore both the z-adic order of the threshold defect
        and the sign that decides growth.  Scan only until that boundary is
        found while validating symmetry; do not construct a reset/carry row.
        """
        values = tuple(map(int, pair))
        base = int(base)
        if not values or base < 2:
            raise ValueError((values, base))
        width = len(values)
        threshold = base - 1
        relation = 0
        offset = width
        for i in range((width + 1) // 2):
            left, right = values[i], values[width - 1 - i]
            if left != right or not (0 <= left <= 2 * threshold):
                raise ValueError((values, base))
            if relation == 0 and left != threshold:
                offset = i
                relation = 1 if left > threshold else -1
        return cls(base, width, offset, relation)

    @property
    def all_neutral(self) -> bool:
        return self.boundary_offset == self.width

    @property
    def growth(self) -> int:
        return int(self.boundary_relation > 0)

    @property
    def relation(self) -> int:
        return self.boundary_relation

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-add-growth-state",
            self.base,
            self.width,
            self.boundary_offset,
            self.boundary_relation,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.base)
            + bit_width(self.width)
            + bit_width(self.boundary_offset)
            + 2
        )


@dataclass(frozen=True, slots=True)
class CollatzValuationState:
    """Exact reduced description of one accelerated odd Collatz *action*.

    ``k=v2(3n+1)`` determines ``n -> (3n+1)/2^k``.  This object is used only
    when the exact accelerated action is required.  Cheaper observers must not
    acquire it first: strict growth is the modulo-four source character, while
    an order-m cyclotomic lane needs only ``k mod m`` (see
    :mod:`number_compiler.sequences.collatz.character`).

    Like :class:`ReverseAddGrowthState`, this is an action state rather than a
    closed orbit state: ``k_t`` alone does not determine ``k_(t+1)``.
    """

    valuation: int

    def __post_init__(self) -> None:
        value = int(self.valuation)
        if value <= 0:
            raise ValueError(value)
        object.__setattr__(self, "valuation", value)

    @classmethod
    def from_odd_value(cls, value: int) -> CollatzValuationState:
        value = int(value)
        if value <= 0 or not (value & 1):
            raise ValueError(value)
        return cls(v2(3 * value + 1))

    @property
    def increases(self) -> bool:
        # For positive odd n, k=1 gives (3n+1)/2 > n; k>=2 gives <=n.
        return self.valuation == 1

    @property
    def phase_symbol(self) -> int:
        return 1 if self.increases else 0

    def shift_phase(self, order: int) -> int:
        order = int(order)
        if order <= 0:
            raise ValueError(order)
        return self.valuation % order

    def apply(self, value: int) -> int:
        value = int(value)
        if value <= 0 or not (value & 1):
            raise ValueError(value)
        numerator = 3 * value + 1
        if v2(numerator) != self.valuation:
            raise ValueError("valuation state does not match source")
        return numerator >> self.valuation

    @property
    def projection(self) -> CollatzValuationProjectionBlock:
        return CollatzValuationProjectionBlock.symbol(self.valuation)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-valuation-state", self.valuation)

    @property
    def description_bits(self) -> int:
        return bit_width(self.valuation)


__all__ = [
    "CollatzValuationState",
    "ReverseAddGrowthState",
]
