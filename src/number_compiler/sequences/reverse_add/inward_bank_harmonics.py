"""Source-owned inward carry forcing and five-band mask selection.

A spatial, one-physical-step relation; it is NOT an autonomous temporal clock.
The Q19 word is symmetric, but carries travel LSD -> MSD. At an inward
position i, the reflected carry b_i=c[w-1-i] is constrained by
b_(i-1)=K_(s_i)(b_i), and the nearest interior non-EQ reset fixes b_i.

The selection is deliberately *set valued* where neither the certified outer
port nor the bounded inward reset search determines b_i. Equal outputs may
still puncture this remaining carry uncertainty. No future Q19 occurrence is
queried and no mask is selected using observed future labels.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BANDS,
    DecimalPairBand,
    decimal_pair_band,
)


def pair_carry(s: int, incoming: int) -> int:
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("carry ingress must be Boolean")
    decimal_pair_band(s)
    return int(s > 9 or (s == 9 and incoming == 1))


def _require_domain(domain: tuple[int, ...]) -> tuple[int, ...]:
    if (
        type(domain) is not tuple
        or not domain
        or any(type(x) is not int or x not in (0, 1) for x in domain)
    ):
        raise ValueError("port domain must contain Boolean carry alternatives")
    return tuple(sorted(set(domain)))


@dataclass(frozen=True, slots=True)
class InwardBankSelection:
    """A proof-scoped set of all admissible next coefficient/band masks."""

    coordinate: int
    source_width: int
    growth: int
    source_coefficient: int
    source_band: DecimalPairBand
    low_carry: int
    reflected_carries: tuple[int, ...]
    reset_distance: int | None
    reset_side: str | None
    possible_coefficients: tuple[int, ...]
    possible_bands: tuple[DecimalPairBand, ...]
    possible_f5: tuple[int, ...]

    @property
    def forced_band(self) -> DecimalPairBand | None:
        return self.possible_bands[0] if len(self.possible_bands) == 1 else None

    @property
    def forced_coefficient(self) -> int | None:
        return (
            self.possible_coefficients[0]
            if len(self.possible_coefficients) == 1
            else None
        )

    @property
    def forced_masks(self) -> dict[DecimalPairBand, int | None]:
        """Mask values: 0/1 where forced, None only when carry still matters."""
        possible = set(self.possible_bands)
        return {
            band: (1 if possible == {band} else 0 if band not in possible else None)
            for band in DECIMAL_PAIR_BANDS
        }

    @property
    def reflected_xor_domain(self) -> tuple[int, ...]:
        return tuple(sorted({self.low_carry ^ c for c in self.reflected_carries}))


@dataclass(frozen=True, slots=True)
class InwardBankWindow:
    """A bounded, source-conditioned spatial window of next mask domains.

    The five masks share a single exact coefficient/carry source. Walsh is
    authorized only when all 64 Boolean lanes of the requested channel are
    individually forced; unknown ports are NEVER filled with zero.
    """

    start: int
    selections: tuple[InwardBankSelection, ...]

    def __post_init__(self) -> None:
        if (
            type(self.start) is not int
            or self.start < 0
            or not self.selections
            or len(self.selections) > 64
            or any(
                v.coordinate != self.start + i for i, v in enumerate(self.selections)
            )
        ):
            raise ValueError("unaligned or excessive inward bank window")

    def mask_domain(self, channel: DecimalPairBand) -> tuple[int | None, ...]:
        if type(channel) is not DecimalPairBand:
            raise ValueError("unsupported five-band channel")
        return tuple(v.forced_masks[channel] for v in self.selections)

    def must_may_masks(self, channel: DecimalPairBand) -> tuple[int, int]:
        """Two Boolean bitmasks enclosing every conditional completion."""
        row = self.mask_domain(channel)
        must = sum(1 << i for i, bit in enumerate(row) if bit == 1)
        may = sum(1 << i for i, bit in enumerate(row) if bit != 0)
        return must, may

    def walsh64_mod5(self, channel: DecimalPairBand) -> tuple[int, ...]:
        """An exact 64-lane Walsh output, never a guessed masked projection."""
        if len(self.selections) != 64:
            raise ValueError("Walsh64 requires exactly 64 selected positions")
        must, may = self.must_may_masks(channel)
        if must != may:
            raise ValueError("unresolved carry may change an output Walsh lane")
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        return walsh64_mod5(must)


def inward_bank_select(
    *,
    width: int,
    coordinate: int,
    growth: int,
    pair_at: Callable[[int], int],
    low_carry: int,
    high_border_carries: tuple[int, ...] = (0, 1),
    inward_lookahead: int = 4,
) -> InwardBankSelection:
    """Condition a next mask on bilateral border and first non-9 reset.

    ``coordinate`` is the final target pair index from the low edge. Growth
    creates coordinate zero as an external seam; all other coordinates use
    the shifted adjacent-pair rule. ``pair_at`` is an authenticated current
    Q19 source accessor, NEVER a future source or trained occurrence table.

    The high-border carry b0=c[w-1] passes inward through EQ=9; an interior
    LT/GT reset breaks the reverse inference. Independently, searching the
    next ``inward_lookahead`` source coefficients finds the first decisive
    reset for b_i, without scanning a physical carry tape.
    """
    if (
        type(width) is not int
        or width < 1
        or type(coordinate) is not int
        or type(growth) is not int
        or growth not in (0, 1)
        or not 0 <= coordinate < width + growth
        or type(inward_lookahead) is not int
        or inward_lookahead < 0
    ):
        raise ValueError("invalid width/position/growth/lookahead")
    if type(low_carry) is not int or low_carry not in (0, 1):
        raise ValueError("low carry must be Boolean")
    admitted = set(_require_domain(high_border_carries))
    if coordinate >= width // 2 and not (growth and coordinate == 0):
        # There is no general interior low-half formula at the moving center.
        # Handle it in the exact Q19 stencil rather than guessing reflection.
        raise ValueError("inward selector only covers protected low-half cells")
    old_i = coordinate
    s = pair_at(old_i if not (growth and coordinate == 0) else 0)
    decimal_pair_band(s)
    if growth and coordinate == 0:
        t = s + 1 - 10 * pair_carry(s, low_carry)
        return InwardBankSelection(
            coordinate,
            width,
            growth,
            s,
            decimal_pair_band(s),
            low_carry,
            tuple(sorted(admitted)),
            None,
            None,
            (t,),
            (decimal_pair_band(t),),
            (t % 5,),
        )
    if growth and coordinate < 1:
        raise AssertionError("growth border should already be handled")
    prior = pair_at(old_i - 1) if growth else None
    if prior is not None:
        decimal_pair_band(prior)

    # Inversion of b_(j-1)=K(s_j)(b_j) along the high-side EQ wire.
    # A non-EQ reset punctures b_j: its output is fixed, but its ingress is not.
    for j in range(1, old_i + 1):
        symbol = pair_at(j)
        if symbol == 9:
            continue
        required = int(symbol > 9)
        if required not in admitted:
            raise ValueError("high border ingress contradicts a Q19 reset")
        admitted = {0, 1}

    # A reset at i+d, d>0, fixes b_i. If the center is reached without a
    # reset in an even width, the EQ wire carries the known low-side c_(i+1).
    center = width // 2
    last = center if width % 2 else center - 1
    reset_distance: int | None = None
    reset_side: str | None = None
    steps_to_center = max(last - old_i, 0)
    for d in range(1, min(inward_lookahead, steps_to_center) + 1):
        symbol = pair_at(old_i + d)
        if symbol != 9:
            admitted.intersection_update({int(symbol > 9)})
            reset_distance = d
            reset_side = "GT" if symbol > 9 else "LT"
            break
    else:
        if inward_lookahead >= steps_to_center:
            # Even widths with no inner reset have an all-EQ middle: it
            # carries the *already known* low-side carry into its mirror.
            if width % 2 == 0:
                admitted.intersection_update({pair_carry(s, low_carry)})
                reset_side = "EQ-center"
            elif steps_to_center == 0:
                # At an odd-width center, this is not a protected cell.
                raise ValueError("center is not a reflected interior pair")
    if not admitted:
        raise ValueError("border and inward reset constraints are inconsistent")

    targets: set[int] = set()
    for b in admitted:
        low_out = pair_carry(s, low_carry)
        high_out = pair_carry(s, b)
        if growth:
            assert prior is not None
            high_after = pair_carry(prior, high_out)
            t = prior + s + low_carry + high_out - 10 * (low_out + high_after)
        else:
            t = 2 * s + low_carry + b - 10 * (low_out + high_out)
        decimal_pair_band(t)
        targets.add(t)
    target_coeffs = tuple(sorted(targets))
    target_bands = {decimal_pair_band(value) for value in targets}
    bands = tuple(band for band in DECIMAL_PAIR_BANDS if band in target_bands)
    return InwardBankSelection(
        coordinate,
        width,
        growth,
        s,
        decimal_pair_band(s),
        low_carry,
        tuple(sorted(admitted)),
        reset_distance,
        reset_side,
        target_coeffs,
        bands,
        tuple(sorted({v % 5 for v in targets})),
    )


__all__ = [
    "DECIMAL_PAIR_BANDS",
    "InwardBankSelection",
    "InwardBankWindow",
    "inward_bank_select",
    "pair_carry",
]
