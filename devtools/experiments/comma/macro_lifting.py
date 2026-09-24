"""Check symbolic comma macro paths over an entire exponent residue ray.

This is proof-certificate development tooling, not production admission. Each
affine inequality is checked on x >= 10**p0, and each floor remainder is fixed
on p0 + 924*t by an exact modular identity. Isabelle refinement of this checker
and its generated finite instance remain separate release obligations.
"""

from __future__ import annotations

from math import gcd

from number_compiler.sequences.comma.arithmetic import decimal_sector
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    AffineWeight,
    BoundaryState,
    MacroTemplate,
)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(f"comma macro lifting: {message}")


def _positive(a: int, b: int, x0: int, *, strict: bool = True) -> bool:
    return a >= 0 and (a * x0 + b > 0 if strict else a * x0 + b >= 0)


def _sum(first: AffineWeight, second: AffineWeight, factor: int = 1) -> AffineWeight:
    return AffineWeight(
        first.numerator_scale * second.denominator
        + factor * second.numerator_scale * first.denominator,
        first.numerator_offset * second.denominator
        + factor * second.numerator_offset * first.denominator,
        first.denominator * second.denominator,
    )


def _sector(a: int, b: int, p0: int, x0: int) -> tuple[int, int, int]:
    sector = decimal_sector(a * x0 + b)
    delta = sector.exponent - p0
    _require(delta >= 0, "negative exponent transport")
    scale = 10**delta
    _require(
        _positive(a - sector.leading * scale, b, x0, strict=False)
        and _positive((sector.leading + 1) * scale - a, -b, x0),
        "sector bound does not lift",
    )
    return sector.leading, b % 10, delta


def _children(f: int, d: int, ha: int, hb: int, x0: int) -> tuple[int, ...]:
    """Return child increments only if their complete region lifts."""
    h0 = ha * x0 + hb
    if f < 9:
        seam = 10 * d + f + 1
        if h0 > seam:
            _require(_positive(ha, hb - seam, x0), "interior child guard")
            return (seam - 1,)
        if h0 == seam:
            _require(ha == 0 and hb == seam, "fork equality does not lift")
            return (seam - 1, seam)
        _require(_positive(-ha, seam - hb, x0), "crossing child guard")
        return (seam,)
    low, high = 10 * d + 1, 10 * d + 9
    if h0 > high:
        _require(_positive(ha, hb - high, x0), "nine-sector interior guard")
        return (high,)
    if h0 <= low:
        _require(_positive(-ha, low - hb, x0, strict=False), "power crossing guard")
        return (low,)
    _require(
        _positive(ha, hb - low, x0) and _positive(-ha, high - hb, x0, strict=False),
        "landmine guard does not lift",
    )
    return ()


def _cycle(f: int, d: int) -> tuple[int, int, int]:
    """Independent bounded definition, without the production safety fold."""
    period = 10 // gcd(f, 10)
    offset = guard = 0
    for _ in range(period):
        guard = max(guard, offset + 10 * d + min(f + 1, 9))
        offset += 10 * d + f
        d = (d + f) % 10
    return period, offset, guard


def check_macro_lifting(macro: MacroTemplate) -> int:
    """Reject a path unless every local arithmetic obligation lifts.

    Returns the number of checked fragments. This says nothing about which
    terminal fork child is infinite or about the global 314-state cycle.
    """
    p0 = macro.source.exponent_residue
    if p0 < 5:
        p0 += PERIOD
    x0 = 10**p0
    count = len(macro.sector_fragments)
    _require(
        len(macro.prefix_weights) == len(macro.prefix_displacements) == count + 1,
        "incomplete prefix index",
    )
    zero = AffineWeight(0, 0, 1)
    _require(
        macro.prefix_weights[0] == macro.prefix_displacements[0] == zero,
        "nonzero prefix origin",
    )
    a, b = macro.source.a, -int(macro.source.kind == "N")
    for index, fragment in enumerate(macro.sector_fragments):
        f, d, delta = _sector(a, b, p0, x0)
        _require((f, d) == (fragment.leading, fragment.entering_digit), "phase binding")
        ha, hb = (f + 1) * 10**delta - a, -b
        children = _children(f, d, ha, hb, x0)
        _require(len(children) == 1, "fragment continues past a fork or landmine")
        period, displacement, guard = _cycle(f, d)
        ma, mb = ha, hb - 1 - guard
        if fragment.period:
            _require(
                (fragment.period, fragment.displacement, fragment.maximum_guard)
                == (period, displacement, guard),
                "cycle transfer differs from phase arithmetic",
            )
            _require(
                fragment.literal_steps == fragment.literal_increment == 0,
                "mixed cycle and literal fragment",
            )
            _require(_positive(ma, mb, x0, strict=False), "cycle margin does not lift")
            _require(
                pow(10, p0 + PERIOD, displacement) == pow(10, p0, displacement),
                "floor remainder period",
            )
            remainder = (ma * x0 + mb) % displacement
            cycles = AffineWeight(ma, mb - remainder + displacement, displacement)
            _require(
                fragment.complete_cycles == cycles, "incorrect maximal cycle count"
            )
            next_weight = _sum(macro.prefix_weights[index], cycles, period)
            next_displacement = _sum(
                macro.prefix_displacements[index], cycles, displacement
            )
            # Multiplication by P cancels the exact floor denominator.
            a += ma
            b += mb - remainder + displacement
        else:
            _require(_positive(-ma, -mb, x0), "literal path skips an admitted cycle")
            _require(
                fragment.literal_steps == 1
                and fragment.literal_increment == children[0]
                and fragment.complete_cycles == zero
                and fragment.displacement == fragment.maximum_guard == 0,
                "incorrect literal seam fragment",
            )
            next_weight = _sum(macro.prefix_weights[index], AffineWeight(0, 1, 1))
            next_displacement = _sum(
                macro.prefix_displacements[index], AffineWeight(0, children[0], 1)
            )
            b += children[0]
        _require(
            macro.prefix_weights[index + 1] == next_weight
            and macro.prefix_displacements[index + 1] == next_displacement,
            "partial-selection prefix differs from complete action",
        )
    f, d, delta = _sector(a, b, p0, x0)
    children = _children(f, d, (f + 1) * 10**delta - a, -b, x0)
    _require(len(children) in (0, 2), "macro stops before a boundary event")
    _require(macro.exponent_delta == delta, "terminal exponent transport")
    _require(macro.endpoint == AffineWeight(a, b, 1), "terminal output")
    _require(macro.weight == macro.prefix_weights[-1], "terminal elapsed weight")
    if children:
        _require(
            macro.outcome == "fork" and macro.destination_a == f + 1, "fork output"
        )
        _require(
            a == (f + 1) * 10**delta and b + children[0] == -1 and b + children[1] == 0,
            "fork children not equal to N/Z constructors",
        )
        expected = (
            BoundaryState("N", f + 1, (p0 + delta) % PERIOD),
            BoundaryState("Z", f + 1, (p0 + delta) % PERIOD),
        )
        _require(
            macro.ordered_children == expected, "missing or reordered fork alternatives"
        )
    else:
        _require(
            macro.outcome == "landmine"
            and macro.destination_a is None
            and macro.ordered_children == (),
            "landmine has a successor",
        )
    return count
