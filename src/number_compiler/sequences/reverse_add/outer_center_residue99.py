"""Conservative cyclotomic/exterior/center join for reverse/add.

At most 99 residues are stored, even for a source with millions of digits.
The source-conditioned global modulus comes from an authenticated Q19 SLP;
outer digit positions remain sets unless certified individually.  A Q19 pair
sum does not determine an even-width ordered exterior residue by itself.
No periodic source or inlet word is inferred from a modular coincidence.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .temporal_inward_constraints import ReverseInwardConstraints

_MASK99 = (1 << 99) - 1


def _rotate99(mask: int, shift: int) -> int:
    shift %= 99
    return ((mask << shift) | (mask >> (99 - shift))) & _MASK99 if shift else mask


def _outer_residues(system: ReverseInwardConstraints, t: int) -> int:
    """Over-approximate outside contributions while respecting Q19 pairs.

    All correlations not represented by the individual pair domains are
    conservatively forgotten: this filter may lose deductions, never invent
    a forced digit.  No full integer or digit string is constructed.
    """
    width = system.widths[t]
    stop = width // 2 if width % 2 else width // 2 - 1
    possible = 1  # residue zero
    powers = [pow(10, width - 1 - j, 99) for j in range(stop)]
    for i in range(stop):
        hi, lo = i, width - i - 1
        coefficient = powers[i]
        reverse_coefficient = pow(10, i, 99)
        pair_values = set(system.pair_domain(t, i))
        residues = {
            (a * coefficient + b * reverse_coefficient) % 99
            for a in system.digit_domain(t, hi)
            for b in system.digit_domain(t, lo)
            if a + b in pair_values
        }
        if not residues:
            from .temporal_inward_constraints import InconsistentReverseConstraints

            raise InconsistentReverseConstraints("outer symmetric pair has no source")
        next_possible = 0
        for r in residues:
            next_possible |= _rotate99(possible, r)
            if next_possible == _MASK99:
                break
        possible = next_possible
        if possible == _MASK99:
            break
    return possible


def constrain_center_from_outer_pairs(
    system: ReverseInwardConstraints,
    t: int,
    global_residue: int,
    exact_exterior: int | None = None,
) -> bool:
    """Enforce X = exterior + 10**s * center (mod 99).

    The exterior is a source-domain set unless a producer supplied its exact
    *ordered* residue.  The two-digit 00/99 ambiguity is retained until some
    independent pair/F5/physical-digit constraint separates it.
    """
    from .temporal_inward_constraints import InconsistentReverseConstraints

    width = system.widths[t]
    if exact_exterior is not None:
        possible = 1 << exact_exterior
    else:
        possible = _outer_residues(system, t)
    changed = False
    if width % 2:
        index = width // 2
        power = pow(10, index, 99)
        allowed = tuple(
            d
            for d in system.digit_domain(t, index)
            if possible & (1 << ((global_residue - d * power) % 99))
        )
        if not allowed:
            raise InconsistentReverseConstraints("outer/odd-center mod99 fiber empty")
        old = system.digit_domain(t, index)
        system.constrain_digit(t, index, allowed)
        return old != system.digit_domain(t, index)
    j = width // 2 - 1
    power = pow(10, j, 99)
    pair_domain = set(system.pair_domain(t, j))
    options = {
        (a, b)
        for a in system.digit_domain(t, j)
        for b in system.digit_domain(t, j + 1)
        if a + b in pair_domain
        and (possible & (1 << ((global_residue - (10 * a + b) * power) % 99)))
    }
    if not options:
        raise InconsistentReverseConstraints("outer/even-center mod99 fiber empty")
    for index, digits in (
        (j, {a for a, _ in options}),
        (j + 1, {b for _, b in options}),
    ):
        old = system.digit_domain(t, index)
        system.constrain_digit(t, index, tuple(sorted(digits)))
        changed |= old != system.digit_domain(t, index)
    old = system.pair_domain(t, j)
    system.constrain_pair(t, j, tuple(sorted({a + b for a, b in options})))
    changed |= old != system.pair_domain(t, j)
    return changed


__all__ = ["constrain_center_from_outer_pairs"]
