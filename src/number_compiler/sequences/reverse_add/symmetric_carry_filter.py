"""Exact local filter for a symmetric reverse/add carry transfer.

Pair coefficients are ordered from the outside towards the center.  The
transfer is the first non-nine coefficient's carry map; if every pair is
nine, the center (or the even-width identity seam) determines it.  This is a
finite spatial constraint only and does not assert temporal repetition.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn


def _category(coefficient: int) -> CarryFn:
    return (
        CarryFn.CONST0
        if coefficient < 9
        else CarryFn.ID
        if coefficient == 9
        else CarryFn.CONST1
    )


@dataclass(frozen=True, slots=True)
class InwardCarryFilter:
    """Supported local values and all transfer maps admitted by the domains."""

    pairs: tuple[tuple[int, ...], ...]
    possible_transfers: tuple[CarryFn, ...]
    center: tuple[int, ...] | None
    supported_pairs: tuple[tuple[int, ...], ...]
    supported_center: tuple[int, ...] | None

    def requires(self, function: CarryFn) -> bool:
        if type(function) is not CarryFn:
            raise TypeError("a carry map is required")
        return function in self.possible_transfers


def _validate_domains(
    domains: tuple[tuple[int, ...], ...], center: tuple[int, ...] | None
) -> None:
    if type(domains) is not tuple or any(type(row) is not tuple for row in domains):
        raise TypeError("pair domains must be immutable tuples")
    if any(
        not row
        or any(type(value) is not int or not 0 <= value <= 18 for value in row)
        or tuple(sorted(set(row))) != row
        for row in domains
    ):
        raise ValueError("pair domains must be sorted nonempty Q19 sets")
    if center is not None and (
        type(center) is not tuple
        or not center
        or any(
            type(value) is not int or value not in range(0, 19, 2) for value in center
        )
        or tuple(sorted(set(center))) != center
    ):
        raise ValueError("center domain must be a sorted nonempty even Q19 set")


def filter_symmetric_transfer(
    domains: tuple[tuple[int, ...], ...],
    allowed: tuple[CarryFn, ...],
    *,
    center: tuple[int, ...] | None = None,
    on_value_visit: Callable[[], None] | None = None,
) -> InwardCarryFilter:
    """Retain values that have a complete local witness for an allowed map.

    The source domains are never treated as independent proof of a global
    number.  This function computes exact supports for this one symmetric
    carry factor, and the optional callback counts candidate values as they
    are inspected (including a failing call).
    """
    _validate_domains(domains, center)
    if (
        type(allowed) is not tuple
        or not allowed
        or any(type(function) is not CarryFn for function in allowed)
        or len(set(allowed)) != len(allowed)
    ):
        raise ValueError("allowed transfers must be a nonempty tuple of unique maps")
    if on_value_visit is not None and not callable(on_value_visit):
        raise TypeError("visit counter must be callable")

    wanted = set(allowed)
    suffix: list[set[CarryFn]] = [set() for _ in range(len(domains) + 1)]
    suffix[-1] = (
        {CarryFn.ID} if center is None else {_category(value) for value in center}
    )
    for index in range(len(domains) - 1, -1, -1):
        suffix[index] = {_category(value) for value in domains[index] if value != 9}
        if 9 in domains[index]:
            suffix[index].update(suffix[index + 1])

    prefix_maps: set[CarryFn] = set()
    prefix_can_eq = True
    supported_rows: list[tuple[int, ...]] = []
    for index, domain in enumerate(domains):
        retained: list[int] = []
        for coefficient in domain:
            if on_value_visit is not None:
                on_value_visit()
            feasible = bool(prefix_maps & wanted)
            if prefix_can_eq:
                if coefficient != 9:
                    feasible |= _category(coefficient) in wanted
                else:
                    feasible |= bool(suffix[index + 1] & wanted)
            if feasible:
                retained.append(coefficient)
        supported_rows.append(tuple(retained))
        if prefix_can_eq:
            prefix_maps.update(_category(value) for value in domain if value != 9)
            # Must remain true only if every earlier slot can choose EQ.
            prefix_can_eq = prefix_can_eq and 9 in domain

    supported_center: tuple[int, ...] | None = None
    if center is not None:
        retained_center: list[int] = []
        for coefficient in center:
            if on_value_visit is not None:
                on_value_visit()
            if prefix_maps & wanted or (
                prefix_can_eq and _category(coefficient) in wanted
            ):
                retained_center.append(coefficient)
        supported_center = tuple(retained_center)

    possible = tuple(function for function in CarryFn if function in suffix[0] & wanted)
    return InwardCarryFilter(
        domains,
        possible,
        center,
        tuple(supported_rows),
        supported_center,
    )


__all__ = ["InwardCarryFilter", "filter_symmetric_transfer"]
