"""Width-aware middle-carry port adapter for NC16's symmetric Q19 filter.

The canonical source coefficient word is palindromic. The first non-9
coefficient from the upper border determines the complete middle transfer;
all-EQ is possible only for even width. This adapter projects the existing
exact symmetric_carry_filter into the finite multi-time ring constraint engine
and retains exact first-reset/map witness pairs, without duplicating the exact
regular-language pruning algorithm.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn

from .symmetric_carry_filter import filter_symmetric_transfer

_MAPS = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)


@dataclass(frozen=True, slots=True)
class MiddleCarryWire:
    """Supported transfer maps and full inward coefficient domains."""

    outer_pairs: int
    pair_domains: tuple[tuple[int, ...], ...]
    transfers: tuple[CarryFn, ...]
    reset_witnesses: tuple[tuple[int, CarryFn], ...]
    possible_first_resets: tuple[int, ...]
    source_width: int

    def input_output(self, low_carry: int) -> tuple[int, ...]:
        if type(low_carry) is not int or low_carry not in (0, 1):
            raise ValueError("incoming carry must be Boolean")
        return tuple(
            sorted(
                {
                    low_carry if fn is CarryFn.ID else int(fn is CarryFn.CONST1)
                    for fn in self.transfers
                }
            )
        )


def _reset_transfer_witnesses(
    pair_domains: tuple[tuple[int, ...], ...],
    center: tuple[int, ...] | None,
    possible_transfers: tuple[CarryFn, ...],
) -> tuple[tuple[int, CarryFn], ...]:
    """Retain exact first-reset/map pairs for the local symmetric factor.

    A position is reachable with transfer ``fn`` exactly when every earlier
    pair can be EQ=9 and the selected coefficient at that position induces
    ``fn``. Later coefficients are unrestricted because the first non-9
    coefficient fixes the composed carry map. The even-width all-EQ seam is
    recorded separately as ``(-1, ID)``.
    """
    possible = set(possible_transfers)
    witnesses: list[tuple[int, CarryFn]] = []
    prefix_can_be_eq = True
    for index, domain in enumerate(pair_domains):
        if prefix_can_be_eq:
            for coefficient in domain:
                if coefficient == 9:
                    continue
                transfer = CarryFn.CONST0 if coefficient < 9 else CarryFn.CONST1
                if transfer in possible:
                    witnesses.append((index, transfer))
        prefix_can_be_eq = prefix_can_be_eq and 9 in domain

    if center is not None and prefix_can_be_eq:
        for coefficient in center:
            transfer = CarryFn.CONST0 if coefficient < 9 else CarryFn.CONST1
            if transfer in possible:
                witnesses.append((len(pair_domains), transfer))
    elif center is None and prefix_can_be_eq and CarryFn.ID in possible:
        witnesses.append((-1, CarryFn.ID))

    return tuple(
        sorted(
            set(witnesses),
            key=lambda item: (item[0] == -1, item[0], item[1].value),
        )
    )


def restrict_middle_carry_wire(
    source_width: int,
    outer_pairs: int,
    pair_domains: tuple[tuple[int, ...], ...],
    admitted: tuple[CarryFn, ...] = _MAPS,
    *,
    on_value_visit: Callable[[], None] | None = None,
) -> MiddleCarryWire:
    """Project an authenticated middle-transfer map over all pair domains.

    Index zero refers to the first symmetric pair immediately inward of the
    K-digit border. For odd width the final source coefficient is a center
    sum 2*d, never EQ=9; for even width the word has a genuine mirror.
    """
    if (
        type(source_width) is not int
        or type(outer_pairs) is not int
        or outer_pairs < 1
        or source_width < 2 * outer_pairs + 1
        or type(pair_domains) is not tuple
        or len(pair_domains) != (source_width + 1) // 2 - outer_pairs
        or any(
            type(domain) is not tuple
            or not domain
            or any(type(value) is not int or not 0 <= value <= 18 for value in domain)
            or tuple(sorted(set(domain))) != domain
            for domain in pair_domains
        )
        or not admitted
        or any(type(fn) is not CarryFn for fn in admitted)
    ):
        raise ValueError("invalid palindromic carry wire and border")
    center: tuple[int, ...] | None = None
    if source_width & 1:
        candidate_center = pair_domains[-1]
        if any(s not in range(0, 19, 2) for s in candidate_center):
            raise ValueError("odd center domain must contain only even coefficients")
        result = filter_symmetric_transfer(
            pair_domains[:-1],
            admitted,
            center=candidate_center,
            on_value_visit=on_value_visit,
        )
        center = result.supported_center
        if center is None:
            raise ValueError("odd center has no supported carry projection")
        projected = result.supported_pairs + (center,)
    else:
        result = filter_symmetric_transfer(
            pair_domains, admitted, on_value_visit=on_value_visit
        )
        projected = result.supported_pairs
    if not result.possible_transfers or any(not row for row in projected):
        raise ValueError("border carry map contradicts the entire inner bank")
    reset_witnesses = _reset_transfer_witnesses(
        pair_domains if center is None else pair_domains[:-1],
        center,
        result.possible_transfers,
    )
    first = tuple(dict.fromkeys(position for position, _ in reset_witnesses))
    if not reset_witnesses:
        raise ValueError("supported carry maps have no first-reset witness")
    return MiddleCarryWire(
        outer_pairs,
        projected,
        result.possible_transfers,
        reset_witnesses,
        first,
        source_width,
    )


__all__ = ["MiddleCarryWire", "restrict_middle_carry_wire"]
