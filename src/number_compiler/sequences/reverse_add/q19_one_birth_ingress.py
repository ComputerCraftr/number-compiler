"""Bounded all-inlet carry check for one authenticated decimal birth.

The input is a physical source digit word in either orientation; symmetric
pair sums are identical in both. A singleton result authorizes only the
inner carry after the first birth at the two-digit border cut. Production
use requires the explicit ``NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS=1``
opt-in; the Isabelle source-to-inlet bridge remains open.
"""

from __future__ import annotations

import os
from collections.abc import Callable
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

if TYPE_CHECKING:
    from .border_carry_safety import BorderTile
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


def first_birth_inner_carry(
    digits: tuple[int, ...], max_inspections: int
) -> tuple[int | None, int]:
    """Return a universal carry if both source and future inlets agree.

    The source is already authenticated by the caller. Unresolved and
    unadmitted cases return ``None`` and grant no temporal authority.
    """
    width = len(digits)
    if width < 8 or max_inspections < 1:
        return None, 0
    if digits[0] + digits[-1] != 17 or max_inspections < 3:
        return None, 1
    q = digits[1] + digits[-2]
    carry, inspected = _first_birth_at(
        width, digits.__getitem__, q, max_inspections - 2
    )
    return carry, inspected + 2


def _first_birth_at(
    width: int, digit: Callable[[int], int], q: int, max_inspections: int
) -> tuple[int | None, int]:
    carry = (q + 1) // 10
    prior = q % 10
    reset0 = reset1 = -1
    inspected = 0
    for i in range(2, width // 2 - 1):
        if inspected >= max_inspections:
            return None, inspected
        pair = digit(i) + digit(width - 1 - i)
        low = (pair + carry) % 10
        out0 = pair // 10
        out1 = (pair + 1) // 10
        old0, old1 = reset0, reset1
        r0 = old1 if out0 else old0
        r1 = old1 if out1 else old0
        v0 = low + (prior + out0) % 10
        v1 = low + (prior + out1) % 10
        reset0 = r0 if r0 >= 0 else -1 if v0 == 9 else int(v0 > 9)
        reset1 = r1 if r1 >= 0 else -1 if v1 == 9 else int(v1 > 9)
        inspected += 1
        if reset0 == reset1 and reset0 >= 0:
            return reset0, inspected
        carry = (pair + carry) // 10
        prior = pair % 10
    return None, inspected


def bound_first_birth_inlet(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    digits: tuple[int, ...] | None,
    border: BorderTile,
    horizon: int,
    remaining: int,
) -> tuple[int | None, int]:
    """Apply the bounded check to the receiving owner's physical source."""
    if os.environ.get("NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS") != "1":
        return None, 0
    if horizon < 2 or border.k != 2 or border.high // 10 + border.low % 10 != 17:
        return None, 0
    physical_width = len(digits) if digits is not None else source.output_width
    if physical_width < 8 or remaining < 1:
        return None, 0
    q = border.high % 10 + border.low // 10

    def digit(index: int) -> int:
        if digits is not None:
            return digits[index]
        return owner.digit(source, index)

    carry, visited = _first_birth_at(physical_width, digit, q, remaining)
    if visited:
        owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_BORDER_CONTROL_SOURCE_PAIR_INSPECTIONS,
            visited,
        )
    return carry, visited


def border_inlets(tick: int, initial: int, guarded: int | None) -> tuple[int, ...]:
    """Select only source-authorized carries at this physical boundary."""
    if tick == 0:
        return (initial,)
    return (guarded,) if tick == 1 and guarded is not None else (0, 1)


def forced_outer_pair(
    tiles: set[tuple[int, int]], width: int
) -> tuple[int, int] | None:
    """Read the outer physical pair only when every admitted tile agrees."""
    choices = {(high // (10 ** (width - 1)), low % 10) for high, low in tiles}
    return next(iter(choices)) if len(choices) == 1 else None
