"""Exact width/mod-9/mod-99 birth clocks for the standard 2rev10 cylinder.

An exact four-phase width clock and mod-9/mod-99 action supply a genuine
infinite boundary *clock*.  The inlet for the next inward digit is NOT
inferred from that clock: the input word is projected from one authenticated
(K+1)-pair source action, with all two-sided carry constraints intact.

Digit-layer induction and its separate source-conditional lasso are handled
by temporal_birth_ring, with moving physical border coordinates.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import lcm
from typing import TYPE_CHECKING

from .temporal_ports import decimal_carry_port

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource


# Match the common query index allowance.  Clock powering is cheap, but a
# public caller must not pass an unbounded Python integer into it.
MAX_BIRTH_DURATION_BITS = 1_000_000


def _validate_birth_duration(physical_steps: int) -> int:
    if type(physical_steps) is not int or physical_steps < 0:
        raise ValueError("physical duration must be a nonnegative integer")
    if physical_steps.bit_length() > MAX_BIRTH_DURATION_BITS:
        raise ValueError("physical duration exceeds the query bit budget")
    return physical_steps


@dataclass(frozen=True, slots=True)
class CertifiedBirthClock:
    """Exact width/residue arithmetic derived from a source cursor.

    The value is an arithmetic model, not a source-authority token. A clock
    embedded in a source packet is protected by that packet's source seal;
    constructing this dataclass alone cannot issue digit or future authority.
    """

    phase: int
    width: int
    residue9: int
    residue99: int
    mod9_period: int
    width_mod9_period: int
    width_mod99_period: int
    births_per_mod9_period: tuple[int, int]
    births_per_mod99_period: tuple[int, int]

    def state(self, physical_steps: int) -> tuple[int, int, int]:
        """Phase, width, and mod-99 residue, without intermediate integers."""
        physical_steps = _validate_birth_duration(physical_steps)
        phase = self.phase
        width = self.width
        residue = self.residue99
        for _ in range(physical_steps % 4):
            residue = (2 * (10 if width % 2 == 0 else 1) * residue) % 99
            width += int(phase in (0, 3))
            phase = (phase + 1) % 4
        blocks = physical_steps // 4
        # Every certified four-phase block adds two digits, and the exact
        # residue multiplier is 160, irrespective of its entry phase.
        residue = residue * pow(160, blocks, 99) % 99
        width += 2 * blocks
        return phase, width, residue


def birth_clock_for_source(source: PointedBankSource) -> CertifiedBirthClock:
    """Derive the exact width/modular clocks from an owner-issued cursor."""
    source.validate(require_issued_cursor=True)
    if source.phase not in (0, 1, 2, 3):
        raise ValueError("birth clock requires a standard four-phase source")
    arena = source.arena
    root = source.root
    fold = decimal_carry_port(arena, root, modulus=99, max_bits=64)
    if fold.width != source.width_in:
        raise AssertionError("birth clock source width and authority disagree")
    residue = fold.forward
    r9 = residue % 9
    order9 = next(t for t in range(1, 7) if (r9 * pow(2, t, 9)) % 9 == r9)
    period9 = lcm(4, order9)
    current = (source.phase, source.width_in % 2, residue)
    phase, parity, mod99 = current
    period99 = 0
    while True:
        mod99 = 2 * (10 if parity == 0 else 1) * mod99 % 99
        parity = (parity + int(phase in (0, 3))) % 2
        phase = (phase + 1) % 4
        period99 += 1
        if (phase, parity, mod99) == current:
            break
        if period99 > 792:
            raise AssertionError("mod-99 clock exceeded its finite state bound")
    if period99 % 4:
        raise AssertionError("width/residue return lost its border phase")
    return CertifiedBirthClock(
        source.phase,
        source.width_in,
        r9,
        residue,
        order9,
        period9,
        period99,
        (period9 // 4, period9 // 4),
        (period99 // 4, period99 // 4),
    )


__all__ = [
    "MAX_BIRTH_DURATION_BITS",
    "CertifiedBirthClock",
    "birth_clock_for_source",
]
