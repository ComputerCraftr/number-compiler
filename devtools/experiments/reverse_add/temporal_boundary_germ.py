"""Bounded audit of the proposed three-cell decimal temporal boundary germ.

This is a research observer over *supplied* powered blocks.  It never grants
semantic cache identity or constructs a future source in production.  A finite
absence of collisions is not a successor-closure theorem.  A collision across
different occurrences refutes a key-only transition table, but does not refute
an action that also consumes its authenticated recursive occurrence.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import asdict, dataclass
import json
from typing import Final

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_pair_carry_action,
    decimal_q95_coordinates,
)

from devtools.experiments.reverse_add.powered_f5f2_carrier import (
    PairOrbitRow,
    cocycle_word,
    powered_block,
    reverse_add_pair_orbit,
)

# Blank is a boundary marker, not a twentieth pair symbol.  In particular it
# must not be passed to decimal_q95_coordinates or the physical carry law.
BLANK: Final[int] = 95
HALO: Final[int] = 3


@dataclass(frozen=True, slots=True)
class BoundaryGerm3:
    """Both physical ends, ordered outermost to innermost in each chart."""

    low: tuple[int, int, int]
    high: tuple[int, int, int]

    def __post_init__(self) -> None:
        for edge in (self.low, self.high):
            if type(edge) is not tuple or len(edge) != HALO:
                raise ValueError("each boundary edge requires exactly three cells")
            blank_seen = False
            for cell in edge:
                if type(cell) is not int or not 0 <= cell <= BLANK:
                    raise ValueError("boundary cell must be Q95 or the distinct blank")
                if cell == BLANK:
                    blank_seen = True
                elif blank_seen:
                    raise ValueError("blank padding must follow all real edge cells")
        if self.low.count(BLANK) != self.high.count(BLANK):
            raise ValueError("both boundary charts must have the same extent")

    def reflected(self) -> BoundaryGerm3:
        """Exchange coordinate charts, without reversing physical carry."""
        return BoundaryGerm3(self.high, self.low)


def boundary_germ(word: tuple[int, ...]) -> BoundaryGerm3:
    """Extract the coupled Q95 halo; absent cells receive a distinct marker."""
    if not word or any(type(cell) is not int or not 0 <= cell < BLANK for cell in word):
        raise ValueError("word must contain one or more exact Q95 cells")
    low = (
        word[0],
        word[1] if len(word) > 1 else BLANK,
        word[2] if len(word) > 2 else BLANK,
    )
    high = (
        word[-1],
        word[-2] if len(word) > 1 else BLANK,
        word[-3] if len(word) > 2 else BLANK,
    )
    return BoundaryGerm3(low, high)


def local_carry_digit(q95: int, incoming: int) -> tuple[int, int, CarryFn]:
    """The exact local LSD-to-MSD action, including equality at pair sum 9."""
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be a bit")
    pair, _forcing = decimal_q95_coordinates(q95)
    action = decimal_pair_carry_action(pair)
    outgoing = incoming if action is CarryFn.ID else int(action is CarryFn.CONST1)
    return ((pair + incoming) % 10, outgoing, action)


def reflected_pair_symbol(symbol: int) -> int:
    """The symbol-only 18-S involution; no F5 forcing transport is implied."""
    if type(symbol) is not int or not 0 <= symbol <= 18:
        raise ValueError("decimal pair symbol must lie in 0..18")
    return 18 - symbol


@dataclass(frozen=True, slots=True)
class GermWitness:
    first_start: int
    second_start: int
    half_steps: int
    key: tuple[int, int, BoundaryGerm3]
    first_successor: tuple[int, int, BoundaryGerm3]
    second_successor: tuple[int, int, BoundaryGerm3]


@dataclass(frozen=True, slots=True)
class GermAudit:
    half_steps: int
    checked: int
    repeated_keys: int
    singleton_keys: int
    clock_conflicts: tuple[GermWitness, ...]
    germ_conflicts: tuple[GermWitness, ...]
    different_complete_words: int


def audit_supplied_orbit(
    orbit: tuple[PairOrbitRow, ...], half_steps: int, starts: range
) -> GermAudit:
    """Compare actual D_h boundary keys with actual D_2h continuations.

    This reference necessarily uses a supplied orbit and full Q95 words.  It
    measures whether the key alone predicts the doubled boundary.  The exact
    occurrence remains a separate input to any complete transformer.
    """
    if type(half_steps) is not int or half_steps < 1:
        raise ValueError("half_steps must be positive")
    classes: dict[
        tuple[int, int, BoundaryGerm3],
        list[tuple[int, tuple[int, int, BoundaryGerm3], tuple[int, ...]]],
    ] = defaultdict(list)
    for start in starts:
        if start < 0 or start + 2 * half_steps >= len(orbit):
            raise IndexError((start, half_steps, len(orbit)))
        left = powered_block(orbit, start, half_steps)
        doubled = powered_block(orbit, start, 2 * half_steps)
        # The reduced Q95 local alphabet has a checked F2 admission boundary.
        if left.no_growths < 1 or doubled.no_growths < 1:
            continue
        current_word = cocycle_word(left)
        future_word = cocycle_word(doubled)
        key = (left.no_growths % 4, left.growths, boundary_germ(current_word))
        successor = (
            doubled.no_growths % 4,
            doubled.growths,
            boundary_germ(future_word),
        )
        classes[key].append((start, successor, future_word))

    clocks: list[GermWitness] = []
    germs: list[GermWitness] = []
    differing_words = 0
    for key, members in classes.items():
        first_start, first_successor, first_word = members[0]
        for start, successor, word in members[1:]:
            if word != first_word:
                differing_words += 1
            if successor != first_successor:
                witness = GermWitness(
                    first_start, start, half_steps, key, first_successor, successor
                )
                germs.append(witness)
                if successor[:2] != first_successor[:2]:
                    clocks.append(witness)
    return GermAudit(
        half_steps,
        sum(map(len, classes.values())),
        sum(len(members) > 1 for members in classes.values()),
        sum(len(members) == 1 for members in classes.values()),
        tuple(clocks),
        tuple(germs),
        differing_words,
    )


def main() -> None:
    """Emit the complete bounded seed-196 audit as one reproducible JSON value."""
    orbit = reverse_add_pair_orbit(196, 256)
    audits = [
        asdict(audit_supplied_orbit(orbit, half_steps, range(257 - 2 * half_steps)))
        for half_steps in (4, 8, 16, 32, 64)
    ]
    print(
        json.dumps(
            {"seed": 196, "last_orbit_index": 256, "audits": audits}, sort_keys=True
        )
    )


if __name__ == "__main__":
    main()
