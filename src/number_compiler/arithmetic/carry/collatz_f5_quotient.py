"""Exact finite directional consumers of the Collatz carry/F5 projection.

Fifteen joint leaf classes occur, but they do not close under the Hensel
neighbor action. For a fixed residual shift, equal rows/columns of the exact
64-cell join law give the minimal separate directional response classes.
These are consumer quotients, not source occurrences or temporal identities.
Import this optional observer only on demand.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.collatz_binary_forcing import radix64_phi5
from number_compiler.arithmetic.carry.collatz_carry_wires import (
    compose_collatz_carry_actions,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    DOMAIN_ACTIONS,
    radix64_domain,
    radix64_join_shift_views,
    radix64_shift_views,
)

RADIX64_F5_PARTS = tuple((radix64_domain(d), radix64_phi5(d)) for d in range(64))
RADIX64_F5_CLASSES = tuple(dict.fromkeys(RADIX64_F5_PARTS))
RADIX64_F5_DIGIT_CLASSES = tuple(
    RADIX64_F5_CLASSES.index(parts) for parts in RADIX64_F5_PARTS
)


@dataclass(frozen=True, slots=True, order=True)
class CollatzF5SpatialAction:
    """Nonempty spatial carry action and additive phase observer.

    The phase sums leaf phi5 values; it is not the full word's binary jet.
    Spatial concatenation does not supply the temporal Hensel successor law.
    The empty carry identity is deliberately outside this five-action sort.
    """

    carry_action: int
    phase: int

    def __post_init__(self) -> None:
        if type(self.carry_action) is not int or type(self.phase) is not int:
            raise TypeError("spatial F5 actions require exact finite coordinates")
        if not 0 <= self.carry_action < 5 or not 0 <= self.phase < 5:
            raise ValueError("spatial F5 action outside its finite domain")

    def then(self, higher: CollatzF5SpatialAction) -> CollatzF5SpatialAction:
        """Concatenate in physical LSD-to-MSD carry order."""
        if type(higher) is not CollatzF5SpatialAction:
            raise TypeError("spatial F5 actions compose with their own sort")
        self.__post_init__()
        higher.__post_init__()
        carry = compose_collatz_carry_actions(
            DOMAIN_ACTIONS[higher.carry_action], DOMAIN_ACTIONS[self.carry_action]
        )
        return CollatzF5SpatialAction(
            DOMAIN_ACTIONS.index(carry), (self.phase + higher.phase) % 5
        )

    def repeat(self, count: int) -> CollatzF5SpatialAction:
        """Repeat a supplied nonempty spatial action without language expansion.

        Each of the five carry maps is idempotent; only the additive phase
        changes. Count zero needs the separate empty-interval identity. This
        rule does not repeat a temporal source occurrence or its emissions.
        """
        self.__post_init__()
        if type(count) is not int or count <= 0:
            raise ValueError("spatial repetition requires a positive exact count")
        return CollatzF5SpatialAction(self.carry_action, self.phase * (count % 5) % 5)


RADIX64_F5_SPATIAL_LEAVES = tuple(
    CollatzF5SpatialAction(*parts) for parts in RADIX64_F5_PARTS
)

F5_SPATIAL_LEAF_ALPHABET = frozenset(RADIX64_F5_SPATIAL_LEAVES)
_CONSTANT_F5_MACROS = frozenset(
    CollatzF5SpatialAction(carry, phase)
    for carry, action in enumerate(DOMAIN_ACTIONS)
    for phase in range(5)
    if len(set(action)) == 1
)
# Nonconstant words consist entirely of one boundary digit. Their phase is
# transported by the known spatial extent, not an inferred temporal history.
_BOUNDARY_LEAVES = frozenset(
    action
    for action in F5_SPATIAL_LEAF_ALPHABET
    if len(set(DOMAIN_ACTIONS[action.carry_action])) != 1
)
_F5_ALPHABETS_BY_LENGTH_PHASE = tuple(
    _CONSTANT_F5_MACROS
    | frozenset(
        CollatzF5SpatialAction(action.carry_action, action.phase * phase % 5)
        for action in _BOUNDARY_LEAVES
    )
    for phase in range(5)
)
F5_SPATIAL_MACRO_ALPHABET = _F5_ALPHABETS_BY_LENGTH_PHASE[0]


def spatial_action_alphabet(length: int) -> frozenset[CollatzF5SpatialAction]:
    """Exact alphabet for a supplied nonempty radix-64 interval length.

    Lengths >=2 have 17 effects, with a boundary phase depending on length
    modulo five. The radix-five macro alphabet is the phase-zero case. These
    are spatial rule effects, never exact reachable temporal occurrences.
    """
    if type(length) is not int or length <= 0:
        raise ValueError("spatial alphabet requires a positive exact length")
    return (
        F5_SPATIAL_LEAF_ALPHABET
        if length == 1
        else _F5_ALPHABETS_BY_LENGTH_PHASE[length % 5]
    )


def radix64_f5_class(digit: int) -> int:
    radix64_domain(digit)  # The canonical strict finite-domain validator.
    return RADIX64_F5_DIGIT_CLASSES[digit]


def _partition(rows: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    unique = tuple(dict.fromkeys(rows))
    return tuple(unique.index(row) for row in rows)


def _directional_tables() -> tuple[
    tuple[tuple[int, ...], ...],
    tuple[tuple[int, ...], ...],
    tuple[tuple[tuple[int, ...], ...], ...],
]:
    left: list[tuple[int, ...]] = []
    right: list[tuple[int, ...]] = []
    tables: list[tuple[tuple[int, ...], ...]] = []
    for shift in range(6):
        rows = tuple(
            tuple(
                radix64_f5_class(radix64_join_shift_views(q, r, shift))
                for r in range(1 << shift)
            )
            for q in range(64 >> shift)
        )
        columns = tuple(zip(*rows, strict=True))
        lclasses, rclasses = _partition(rows), _partition(columns)
        lrepresentatives = tuple(lclasses.index(i) for i in range(max(lclasses) + 1))
        rrepresentatives = tuple(rclasses.index(i) for i in range(max(rclasses) + 1))
        left.append(lclasses)
        right.append(rclasses)
        tables.append(
            tuple(tuple(rows[q][r] for r in rrepresentatives) for q in lrepresentatives)
        )
    return tuple(left), tuple(right), tuple(tables)


F5_LEFT_CLASSES, F5_RIGHT_CLASSES, F5_JOIN_TABLES = _directional_tables()
F5_DIRECTIONAL_COUNTS = tuple((len(rows), len(rows[0])) for rows in F5_JOIN_TABLES)


def radix64_f5_directional_views(raw: int, shift: int) -> tuple[int, int]:
    quotient, remainder = radix64_shift_views(raw, shift)
    return F5_LEFT_CLASSES[shift][quotient], F5_RIGHT_CLASSES[shift][remainder]


def radix64_pair_f5_views(left: int, right: int, shift: int) -> int:
    radix64_shift_views(0, shift)
    lsize, rsize = F5_DIRECTIONAL_COUNTS[shift]
    if type(left) is not int or type(right) is not int:
        raise TypeError("F5 directional ports require exact integers")
    if not 0 <= left < lsize or not 0 <= right < rsize:
        raise ValueError("F5 directional port outside its admitted shift domain")
    return F5_JOIN_TABLES[shift][left][right]
