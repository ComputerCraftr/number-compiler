"""The radix-64 raw carry/output quotient and its separate value potential.

The 17 classes observe the current carry action and, for each incoming carry,
the outgoing carry and raw output action. They are not successor classes after
a residual shift. The within-class offset stays on the exact value wire.
"""

from __future__ import annotations

from bisect import bisect_right

from number_compiler.arithmetic.carry.collatz_carry_wires import (
    collatz_digit_carry_action,
    collatz_dyadic_carry_partition,
    compose_collatz_carry_actions,
)

# Algebraic threshold cuts, not a source-dependent learned partition.
RAW_CLASS_STARTS = (0, 7, 8, 14, 15, 21, 22, 28, 29, 35, 36, 42, 43, 49, 50, 56, 57)
CORRECTIONS = (-128, -127, -126, -64, -63, -62, 0, 1, 2)
# Fixed primitive theorem tables, compiled once from the canonical wire law.
# Neither table depends on a source, temporal program, or observed register.
_CLASS_CARRIES = tuple(collatz_digit_carry_action(d, base=64) for d in RAW_CLASS_STARTS)
_DYADIC_CARRY_PARTITIONS = tuple(
    collatz_dyadic_carry_partition(bits) for bits in range(7)
)
DOMAIN_ACTIONS, _DIGIT_DOMAINS = _DYADIC_CARRY_PARTITIONS[6]
RADIX64_FREE_CARRY_ACTIONS = tuple(
    dict.fromkeys(
        action for actions, _classes in _DYADIC_CARRY_PARTITIONS for action in actions
    )
)


def _bounded(value: int, count: int, name: str) -> None:
    if type(value) is not int:
        raise TypeError(f"{name} requires an exact integer")
    if not 0 <= value < count:
        raise ValueError(f"{name} is outside its finite domain")


def radix64_domain(digit: int) -> int:
    """Index of the existing five nonempty two-wire carry actions."""
    _bounded(digit, 64, "radix-64 digit")
    return _DIGIT_DOMAINS[digit]


def radix64_raw_class(digit: int) -> int:
    _bounded(digit, 64, "radix-64 digit")
    return bisect_right(RAW_CLASS_STARTS, digit) - 1


def radix64_value_potential(digit: int) -> int:
    """The source offset; raw output adds three times this bounded register."""
    return digit - RAW_CLASS_STARTS[radix64_raw_class(digit)]


def radix64_split(digit: int) -> tuple[int, int]:
    """Classify once when both control and value potential are consumed."""
    kind = radix64_raw_class(digit)
    return kind, digit - RAW_CLASS_STARTS[kind]


def radix64_raw_emit(raw_class: int, potential: int, carry: int) -> tuple[int, int]:
    """Return (outgoing carry, exact raw digit) without refining the class."""
    _bounded(raw_class, 17, "raw output class")
    _bounded(carry, 3, "multiplication carry")
    start = RAW_CLASS_STARTS[raw_class]
    stop = RAW_CLASS_STARTS[raw_class + 1] if raw_class < 16 else 64
    _bounded(potential, stop - start, "within-class value potential")
    outgoing = _CLASS_CARRIES[raw_class][carry]
    representative = 3 * start + carry - 64 * outgoing
    return outgoing, representative + 3 * potential


def radix64_geometry_emit(digit: int, carry: int) -> tuple[int, int]:
    """Derive carry from five-way geometry, then expose its exact value view."""
    _bounded(digit, 64, "radix-64 digit")
    _bounded(carry, 3, "multiplication carry")
    outgoing = DOMAIN_ACTIONS[radix64_domain(digit)][carry]
    return outgoing, (3 * digit + carry) % 64


def radix64_correction(carry: int, outgoing: int) -> int:
    _bounded(carry, 3, "multiplication carry")
    _bounded(outgoing, 3, "multiplication carry")
    return carry - 64 * outgoing


def radix64_shift(raw: int, next_raw: int, shift: int) -> int:
    """Exact two-cell bit wiring, including the identity shift."""
    quotient, _ = radix64_shift_views(raw, shift)
    _, remainder = radix64_shift_views(next_raw, shift)
    return radix64_join_shift_views(quotient, remainder, shift)


def radix64_shift_views(raw: int, shift: int) -> tuple[int, int]:
    """Return the two directional value views consumed at a shift seam."""
    _bounded(raw, 64, "raw output digit")
    _bounded(shift, 6, "residual shift")
    return raw >> shift, raw % (1 << shift)


def radix64_join_shift_views(quotient: int, adjacent_remainder: int, shift: int) -> int:
    """Reconstruct one exact target digit from adjacent directional views."""
    _bounded(shift, 6, "residual shift")
    _bounded(quotient, 64 >> shift, "directional quotient")
    _bounded(adjacent_remainder, 1 << shift, "adjacent directional remainder")
    return quotient + (adjacent_remainder << (6 - shift))


def radix64_growth_edge(carry: int, shift: int) -> int:
    """Zero means no extra cell; every nonzero edge is LT (digit 1 or 2)."""
    _bounded(carry, 3, "terminal carry")
    _bounded(shift, 6, "residual shift")
    return carry >> shift


def _directional_domain_tables() -> tuple[
    tuple[tuple[int, ...], ...],
    tuple[tuple[int, ...], ...],
    tuple[tuple[tuple[int, ...], ...], ...],
]:
    """Compile the six exact one-sided domain quotients once."""
    left_classes = []
    right_classes = []
    pairings = []
    for shift in range(6):
        left_actions, left = _DYADIC_CARRY_PARTITIONS[6 - shift]
        right_actions, right = _DYADIC_CARRY_PARTITIONS[shift]
        if left != tuple(sorted(left)) or right != tuple(sorted(right)):
            raise AssertionError("directional domain quotient is not a staircase")
        left_classes.append(left)
        right_classes.append(right)
        pairings.append(
            tuple(
                tuple(
                    DOMAIN_ACTIONS.index(compose_collatz_carry_actions(right, left))
                    for right in right_actions
                )
                for left in left_actions
            )
        )
    return tuple(left_classes), tuple(right_classes), tuple(pairings)


(
    RADIX64_LEFT_VIEW_CLASSES,
    RADIX64_RIGHT_VIEW_CLASSES,
    RADIX64_DIRECTIONAL_DOMAIN_TABLES,
) = _directional_domain_tables()

RADIX64_DIRECTIONAL_DOMAIN_COUNTS = tuple(
    (len(table), len(table[0]))
    for shift, table in enumerate(RADIX64_DIRECTIONAL_DOMAIN_TABLES)
)
RADIX64_DIRECTIONAL_VALUE_COUNTS = tuple(
    left * right for left, right in RADIX64_DIRECTIONAL_DOMAIN_COUNTS
)


def radix64_left_domain_view(raw: int, shift: int) -> int:
    """Classify the left value view without retaining its exact digit."""
    quotient, _ = radix64_shift_views(raw, shift)
    return RADIX64_LEFT_VIEW_CLASSES[shift][quotient]


def radix64_right_domain_view(raw: int, shift: int) -> int:
    """Classify the right value view without retaining its exact digit."""
    _, remainder = radix64_shift_views(raw, shift)
    return RADIX64_RIGHT_VIEW_CLASSES[shift][remainder]


def radix64_free_directional_actions(raw: int, shift: int) -> tuple[int, int]:
    """Global action IDs for an unbound future left/right consumer.

    The phase-specific domain classes remain smaller. These eight-way IDs are
    used only while ``shift`` is still a free root-query result.
    """
    quotient, remainder = radix64_shift_views(raw, shift)
    left_actions, left_classes = _DYADIC_CARRY_PARTITIONS[6 - shift]
    right_actions, right_classes = _DYADIC_CARRY_PARTITIONS[shift]
    return (
        RADIX64_FREE_CARRY_ACTIONS.index(left_actions[left_classes[quotient]]),
        RADIX64_FREE_CARRY_ACTIONS.index(right_actions[right_classes[remainder]]),
    )


def radix64_free_directional_row(shift: int, carry: int) -> tuple[tuple[int, int], ...]:
    """Build one demanded primitive row without retaining all free contexts."""
    _bounded(shift, 6, "residual shift")
    _bounded(carry, 3, "multiplication carry")
    return tuple(
        radix64_free_directional_actions((3 * digit + carry) % 64, shift)
        for digit in range(64)
    )


RADIX64_FREE_GROWTH_TABLE = tuple(
    tuple(radix64_growth_edge(carry, shift) for carry in range(3)) for shift in range(6)
)


def radix64_domain_from_directional_views(left: int, right: int, shift: int) -> int:
    """Pair independently reduced adjacent streams into the next domain."""
    _bounded(shift, 6, "residual shift")
    left_count, right_count = RADIX64_DIRECTIONAL_DOMAIN_COUNTS[shift]
    _bounded(left, left_count, "left domain view")
    _bounded(right, right_count, "right domain view")
    return RADIX64_DIRECTIONAL_DOMAIN_TABLES[shift][left][right]
