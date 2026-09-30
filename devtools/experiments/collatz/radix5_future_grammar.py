"""Radix-5 structural grammar for the Collatz carry x F5 carrier.

This experiment deliberately separates three layers:

* exact radix-64 digit occurrences, bound at centered coordinates ``x``;
* a finite local action ``(carry_action, phi5)``;
* radix-5 structural region nodes, whose literal identities may grow while the
  arithmetic rule catalog remains fixed.

The local action is an observer/action quotient, not by itself a proof of
Collatz temporal successor closure.  It is intended to compose with the Hensel
cylinder pullback owner rather than replace exact endpoint occurrences.
"""

from __future__ import annotations

from dataclasses import dataclass
from random import Random
from statistics import mean

from number_compiler.arithmetic.carry.collatz_f5_quotient import (
    RADIX64_F5_SPATIAL_LEAVES as LEAF_BY_DIGIT,
)
from number_compiler.arithmetic.carry.collatz_f5_quotient import (
    CollatzF5SpatialAction as CollatzF5Carrier,
)
from number_compiler.arithmetic.carry.collatz_f5_quotient import (
    spatial_action_alphabet as exact_length_states,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    DOMAIN_ACTIONS,
    radix64_domain,
)
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.arithmetic.fields.two_adic import v2_positive

LEAF_STATES = frozenset(LEAF_BY_DIGIT)


def compose_carrier(
    lower: CollatzF5Carrier, higher: CollatzF5Carrier
) -> CollatzF5Carrier:
    """Compose spatially as ``lower || higher`` (LSD toward MSD)."""
    return lower.then(higher)


def carrier_from_digits(digits: tuple[int, ...]) -> CollatzF5Carrier:
    if not digits:
        raise ValueError("carrier word must be nonempty")
    for digit in digits:
        radix64_domain(digit)
    result = LEAF_BY_DIGIT[digits[0]]
    for digit in digits[1:]:
        result = compose_carrier(result, LEAF_BY_DIGIT[digit])
    return result


@dataclass(slots=True)
class _RegionInterner:
    keys: dict[tuple[int, ...], int]

    def __init__(self) -> None:
        self.keys = {}

    def intern(self, key: tuple[int, ...]) -> tuple[int, bool]:
        found = self.keys.get(key)
        if found is not None:
            return found, False
        node_id = len(self.keys)
        self.keys[key] = node_id
        return node_id, True


@dataclass(frozen=True, slots=True)
class RegionOccurrence:
    level: int
    size: int
    start: int
    center_x: int
    node_id: int
    action: CollatzF5Carrier


def _region_level(
    child_ids: list[int],
    child_actions: list[CollatzF5Carrier],
    *,
    level: int,
    child_size: int,
    width: int,
    interner: _RegionInterner,
) -> tuple[list[int], list[CollatzF5Carrier], list[RegionOccurrence], int]:
    out_ids: list[int] = []
    out_actions: list[CollatzF5Carrier] = []
    rows: list[RegionOccurrence] = []
    new_nodes = 0
    usable = (len(child_ids) // 5) * 5
    region_size = child_size * 5
    for child_start in range(0, usable, 5):
        key = tuple(child_ids[child_start : child_start + 5])
        node_id, created = interner.intern(key)
        new_nodes += int(created)
        action = child_actions[child_start]
        for higher in child_actions[child_start + 1 : child_start + 5]:
            action = compose_carrier(action, higher)
        start = child_start * child_size
        # x = 2*i-(width-1); the center cell of an odd-sized region is exact.
        center_x = 2 * start + region_size - width
        out_ids.append(node_id)
        out_actions.append(action)
        rows.append(
            RegionOccurrence(level, region_size, start, center_x, node_id, action)
        )
    return out_ids, out_actions, rows, new_nodes


def region_occurrences(
    digits: tuple[int, ...],
    interners: tuple[_RegionInterner, _RegionInterner, _RegionInterner],
) -> tuple[tuple[RegionOccurrence, ...], tuple[int, int, int]]:
    """Build aligned 5/25/125-cell structural occurrences for one exact word."""
    for digit in digits:
        radix64_domain(digit)
    width = len(digits)
    leaf_ids = list(digits)  # exact leaf occurrence alphabet is radix-64 itself
    leaf_actions = [LEAF_BY_DIGIT[digit] for digit in digits]
    all_rows: list[RegionOccurrence] = []
    new_counts: list[int] = []
    child_ids, child_actions = leaf_ids, leaf_actions
    child_size = 1
    for level, interner in enumerate(interners, start=1):
        child_ids, child_actions, rows, new_nodes = _region_level(
            child_ids,
            child_actions,
            level=level,
            child_size=child_size,
            width=width,
            interner=interner,
        )
        all_rows.extend(rows)
        new_counts.append(new_nodes)
        child_size *= 5
    return tuple(all_rows), (new_counts[0], new_counts[1], new_counts[2])


def _accelerated(value: int) -> int:
    raw = 3 * value + 1
    return raw >> v2_positive(raw)


def _source_corpus(*, count: int, width: int, seed: int = 196) -> tuple[int, ...]:
    if type(count) is not int or type(width) is not int or count < 1 or width < 1:
        raise ValueError("positive corpus count and width required")
    rng = Random(seed)
    values: list[int] = []
    for _ in range(count):
        digits = [rng.randrange(64) for _ in range(width)]
        digits[0] |= 1
        if digits[-1] == 0:
            digits[-1] = 1 + rng.randrange(63)
        values.append(value_from_lsd_digits(tuple(digits), 64))
    return tuple(values)


def growth_table(
    *,
    count: int = 96,
    width: int = 240,
    horizons: tuple[int, ...] = (0, 1, 2, 4, 8, 16, 32),
) -> tuple[dict[str, object], ...]:
    """Measure occurrence growth separately from the fixed action grammar."""
    if not horizons or horizons != tuple(sorted(set(horizons))) or horizons[0] < 0:
        raise ValueError(horizons)
    endpoints: dict[int, tuple[int, ...]] = {
        0: _source_corpus(count=count, width=width)
    }
    current = endpoints[0]
    for step in range(1, horizons[-1] + 1):
        current = tuple(map(_accelerated, current))
        if step in horizons:
            endpoints[step] = current

    warm = (_RegionInterner(), _RegionInterner(), _RegionInterner())
    result: list[dict[str, object]] = []
    for horizon in horizons:
        widths: list[int] = []
        region_ids: list[set[int]] = [set(), set(), set()]
        region_actions: list[set[CollatzF5Carrier]] = [set(), set(), set()]
        new_nodes = [0, 0, 0]
        symbols: set[int] = set()
        leaf_actions: set[CollatzF5Carrier] = set()
        for value in endpoints[horizon]:
            digits = digits_lsd(value, 64)
            widths.append(len(digits))
            symbols.update(digits)
            leaf_actions.update(LEAF_BY_DIGIT[digit] for digit in digits)
            rows, created = region_occurrences(digits, warm)
            for i in range(3):
                new_nodes[i] += created[i]
            for row in rows:
                index = row.level - 1
                region_ids[index].add(row.node_id)
                region_actions[index].add(row.action)
        result.append(
            {
                "horizon": horizon,
                "sources": count,
                "min_width": min(widths),
                "avg_width": mean(widths),
                "max_width": max(widths),
                "leaf_symbols": len(symbols),
                "leaf_action_classes": len(leaf_actions),
                "region5_nodes": len(region_ids[0]),
                "region5_actions": len(region_actions[0]),
                "new_region5_nodes": new_nodes[0],
                "region25_nodes": len(region_ids[1]),
                "region25_actions": len(region_actions[1]),
                "new_region25_nodes": new_nodes[1],
                "region125_nodes": len(region_ids[2]),
                "region125_actions": len(region_actions[2]),
                "new_region125_nodes": new_nodes[2],
            }
        )
    return tuple(result)


def leaf_class_rows() -> tuple[dict[str, object], ...]:
    rows: list[dict[str, object]] = []
    for class_id, state in enumerate(sorted(LEAF_STATES)):
        digits = tuple(d for d, action in enumerate(LEAF_BY_DIGIT) if action == state)
        rows.append(
            {
                "class_id": class_id,
                "carry_action": state.carry_action,
                "carry_map": DOMAIN_ACTIONS[state.carry_action],
                "f5_phase": state.phase,
                "digits": digits,
            }
        )
    return tuple(rows)


__all__ = [
    "LEAF_BY_DIGIT",
    "LEAF_STATES",
    "CollatzF5Carrier",
    "RegionOccurrence",
    "carrier_from_digits",
    "compose_carrier",
    "exact_length_states",
    "growth_table",
    "leaf_class_rows",
    "region_occurrences",
]
