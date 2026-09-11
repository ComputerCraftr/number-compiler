"""Deterministically rebuild the exact minimized decimal T^2 block kernel.

The kernel is seed-independent. It enumerates the complete elementary boundary
state spaces, constructs ``T o T`` extensionally, then minimizes both context
DFAs by exact output behavior followed by deterministic transition refinement.
"""

from __future__ import annotations

import argparse
import hashlib
import struct
import sys
import zlib
from array import array
from collections import deque
from collections.abc import Callable, Hashable, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TypeVar

from devtools.paths import repository_root
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect

HERE = repository_root()

StateT = TypeVar("StateT", bound=Hashable)

MAGIC = b"RAT2K1"
HEADER = struct.Struct("<6sBBHHHH")


@dataclass(frozen=True)
class RawLeft:
    a_left: int
    f: tuple[int, ...]


@dataclass(frozen=True)
class RawRight:
    a_right: int
    h: tuple[int, ...]


def _enumerate_side(
    initial: StateT, transition: Callable[[StateT, int], StateT], alphabet: range
) -> tuple[list[StateT], dict[StateT, int]]:
    states = [initial]
    index = {initial: 0}
    todo = deque([initial])
    while todo:
        state = todo.popleft()
        for symbol in alphabet:
            nxt = transition(state, symbol)
            if nxt not in index:
                index[nxt] = len(states)
                states.append(nxt)
                todo.append(nxt)
    return states, index


def _partition(signatures: Sequence[Hashable]) -> tuple[list[int], list[int]]:
    lookup: dict[Hashable, int] = {}
    classes: list[int] = []
    reps: list[int] = []
    for state_id, signature in enumerate(signatures):
        cls = lookup.get(signature)
        if cls is None:
            cls = len(reps)
            lookup[signature] = cls
            reps.append(state_id)
        classes.append(cls)
    return classes, reps


def _refine(
    initial_classes: list[int], transitions: list[tuple[int, ...]]
) -> tuple[list[int], list[int]]:
    classes = initial_classes
    while True:
        signatures = [
            (classes[state], tuple(classes[nxt] for nxt in transitions[state]))
            for state in range(len(transitions))
        ]
        refined, reps = _partition(signatures)
        if refined == classes:
            return refined, reps
        classes = refined


def build_kernel(base: int = 10) -> tuple[bytes, dict[str, int | str]]:
    if base != 10:
        raise ValueError("this retained kernel format currently targets base 10")
    t = BaseBlockEffect(base)
    alphabet = range(t.blank + 1)

    left_states, left_index = _enumerate_side(
        t.initial(BoundarySide.LEFT),
        lambda state, symbol: t.advance(BoundarySide.LEFT, state, symbol),
        alphabet,
    )
    right_states, right_index = _enumerate_side(
        t.initial(BoundarySide.RIGHT),
        lambda state, symbol: t.advance(BoundarySide.RIGHT, state, symbol),
        alphabet,
    )
    L, R = len(left_states), len(right_states)

    left_delta = [[0] * len(alphabet) for _ in range(L)]
    right_delta = [[0] * len(alphabet) for _ in range(R)]
    for li, state in enumerate(left_states):
        for symbol in alphabet:
            left_delta[li][symbol] = left_index[
                t.advance(BoundarySide.LEFT, state, symbol)
            ]
    for ri, state in enumerate(right_states):
        for symbol in alphabet:
            right_delta[ri][symbol] = right_index[
                t.advance(BoundarySide.RIGHT, state, symbol)
            ]

    out1 = [[[0] * R for _ in alphabet] for _ in range(L)]
    for li, left in enumerate(left_states):
        for symbol in alphabet:
            row = out1[li][symbol]
            for ri, right in enumerate(right_states):
                row[ri] = t.emit(left, symbol, right)

    raw_left = [
        RawLeft(
            left_index[t.initial(BoundarySide.LEFT)],
            (left_index[t.initial(BoundarySide.LEFT)],) * R,
        )
    ]
    raw_left_index = {raw_left[0]: 0}
    raw_left_trans: list[tuple[int, ...]] = []
    cursor = 0
    while cursor < len(raw_left):
        state = raw_left[cursor]
        row = []
        for symbol in alphabet:
            new_f = []
            for r_after in range(R):
                r_before = right_delta[r_after][symbol]
                first_symbol = out1[state.a_left][symbol][r_after]
                new_f.append(left_delta[state.f[r_before]][first_symbol])
            nxt = RawLeft(left_delta[state.a_left][symbol], tuple(new_f))
            nid = raw_left_index.get(nxt)
            if nid is None:
                nid = len(raw_left)
                raw_left_index[nxt] = nid
                raw_left.append(nxt)
            row.append(nid)
        raw_left_trans.append(tuple(row))
        cursor += 1

    raw_right = [
        RawRight(
            right_index[t.initial(BoundarySide.RIGHT)],
            (right_index[t.initial(BoundarySide.RIGHT)],) * L,
        )
    ]
    raw_right_index = {raw_right[0]: 0}
    raw_right_trans: list[tuple[int, ...]] = []
    cursor = 0
    while cursor < len(raw_right):
        state = raw_right[cursor]
        row = []
        for symbol in alphabet:
            new_h = []
            for l_before in range(L):
                l_after = left_delta[l_before][symbol]
                first_symbol = out1[l_before][symbol][state.a_right]
                new_h.append(right_delta[state.h[l_after]][first_symbol])
            next_right = RawRight(right_delta[state.a_right][symbol], tuple(new_h))
            nid = raw_right_index.get(next_right)
            if nid is None:
                nid = len(raw_right)
                raw_right_index[next_right] = nid
                raw_right.append(next_right)
            row.append(nid)
        raw_right_trans.append(tuple(row))
        cursor += 1

    RL, RR = len(raw_left), len(raw_right)

    def composed_output(li: int, symbol: int, ri: int) -> int:
        left = raw_left[li]
        right = raw_right[ri]
        first_symbol = out1[left.a_left][symbol][right.a_right]
        second_left = left.f[right_delta[right.a_right][symbol]]
        second_right = right.h[left_delta[left.a_left][symbol]]
        return out1[second_left][first_symbol][second_right]

    left_sigs: list[bytes] = []
    for li in range(RL):
        sig = bytearray()
        for symbol in alphabet:
            sig.extend(composed_output(li, symbol, ri) for ri in range(RR))
        left_sigs.append(bytes(sig))
    left_classes0, _ = _partition(left_sigs)

    right_sigs: list[bytes] = []
    for ri in range(RR):
        sig = bytearray()
        for li in range(RL):
            sig.extend(composed_output(li, symbol, ri) for symbol in alphabet)
        right_sigs.append(bytes(sig))
    right_classes0, _ = _partition(right_sigs)

    left_classes, left_reps = _refine(left_classes0, raw_left_trans)
    right_classes, right_reps = _refine(right_classes0, raw_right_trans)
    ML, MR = len(left_reps), len(right_reps)
    if ML >= 65536 or MR >= 65536:
        raise RuntimeError("kernel state IDs no longer fit uint16")

    left_table = array("H")
    for rep_1 in left_reps:
        left_table.extend(left_classes[nxt] for nxt in raw_left_trans[rep_1])
    right_table = array("H")
    for rep_2 in right_reps:
        right_table.extend(right_classes[nxt] for nxt in raw_right_trans[rep_2])

    outputs = bytearray()
    for left_rep in left_reps:
        for symbol in alphabet:
            outputs.extend(
                composed_output(left_rep, symbol, right_rep) for right_rep in right_reps
            )

    if left_table.itemsize != 2 or right_table.itemsize != 2:
        raise RuntimeError("unexpected uint16 array item size")
    if sys.byteorder != "little":
        left_table.byteswap()
        right_table.byteswap()

    initial_left_raw = raw_left_index[
        RawLeft(
            left_index[t.initial(BoundarySide.LEFT)],
            (left_index[t.initial(BoundarySide.LEFT)],) * R,
        )
    ]
    initial_right_raw = raw_right_index[
        RawRight(
            right_index[t.initial(BoundarySide.RIGHT)],
            (right_index[t.initial(BoundarySide.RIGHT)],) * L,
        )
    ]
    raw = (
        HEADER.pack(
            MAGIC,
            base,
            len(alphabet),
            ML,
            MR,
            left_classes[initial_left_raw],
            right_classes[initial_right_raw],
        )
        + left_table.tobytes()
        + right_table.tobytes()
        + bytes(outputs)
    )
    packed = zlib.compress(raw, level=9)
    stats: dict[str, int | str] = {
        "base_left_states": L,
        "base_right_states": R,
        "raw_t2_left_states": RL,
        "raw_t2_right_states": RR,
        "initial_output_left_classes": len(set(left_classes0)),
        "initial_output_right_classes": len(set(right_classes0)),
        "minimized_t2_left_states": ML,
        "minimized_t2_right_states": MR,
        "raw_bytes": len(raw),
        "packed_bytes": len(packed),
        "sha256": hashlib.sha256(packed).hexdigest(),
    }
    return packed, stats


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=HERE / "src" / "number_compiler" / "kernels" / "base10_t2_kernel.zlib",
    )
    parser.add_argument("--verify-existing", action="store_true")
    args = parser.parse_args()
    packed, stats = build_kernel(10)
    if args.verify_existing:
        if args.output.read_bytes() != packed:
            raise SystemExit("kernel differs from deterministic rebuild")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(packed)
    for key, value in stats.items():
        print(key, value)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
