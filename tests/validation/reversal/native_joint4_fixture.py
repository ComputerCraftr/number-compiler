"""Independent physical Q19 checks executed inside an installed wheel."""

from __future__ import annotations

from importlib import import_module
from typing import Any, Never


def joint_native_both_clocks_and_rejected_eq_core() -> None:
    import random

    native: Any = import_module("number_compiler.kernels._reverse_quotients")

    random_source = random.Random(196)
    clocks: set[int] = set()
    for i in range(100):
        half = bytes(
            [18]
            + [random_source.randrange(19) for _ in range(i % 5)]
            + [random_source.choice((8, 17, 18)) for _ in range(100 + i % 31)]
            + [random_source.randrange(19) for _ in range(i % 20)]
        )
        center = -1 if i % 2 == 0 else i % 10
        low = [min(s, 9) for s in half]
        high = [s - d for s, d in zip(half, low, strict=False)]
        source = int(
            "".join(map(str, high))
            + ("" if center < 0 else str(center))
            + "".join(map(str, reversed(low)))
        )
        for ticks in (4, 5, 17):
            base = native.add_folded(half, center, ticks, 4 << 20)
            result = native.add_folded_joint4(half, center, ticks, 4 << 20)
            assert result[:2] == base[:2]
            assert result[2][7] == 1 and result[2][8] >= 48
            if ticks == 4:
                assert result[2][0] == result[2][2] == result[2][3] == 0
            assert result[2][11] + result[2][12] == 1
            value = source
            clock = 0
            for step in range(ticks):
                nxt = value + int(str(value)[::-1])
                if step < 4:
                    clock |= (len(str(nxt)) - len(str(value))) << step
                value = nxt
            digits = str(value)
            physical = bytes(
                int(a) + int(b) for a, b in zip(digits, digits[::-1], strict=False)
            )
            actual = (
                result[0]
                + (b"" if result[1] < 0 else bytes([2 * result[1]]))
                + result[0][::-1]
            )
            assert actual == physical and clock in (7, 13)
            assert (result[2][11], result[2][12]) == ((1, 0) if clock == 13 else (0, 1))
            clocks.add(clock)
    assert clocks == {7, 13}
    for size in (64, 65, 101, 127, 128):
        half = bytes([18] + [9] * (size - 1))
        refused = native.add_folded_joint4(half, -1, 4, 4 << 20)
        assert refused[:2] == native.add_folded(half, -1, 4, 4 << 20)[:2]
        assert refused[2][7] == 0 and refused[2][9] == size - 64
    for padding in (0, 8, 126, 127):
        half = bytes([18] + [9] * padding + [17] * 64)
        result = native.add_folded_joint4(half, -1, 4, 4 << 20)
        assert result[:2] == native.add_folded(half, -1, 4, 4 << 20)[:2]
        assert result[2][7:9] == ((1, 48) if padding < 127 else (0, 0))


def joint_action_warm_publication_reuses_completed_result() -> None:
    import os

    os.environ["NUMBER_COMPILER_ENABLE_NATIVE_REVERSE"] = "1"
    os.environ["NUMBER_COMPILER_ENABLE_Q19_JOINT4"] = "1"
    from number_compiler.arithmetic.carry import native_reverse_actions
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    value = int("1" * 500 + "8" * 500)
    for _ in range(202):
        value += int(str(value)[::-1])
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, tuple(map(int, reversed(str(value)))), base=10
    )
    try:
        first = owner.publish_carry_window_continuation(1024, shared_cache=False)
        assert ledger.counters["native_pair_joint_bands"] >= 1

        def refuse(*args: object, **kwargs: object) -> Never:
            raise AssertionError("completed endpoint rebuilt")

        native_reverse_actions.native_folded_pair_action = refuse
        assert (
            owner.publish_carry_window_continuation(1024, shared_cache=False) == first
        )
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def two_birth_slabs_match_physical_rows_and_mixed_receipts() -> None:
    from collections import Counter
    from random import Random

    native: Any = import_module("number_compiler.kernels._reverse_quotients")

    r = Random(4095)
    clocks: Counter[int] = Counter()
    for j in range(500):
        half = bytes(
            [r.randrange(10, 19)]
            + [r.randrange(19) for _ in range(j % 14)]
            + [r.choice((8, 17, 18)) for _ in range(96 + j % 29)]
            + [r.randrange(19) for _ in range(j % 13)]
        )
        center = -1 if j % 2 == 0 else j % 10
        low = [max(x - 9, 0) for x in half]
        high = [x - y for x, y in zip(half, low, strict=False)]
        value = int(
            "".join(map(str, high))
            + ("" if center < 0 else str(center))
            + "".join(map(str, reversed(low)))
        )
        for ticks in (4, 5, 17):
            got = native.add_folded_joint4(half, center, ticks, 4 << 20)
            assert got[:2] == native.add_folded(half, center, ticks, 4 << 20)[:2]
            v = value
            clock = 0
            births = 0
            for k in range(ticks):
                after = v + int(str(v)[::-1])
                birth = len(str(after)) - len(str(v))
                births += birth
                if k < 4:
                    clock |= birth << k
                v = after
            digits = str(v)
            physical = bytes(
                int(a) + int(b) for a, b in zip(digits, digits[::-1], strict=False)
            )
            produced = (
                got[0] + (b"" if got[1] < 0 else bytes([2 * got[1]])) + got[0][::-1]
            )
            assert physical == produced and got[2][4] == births
            if got[2][7]:
                clocks[clock] += 1
    assert clocks[1] > 0 and clocks[5] > 0 and clocks[9] > 0
    # Two source-admitted two-birth slabs followed by the exact continuation.
    half = bytes([13, 17, 18, 3, 6, 12, 6, 4, 4] + [18] * 100)
    result = native.add_folded_joint4(half, -1, 16, 4 << 20)
    assert result[:2] == native.add_folded(half, -1, 16, 4 << 20)[:2]
    assert result[2][7] == result[2][13] == 2 and result[2][4] == 7
    # The exterior is not an unconditional admission. A first-tick no-birth
    # source must use the exact continuation.
    for outer in range(1, 9):
        got = native.add_folded_joint4(bytes([outer] + [18] * 100), -1, 4, 4 << 20)
        assert got[2][7] == 0
    # The first physical carry can also be issued by an EQ exterior when its
    # checked inward carry is one. This fixture has the 1100 clock.
    half = bytes([9, 14, 2, 4, 11, 0, 17, 8, 17, 18, 17, 17, 17, 8] + [18] * 100)
    for center in (-1, 3):
        got = native.add_folded_joint4(half, center, 4, 4 << 20)
        assert got[:2] == native.add_folded(half, center, 4, 4 << 20)[:2]
        assert got[2][7] == got[2][13] == 1
        low = [max(x - 9, 0) for x in half]
        high = [x - y for x, y in zip(half, low, strict=False)]
        value = int(
            "".join(map(str, high))
            + ("" if center < 0 else str(center))
            + "".join(map(str, reversed(low)))
        )
        clock = 0
        for k in range(4):
            after = value + int(str(value)[::-1])
            clock |= (len(str(after)) - len(str(value))) << k
            value = after
        assert clock == 3
        digits = str(value)
        assert bytes(
            int(a) + int(b) for a, b in zip(digits, digits[::-1], strict=False)
        ) == (got[0] + (b"" if got[1] < 0 else bytes([2 * got[1]])) + got[0][::-1])


def one_birth_slab_uses_physical_collars_and_center() -> None:
    import sys

    native: Any = import_module("number_compiler.kernels._reverse_quotients")

    source = int(sys.argv[1])
    for _ in range(12):
        source += int(str(source)[::-1])
    digits = str(source)
    half = bytes(
        int(a) + int(b)
        for a, b in zip(digits[: len(digits) // 2], reversed(digits), strict=False)
    )
    for center in (-1, 4):
        low = [max(x - 9, 0) for x in half]
        high = [x - y for x, y in zip(half, low, strict=False)]
        value = int(
            "".join(map(str, high))
            + ("" if center < 0 else str(center))
            + "".join(map(str, reversed(low)))
        )
        got = native.add_folded_joint4(half, center, 4, 4 << 20)
        assert got[:2] == native.add_folded(half, center, 4, 4 << 20)[:2]
        assert got[2][7] == got[2][14] == 1 and got[2][8] >= 48
        clock = 0
        for k in range(4):
            after = value + int(str(value)[::-1])
            clock |= (len(str(after)) - len(str(value))) << k
            value = after
        assert clock == 1
        output = str(value)
        assert bytes(
            int(a) + int(b) for a, b in zip(output, output[::-1], strict=False)
        ) == (got[0] + (b"" if got[1] < 0 else bytes([2 * got[1]])) + got[0][::-1])
        broken = bytearray(half)
        for i in range(90, len(broken)):
            broken[i] = 9
        rejected = native.add_folded_joint4(bytes(broken), center, 4, 4 << 20)
        assert rejected[2][7] == 0
        assert rejected[:2] == native.add_folded(bytes(broken), center, 4, 4 << 20)[:2]


def four_tick_carries_match_literal_width_and_center_transitions() -> None:
    import random

    native: Any = import_module("number_compiler.kernels._reverse_quotients")

    r = random.Random(11319)
    admitted = refused = 0
    for width in (64, 65, 95, 96, 127, 128, 129, 160, 193):
        for case in range(40):
            values = bytes(
                [r.randrange(1, 19)] + [r.randrange(19) for _ in range(width // 2 - 1)]
            )
            center = r.randrange(10) if width % 2 else -1
            high = [min(s, 9) for s in values]
            low = [s - d for s, d in zip(values, high, strict=False)]
            source = int(
                "".join(map(str, high))
                + ("" if center < 0 else str(center))
                + "".join(map(str, reversed(low)))
            )
            for ticks in (4, 5, 9, 16):
                result = native.add_folded(values, center, ticks, 4 << 20)
                number = source
                for _ in range(ticks):
                    number += int(str(number)[::-1])
                digits = str(number)
                physical = bytes(
                    int(a) + int(b) for a, b in zip(digits, digits[::-1], strict=False)
                )
                got = (
                    result[0]
                    + (b"" if result[1] < 0 else bytes([2 * result[1]]))
                    + result[0][::-1]
                )
                assert physical == got, (width, case, ticks)
                attempts, actions, tiles, declined, _, _ = result[2][19:25]
                assert attempts == actions + declined
                assert tiles >= actions
                admitted += actions
                refused += declined
    assert admitted > 0 and refused > 0


def four_tick_failed_publication_releases_native_reservation() -> None:
    from number_compiler.arithmetic.carry.native_reverse_actions import (
        PairWork,
        native_folded_pair_action,
    )
    from number_compiler.resources.ledger import ResourceLedger

    ledger = ResourceLedger()
    owner = ledger.register("four tick publication", "scratch")

    def publish(half: bytes, center: int | None, work: PairWork) -> Never:
        assert half and center in (None, *range(10))
        assert work.tile_actions == 128 and work.tile_refusals == 0
        assert work.states == work.joins == work.table_bytes == 0
        raise RuntimeError("publication interrupted")

    try:
        try:
            native_folded_pair_action(
                ledger,
                owner,
                lambda: bytes([18] * 128),
                None,
                512,
                publish,
                source_width=256,
            )
        except RuntimeError as error:
            assert str(error) == "publication interrupted"
        else:
            raise AssertionError("publication fault was lost")
        assert ledger.nodes == ledger.entries == 0
    finally:
        ledger.mark_disposed(owner)


def run_task(task: str) -> None:
    tasks = {
        "joint_native_both_clocks_and_rejected_eq_core": joint_native_both_clocks_and_rejected_eq_core,
        "joint_action_warm_publication_reuses_completed_result": joint_action_warm_publication_reuses_completed_result,
        "two_birth_slabs_match_physical_rows_and_mixed_receipts": two_birth_slabs_match_physical_rows_and_mixed_receipts,
        "one_birth_slab_uses_physical_collars_and_center": one_birth_slab_uses_physical_collars_and_center,
        "four_tick_carries_match_literal_width_and_center_transitions": four_tick_carries_match_literal_width_and_center_transitions,
        "four_tick_failed_publication_releases_native_reservation": four_tick_failed_publication_releases_native_reservation,
    }
    tasks[task]()
