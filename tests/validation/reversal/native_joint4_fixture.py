"""Independent physical Q19 checks executed inside an installed wheel."""

from __future__ import annotations

from importlib import import_module
from typing import Any, Never


def _literal_source(half: bytes, center: int, *, high_first: bool) -> int:
    selected = [min(pair, 9) for pair in half]
    remainder = [pair - digit for pair, digit in zip(half, selected, strict=False)]
    high, low = (selected, remainder) if high_first else (remainder, selected)
    return int(
        "".join(map(str, high))
        + ("" if center < 0 else str(center))
        + "".join(map(str, reversed(low)))
    )


def _literal_steps(source: int, ticks: int) -> tuple[int, int, int]:
    clock = births = 0
    for step in range(ticks):
        after = source + int(str(source)[::-1])
        birth = len(str(after)) - len(str(source))
        births += birth
        if step < 4:
            clock |= birth << step
        source = after
    return source, clock, births


def _assert_physical_fold(
    result: tuple[bytes, int, tuple[int, ...]], source: int, context: object = None
) -> None:
    digits = str(source)
    physical = bytes(
        int(a) + int(b) for a, b in zip(digits, digits[::-1], strict=False)
    )
    folded = result[0] + (b"" if result[1] < 0 else bytes([2 * result[1]]))
    assert physical == folded + result[0][::-1], context


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
        source = _literal_source(half, center, high_first=False)
        for ticks in (4, 5, 17):
            base = native.add_folded(half, center, ticks, 4 << 20)
            result = native.add_folded_joint4(half, center, ticks, 4 << 20)
            assert result[:2] == base[:2]
            assert result[2][7] == 1 and result[2][8] >= 48
            if ticks == 4:
                assert result[2][0] == result[2][2] == result[2][3] == 0
            assert result[2][11] + result[2][12] == 1
            value, clock, _ = _literal_steps(source, ticks)
            _assert_physical_fold(result, value)
            assert clock in (7, 13)
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
        value = _literal_source(half, center, high_first=True)
        for ticks in (4, 5, 17):
            got = native.add_folded_joint4(half, center, ticks, 4 << 20)
            assert got[:2] == native.add_folded(half, center, ticks, 4 << 20)[:2]
            v, clock, births = _literal_steps(value, ticks)
            _assert_physical_fold(got, v)
            assert got[2][4] == births
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
        value = _literal_source(half, center, high_first=True)
        value, clock, _ = _literal_steps(value, 4)
        assert clock == 3
        _assert_physical_fold(got, value)


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
        value = _literal_source(half, center, high_first=True)
        got = native.add_folded_joint4(half, center, 4, 4 << 20)
        assert got[:2] == native.add_folded(half, center, 4, 4 << 20)[:2]
        assert got[2][7] == got[2][14] == 1 and got[2][8] >= 48
        value, clock, _ = _literal_steps(value, 4)
        assert clock == 1
        _assert_physical_fold(got, value)
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
            source = _literal_source(values, center, high_first=True)
            for ticks in (4, 5, 9, 16):
                result = native.add_folded(values, center, ticks, 4 << 20)
                number, _, _ = _literal_steps(source, ticks)
                _assert_physical_fold(result, number, (width, case, ticks))
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
