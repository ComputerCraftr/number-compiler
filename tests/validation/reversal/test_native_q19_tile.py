"""Physical source and boundary checks for the four-tick Q19 tiles."""

from __future__ import annotations

import random

import pytest


def _field(value: int) -> tuple[bytes, int]:
    digits = str(value)
    half = bytes(
        int(a) + int(b) for a, b in zip(digits[: len(digits) // 2], reversed(digits))
    )
    center = int(digits[len(half)]) if len(digits) % 2 else -1
    return half, center


def _literal(value: int, ticks: int) -> int:
    for _ in range(ticks):
        value += int(str(value)[::-1])
    return value


def test_four_tick_packed_tiles_match_literal_physical_sources() -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    random_source = random.Random(782)
    for width in (63, 64, 65, 66, 95, 127, 128, 129, 193):
        for _ in range(8):
            digits = [random_source.randrange(10) for _ in range(width)]
            digits[0] = random_source.randrange(1, 10)
            source = int("".join(map(str, digits)))
            half, center = _field(source)
            for ticks in (4, 5, 9, 16):
                pairs, middle, work = native.add_folded(half, center, ticks, 4 << 20)
                assert (pairs, middle) == _field(_literal(source, ticks))
                assert work[19] == work[20] + work[22]
                assert work[21] >= work[20]


def test_four_tick_refusal_keeps_source_and_avoids_early_table_work() -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    # All equal pair sums do not fix the inward carry from this prefix.
    equal = bytes((9,)) * 40
    pairs, center, work = native.add_folded(equal, -1, 4, 4 << 20)
    assert work[19:25] == (1, 0, 0, 1, 0, 0)
    full, _ = native.add(equal + equal[::-1], 4, 2, 1, 4 << 20)
    assert pairs + (bytes((2 * center,)) if center >= 0 else b"") + pairs[::-1] == full

    # The first tile has a valid width clock but the second lacks a full
    # carry-reset aperture. The partially written result must be discarded.
    halo = bytes.fromhex(
        "0800010c1207060e090909090909090909090909090909090909090909090909"
    )
    pairs, center, work = native.add_folded(halo, -1, 4, 4 << 20)
    assert work[19:25] == (1, 0, 2, 1, 32, 80)
    full, _ = native.add(halo + halo[::-1], 4, 2, 1, 4 << 20)
    assert pairs + (bytes((2 * center,)) if center >= 0 else b"") + pairs[::-1] == full


def test_four_tick_admitted_source_skips_two_tick_compiler() -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    value = int("12345678901234567890" * 4)
    half, center = _field(value)
    pairs, middle, work = native.add_folded(half, center, 4, 1)
    assert (pairs, middle) == _field(_literal(value, 4))
    assert work[19:21] == (1, 1)
    assert work[0] == work[5] == 0


@pytest.mark.parametrize(
    "tile",
    (
        (1, 2, 2, 0, 0, 0),
        (1, 1, 0, 0, 0, 0),
        (1, 0, 0, 0, 0, 0),
        (1, 1, 1, 0, 0, 10**9),
        (-1, 0, 0, 0, 0, 0),
    ),
)
def test_invalid_packed_receipt_never_reaches_receiver(
    tile: tuple[int, ...], monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions as actions
    from number_compiler.resources.ledger import ResourceLedger

    class Native:
        @staticmethod
        def add_folded(*_args: object) -> tuple[bytes, int, tuple[int, ...]]:
            return b"\x01\x01", -1, (1, 256, 20, 20, 0, 1, 1, *([0] * 12), *tile)

    monkeypatch.setattr(actions, "_load", lambda: Native())
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_Q19_JOINT4", raising=False)
    ledger = ResourceLedger()
    owner = ledger.register("invalid packed receipt", "scratch")

    def receive(_half: bytes, _center: int | None, _work: actions.PairWork) -> None:
        pytest.fail("invalid receipt reached publication")

    with pytest.raises(RuntimeError, match="invalid native folded causal endpoint"):
        actions.native_folded_pair_action(
            ledger, owner, lambda: b"\x01\x01", None, 512, receive, source_width=4
        )
    assert ledger.nodes == ledger.entries == 0
