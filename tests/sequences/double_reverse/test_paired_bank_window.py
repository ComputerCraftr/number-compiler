"""Batched pointed banks preserve exact physical digits and guard fallback."""

from __future__ import annotations

import pytest

from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
)


@pytest.mark.parametrize(
    "seed,steps,start,count", [(196, 64, 0, 14), (173488, 96, 1, 12), (196, 128, 1, 19)]
)
def test_paired_window_uses_shared_halos_and_literal_physical_rows(
    monkeypatch: pytest.MonkeyPatch, seed: int, steps: int, start: int, count: int
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("per-cell pointed cone rebuilt")

    monkeypatch.setattr(DoubleReverseTemporalHashlife, "pointed_stencil", forbidden)
    value = seed
    for _ in range(steps):
        value = 2 * int(str(value)[::-1])
    current = str(value)
    for _ in range(2):
        value = 2 * int(str(value)[::-1])
    following = str(value)
    with DoubleReverseTerm(seed, steps) as term:
        window = term.exact_temporal_bank_window(start, count)
        for index, frame in enumerate(window.frames, start):
            assert frame.digits == (int(current[index]), int(current[-1 - index]))
            shifted = index + frame.growth_left
            assert frame.next_digits == (
                int(following[shifted]),
                int(following[-1 - shifted]),
            )


def test_capped_ledger_keeps_exact_pointed_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("optional batched path used with capped ledger")

    monkeypatch.setattr(DoubleReverseTemporalHashlife, "pointed_window", forbidden)
    with DoubleReverseTerm(196, 32, max_context_nodes=4_000) as term:
        assert len(term.exact_temporal_bank_window(0, 4).frames) == 4


def test_interrupted_batch_releases_temporary_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def interrupted(*args: object, **kwargs: object) -> None:
        raise RuntimeError("interrupted batch")

    monkeypatch.setattr(DoubleReverseTemporalHashlife, "pointed_window", interrupted)
    with DoubleReverseTerm(196, 64) as term:
        with pytest.raises(RuntimeError, match="interrupted batch"):
            term.exact_temporal_bank_window(0, 14)
        assert term.resource_ledger.account_usage(term.scratch_owner) == (0, 0)
