"""The bounded native threshold keeps its physical and family guards."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.carry import native_reverse_actions
from number_compiler.resources.ledger import ResourceLedger


def test_native_threshold_is_five_reverse_only(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[str, int, int, int]] = []
    value = 73
    for _ in range(128):
        value = 5 * int(str(value)[::-1])

    class Native:
        @staticmethod
        def multiply(
            source: str, multiplier: int, steps: int, side: int
        ) -> tuple[str, tuple[int, int, int, int, int, int, float, float]]:
            calls.append((source, multiplier, steps, side))
            result = int(source)
            for _ in range(steps):
                result = multiplier * int(str(result)[::-1])
            return str(result), (1, 1, 0, 0, 1, 1, 0.0, 0.0)

    monkeypatch.setattr(native_reverse_actions, "_load", lambda: Native())
    ledger = ResourceLedger()
    owner = ledger.register("native admission test", "scratch")

    def receive(digits: str, _work: native_reverse_actions.DiagonalWork) -> int:
        return int(digits)

    action = native_reverse_actions.diagonal_endpoint
    assert action(ledger, owner, 73, 2, 128, 8192, receive) is None
    assert action(ledger, owner, 73, 5, 63, 8192, receive) is None
    assert action(ledger, owner, 1 << 512, 5, 64, 8192, receive) is None
    assert action(ledger, owner, 6, 5, 128, 4, receive) is None
    assert not calls
    expected_short = 73
    for _ in range(64):
        expected_short = 5 * int(str(expected_short)[::-1])
    assert action(ledger, owner, 73, 5, 64, 8192, receive) == expected_short
    assert action(ledger, owner, 73, 5, 128, 8192, receive) == value
    assert calls == [("73", 5, 64, 3), ("73", 5, 128, 3)]
    assert ledger.entries == ledger.nodes == 0
    ledger.mark_disposed(owner)
