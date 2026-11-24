"""Terminal transfers consume the existing source-bound endpoint action."""

from __future__ import annotations

import pytest

from number_compiler.sequences.five_reverse.ports import FiveBorderPort, FiveCarryPort
from number_compiler.sequences.five_reverse.source_adapter import (
    FiveReverseSourceAdapter,
)
from number_compiler.sequences.five_reverse.term import FiveReverseTerm
from tests.support.private_attributes import private_test_attribute


def test_terminal_transfer_uses_packed_action(monkeypatch: pytest.MonkeyPatch) -> None:
    seed, steps = 73, 256
    expected = seed
    for _ in range(steps):
        expected = 5 * int(str(expected)[::-1])
    with FiveReverseTerm(seed, 0, max_steps=steps, max_state_bits=4096) as term:

        def forbidden(_self: FiveReverseTerm, _value: int) -> int:
            raise AssertionError("terminal consumer replayed steps")

        monkeypatch.setattr(FiveReverseTerm, "_next", forbidden)
        packet = term.source_transfer(steps)
        assert packet.terminal_port == term.source_port(expected)
        assert packet.trace == ()
        assert (
            term.resource_ledger.counters.get("five_reverse_packed_executed_pairs", 0)
            == 128
        )


def test_guarded_terminal_consumes_authenticated_target(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with FiveReverseTerm(196, 180, max_steps=184) as term:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("guarded terminal replayed transitions")

        monkeypatch.setattr(FiveReverseTerm, "_advance_guarded_window", forbidden)
        packet = term.source_transfer(4)
        assert packet.trace == ()
        assert isinstance(packet.initial_port, FiveCarryPort)
        assert isinstance(packet.terminal_port, FiveCarryPort)
        assert packet.initial_port.head3 == 348
        assert packet.terminal_port.head3 == 311
        assert packet.terminal_port.tail3 == 260


def test_terminal_only_reservation_does_not_scale_with_horizon() -> None:
    with FiveReverseTerm(
        0,
        0,
        max_steps=2048,
        max_state_bits=64,
        max_context_nodes=512,
        max_cache_entries=512,
    ) as term:
        packet = term.source_transfer(2048)
        assert isinstance(packet.terminal_port, FiveBorderPort)
        assert packet.terminal_port.low_digits == (0,)
        assert packet.trace == ()


def test_source_adapter_rejects_invalid_steps_and_closed_owner() -> None:
    with FiveReverseTerm(1, 0, max_steps=2) as term:
        adapter = private_test_attribute(term, "_adapter")
        assert isinstance(adapter, FiveReverseSourceAdapter)
        for steps in (True, -1, 3):
            with pytest.raises(ValueError):
                adapter.apply_steps(1, steps)
    with pytest.raises(ValueError, match="disposed"):
        adapter.apply_steps(1, 0)
