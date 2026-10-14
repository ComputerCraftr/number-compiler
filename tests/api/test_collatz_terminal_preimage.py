"""Production Collatz routes consume exact terminal preimage macros."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.api.number_api import (
    NumberCompiler,
    PoweredCollatzTermPayload,
)
from number_compiler.api.query_types import CollatzTermQuery
from number_compiler.sequences.collatz import temporal_mixed_execution
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable

_POWER_TWO_PREIMAGE = ((1 << 160) - 1) // 3


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("terminal preimage route fell through to mixed discovery")


def test_public_terminal_preimage_route_precedes_mixed_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        temporal_mixed_execution, "select_mixed_clock_macro", _forbidden
    )
    monkeypatch.setattr(temporal_mixed_execution, "select_mixed_macro", _forbidden)
    monkeypatch.setattr(
        "number_compiler.sequences.collatz.temporal_run_executor.select_mixed_macro",
        _forbidden,
    )
    monkeypatch.setattr(D8TemporalTable, "select", _forbidden)

    projected = NumberCompiler().project(
        CollatzTermQuery(161, seed=_POWER_TWO_PREIMAGE)
    )
    assert type(projected.payload) is PoweredCollatzTermPayload
    assert projected.payload.materialize(max_bits=512) == 1

    counters = projected.payload.term._ledger.counters
    assert counters["collatz_terminal_power2_probe_attempts"] == 1
    assert counters["collatz_terminal_power2_preimage_actions"] == 1
    assert counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) == 0
    assert counters.get("collatz_hashlife_joint_parent_joins", 0) == 0
    assert not any(
        name.startswith("collatz_global_innovation_") and value
        for name, value in counters.items()
    )


@pytest.mark.parametrize("steps", (1_000_000, 10**12))
def test_large_power_two_preimage_continues_on_the_exact_one_two_cycle(
    steps: int,
) -> None:
    projected = NumberCompiler().project(
        CollatzTermQuery(steps, seed=_POWER_TWO_PREIMAGE)
    )
    assert type(projected.payload) is PoweredCollatzTermPayload
    expected = (1, 4, 2)[(steps - 161) % 3]
    assert projected.payload.materialize(max_bits=512) == expected
