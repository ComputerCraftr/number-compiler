"""Certified field observations never enter the generic continuation codec."""

from __future__ import annotations

from collections.abc import Callable
from typing import Never

import pytest

from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.parametrize(
    ("term", "coordinate", "expected"),
    (
        (lambda: ReverseAddPoweredTerm(196, 16), 0, 8),
        (lambda: PoweredCollatzTerm(27, 16), 0, 1),
    ),
)
def test_certified_powered_observation_poison_generic_state_codec(
    monkeypatch: pytest.MonkeyPatch,
    term: Callable[[], ReverseAddPoweredTerm | PoweredCollatzTerm],
    coordinate: int,
    expected: int,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "certified field observation entered the generic state codec"
        )

    monkeypatch.setattr(
        "number_compiler.hashlife.interfaces.semantic_state_codec.StateCodecArena.compile",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.diamond_runtime.DiamondRuntime.execute",
        forbidden,
    )
    powered = term()
    assert powered.width() > 0
    assert powered.digit(coordinate) == expected


@pytest.mark.validation  # N=64 end-to-end reverse point, width and route poisons.
def test_reverse_fused_parent_bypasses_retired_provider_and_higher_point_routes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("reverse fused parent entered a retired point route")

    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.provider_absorption.ProviderAbsorptionArena.point",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.higher_bimachine.HigherBimachineRuntime.point",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.higher_bimachine.HigherBimachineRuntime.point_structural",
        forbidden,
    )
    term = ReverseAddPoweredTerm(196, 64)
    assert term.digit(0) == 8
    assert term.width() == 31
    assert term._ledger.counters["powered_absorption_successes"] > 0
    assert term._ledger.counters.get("provider_fused_point_evaluations", 0) == 0
