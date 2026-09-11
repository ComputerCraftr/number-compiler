"""Completed exact output summaries answer interface observations without replay."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    interface_payload_from_causal,
)
from number_compiler.hashlife.execution.tile_causal_tasks import result_payload
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


@pytest.mark.parametrize("source", ((0, 0, 0, 1), (5, 5, 5, 5)))
def test_completed_activity_never_reexecutes_semantic_function(
    monkeypatch: pytest.MonkeyPatch, source: tuple[int, int, int, int]
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with (
        _tile(tiles, adapter, primitive, source) as original,
        scheduler.complete(
            action, original.tile, adapter.initial_ports(action), adapter.wiring(action)
        ) as completed,
    ):
        causal = result_payload(tiles, completed)
        expected = interface_payload_from_causal(
            scheduler.results, action, causal, adapter.wiring(action), expected_level=2
        )
        assert expected.active == (
            tiles.resolve(completed.output).first_active is not None
        )

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("completed activity reran a semantic observer")

        monkeypatch.setattr(adapter, "_observe", forbidden)
        before = ledger.snapshot()
        assert (
            interface_payload_from_causal(
                scheduler.results,
                action,
                causal,
                adapter.wiring(action),
                expected_level=2,
            )
            == expected
        )
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        for counter in (
            "semantic_function_evaluations",
            "primitive_transition_evaluations",
            "primitive_output_evaluations",
            "tile_causal_frames",
        ):
            assert after.counters.get(counter, 0) == before.counters.get(counter, 0)
