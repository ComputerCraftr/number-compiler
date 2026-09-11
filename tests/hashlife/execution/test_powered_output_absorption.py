"""A compiled parent must absorb temporal output, not replay its recipe.

These gates deliberately bypass both acceleration caches.  Compiling a small
image DAG is insufficient: observations of that parent must execute the
published output behavior without returning to the higher temporal interpreter.
"""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.hashlife.execution.continuations.higher_summaries import (
    HigherSummaryArena,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeValueArena,
)
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.projection.point_response import PointResponseRegister
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _reverse_digits(steps: int) -> tuple[int, ...]:
    value = 196
    for _ in range(steps):
        value += int(str(value)[::-1])
    return tuple(map(int, str(value)[::-1]))


@pytest.mark.validation  # The unchanged N=16…256 production release gate.
@pytest.mark.representation
@pytest.mark.parametrize("steps", (16, 32, 64, 128, 256))
@pytest.mark.parametrize("observation", ("point", "width"))
def test_reverse_compiled_parent_absorbs_powered_output(
    steps: int, observation: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    import number_compiler.hashlife.execution.temporal_leaf_diamond as leaf_runtime

    monkeypatch.setattr(MicroblockCache, "get", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(MicroblockCache, "put", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(
        PointResponseRegister,
        "query",
        lambda _self, _program, coordinate, evaluate: evaluate(coordinate),
    )
    expected = _reverse_digits(steps)
    term = ReverseAddPoweredTerm(196, steps)
    application = term._point_index()._lazy_application
    assert isinstance(application, LazyProjection)
    application._application.interface()
    assert application._application._root is None
    before = term._ledger.snapshot()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("compiled parent replayed the temporal output interpreter")

    monkeypatch.setattr(leaf_runtime, "evaluate_temporal_leaf", forbidden)
    monkeypatch.setattr(RuntimeValueArena, "action_function", forbidden)
    monkeypatch.setattr(HigherSummaryArena, "runtime_unary", forbidden)

    # No coordinate has been observed before these checks.  Legitimate spatial
    # descent remains available; interpreting temporal continuations does not.
    if observation == "point":
        for coordinate in (0, len(expected) // 2, len(expected) - 1):
            assert application.point(coordinate) == expected[coordinate]
    else:
        assert application.active_width() == len(expected)
    after = term._ledger.snapshot()
    for name in (
        "higher_concrete_operation_evaluations",
        "temporal_leaf_diamond_descents",
    ):
        assert after.counters.get(name, 0) == before.counters.get(name, 0)
    assert after.counters.get("microblock_publications", 0) == 0
