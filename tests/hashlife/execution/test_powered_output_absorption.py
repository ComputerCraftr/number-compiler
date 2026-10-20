"""A compiled parent must absorb temporal output, not replay its recipe.

These gates deliberately bypass both acceleration caches.  Compiling a small
image DAG is insufficient: observations of that parent must execute the
published output behavior without returning to the higher temporal interpreter.
"""

from __future__ import annotations

from collections.abc import Callable
from importlib.util import find_spec
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    HigherSummaryArena,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeValueArena,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
    SourceImageID,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.projection.point_response import PointResponseRegister
from number_compiler.resources.payload_audit import audit_registered_payloads
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
    assert find_spec("number_compiler.hashlife.execution.temporal_leaf_diamond") is None

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("compiled parent replayed the temporal output interpreter")

    def direct_response(
        _self: PointResponseRegister,
        _program: ActionProgramID,
        coordinate: int,
        evaluate: Callable[[int], int],
    ) -> int:
        return evaluate(coordinate)

    monkeypatch.setattr(MicroblockCache, "get", forbidden)
    monkeypatch.setattr(MicroblockCache, "put", forbidden)
    monkeypatch.setattr(PointResponseRegister, "query", direct_response)
    expected = _reverse_digits(steps)
    term = ReverseAddPoweredTerm(196, steps)
    application = term.source_workspace()
    demand_image = cast(
        Callable[[SourceImageDemand], SourceImageID],
        object.__getattribute__(application, "_demanded_image"),
    )
    image = demand_image(SourceImageDemand("width"))
    view = application.scheduler.source_image_core().view(image)
    assert view.binding.source == application.source
    assert view.binding.action == application.root_action
    # Admission must publish support, not retain an intermediate endpoint.
    audit = audit_registered_payloads(term.resource_ledger)
    assert audit.forbidden_future_payloads == audit.unknown_payloads == 0
    before = term.resource_ledger.snapshot()

    monkeypatch.setattr(CausalTileEngine, "_run", forbidden)
    monkeypatch.setattr(type(application.adapter), "apply_composite", forbidden)
    monkeypatch.setattr(type(application.adapter), "compose_chronological", forbidden)
    monkeypatch.setattr(RuntimeValueArena, "action_function", forbidden)
    monkeypatch.setattr(HigherSummaryArena, "runtime_unary", forbidden)

    # No coordinate has been observed before these checks.  Legitimate spatial
    # descent remains available; interpreting temporal continuations does not.
    if observation == "point":
        for coordinate in (0, len(expected) // 2, len(expected) - 1):
            assert application.digit(coordinate) == expected[coordinate]
    else:
        assert application.width() == len(expected)
    after = term.resource_ledger.snapshot()
    for name in (
        "higher_concrete_operation_evaluations",
        "temporal_leaf_diamond_descents",
        "source_image_primitive_applications",
        "source_image_chronological_compositions",
        "source_image_publications",
    ):
        assert after.counters.get(name, 0) == before.counters.get(name, 0)
    assert after.counters.get("microblock_publications", 0) == 0
