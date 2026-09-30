"""Shared containment checks for retired reverse temporal execution paths."""

import importlib.util
from collections.abc import Callable
from typing import Never

import pytest

from devtools.experiments.reverse_add import uniform_projection_reference


def forbid_uniform_context_compilation(
    monkeypatch: pytest.MonkeyPatch,
    forbidden: Callable[..., Never],
) -> None:
    assert importlib.util.find_spec("number_compiler.hashlife.actions.power") is None
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade_power")
        is None
    )
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade") is None
    )
    for name in (
        "uniform_successor",
        "uniform_no_growth_power",
        "edge_core_successors",
        "select_clause",
    ):
        monkeypatch.setattr(uniform_projection_reference, name, forbidden)
    monkeypatch.setattr(
        uniform_projection_reference.ProjectionClause, "instantiate", forbidden
    )
