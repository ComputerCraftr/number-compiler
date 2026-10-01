"""Shared containment checks for retired reverse temporal execution paths."""

import importlib.util
from collections.abc import Callable, Mapping
from typing import Never

import pytest

from devtools.experiments.reverse_add import uniform_projection_reference
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


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


def assert_completed_child_work(counters: Mapping[str, int]) -> None:
    """Require actual provider joins and reject causal/terminal reconstruction."""
    for name in (
        "reverse_recursive_completed_child_joins",
        "reverse_provider_parent_substitutions",
    ):
        assert counters.get(name, 0) > 0
    for name in (
        "source_image_primitive_applications",
        "reverse_recursive_direct_temporal_publications",
        "reverse_recursive_terminal_publications",
    ):
        assert counters.get(name, 0) == 0


def assert_mirror_scratch_released(term: ReverseAddPoweredTerm) -> None:
    """Both mirror consumers return their shared buffer and reservation."""
    scratch = term._mirror_output_scratch
    assert scratch is not None and not scratch
    account = next(
        item for item in term._ledger.inventory() if item.owner == scratch.owner
    )
    assert account.entries == account.nodes == account.accounting_delta == 0
