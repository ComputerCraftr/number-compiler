"""Actual primitive macro bindings expose their provenance and resource units."""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import replace
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
    PrimitiveMacroBinding,
)
from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
    PrimitiveMacroKey,
    PrimitiveMacroObservation,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict
from tests.support.collatz_diamond_fixtures import collatz_higher_context_runtime

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import CellID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
        PrimitiveMacroArena,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import (
        LocalInterfaceID,
    )


def setup() -> tuple[
    DiamondRuntime, PrimitiveMacroArena, ActionProgramID, CellID, LocalInterfaceID
]:
    runtime, action = collatz_higher_context_runtime((1, 0, 1), 4)
    runtime.kernel(action)
    kernel = runtime.primitive_ids[action]
    source = runtime.cells.source(0, 2)
    quotient = runtime.compile_primitive_macro(kernel, source)
    arena = runtime.primitive_macros
    assert arena is not None
    return runtime, arena, kernel, source, quotient


def test_shared_macro_inventory_and_warm_reuse_do_not_execute_the_producer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, arena, kernel, source, quotient = setup()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm parent or audit replayed the source producer")

    for method in ("_leaf", "_parent"):
        monkeypatch.setattr(arena, method, forbidden)
    monkeypatch.setattr(runtime.cells, "source_symbol", forbidden)
    monkeypatch.setattr(runtime.cells, "split", forbidden)
    before = runtime.ledger.snapshot()
    assert runtime.compile_primitive_macro(kernel, source) == quotient
    after = runtime.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert (
        after.counters["primitive_macro_early_hits"]
        == before.counters.get("primitive_macro_early_hits", 0) + 1
    )
    assert (
        after.counters["primitive_macro_source_frames"]
        == before.counters["primitive_macro_source_frames"]
    )
    assert (
        after.counters["semantic_function_published_nodes"]
        == before.counters["semantic_function_published_nodes"]
    )
    assert runtime.observe_primitive_macro(quotient, left=0, right=0, coordinate=0) in (
        0,
        1,
        2,
    )
    observed = runtime.ledger.snapshot()
    assert (observed.entries, observed.nodes) == (after.entries, after.nodes)
    report = collect_ledger_metrics(runtime.ledger)
    assert runtime.ledger.snapshot() == observed
    assert report.representation_boundary_complete == 1
    assert (
        report.diamond_quotient_nodes == len(arena.quotients.audit_snapshot().nodes) > 0
    )
    assert report.spatial_parent_cache_entries >= len(arena.bindings) > 0
    assert report.primitive_macro_cache_entries == len(arena.bindings)
    for name in (
        "primitive_macro_requests",
        "primitive_macro_early_hits",
        "primitive_macro_evaluations",
        "primitive_macro_compilations",
        "primitive_macro_source_frames",
        "primitive_macro_spatial_compositions",
        "primitive_macro_observation_requests",
        "primitive_macro_observation_evaluations",
    ):
        assert getattr(report, name) == runtime.ledger.counters.get(name, 0)
    assert report.primitive_macro_observation_evaluations > 0
    assert report.primitive_macro_spatial_compositions > 0


@pytest.mark.parametrize(
    "fault",
    ("extent", "boolean-extent", "foreign-source", "foreign-quotient", "kernel-alias"),
)
def test_macro_binding_requires_actual_source_kernel_quotient_and_extent(
    fault: str,
) -> None:
    runtime, arena, kernel, source, _quotient = setup()
    key = PrimitiveMacroKey(kernel, source)
    binding = arena.bindings[key]
    if fault == "extent":
        cast(
            MutableMapping[object, object],
            object.__getattribute__(arena.bindings, "_data"),
        )[key] = replace(binding, original_extent=2)
    elif fault == "boolean-extent":
        cast(
            MutableMapping[object, object],
            object.__getattribute__(arena.bindings, "_data"),
        )[key] = replace(binding, original_extent=True)
    elif fault in ("foreign-source", "foreign-quotient"):
        other, _, _, other_source, other_quotient = setup()
        if fault == "foreign-source":
            runtime.ledger.reserve(arena.bindings.owner, entries=1)
            cast(
                MutableMapping[object, object],
                object.__getattribute__(arena.bindings, "_data"),
            )[PrimitiveMacroKey(kernel, other_source)] = binding
        else:
            cast(
                MutableMapping[object, object],
                object.__getattribute__(arena.bindings, "_data"),
            )[key] = replace(binding, quotient=other_quotient)
        assert other.ledger is not runtime.ledger
    else:
        runtime.ledger.reserve(arena.bindings.owner, entries=1)
        cast(
            MutableMapping[object, object],
            object.__getattribute__(arena.bindings, "_data"),
        )[PrimitiveMacroKey(replace(kernel, kind="diamond-action"), source)] = binding
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0
    assert runtime.ledger.snapshot() == before


def test_observation_request_result_pair_cannot_enter_a_retained_macro_store() -> None:
    runtime, _arena, _, _, quotient = setup()
    owner = runtime.ledger.register("forged-primitive-output-cache", "query_memo")
    records: LedgerDict[object, object]
    records = runtime.ledger.make_dict(owner)
    runtime.ledger.reserve(owner, entries=1)
    records[PrimitiveMacroObservation(quotient, "output", 0, 0, 0)] = 1
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0
    assert runtime.ledger.snapshot() == before


def test_original_extent_is_reconstructed_from_original_dag_not_trusted_record() -> (
    None
):
    runtime, arena, kernel, source, quotient = setup()
    assert arena.bindings[PrimitiveMacroKey(kernel, source)] == PrimitiveMacroBinding(
        quotient, 3
    )
    # A valid QID with a changed geometry record is still not an admitted source binding.
    cast(
        MutableMapping[object, object], object.__getattribute__(arena.bindings, "_data")
    )[PrimitiveMacroKey(kernel, source)] = PrimitiveMacroBinding(quotient, 4)
    report = collect_ledger_metrics(runtime.ledger)
    assert report.forbidden_future_payloads > 0
