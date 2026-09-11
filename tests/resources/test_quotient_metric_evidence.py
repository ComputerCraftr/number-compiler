"""Canonical-normal-form hits are distinct from parent and late interner work."""

from dataclasses import fields
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondKey,
    DiamondQuotientArena,
    MacroComponents,
    MacroInterface,
)
from number_compiler.resources.metric_collection import (
    collect_ledger_metrics,
    ledger_metric_values,
)
from tests.support.diamond_continuation_reduction import machine


def test_early_normal_form_counter_is_reported_from_actual_work_without_new_retention(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, _ = machine()
    functions = SemanticFunctionArena(runtime.ledger)
    arena = DiamondQuotientArena(functions, runtime.cells)
    signature = FunctionSignature((), BOOL)
    zero, one = functions.atom(signature, 0), functions.atom(signature, 1)
    interface = arena.intern_interface(
        MacroInterface(
            SemanticIdentity("metric-fixture", ("finite-constant",)),
            (),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
        )
    )
    quotient = arena.intern(
        interface, MacroComponents(*(zero for _ in COMPONENT_ROLES))
    )
    normalized = arena.resolve(quotient).components
    before = collect_ledger_metrics(runtime.ledger)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("canonical-normal-form hit performed normalization")

    monkeypatch.setattr(arena, "_prepare_normalization", forbidden)
    assert arena.intern(interface, normalized) == quotient
    after = collect_ledger_metrics(runtime.ledger)
    assert (
        after.quotient_normal_form_early_hits
        == before.quotient_normal_form_early_hits + 1
    )
    assert (
        after.quotient_complete_normalizations
        == before.quotient_complete_normalizations
    )
    assert (
        after.quotient_semantic_interner_hits == before.quotient_semantic_interner_hits
    )
    assert after.quotient_parent_early_hits == before.quotient_parent_early_hits
    assert after.resource_ledger_entries == before.resource_ledger_entries
    assert after.resource_ledger_nodes == before.resource_ledger_nodes
    assert after.resource_inventory == before.resource_inventory
    assert (
        after.quotient_normal_form_early_hits
        == runtime.ledger.counters["quotient_normal_form_early_hits"]
    )
    assert (
        ledger_metric_values(runtime.ledger)["quotient_normal_form_early_hits"]
        == after.quotient_normal_form_early_hits
    )
    assert "quotient_normal_form_early_hits" in {item.name for item in fields(after)}
    cell = runtime.cells.source_span(0, 2)[0][1]
    key = DiamondKey(quotient, quotient, cell, 1, 0, 0, interface)
    assert arena.probe(key) is None
    assert arena.normalize_and_publish(key, normalized) == quotient
    published = collect_ledger_metrics(runtime.ledger)
    assert (
        published.quotient_normal_form_early_hits
        == after.quotient_normal_form_early_hits + 1
    )
    assert (
        published.quotient_semantic_interner_hits
        == after.quotient_semantic_interner_hits
    )
    assert (
        published.quotient_complete_normalizations
        == after.quotient_complete_normalizations
    )
    assert (
        published.quotient_parent_publications == after.quotient_parent_publications + 1
    )
    assert arena.probe(key) == quotient
    warm = collect_ledger_metrics(runtime.ledger)
    assert warm.quotient_parent_early_hits == published.quotient_parent_early_hits + 1
    assert (
        warm.quotient_normal_form_early_hits
        == published.quotient_normal_form_early_hits
    )
