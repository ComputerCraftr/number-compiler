"""Universal conversion caches must preserve the complete source function."""

from typing import Never, cast

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics


@pytest.mark.parametrize("kind", ("constant", "variable", "partial"))
def test_scalar_conversion_full_function_agreement_audit_is_read_only(
    kind: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    arena = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "input", 0), 3)
    source = (
        arena.functions.atom(FunctionSignature((port,), BOOL), 1)
        if kind == "constant"
        else arena.functions.invalid(FunctionSignature((port,), BOOL))
        if kind == "partial"
        else arena.functions.variable((port,), port)
    )
    arena.from_scalar(source)
    before = arena.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("inventory audit executed or rebuilt a semantic function")

    monkeypatch.setattr(arena.functions, "evaluate", forbidden)
    monkeypatch.setattr(arena, "from_scalar", forbidden)
    report = collect_ledger_metrics(arena.ledger)
    assert report.resource_audit_complete == 1
    assert report.forbidden_future_payloads == 0
    assert arena.ledger.snapshot() == before


@pytest.mark.parametrize(
    "wrong", ("same-signature-value", "same-ledger-owner", "wrong-signature")
)
def test_actual_scalar_conversion_binding_rejects_foreign_or_inequivalent_target(
    wrong: str,
) -> None:
    arena = BitFunctionArena(ResourceLedger())
    signature = FunctionSignature((), BOOL)
    source = arena.functions.atom(signature, 0)
    arena.from_scalar(source)
    other = (
        BitFunctionArena(arena.ledger, arena.functions)
        if wrong == "same-ledger-owner"
        else arena
    )
    if wrong == "wrong-signature":
        port = FinitePort(PortVariable(0, 0, "extra", 0), 2)
        signature = FunctionSignature((port,), BOOL)
    result = other.constant(signature, 1)
    scalar_sources = cast(
        OwnedMemo[SemanticFunctionID, FactoredFunctionID],
        object.__getattribute__(arena, "_scalar_sources"),
    )
    scalar_sources[source] = result
    before = arena.ledger.snapshot()
    report = collect_ledger_metrics(arena.ledger)
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0
    assert arena.ledger.snapshot() == before
