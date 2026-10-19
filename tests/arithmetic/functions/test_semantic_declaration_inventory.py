"""Declaration bindings need independent semantic and lexical agreement."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    BooleanCircuit,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_structures import (
        StructureID,
    )


def fixture(
    width: int = 3,
) -> tuple[StructureArena, FinitePort, FinitePort, StructureID]:
    bits = BitFunctionArena(ResourceLedger())
    arena = StructureArena(bits)
    x = FinitePort(PortVariable(0, 0, "x", 0), width)
    y = FinitePort(PortVariable(0, 0, "y", 0), 3)
    sort = AtomSort("value", width)
    value = arena.atom(bits.variable((x,), x, sort))
    return arena, x, y, value


@pytest.mark.parametrize("kind", ("atom", "product", "function", "nested", "wide"))
def test_declaration_audit_transports_binders_and_checks_padding_without_execution(
    kind: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    arena, x, y, value = fixture(1 << 64 if kind == "wide" else 3)
    if kind in ("function", "nested"):
        value = arena.curry(value, (x,))
        # New free input collides with the old canonical internal binder.
        alias = arena.resolve(value).bound[0]
        y = FinitePort(alias.variable, 3)
        if kind == "nested":
            value = arena.declare(value, (y,))
            value = arena.curry(value, (y,))
            y = FinitePort(arena.resolve(value).bound[0].variable, 3)
    if kind == "product":
        value = arena.product((value, value))
    inputs = tuple(
        sorted(
            (*arena.resolve(value).signature.inputs, y), key=lambda port: port.variable
        )
    )
    result = arena.declare(value, inputs)
    assert arena.declare(value, inputs) == result
    before = arena.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("inventory executed a producer or scalar observation")

    monkeypatch.setattr(arena, "declare", forbidden)
    monkeypatch.setattr(arena, "substitute", forbidden)
    monkeypatch.setattr(arena, "evaluate_atom", forbidden)
    monkeypatch.setattr(arena.bits.functions, "evaluate", forbidden)
    report = collect_ledger_metrics(arena.ledger)
    assert report.forbidden_future_payloads == 0
    assert report.resource_audit_complete == 1
    assert report.semantic_structure_declaration_cache_entries == len(
        arena._declarations
    )
    for suffix in ("requests", "identity_hits", "early_hits", "evaluations"):
        name = "semantic_structure_declaration_" + suffix
        assert getattr(report, name) == arena.ledger.counters.get(name, 0)
    assert arena.ledger.snapshot() == before


@pytest.mark.parametrize(
    "mode",
    (
        "wrong-value",
        "foreign-source",
        "foreign-target",
        "missing-input",
        "changed-domain",
        "mutable-inputs",
        "boolean-cardinality",
    ),
)
def test_injected_declaration_binding_requires_actual_owner_interface_and_values(
    mode: str,
) -> None:
    arena, x, y, value = fixture()
    result = arena.declare(value, (x, y))
    key = next(iter(arena._declarations))
    if mode == "wrong-value":
        result = arena.atom(arena.bits.constant(arena.resolve(result).signature, 0))
    elif mode.startswith("foreign"):
        foreign = StructureArena(arena.bits)
        replacement = foreign.atom(
            arena.bits.constant(
                arena.resolve(result if mode == "foreign-target" else value).signature,
                0,
            )
        )
        if mode == "foreign-target":
            result = replacement
        else:
            key = replace(key, value=replacement)
    elif mode == "missing-input":
        key = replace(key, inputs=(y,))
    elif mode == "changed-domain":
        key = replace(key, inputs=(replace(x, cardinality=4), y))
    elif mode == "mutable-inputs":
        object.__setattr__(key, "inputs", list(key.inputs))
    else:
        object.__setattr__(y, "cardinality", True)
    if mode not in ("mutable-inputs", "boolean-cardinality"):
        if key not in arena._declarations:
            arena.ledger.reserve(arena._declarations.owner, entries=1)
        arena._declarations._data[key] = result
    before = arena.ledger.snapshot()
    report = collect_ledger_metrics(arena.ledger)
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0
    assert arena.ledger.snapshot() == before


def test_declaration_audit_rejects_unmasked_extra_port_storage_codes() -> None:
    arena, x, y, _ = fixture()
    value = arena.atom(arena.bits.constant(FunctionSignature((x,), BOOL), 1))
    arena.declare(value, (x, y))
    key = next(iter(arena._declarations))
    circuit = BooleanCircuit(arena.functions, (x, y))
    one = circuit.one
    raw = circuit.normalized(FunctionSignature((x, y), BOOL), (one,), one)
    bad = arena.atom(arena.bits.publish_circuit(circuit, (raw,))[0])
    arena._declarations._data[key] = bad
    before = arena.ledger.snapshot()
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0
    assert arena.ledger.snapshot() == before


def test_declaration_audit_rejects_wrong_function_body_with_identical_complete_sort() -> (
    None
):
    arena, x, y, value = fixture()
    function = arena.curry(value, (x,))
    arena.declare(function, (y,))
    key = next(iter(arena._declarations))
    zero = arena.atom(arena.bits.constant(arena.resolve(value).signature, 0))
    wrong = arena.declare(arena.curry(zero, (x,)), (y,))
    assert (
        arena.resolve(wrong).signature
        == arena.resolve(arena._declarations[key]).signature
    )
    arena._declarations._data[key] = wrong
    before = arena.ledger.snapshot()
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0
    assert arena.ledger.snapshot() == before
