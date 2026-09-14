"""Actual semantic containers must not acquire authority from record names."""

from __future__ import annotations

from typing import Literal

import pytest

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemanticsAdapter,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.semantic_payload import SemanticPayloadRegistry


def _registry(
    ledger: ResourceLedger,
) -> SemanticPayloadRegistry:
    diamond = DiamondPayloadRegistry(ledger)
    return SemanticPayloadRegistry(ledger, lambda value: False, diamond._handle)


class _EqualToEverything:
    def __init__(self) -> None:
        self.calls = 0

    def __eq__(self, other: object) -> bool:
        self.calls += 1
        return True


def test_terminal_opcode_admission_never_executes_a_payload_equality_callback() -> None:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    function = functions.invalid(FunctionSignature((), BOOL))
    terminal = functions.resolve(function).terminal
    assert terminal is not None
    callback = _EqualToEverything()
    object.__setattr__(terminal, "kind", callback)
    try:
        registry = _registry(ledger)
        assert callback.calls == 0, (
            "semantic audit executed a retained payload callback"
        )
        assert not registry.valid(function)
        assert not registry.valid(terminal)
    finally:
        object.__setattr__(terminal, "kind", "invalid")


@pytest.mark.parametrize("field", ("low", "high"))
def test_terminal_child_sentinels_require_exact_integers(
    field: Literal["high", "low"],
) -> None:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    function = functions.atom(FunctionSignature((), BOOL), 0)
    node = functions.resolve(function)
    object.__setattr__(node, field, -1.0)
    try:
        assert not _registry(ledger).valid(function)
    finally:
        object.__setattr__(node, field, -1)


@pytest.mark.parametrize(
    "field,value",
    (
        ("initial_left", 1 << 1000),
        ("initial_right", True),
        ("base", 17),
        ("blank", 1 << 1000),
        ("blank_left_tail", 1 << 1000),
        ("blank_right_tail", -1),
        ("stable_blank_output", lambda: 0),
        ("left_sort", AtomSort("wrong-left", 1)),
        ("symbol_sort", AtomSort("wrong-symbol", 2)),
        ("right_sort", AtomSort("wrong-right", 1)),
    ),
    ids=(
        "initial-left",
        "initial-right",
        "base",
        "blank",
        "left-tail",
        "right-tail",
        "stable-output",
        "left-sort",
        "symbol-sort",
        "right-sort",
    ),
)
def test_primitive_record_checks_every_declared_domain_and_definition_field(
    field: Literal[
        "base",
        "blank",
        "blank_left_tail",
        "blank_right_tail",
        "initial_left",
        "initial_right",
        "left_sort",
        "right_sort",
        "stable_blank_output",
        "symbol_sort",
    ],
    value: object,
) -> None:
    ledger = ResourceLedger()
    adapter = PrimitiveSemanticsAdapter(
        DiamondKernelArena(ledger), SemanticFunctionArena(ledger)
    )
    record = adapter.compile(NonblankBlockEffect(2, 2))
    assert _registry(ledger).valid(record)
    original = getattr(record, field)
    object.__setattr__(record, field, value)
    try:
        assert not _registry(ledger).valid(record)
    finally:
        object.__setattr__(record, field, original)


def test_primitive_port_bundle_is_immutable_and_complete() -> None:
    ledger = ResourceLedger()
    adapter = PrimitiveSemanticsAdapter(
        DiamondKernelArena(ledger), SemanticFunctionArena(ledger)
    )
    record = adapter.compile(NonblankBlockEffect(2, 2))
    original = record.ports
    object.__setattr__(record, "ports", list(original))
    try:
        assert not _registry(ledger).valid(record)
    finally:
        object.__setattr__(record, "ports", original)


@pytest.mark.parametrize("foreign", (False, True))
def test_primitive_channel_function_requires_its_actual_owner_and_full_signature(
    foreign: bool,
) -> None:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    adapter = PrimitiveSemanticsAdapter(DiamondKernelArena(ledger), functions)
    record = adapter.compile(NonblankBlockEffect(2, 2))
    arena = SemanticFunctionArena(ledger) if foreign else functions
    signature = (
        functions.signature(record.emit) if foreign else FunctionSignature((), BOOL)
    )
    wrong = arena.atom(signature, 0)
    original = record.emit
    object.__setattr__(record, "emit", wrong)
    try:
        assert not _registry(ledger).valid(record)
    finally:
        object.__setattr__(record, "emit", original)


def test_decision_support_never_executes_a_payload_equality_callback() -> None:
    from number_compiler.arithmetic.functions.finite_function_types import FinitePort
    from number_compiler.arithmetic.functions.finite_port_action import PortVariable

    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    port = FinitePort(PortVariable(0, 0, "input", 0), 2)
    function = functions.variable((port,), port, BOOL)
    node = functions.resolve(function)
    original = node.support
    callback = _EqualToEverything()
    object.__setattr__(node, "support", (callback,))
    try:
        registry = _registry(ledger)
        assert callback.calls == 0, (
            "semantic audit executed a retained support callback"
        )
        assert not registry.valid(function)
    finally:
        object.__setattr__(node, "support", original)


def test_semantic_request_requires_operation_arity_and_same_arena_roots() -> None:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticRequest,
    )

    ledger = ResourceLedger()
    first = SemanticFunctionArena(ledger)
    second = SemanticFunctionArena(ledger)
    a = first.atom(FunctionSignature((), BOOL), 0)
    b = second.atom(FunctionSignature((), BOOL), 1)
    registry = _registry(ledger)
    assert not registry.valid(SemanticRequest("ite", ()))
    assert not registry.valid(SemanticRequest("ite", (a, a, b)))


def test_forged_semantic_owner_cannot_execute_hash_during_audit() -> None:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
    )

    class HashCallback:
        def __init__(self) -> None:
            self.calls = 0

        def __hash__(self) -> int:
            self.calls += 1
            return 0

    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    valid = functions.atom(FunctionSignature((), BOOL), 0)
    forged = object.__new__(SemanticFunctionID)
    owner = HashCallback()
    object.__setattr__(forged, "owner", owner)
    object.__setattr__(forged, "kind", valid.kind)
    object.__setattr__(forged, "local_id", valid.local_id)
    assert not _registry(ledger).valid(forged)
    assert owner.calls == 0
