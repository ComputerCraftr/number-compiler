"""A cached hash accelerates lookup; it cannot attest a semantic signature."""

from __future__ import annotations

from collections.abc import Callable, Hashable
from typing import Never, TypeVar, cast

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.semantic_payload import SemanticPayloadRegistry
from number_compiler.resources.stores import LedgerDict

KeyT = TypeVar("KeyT", bound=Hashable)
ValueT = TypeVar("ValueT")


@pytest.mark.parametrize(
    "mutation", ("integer", "boolean", "callback", "changed-input", "changed-output")
)
def test_forged_or_stale_signature_hash_rejects_before_any_interner_lookup(
    monkeypatch: pytest.MonkeyPatch, mutation: str
) -> None:
    ledger = ResourceLedger()
    arena = SemanticFunctionArena(ledger)
    signature = FunctionSignature((), BOOL)
    handle = arena.atom(signature, 0)
    original = (
        signature.inputs,
        signature.output,
        object.__getattribute__(signature, "_hash"),
    )

    class Callback:
        def __hash__(self) -> Never:
            raise AssertionError("forged cached hash was executed")

        def __eq__(self, other: object) -> Never:
            raise AssertionError("forged cached hash was compared")

    if mutation == "changed-input":
        object.__setattr__(
            signature, "inputs", (FinitePort(PortVariable(0, 0, "added", 0), 2),)
        )
    elif mutation == "changed-output":
        object.__setattr__(signature, "output", AtomSort("changed", 2))
    else:
        value = (
            object.__getattribute__(signature, "_hash") + 1
            if mutation == "integer"
            else True
            if mutation == "boolean"
            else Callback()
        )
        object.__setattr__(signature, "_hash", value)
    before = ledger.snapshot()
    old_get = object.__getattribute__(LedgerDict, "__getitem__")

    def lookup(store: LedgerDict[KeyT, ValueT], key: KeyT) -> ValueT:
        if store is arena.keys:
            raise AssertionError("invalid signature reached the semantic interner")
        original = cast(Callable[[LedgerDict[KeyT, ValueT], KeyT], ValueT], old_get)
        return original(store, key)

    monkeypatch.setattr(LedgerDict, "__getitem__", lookup)
    try:
        with pytest.raises(ValueError, match="forged or stale cached hash"):
            arena.atom(signature, 0)
        diamond = DiamondPayloadRegistry(ledger)
        audit = SemanticPayloadRegistry(
            ledger, lambda value: False, diamond.valid_handle
        )
        assert not audit.valid(signature)
        assert not audit.valid(handle)
        assert ledger.snapshot() == before
    finally:
        for name, original_value in zip(
            ("inputs", "output", "_hash"), original, strict=True
        ):
            object.__setattr__(signature, name, original_value)


def test_valid_cached_hash_collision_still_uses_complete_signature_equality(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.functions.finite_function_types as semantic

    def collision(_sort: object) -> int:
        return 7

    monkeypatch.setattr(semantic, "_sort_hash", collision)
    first = FunctionSignature((), AtomSort("first", 2))
    second = FunctionSignature((), AtomSort("second", 2))
    assert hash(first) == hash(second)
    assert first != second
    arena = SemanticFunctionArena(ResourceLedger())
    assert arena.atom(first, 0) != arena.atom(second, 0)
