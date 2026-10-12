"""Runtime construction aborts only resources created inside its scope."""

from __future__ import annotations

from contextvars import Context, copy_context
from typing import Never
from weakref import ReferenceType, ref

import pytest

from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict


class _ExecutionRoot:
    pass


def _owned_value(ledger: ResourceLedger, name: str) -> tuple[int, LedgerDict[str, str]]:
    owner = ledger.register(name, "construction_test_owner")
    store: LedgerDict[str, str] = ledger.make_dict(owner, nodes_per_entry=1)
    ledger.reserve(owner, entries=1, nodes=1)
    store["value"] = name
    return owner, store


def test_abort_preserves_unrelated_owners_created_before_scope_entry() -> None:
    ledger = ResourceLedger()
    construction = RuntimeConstruction(ledger)
    unrelated_owner, unrelated_store = _owned_value(ledger, "unrelated")
    unrelated_root = _ExecutionRoot()
    ledger.register_execution_root(unrelated_root)

    with pytest.raises(RuntimeError, match="abort construction"), construction:
        owned_owner, owned_store = _owned_value(ledger, "owned")
        owned_root = _ExecutionRoot()
        ledger.register_execution_root(owned_root)
        raise RuntimeError("abort construction")

    inventory = {row.owner: row for row in ledger.inventory()}
    assert inventory[unrelated_owner].entries == 1
    assert inventory[unrelated_owner].nodes == 1
    assert unrelated_store["value"] == "unrelated"
    assert inventory[owned_owner].disposed
    assert not owned_store
    assert tuple(ledger.iter_execution_roots()) == (unrelated_root,)
    assert ledger.entries == ledger.nodes == 1


def test_abort_preserves_owner_registered_in_independent_context() -> None:
    ledger = ResourceLedger()
    unrelated: dict[str, object] = {}
    scope = RuntimeConstruction(ledger)

    def register_unrelated() -> None:
        owner, store = _owned_value(ledger, "independent-context")
        root = _ExecutionRoot()
        ledger.register_execution_root(root)
        unrelated.update(owner=owner, store=store, root=root)

    with pytest.raises(RuntimeError, match="abort construction"), scope:
        Context().run(register_unrelated)
        raise RuntimeError("abort construction")

    owner = unrelated["owner"]
    store = unrelated["store"]
    root = unrelated["root"]
    assert type(owner) is int and isinstance(store, LedgerDict)
    assert store["value"] == "independent-context"
    assert tuple(ledger.iter_execution_roots()) == (root,)
    assert not ledger.inventory()[owner].disposed
    assert ledger.entries == ledger.nodes == 1


def test_nested_abort_is_scoped_and_outer_abort_includes_successful_child() -> None:
    ledger = ResourceLedger()
    with pytest.raises(RuntimeError, match="abort outer"), RuntimeConstruction(ledger):
        outer_owner, outer_store = _owned_value(ledger, "outer")
        with (
            pytest.raises(RuntimeError, match="abort inner"),
            RuntimeConstruction(ledger),
        ):
            inner_owner, inner_store = _owned_value(ledger, "inner")
            raise RuntimeError("abort inner")
        assert ledger.inventory()[inner_owner].disposed
        assert not inner_store

        with RuntimeConstruction(ledger):
            child_owner, child_store = _owned_value(ledger, "successful-child")
        assert ledger.inventory()[child_owner].entries == 1
        assert child_store["value"] == "successful-child"
        raise RuntimeError("abort outer")

    inventory = {row.owner: row for row in ledger.inventory()}
    assert inventory[outer_owner].disposed and not outer_store
    assert inventory[child_owner].disposed and not child_store
    assert inventory[inner_owner].disposed
    assert ledger.entries == ledger.nodes == 0


def test_out_of_order_manual_exit_does_not_mutate_scopes() -> None:
    ledger = ResourceLedger()
    outer = RuntimeConstruction(ledger)
    inner = RuntimeConstruction(ledger)
    outer.__enter__()
    outer_owner, outer_store = _owned_value(ledger, "outer-lifo")
    inner.__enter__()
    inner_owner, inner_store = _owned_value(ledger, "inner-lifo")

    with pytest.raises(RuntimeError, match="LIFO"):
        outer.__exit__(RuntimeError, RuntimeError("out of order"), None)

    assert not ledger.inventory()[outer_owner].disposed
    assert not ledger.inventory()[inner_owner].disposed
    assert outer_store["value"] == "outer-lifo"
    assert inner_store["value"] == "inner-lifo"
    inner.__exit__(None, None, None)
    outer.__exit__(RuntimeError, RuntimeError("abort outer"), None)

    assert ledger.inventory()[outer_owner].disposed
    assert ledger.inventory()[inner_owner].disposed
    assert ledger.entries == ledger.nodes == 0


def test_copied_context_cannot_abort_origin_scope() -> None:
    ledger = ResourceLedger()
    scope = RuntimeConstruction(ledger)
    scope.__enter__()
    owner, store = _owned_value(ledger, "origin-context")

    with pytest.raises(ValueError, match="different Context"):
        copy_context().run(
            scope.__exit__, RuntimeError, RuntimeError("copied exit"), None
        )

    assert not ledger.inventory()[owner].disposed
    assert store["value"] == "origin-context"
    assert scope._token is not None
    scope.__exit__(RuntimeError, RuntimeError("origin abort"), None)
    assert ledger.inventory()[owner].disposed
    assert ledger.entries == ledger.nodes == 0


def test_abort_does_not_expire_replacement_execution_root() -> None:
    ledger = ResourceLedger()
    scope = RuntimeConstruction(ledger)
    root = _ExecutionRoot()
    scope.__enter__()
    ledger.register_execution_root(root)
    identity = id(root)
    old_reference = ledger._execution_roots[identity]

    replacement = _ExecutionRoot()
    replacement_reference: ReferenceType[object] = ref(
        replacement,
        lambda _reference: None,
    )
    ledger._execution_roots[identity] = replacement_reference
    scope.__exit__(RuntimeError, RuntimeError("abort"), None)

    assert ledger._execution_roots[identity] is replacement_reference
    ledger._expire_execution_root(identity, old_reference)
    assert ledger._execution_roots[identity] is replacement_reference


def test_scope_bookkeeping_allocation_failure_does_not_publish_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scope = RuntimeConstruction(ledger)
    before = ledger.owner_count
    original = scope._record_owner

    def fail_after_record(owner: int) -> Never:
        original(owner)
        raise MemoryError("scope owner bookkeeping failed")

    with scope:
        monkeypatch.setattr(scope, "_record_owner", fail_after_record)
        with pytest.raises(MemoryError, match="bookkeeping"):
            ledger.register("not-published", "construction_test_owner")

    assert ledger.owner_count == before
    assert not scope._owners
    assert ledger.entries == ledger.nodes == 0
