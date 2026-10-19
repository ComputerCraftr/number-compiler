"""Per-list authority revisions include adversarial backing mutations."""

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList


@pytest.mark.parametrize(
    "mutation",
    (
        "append",
        "extend",
        "set",
        "delete",
        "clear",
        "insert",
        "pop",
        "remove",
        "reverse",
        "imul",
    ),
)
def test_backing_mutators_invalidate_local_and_global_revisions(mutation: str) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("test.revision", "test revision")
    store: LedgerList[int] = ledger.make_list(owner, append_only=True)
    ledger.reserve(owner, entries=3, nodes=3)
    store.extend((1, 2, 3))
    identity, version = store.mutation_stamp
    global_version = ledger.mutation_version
    backing = store._data
    if mutation == "append":
        backing.append(4)
    elif mutation == "extend":
        backing.extend((4, 5))
    elif mutation == "set":
        backing[1] = 7
    elif mutation == "delete":
        del backing[1]
    elif mutation == "clear":
        backing.clear()
    elif mutation == "insert":
        backing.insert(1, 7)
    elif mutation == "pop":
        backing.pop()
    elif mutation == "remove":
        backing.remove(2)
    elif mutation == "reverse":
        backing.reverse()
    else:
        backing.__imul__(2)
    assert store.mutation_stamp == (identity, version + 1)
    assert ledger.mutation_version == global_version + 1


def test_revision_is_read_only_and_unrelated_stores_do_not_invalidate_it() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("test.revision", "test revision")
    store: LedgerList[int] = ledger.make_list(owner, append_only=True)
    stamp = store.mutation_stamp
    foreign_owner = ledger.register("test.foreign", "test revision")
    foreign: LedgerList[int] = ledger.make_list(foreign_owner, append_only=True)
    ledger.reserve(foreign_owner, entries=1, nodes=1)
    foreign.append(1)
    assert store.mutation_stamp == stamp
    read_only_attribute = "mutation_stamp"
    with pytest.raises(AttributeError, match="immutable"):
        setattr(store, read_only_attribute, (object(), 0))
    with pytest.raises(TypeError, match="in-place sorting"):
        store._data.sort()
    with pytest.raises(TypeError, match="in-place addition"):
        store._data.__iadd__((1,))
    with pytest.raises(TypeError, match="concatenated backing"):
        store._data.__add__([1])
    object.__setattr__(store, "_data", foreign._data)
    assert store.mutation_stamp[0] is not stamp[0]


def test_append_rolls_back_postmutation_hook_failure_without_masking_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("test.append-rollback", "test append rollback")
    store: LedgerList[object] = ledger.make_list(owner, append_only=False)
    ledger.reserve(owner, entries=2, nodes=2)
    existing = object()
    attempted = object()
    store.append(existing)
    identity, version = store.mutation_stamp
    calls = 0

    def fail_invalidation() -> None:
        nonlocal calls
        calls += 1
        raise RuntimeError("mutation invalidation failed")

    monkeypatch.setattr(ledger, "note_store_mutation", fail_invalidation)
    with pytest.raises(RuntimeError, match="mutation invalidation failed"):
        store.append(attempted)

    assert calls == 2
    assert store.snapshot() == (existing,)
    assert len(store) == 1
    assert store.mutation_stamp[0] is identity
    assert store.mutation_stamp[1] == version + 2
    assert ledger.entries == 2
