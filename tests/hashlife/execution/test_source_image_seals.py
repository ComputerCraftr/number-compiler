from __future__ import annotations

import gc
import weakref
from dataclasses import dataclass
from enum import Enum

import pytest

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.fields.symbolic_innovation import InnovationID
from number_compiler.hashlife.execution.source_image_seals import (
    PublicationSeals,
    _TypedKey,
    publication_matches,
    publication_seal,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.powered_local_codec import CollatzLocalActionID
from number_compiler.sequences.reverse_add.powered_local_codec import (
    ReverseLocalActionID,
)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class _Leaf:
    values: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _Envelope:
    leaf: _Leaf


@dataclass(frozen=True, slots=True, eq=False)
class _CompatibleToken:
    label: str = ""


@dataclass(frozen=True, slots=True)
class _MutablePayloadHandle(ArenaHandle):
    payload: object = None


_MutableEnum = Enum("_MutableEnum", {"ITEM": [1]})


def test_warm_validation_skips_large_immutable_primitive_tuple() -> None:
    ledger = ResourceLedger()
    leaf = _Leaf(tuple(range(10_000)))
    root = (_Envelope(leaf), 7)
    seal = publication_seal(root, ledger)
    creation = ledger.counters["source_image_seal_creation_visits"]
    assert publication_matches(root, seal, ledger)
    assert creation > 10_000
    assert ledger.counters["source_image_seal_validation_visits"] == 3


def test_nested_mutation_and_equal_replacement_are_rejected() -> None:
    ledger = ResourceLedger()
    leaf = _Leaf((1, 2, 3))
    envelope = _Envelope(leaf)
    seal = publication_seal((envelope,), ledger)
    object.__setattr__(leaf, "values", (1, 2, 4))
    assert not publication_matches((envelope,), seal, ledger)
    object.__setattr__(leaf, "values", (1, 2, 3))
    replacement = _Leaf((1, 2, 3))
    object.__setattr__(envelope, "leaf", replacement)
    assert not publication_matches((envelope,), seal, ledger)


def test_flat_guard_keeps_the_original_untraversed_owner_type() -> None:
    ledger = ResourceLedger()
    owner = ArenaToken("source")
    handle = ArenaHandle(owner, "node", 0)
    seal = publication_seal((handle,), ledger)
    assert publication_matches((handle,), seal, ledger)
    # The owner is identity-anchored inside the handle guard; it is not
    # recursively traversed. A compatible in-place class mutation must still
    # fail against the separately pinned original type.
    object.__setattr__(owner, "__class__", _CompatibleToken)
    assert not publication_matches((handle,), seal, ledger)


@pytest.mark.parametrize("handle_type", (ReverseLocalActionID, CollatzLocalActionID))
def test_subclass_transform_is_sealed_and_part_of_typed_identity(
    handle_type: type[ReverseLocalActionID | CollatzLocalActionID],
) -> None:
    owner = ArenaToken("source")
    original = handle_type(owner, "action", 0, ActionTransform.IDENTITY)
    mirrored = handle_type(owner, "action", 0, ActionTransform.MIRROR)
    assert _TypedKey(original) != _TypedKey(mirrored)
    assert len({_TypedKey(original): 1, _TypedKey(mirrored): 2}) == 2
    ledger = ResourceLedger()
    seal = publication_seal((original,), ledger)
    assert publication_matches((original,), seal, ledger)
    object.__setattr__(original, "transform", ActionTransform.MIRROR)
    assert not publication_matches((original,), seal, ledger)


def test_innovation_seal_is_sealed_and_part_of_typed_identity() -> None:
    owner = ArenaToken("source")
    first = InnovationID(owner, "innovation", 0, "first")
    second = InnovationID(owner, "innovation", 0, "second")
    assert _TypedKey(first) != _TypedKey(second)
    ledger = ResourceLedger()
    seal = publication_seal((first,), ledger)
    object.__setattr__(first, "seal", "second")
    assert not publication_matches((first,), seal, ledger)


def test_typed_handle_key_rejects_unsupported_mutable_subclass_field() -> None:
    handle = _MutablePayloadHandle(ArenaToken("source"), "node", 0, [1])
    with pytest.raises(TypeError, match="structural immutable key"):
        _TypedKey(handle)
    enum_handle = _MutablePayloadHandle(
        ArenaToken("source"), "node", 0, _MutableEnum.ITEM
    )
    with pytest.raises(TypeError, match="structural immutable key"):
        _TypedKey(enum_handle)


def test_identity_anchors_pin_replaced_nested_objects() -> None:
    ledger = ResourceLedger()
    leaf = _Leaf((1,))
    reference = weakref.ref(leaf)
    envelope = _Envelope(leaf)
    seal = publication_seal((envelope,), ledger)
    object.__setattr__(envelope, "leaf", _Leaf((1,)))
    del leaf
    gc.collect()
    assert reference() is not None
    assert not publication_matches((envelope,), seal, ledger)


def test_expected_seal_is_intrinsically_immutable() -> None:
    seal = publication_seal((_Leaf((1,)),), ResourceLedger())
    try:
        object.__setattr__(seal, "root", ("forged",))
    except AttributeError:
        pass
    else:
        raise AssertionError("publication seal accepted reflected mutation")


def test_seal_registry_uses_ledger_created_visible_stores() -> None:
    ledger = ResourceLedger()
    registry = PublicationSeals(ledger, "seal-registry-test")
    image = publication_seal((_Leaf((1, 2)),), ledger)
    projection = publication_seal((_Envelope(_Leaf((3,))),), ledger)
    registry.append_image(image)
    registry.put_projection(("projection", 0), projection)
    assert ledger.is_factory_container(registry.images)
    assert ledger.is_factory_container(registry.projections)
    containers = dict(ledger.iter_containers())
    assert any(container is registry.images for container in containers.values())
    assert any(container is registry.projections for container in containers.values())
    rows = [
        row for row in ledger.inventory() if row.role == "source_image_publication_seal"
    ]
    assert len(rows) == 2
    assert all(row.entries == 1 and row.nodes > 0 for row in rows)
    assert all(row.accounting_delta == 0 for row in rows)
    registry.clear()
    assert all(row.entries == row.nodes == 0 for row in ledger.inventory())


def test_root_tuple_anchors_are_charged_even_without_mutable_guards() -> None:
    ledger = ResourceLedger()
    registry = PublicationSeals(ledger, "root-anchors")
    small = publication_seal((1,), ledger)
    large = publication_seal(tuple(range(4096)), ledger)
    assert not large.guards
    assert large.retained_nodes >= small.retained_nodes + 2 * 4095
    registry.append_image(large)
    assert sum(row.nodes for row in ledger.inventory()) >= large.retained_nodes
    assert all(row.accounting_delta == 0 for row in ledger.inventory())
    registry.clear()
    assert all(row.nodes == 0 for row in ledger.inventory())


def test_tuple_anchor_budget_is_checked_before_allocation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.hashlife.execution import source_image_seals

    def forbidden_anchor(_value: object) -> object:
        raise AssertionError("anchor allocation preceded budget admission")

    monkeypatch.setattr(source_image_seals, "_root_anchor", forbidden_anchor)
    ledger = ResourceLedger(max_nodes=20)
    with pytest.raises(BlockContextBudgetExceeded):
        publication_seal(tuple(range(4096)), ledger)
    assert ledger.nodes == 0
