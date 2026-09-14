from __future__ import annotations

import gc
import weakref
from dataclasses import dataclass

from number_compiler.hashlife.execution.source_image_seals import (
    PublicationSeals,
    publication_matches,
    publication_seal,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True, weakref_slot=True)
class _Leaf:
    values: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _Envelope:
    leaf: _Leaf


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
