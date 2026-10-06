"""Exact family-owned bindings used by the reverse source payload audit."""

from __future__ import annotations

from typing import cast

from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding


def source_audit_owners(roots: tuple[object, ...]) -> set[int]:
    """List only ledger owners reached by one source-image family root."""
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    owners: set[int] = set()

    def add_store(store: object) -> None:
        owner = getattr(store, "owner", None)
        if type(owner) is int:
            owners.add(owner)

    for root in roots:
        if type(root) is SourceCarryPorts:
            add_store(root._cache)
        elif type(root) is ReverseSourceImageWorkspace:
            actions = root.actions
            for store in (
                actions._nodes,
                actions._normal,
                actions._sources,
                actions._workspace,
                root.adapter._recursive_occurrences,
            ):
                add_store(store)
            recursive = root.adapter._recursive
            if recursive is not None:
                for nested_store in (
                    recursive.adapter._composers,
                    recursive.adapter._signatures,
                ):
                    add_store(nested_store)
    return owners


def _nested_stores(
    root: object,
) -> tuple[tuple[OwnedMemo[object, object], str, str], ...]:
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )

    if type(root) is not ReverseSourceImageWorkspace:
        return ()
    recursive = root.adapter._recursive
    if recursive is None:
        return ()
    adapter = recursive.adapter
    nested = (
        (
            adapter._composers,
            "_audit_recursive_composers",
            "reverse_recursive_composer_memo",
        ),
        (
            adapter._signatures,
            "_audit_recursive_signatures",
            "reverse_recursive_signature_memo",
        ),
    )
    return tuple(
        (cast(OwnedMemo[object, object], store), attribute, role)
        for store, attribute, role in nested
        if type(store) is OwnedMemo
    )


def bind_nested_source_stores(
    root: object,
) -> tuple[PayloadAuditStoreBinding, ...]:
    """Expose exact recursive memo containers as authenticated root bindings."""
    bindings: list[PayloadAuditStoreBinding] = []
    for store, attribute, role in _nested_stores(root):
        setattr(root, attribute, store._data)
        bindings.append(PayloadAuditStoreBinding(store.owner, attribute, role))
    return tuple(bindings)


def nested_source_store_bindings(
    root: object,
) -> tuple[PayloadAuditStoreBinding, ...]:
    """Describe nested stores only while their exact root aliases remain valid."""
    bindings: list[PayloadAuditStoreBinding] = []
    for store, attribute, role in _nested_stores(root):
        if getattr(root, attribute, None) is store._data:
            bindings.append(PayloadAuditStoreBinding(store.owner, attribute, role))
    return tuple(bindings)


__all__ = [
    "bind_nested_source_stores",
    "nested_source_store_bindings",
    "source_audit_owners",
]
