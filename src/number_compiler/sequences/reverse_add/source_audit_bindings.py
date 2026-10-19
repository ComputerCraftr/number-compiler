"""Exact family-owned bindings used by the reverse source payload audit."""

from __future__ import annotations

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
            add_store(root.audit_snapshot().cache_identity)
        elif type(root) is ReverseSourceImageWorkspace:
            state = root.audit_snapshot()
            actions = state.actions.audit_snapshot()
            for store in (
                actions.nodes,
                actions.normal,
                actions.sources,
                state.actions.audit_snapshot().workspace,
                state.adapter.audit_snapshot().recursive_occurrences,
                state.pointed_gt_banks,
            ):
                add_store(store)
            recursive = state.adapter.audit_snapshot().recursive
            if recursive is not None:
                recursive_adapter = recursive.adapter.audit_snapshot()
                add_store(recursive_adapter.composers)
                add_store(recursive_adapter.signatures)
    return owners


def _nested_stores(
    root: object,
) -> tuple[tuple[int, object, str, str], ...]:
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )

    if type(root) is not ReverseSourceImageWorkspace:
        return ()
    state = root.audit_snapshot()
    recursive = state.adapter.audit_snapshot().recursive
    if recursive is None:
        return ()
    adapter = recursive.adapter.audit_snapshot()
    nested = (
        (
            adapter.composers.owner,
            adapter.composers.container,
            "_audit_recursive_composers",
            "reverse_recursive_composer_memo",
        ),
        (
            adapter.signatures.owner,
            adapter.signatures.container,
            "_audit_recursive_signatures",
            "reverse_recursive_signature_memo",
        ),
    )
    return nested


def bind_nested_source_stores(
    root: object,
) -> tuple[PayloadAuditStoreBinding, ...]:
    """Expose exact recursive memo containers as authenticated root bindings."""
    bindings: list[PayloadAuditStoreBinding] = []
    for owner, container, attribute, role in _nested_stores(root):
        setattr(root, attribute, container)
        bindings.append(PayloadAuditStoreBinding(owner, attribute, role))
    return tuple(bindings)


def nested_source_store_bindings(
    root: object,
) -> tuple[PayloadAuditStoreBinding, ...]:
    """Describe nested stores only while their exact root aliases remain valid."""
    bindings: list[PayloadAuditStoreBinding] = []
    for owner, container, attribute, role in _nested_stores(root):
        if getattr(root, attribute, None) is container:
            bindings.append(PayloadAuditStoreBinding(owner, attribute, role))
    return tuple(bindings)


__all__ = [
    "bind_nested_source_stores",
    "nested_source_store_bindings",
    "source_audit_owners",
]
