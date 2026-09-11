"""Scoped constant-size provider-layer chains for concrete port evaluation."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class ProviderLayerID(ArenaHandle):
    """Scoped reference to one node in a provider-layer chain."""


@dataclass(frozen=True, slots=True)
class ProviderLayer:
    """One bounded provider substitution and its predecessor."""

    action: FieldCellActionID
    left: object
    right: object


@dataclass(frozen=True, slots=True)
class ProviderLayerNode:
    """Canonical linked-DAG node retained by :class:`ProviderLayerArena`."""

    previous: ProviderLayerID | None
    layer: ProviderLayer


class ProviderLayerArena:
    """Intern provider substitutions without retaining stage-sized tuples."""

    _KIND = "concrete-provider-layer"

    def __init__(
        self,
        ledger: ResourceLedger,
        name: str,
        validate_action: Callable[[FieldCellActionID], object],
        validate_atom: Callable[[object], None],
    ) -> None:
        self.ledger = ledger
        self.owner = ArenaToken("concrete-provider-layers")
        self._validate_action = validate_action
        self._validate_atom = validate_atom
        self._node_owner = ledger.register(name + "-nodes", "query_memo")
        self._key_owner = ledger.register(name + "-keys", "query_memo")
        self._nodes: MutableMapping[int, ProviderLayerNode] = ledger.make_dict(
            self._node_owner,
        )
        self._keys: MutableMapping[ProviderLayerNode, int] = ledger.make_dict(
            self._key_owner,
        )
        ledger.register_container(
            self._node_owner,
            self._nodes,
            payloads=self._nodes.items,
            node_count=lambda: len(self._nodes),
            evict=self.clear,
        )
        ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
            evict=self.clear,
        )
        self._next_id = 0

    def _handle(self, local_id: int) -> ProviderLayerID:
        return ProviderLayerID(self.owner, self._KIND, local_id)

    def resolve(self, reference: ProviderLayerID) -> ProviderLayerNode:
        if type(reference) is not ProviderLayerID:
            raise TypeError("expected a scoped provider-layer reference")
        reference.validate(self.owner, self._KIND, size=self._next_id)
        try:
            return self._nodes[reference.local_id]
        except KeyError as exc:
            raise ValueError("stale provider-layer reference") from exc

    def validate_optional(
        self,
        reference: ProviderLayerID | None,
    ) -> ProviderLayerNode | None:
        if reference is None:
            return None
        return self.resolve(reference)

    def intern(
        self,
        previous: ProviderLayerID | None,
        layer: ProviderLayer,
    ) -> ProviderLayerID:
        if type(layer) is not ProviderLayer:
            raise TypeError("expected one provider layer")
        self.validate_optional(previous)
        self._validate_action(layer.action)
        self._validate_atom(layer.left)
        self._validate_atom(layer.right)
        node = ProviderLayerNode(previous, layer)
        found = self._keys.get(node)
        if found is not None:
            self.ledger.bump("concrete_provider_layer_alias_hits")
            return self._handle(found)
        self.ledger.reserve_many(
            ((self._node_owner, 1, 1), (self._key_owner, 1, 0)),
        )
        local_id = self._next_id
        self._next_id += 1
        self._nodes[local_id] = node
        self._keys[node] = local_id
        self.ledger.bump("concrete_provider_layer_publications")
        return self._handle(local_id)

    def clear(self) -> None:
        for owner, container, nodes in (
            (self._key_owner, self._keys, 0),
            (self._node_owner, self._nodes, len(self._nodes)),
        ):
            count = len(container)
            container.clear()
            self.ledger.release(owner, entries=count, nodes=nodes)


__all__ = [
    "ProviderLayer",
    "ProviderLayerArena",
    "ProviderLayerID",
    "ProviderLayerNode",
]
