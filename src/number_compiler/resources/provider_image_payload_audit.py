"""Independent retained-payload audit for symbolic provider image inputs."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderBindingKey,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInput,
    ProviderImageInputArena,
    ProviderImageInputID,
)
from number_compiler.hashlife.execution.field_images import ImageRequestKey
from number_compiler.hashlife.execution.source_image_seals import _TypedKey


def audit_provider_image_inputs(
    root: ProviderImageInputArena,
    ledger: object,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate all three stores without invoking an observation callback."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    stores = (
        (root._node_owner, root._nodes),
        (root._key_owner, root._keys),
        (root._child_owner, root._children),
    )
    valid_root = (
        root.ledger is ledger
        and root.providers.ledger is ledger
        and root.images.ledger is ledger
        and root.providers.sources is root.sources
        and root.images.sources is root.sources
        and all(containers.get(owner) is store for owner, store in stores)
    )
    for local_id, record in root._nodes.items():
        valid = (
            valid_root
            and type(local_id) is int
            and 0 <= local_id < root._next_id
            and type(record) is ProviderImageInput
        )
        try:
            provider, source, image = root._components(record)
            valid &= record.binding.source == record.source
            valid &= record.binding.image == record.image
            root.images.validate_binding(record.request, record.image)
            valid &= record.request.source == record.source
            valid &= record.request.action == provider.action
            valid &= record.request.geometry == image.geometry
            valid &= record.request.active_extent == record.binding.active_extent
            valid &= _TypedKey(record.context) == _TypedKey(record.binding.context)
            valid &= _TypedKey(record.request.context) == _TypedKey(record.context)
            valid &= (
                record.request.signature
                == root.images.resolve_interface(image.interface).signature
            )
            valid &= record.level == source.level == image.level
            valid &= 0 <= record.active_extent <= source.width
            valid &= (
                record.binding.active_extent is None
                or record.binding.active_extent == record.active_extent
            )
            key = record.binding, record.request, record.active_extent
            valid &= root._keys.get(key) == local_id
            valid &= root.resolve(root._handle(local_id)) is record
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.add(id(record))
        else:
            invalid.add((root._node_owner, id(record)))
    for key, local_id in root._keys.items():
        valid = (
            valid_root
            and type(key) is tuple
            and len(key) == 3
            and type(local_id) is int
            and local_id in root._nodes
        )
        if valid:
            record = root._nodes[local_id]
            valid &= (
                type(key[0]) is ProviderBindingKey
                and type(key[1]) is ImageRequestKey
                and type(key[2]) is int
                and key[0] is record.binding
                and key[1] is record.request
                and key[2] == record.active_extent
            )
        if valid:
            approved.add(id(key))
        else:
            invalid.add((root._key_owner, id(key)))
    for edge_key, children in root._children.items():
        valid = (
            valid_root
            and type(edge_key) is tuple
            and len(edge_key) == 4
            and type(edge_key[0]) is int
            and (edge_key[1] is None or type(edge_key[1]) is FieldCellActionID)
            and (edge_key[2] is None or type(edge_key[2]) is FieldGeometryID)
            and type(edge_key[3]) is _TypedKey
            and type(edge_key[3].value) is tuple
            and len(edge_key[3].value) == 2
            and (edge_key[1] is None) == (edge_key[2] is None)
        )
        parent_id = edge_key[0] if type(edge_key) is tuple and edge_key else -1
        valid &= (
            parent_id in root._nodes
            and type(children) is tuple
            and len(children) == 2
            and all(type(child) is ProviderImageInputID for child in children)
        )
        try:
            parent = root._nodes[parent_id]
            source_left, source_right = root.sources.children(parent.source)
            image_left, image_right = root.images.children(parent.image)
            left, right = root.resolve(children[0]), root.resolve(children[1])
            valid &= left.source == source_left and right.source == source_right
            valid &= left.image == image_left and right.image == image_right
            contexts = cast(tuple[object, ...], edge_key[3].value)
            valid &= _TypedKey(left.context) == _TypedKey(contexts[0])
            valid &= _TypedKey(right.context) == _TypedKey(contexts[1])
            if edge_key[1] is not None:
                root.images.validate_action(edge_key[1])
                assert type(edge_key[2]) is FieldGeometryID
                root.images.geometries.resolve(edge_key[2])
            valid &= left.binding.provider == parent.binding.provider
            valid &= right.binding.provider == parent.binding.provider
            left_width = root.sources.resolve(source_left).width
            valid &= left.active_extent == min(parent.active_extent, left_width)
            valid &= right.active_extent == max(0, parent.active_extent - left_width)
            if parent.binding.active_extent is not None:
                valid &= left.binding.active_extent == left.active_extent
                valid &= right.binding.active_extent == right.active_extent
            else:
                valid &= left.binding.active_extent is None
                valid &= right.binding.active_extent is None
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.add(id(children))
        else:
            invalid.add((root._child_owner, id(children)))
    return approved, invalid


__all__ = ["audit_provider_image_inputs"]
