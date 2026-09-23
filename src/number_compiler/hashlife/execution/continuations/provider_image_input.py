"""Lazy input cells over completed output/interface provider occurrences."""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
    ProviderBindingKey,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    ImageRequestKey,
    RecursiveFieldImageArena,
    SourceCellID,
)


@dataclass(frozen=True, slots=True)
class ProviderImageInputID(ArenaHandle):
    """Scoped occurrence view; it owns no output symbols."""


@dataclass(frozen=True, slots=True)
class ProviderImageInput:
    binding: ProviderBindingKey
    request: ImageRequestKey
    source: SourceCellID
    image: FieldImageID
    level: int
    active_extent: int


class ProviderImageInputArena:
    """Split completed images without observing or retaining their digits."""

    _KIND = "provider-image-input"

    def __init__(
        self,
        providers: ProviderAbsorptionArena,
        images: RecursiveFieldImageArena,
    ) -> None:
        if (
            providers.ledger is not images.ledger
            or providers.sources is not images.sources
        ):
            raise ValueError("provider image inputs require one index runtime")
        self.providers, self.images = providers, images
        self.sources, self.ledger = images.sources, images.ledger
        self.owner = ArenaToken("provider-image-inputs")
        prefix = f"provider-image-inputs-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "image_input_reference"
        )
        self._key_owner = self.ledger.register(
            prefix + "-keys", "image_input_reference_interner"
        )
        self._child_owner = self.ledger.register(
            prefix + "-children", "image_input_reference_binding"
        )
        self._nodes: MutableMapping[int, ProviderImageInput] = self.ledger.make_dict(
            self._node_owner
        )
        self._keys: MutableMapping[
            tuple[ProviderBindingKey, ImageRequestKey, int], int
        ] = self.ledger.make_dict(self._key_owner)
        self._children: MutableMapping[
            int, tuple[ProviderImageInputID, ProviderImageInputID]
        ] = self.ledger.make_dict(self._child_owner)
        for owner, values, nodes in (
            (self._node_owner, self._nodes, True),
            (self._key_owner, self._keys, False),
            (self._child_owner, self._children, False),
        ):
            self.ledger.register_container(
                owner,
                values,
                payloads=values.items,
                node_count=(lambda: len(self._nodes)) if nodes else None,
                evict=self.clear,
            )
        self.ledger.register_execution_root(self)
        self._next_id = 0

    def _handle(self, local_id: int) -> ProviderImageInputID:
        return ProviderImageInputID(self.owner, self._KIND, local_id)

    def resolve(self, value: ProviderImageInputID) -> ProviderImageInput:
        if type(value) is not ProviderImageInputID:
            raise TypeError("expected a completed provider input ID")
        value.validate(self.owner, self._KIND, size=self._next_id)
        try:
            record = self._nodes[value.local_id]
        except KeyError as exc:
            raise ValueError("stale completed provider input ID") from exc
        # A warm image hit must not bypass the occurrence/admission checks that
        # bind() performed. Frozen records alone are not publication authority.
        provider = self.providers.validate_occurrence(record.binding)
        source = self.sources.resolve(record.source)
        image = self.images.resolve(record.image)
        self.images.validate_binding(record.request, record.image)
        if (
            record.binding.source != record.source
            or record.binding.image != record.image
            or record.request.source != record.source
            or record.request.action != provider.action
            or record.request.geometry != image.geometry
            or record.request.active_extent != record.binding.active_extent
            or record.level != source.level
            or record.level != image.level
            or type(record.active_extent) is not int
            or not 0 <= record.active_extent <= source.width
            or (
                record.binding.active_extent is not None
                and record.active_extent != record.binding.active_extent
            )
            or self._keys.get((record.binding, record.request, record.active_extent))
            != value.local_id
        ):
            raise ValueError("completed provider input binding was altered")
        return record

    def bind(
        self,
        binding: ProviderBindingKey,
        source: SourceCellID,
        active_extent: int,
    ) -> ProviderImageInputID:
        provider = self.providers.validate_occurrence(binding)
        key, record = self._prepare_input(
            binding,
            source,
            active_extent,
            provider.action,
        )
        found = self._keys.get(key)
        if found is not None:
            return self._handle(found)
        self.ledger.reserve_many(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        return self._publish_prepared_input(key, record)

    def _prepare_input(
        self,
        binding: ProviderBindingKey,
        source: SourceCellID,
        active_extent: int,
        action: FieldCellActionID,
    ) -> tuple[
        tuple[ProviderBindingKey, ImageRequestKey, int],
        ProviderImageInput,
    ]:
        """Validate one occurrence and construct its unpublished record."""
        source_record = self.sources.resolve(source)
        if binding.source != source:
            raise ValueError("provider input source differs from its occurrence")
        assert binding.image is not None
        image_record = self.images.resolve(binding.image)
        interface_record = self.images.resolve_interface(image_record.interface)
        request = ImageRequestKey(
            action,
            source,
            image_record.geometry,
            interface_record.signature,
            binding.active_extent,
        )
        self.images.validate_binding(request, binding.image)
        if image_record.level != source_record.level:
            raise ValueError("provider input image and source levels differ")
        if (
            type(active_extent) is not int
            or not 0 <= active_extent <= source_record.width
        ):
            raise ValueError("provider input extent lies outside its source cell")
        if binding.active_extent is not None and active_extent != binding.active_extent:
            raise ValueError("provider input extent differs from its completed image")
        key = binding, request, active_extent
        return key, ProviderImageInput(
            binding,
            request,
            source,
            binding.image,
            source_record.level,
            active_extent,
        )

    def _publish_prepared_input(
        self,
        key: tuple[ProviderBindingKey, ImageRequestKey, int],
        record: ProviderImageInput,
    ) -> ProviderImageInputID:
        local_id = self._next_id
        self._next_id += 1
        self._nodes[local_id] = record
        self._keys[key] = local_id
        self.ledger.bump("provider_image_input_publications")
        return self._handle(local_id)

    def children(
        self,
        value: ProviderImageInputID,
    ) -> tuple[ProviderImageInputID, ProviderImageInputID]:
        record = self.resolve(value)
        provider = self.providers.validate_occurrence(record.binding)
        self.images.validate_binding(record.request, record.image)
        found = self._children.get(value.local_id)
        if found is not None:
            for child in found:
                child_record = self.resolve(child)
                self.providers.validate_occurrence(child_record.binding)
                self.images.validate_binding(child_record.request, child_record.image)
            return found
        if not record.level:
            raise ValueError("provider input leaf has no children")
        source_left, source_right = self.sources.children(record.source)
        image_record = self.images.resolve(record.image)
        if image_record.left is None or image_record.right is None:
            raise ValueError("completed provider parent has no image children")
        left_width = self.sources.resolve(source_left).width
        left_extent = min(record.active_extent, left_width)
        right_extent = max(0, record.active_extent - left_width)
        provider_id = record.binding.provider
        left_image = self.images.resolve(image_record.left)
        right_image = self.images.resolve(image_record.right)
        left_scope = left_extent if record.binding.active_extent is not None else None
        right_scope = right_extent if record.binding.active_extent is not None else None
        # Both provider bindings, both input nodes/keys, and the child edge
        # must fit before the first retained occurrence is published.
        prepared_bindings = self.providers._prepare_bindings(
            (
                (
                    provider_id,
                    source_left,
                    left_image.output,
                    left_image.interface,
                    image_record.left,
                    left_scope,
                ),
                (
                    provider_id,
                    source_right,
                    right_image.output,
                    right_image.interface,
                    image_record.right,
                    right_scope,
                ),
            )
        )
        left_binding, right_binding = prepared_bindings
        left_key, left_record = self._prepare_input(
            left_binding,
            source_left,
            left_extent,
            provider.action,
        )
        right_key, right_record = self._prepare_input(
            right_binding,
            source_right,
            right_extent,
            provider.action,
        )
        missing_bindings = tuple(
            dict.fromkeys(
                item
                for item in prepared_bindings
                if item not in self.providers._bindings
            )
        )
        new_inputs = tuple(dict.fromkeys((left_key, right_key)))
        missing_inputs = tuple(key for key in new_inputs if key not in self._keys)
        self.ledger.reserve_many(
            (
                (self.providers._binding_owner, len(missing_bindings), 0),
                (self._node_owner, len(missing_inputs), len(missing_inputs)),
                (self._key_owner, len(missing_inputs), 0),
                (self._child_owner, 1, 0),
            )
        )
        self.providers._publish_prepared_bindings(missing_bindings)
        records = {left_key: left_record, right_key: right_record}
        published: dict[
            tuple[ProviderBindingKey, ImageRequestKey, int], ProviderImageInputID
        ] = {}
        for key in (left_key, right_key):
            existing = self._keys.get(key)
            published[key] = (
                self._handle(existing)
                if existing is not None
                else self._publish_prepared_input(key, records[key])
            )
        left, right = published[left_key], published[right_key]
        self._children[value.local_id] = left, right
        return left, right

    def clear(self) -> None:
        counts = len(self._nodes), len(self._keys), len(self._children)
        self._nodes.clear()
        self._keys.clear()
        self._children.clear()
        for owner, count in zip(
            (self._node_owner, self._key_owner, self._child_owner),
            counts,
            strict=True,
        ):
            self.ledger.release(
                owner, entries=count, nodes=count if owner == self._node_owner else 0
            )


__all__ = ["ProviderImageInput", "ProviderImageInputArena", "ProviderImageInputID"]
