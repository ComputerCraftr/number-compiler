"""Parent-first field images over completed symbolic provider inputs."""

from __future__ import annotations

from typing import Protocol

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInput,
    ProviderImageInputArena,
    ProviderImageInputID,
)
from number_compiler.hashlife.execution.field_executor import FieldImageCandidate
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    ImageRequestKey,
    RecursiveFieldImageArena,
)


class ProviderFieldImageAdapter(Protocol):
    """Output-complete substitution law for one consumer over a provider."""

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def compose_actions(
        self,
        before: FieldCellActionID,
        after: FieldCellActionID,
    ) -> FieldCellActionID: ...

    def signature(
        self,
        action: FieldCellActionID,
        geometry: FieldGeometryID,
    ) -> PortSignatureID: ...

    def compile_leaf(
        self,
        complete: FieldCellActionID,
        consumer: FieldCellActionID,
        provider: ProviderImageInput,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageCandidate: ...

    def join(
        self,
        complete: FieldCellActionID,
        provider: ProviderImageInput,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageCandidate: ...


class ProviderFieldImageExecutor:
    """Apply one action to a completed image without reading midpoint symbols."""

    def __init__(
        self,
        providers: ProviderAbsorptionArena,
        inputs: ProviderImageInputArena,
        images: RecursiveFieldImageArena,
        adapter: ProviderFieldImageAdapter,
    ) -> None:
        if (
            providers is not inputs.providers
            or inputs.images is not images
            or providers.ledger is not images.ledger
        ):
            raise ValueError("provider field execution requires one index runtime")
        self.providers, self.inputs, self.images, self.adapter = (
            providers,
            inputs,
            images,
            adapter,
        )
        self.ledger = images.ledger
        self.ledger.register_execution_root(self)

    def image(
        self,
        consumer: FieldCellActionID,
        provider: ProviderImageInputID,
        geometry: FieldGeometryID,
    ) -> FieldImageID:
        """Compile a complete spatial parent, probing normalized IDs first."""
        self.images.geometries.resolve(geometry)
        self.adapter.validate_action(consumer)
        root = self.inputs.resolve(provider)
        before = self.providers.validate_occurrence(root.binding).action
        complete = self.adapter.compose_actions(before, consumer)
        self.adapter.validate_action(complete)
        signature = self.adapter.signature(complete, geometry)
        root_key = ImageRequestKey(complete, root.source, geometry, signature)
        cached = self.images.probe(root_key)
        self.ledger.bump("provider_field_image_requests")
        if cached is not None:
            self.ledger.bump("provider_field_image_early_hits")
            return cached

        stack: list[tuple[ProviderImageInputID, FieldGeometryID, bool]] = [
            (provider, geometry, False),
        ]
        built: dict[int, FieldImageID] = {}
        while stack:
            current, current_geometry, ready = stack.pop()
            record = self.inputs.resolve(current)
            current_signature = self.adapter.signature(complete, current_geometry)
            key = ImageRequestKey(
                complete,
                record.source,
                current_geometry,
                current_signature,
            )
            found = self.images.probe(key)
            if found is not None:
                built[current.local_id] = found
                continue
            if record.level and not ready:
                left, right = self.inputs.children(current)
                stack.append((current, current_geometry, True))
                stack.append(
                    (right, self.images.geometries.child(current_geometry, 1), False)
                )
                stack.append(
                    (left, self.images.geometries.child(current_geometry, 0), False)
                )
                continue
            if record.level:
                left, right = self.inputs.children(current)
                candidate = self.adapter.join(
                    complete,
                    record,
                    built[left.local_id],
                    built[right.local_id],
                    current_geometry,
                    current_signature,
                )
                left_image: FieldImageID | None = built[left.local_id]
                right_image: FieldImageID | None = built[right.local_id]
            else:
                candidate = self.adapter.compile_leaf(
                    complete,
                    consumer,
                    record,
                    current_geometry,
                    current_signature,
                )
                left_image = right_image = None
            node = FieldImageRecord(
                record.level,
                left_image,
                right_image,
                candidate.interface,
                candidate.output,
                current_geometry,
                candidate.summary,
            )
            built[current.local_id] = self.images.publish(key, node)
            self.ledger.bump("provider_field_image_evaluations")
        return built[provider.local_id]


__all__ = ["ProviderFieldImageAdapter", "ProviderFieldImageExecutor"]
