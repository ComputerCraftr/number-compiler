"""Shared construction helpers for context-qualified provider occurrences."""

from __future__ import annotations

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
    ProviderActionID,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInputArena,
    ProviderImageInputID,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    ImageRequestKey,
    RecursiveFieldImageArena,
    SourceBindingID,
    SourceCellID,
)


def bind_contextual_provider_input(
    providers: ProviderAbsorptionArena,
    images: RecursiveFieldImageArena,
    provider: ProviderActionID,
    source: SourceCellID,
    image: FieldImageID,
    extent: int,
    context: object,
) -> tuple[ProviderImageInputArena, ProviderImageInputID]:
    record = images.resolve(image)
    binding = providers.bind(
        provider, source, record.output, record.interface, image, context=context
    )
    inputs = ProviderImageInputArena(providers, images)
    return inputs, inputs.bind(binding, source, extent)


def publish_contextual_image_occurrence(
    images: RecursiveFieldImageArena,
    action: FieldCellActionID,
    source: SourceBindingID,
    image: FieldImageID,
    active_extent: int | None,
    context: object | None,
) -> FieldImageID:
    """Publish one exact provider source/action/geometry/context occurrence."""
    record = images.resolve(image)
    signature = images.resolve_interface(record.interface).signature
    return images.publish(
        ImageRequestKey(
            action,
            source,
            record.geometry,
            signature,
            active_extent,
            context,
        ),
        record,
    )
