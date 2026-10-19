"""Context-qualified provider image request and child propagation contracts."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometry,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderBindingKey,
)
from number_compiler.hashlife.execution.continuations.provider_field_executor import (
    ProviderFieldImageExecutor,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInput,
    ProviderImageInputArena,
)
from number_compiler.hashlife.execution.field_executor import FieldImageCandidate
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageSummary,
    ImageRequestKey,
    SourceCellID,
)
from tests.support.provider_contexts import (
    bind_contextual_provider_input,
    publish_contextual_image_occurrence,
)
from tests.support.recursive_field_images import completed_provider_setup

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID


def test_provider_context_is_qualified_and_passed_to_cold_child_composition() -> None:
    (
        ledger,
        source,
        signature,
        source_geometry,
        action,
        images,
        _source_adapter,
        _source_executor,
        image,
        providers,
        provider,
        _source_binding,
    ) = completed_provider_setup()
    assert isinstance(source, SourceCellID)
    context_owner = ArenaToken("provider-test-contexts")
    root_context = ArenaHandle(context_owner, "provider-test-context", 0)
    left_context = ArenaHandle(context_owner, "provider-test-context", 1)
    right_context = ArenaHandle(context_owner, "provider-test-context", 2)
    source_left, source_right = images.sources.children(source)
    image_left, image_right = images.children(image)

    # Publish the exact context-qualified occurrences consumed by the generic
    # provider input splitter. Context remains occurrence authority; it is not
    # copied into the canonical semantic image node.
    assert (
        publish_contextual_image_occurrence(
            images, action, source, image, None, root_context
        )
        == image
    )
    for child_source, child_image, child_context in (
        (source_left, image_left, left_context),
        (source_right, image_right, right_context),
    ):
        assert (
            publish_contextual_image_occurrence(
                images, action, child_source, child_image, None, child_context
            )
            == child_image
        )

    inputs, root = bind_contextual_provider_input(
        providers, images, provider, source, image, 2, root_context
    )
    child_pair = (left_context, right_context)
    left_input, right_input = inputs.children(
        root, child_pair, complete=action, geometry=source_geometry
    )
    assert inputs.resolve(left_input).context is left_context
    assert inputs.resolve(right_input).context is right_context
    # The child edge is qualified by the normalized consumer action/geometry
    # and the explicit pair, so a second chart has its own bounded edge.
    alternate_geometry = images.geometries.intern(FieldGeometry(1, orientation=1))
    alternate_left, alternate_right = inputs.children(
        root, child_pair, complete=action, geometry=alternate_geometry
    )
    assert (alternate_left, alternate_right) == (left_input, right_input)
    assert len(inputs._children) == 2

    # A distinct request context cannot reuse a context-qualified root image.
    other_context = ArenaHandle(context_owner, "provider-test-context", 3)
    contextual_output_key = ImageRequestKey(
        action,
        source,
        alternate_geometry,
        signature,
        2,
        root_context,
    )
    assert contextual_output_key != replace(
        contextual_output_key, context=other_context
    )
    assert images.probe(replace(contextual_output_key, context=other_context)) is None

    validated: list[tuple[object, SourceCellID, FieldGeometryID]] = []
    leaf_contexts: list[object | None] = []
    child_derivations = 0
    expected_action = action
    expected_signature = signature

    class Adapter:
        def validate_action(self, action: FieldCellActionID) -> None:
            images.validate_action(action)

        def compose_actions(
            self, before: FieldCellActionID, after: FieldCellActionID
        ) -> FieldCellActionID:
            assert before == after == action
            return action

        def signature(
            self, action: FieldCellActionID, geometry: FieldGeometryID
        ) -> PortSignatureID:
            assert action == expected_action
            images.geometries.resolve(geometry)
            return expected_signature

        def validate_context(
            self,
            context: object,
            complete: FieldCellActionID,
            provider_input: ProviderImageInput,
            geometry: FieldGeometryID,
        ) -> None:
            assert complete == action
            assert isinstance(context, ArenaHandle)
            context.validate(context_owner, "provider-test-context", size=3)
            expected = {
                source: root_context,
                source_left: left_context,
                source_right: right_context,
            }[provider_input.source]
            assert context is expected
            images.geometries.resolve(geometry)
            validated.append((context, provider_input.source, geometry))

        def child_contexts(
            self,
            complete: FieldCellActionID,
            provider_input: ProviderImageInput,
            geometry: FieldGeometryID,
        ) -> tuple[object | None, object | None]:
            nonlocal child_derivations
            assert complete == action and provider_input.context is root_context
            child_derivations += 1
            return left_context, right_context

        def compile_leaf(
            self,
            complete: FieldCellActionID,
            consumer: FieldCellActionID,
            provider: ProviderImageInput,
            geometry: FieldGeometryID,
            signature: PortSignatureID,
        ) -> FieldImageCandidate:
            assert complete == consumer == action
            assert signature == expected_signature
            leaf_contexts.append(provider.context)
            prior = images.resolve(provider.image)
            return FieldImageCandidate(
                prior.interface,
                prior.output,
                FieldImageSummary(True, 0, 0, 1),
            )

        def join(
            self,
            complete: FieldCellActionID,
            provider: ProviderImageInput,
            left: FieldImageID,
            right: FieldImageID,
            geometry: FieldGeometryID,
            signature: PortSignatureID,
        ) -> FieldImageCandidate:
            assert complete == action and provider.context is root_context
            assert signature == expected_signature
            prior = images.resolve(provider.image)
            return FieldImageCandidate(
                prior.interface,
                prior.output,
                FieldImageSummary(True, 0, 1, 2),
            )

    executor = ProviderFieldImageExecutor(providers, inputs, images, Adapter())
    result = executor.image(action, root, alternate_geometry)
    assert child_derivations == 1
    assert leaf_contexts == [left_context, right_context]
    assert any(item[0] is root_context for item in validated)
    assert ledger.counters["provider_field_child_context_derivation_attempts"] == 1
    assert ledger.counters["provider_field_child_context_derivation_evaluations"] == 1
    assert (
        ledger.counters.get("provider_field_child_context_derivation_failures", 0) == 0
    )
    assert images.probe(contextual_output_key) == result


def test_provider_context_authority_is_checked_before_a_warm_image_probe() -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        images,
        _source_adapter,
        _source_executor,
        image,
        providers,
        provider,
        _source_binding,
    ) = completed_provider_setup()
    assert isinstance(source, SourceCellID)
    foreign_owner = ArenaToken("foreign-provider-contexts")
    foreign_context = ArenaHandle(foreign_owner, "provider-test-context", 0)
    assert (
        publish_contextual_image_occurrence(
            images, action, source, image, None, foreign_context
        )
        == image
    )
    assert (
        publish_contextual_image_occurrence(
            images, action, source, image, 2, foreign_context
        )
        == image
    )
    inputs, root = bind_contextual_provider_input(
        providers, images, provider, source, image, 2, foreign_context
    )
    before_requests = ledger.counters.get("field_image_binding_requests", 0)
    expected_action = action
    expected_signature = signature

    class Adapter:
        def validate_action(self, action: FieldCellActionID) -> None:
            images.validate_action(action)

        def compose_actions(
            self, before: FieldCellActionID, after: FieldCellActionID
        ) -> FieldCellActionID:
            assert before == after == action
            return action

        def signature(
            self, action: FieldCellActionID, geometry: FieldGeometryID
        ) -> PortSignatureID:
            assert action == expected_action
            return expected_signature

        def validate_context(
            self,
            context: object,
            complete: FieldCellActionID,
            provider_input: ProviderImageInput,
            selected_geometry: FieldGeometryID,
        ) -> None:
            assert isinstance(context, ArenaHandle)
            context.validate(
                ArenaToken("another-context-owner"),
                "provider-test-context",
                size=1,
            )

        def compile_leaf(
            self,
            complete: FieldCellActionID,
            consumer: FieldCellActionID,
            provider: ProviderImageInput,
            geometry: FieldGeometryID,
            signature: PortSignatureID,
        ) -> FieldImageCandidate:
            raise AssertionError("warm root unexpectedly traversed a leaf")

        def join(
            self,
            complete: FieldCellActionID,
            provider: ProviderImageInput,
            left: FieldImageID,
            right: FieldImageID,
            geometry: FieldGeometryID,
            signature: PortSignatureID,
        ) -> FieldImageCandidate:
            raise AssertionError("warm root unexpectedly traversed a parent")

    executor = ProviderFieldImageExecutor(providers, inputs, images, Adapter())
    before_inventory = ledger.inventory()
    with pytest.raises(ValueError, match="different arena"):
        executor.image(action, root, geometry)
    assert ledger.inventory() == before_inventory
    assert ledger.counters.get("field_image_binding_requests", 0) == before_requests
    assert ledger.counters["provider_field_context_validation_attempts"] == 1
    assert ledger.counters["provider_field_context_validation_failures"] == 1
    assert ledger.counters.get("provider_field_context_validation_evaluations", 0) == 0


def test_provider_context_keys_distinguish_numeric_aliases_recursively() -> None:
    (
        _ledger,
        source,
        signature,
        geometry,
        action,
        _images,
        _source_adapter,
        _source_executor,
        _image,
        _providers,
        _provider,
        binding,
    ) = completed_provider_setup()
    assert isinstance(source, SourceCellID)
    image_request_true = ImageRequestKey(
        action, source, geometry, signature, None, True
    )
    image_request_one = ImageRequestKey(action, source, geometry, signature, None, 1)
    image_request_nested_true = replace(
        image_request_true, context=("context", (True,))
    )
    image_request_nested_one = replace(image_request_true, context=("context", (1,)))
    assert image_request_true != image_request_one
    assert image_request_nested_true != image_request_nested_one
    assert (
        len(
            {
                image_request_true,
                image_request_one,
                image_request_nested_true,
                image_request_nested_one,
            }
        )
        == 4
    )

    binding_true = replace(binding, context=True)
    binding_one = replace(binding, context=1)
    binding_nested_true = replace(binding, context=("context", (True,)))
    binding_nested_one = replace(binding, context=("context", (1,)))
    assert all(
        type(item) is ProviderBindingKey
        for item in (
            binding_true,
            binding_one,
            binding_nested_true,
            binding_nested_one,
        )
    )
    assert binding_true != binding_one
    assert binding_nested_true != binding_nested_one
    assert (
        len({binding_true, binding_one, binding_nested_true, binding_nested_one}) == 4
    )


def test_provider_child_context_pair_key_distinguishes_true_from_one() -> None:
    (
        _ledger,
        source,
        _signature,
        geometry,
        action,
        images,
        _source_adapter,
        _source_executor,
        image,
        providers,
        _provider,
        binding,
    ) = completed_provider_setup()
    assert isinstance(source, SourceCellID)
    source_left, _source_right = images.sources.children(source)
    image_left, _image_right = images.children(image)
    assert (
        publish_contextual_image_occurrence(
            images, action, source_left, image_left, None, True
        )
        == image_left
    )
    assert (
        publish_contextual_image_occurrence(
            images, action, source_left, image_left, None, 1
        )
        == image_left
    )
    inputs = ProviderImageInputArena(providers, images)
    root = inputs.bind(binding, source, 2)
    true_children = inputs.children(
        root, (True, None), complete=action, geometry=geometry
    )
    one_children = inputs.children(root, (1, None), complete=action, geometry=geometry)
    assert true_children[0] != one_children[0]
    assert true_children[1] == one_children[1]
    assert len(inputs._children) == 2
