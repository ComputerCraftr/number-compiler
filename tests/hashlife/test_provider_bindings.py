"""Recursive field images separate source occurrences from semantic macrocells."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Literal, Never

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
)
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometry,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
    ProviderAction,
    ProviderBindingKey,
    ProviderBoundary,
    ProviderPointKey,
)
from number_compiler.hashlife.execution.continuations.provider_field_executor import (
    ProviderFieldImageExecutor,
)
from number_compiler.hashlife.execution.continuations.provider_fused_transfer import (
    FusedProviderBinding,
    ProviderFusedTransfer,
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
from number_compiler.hashlife.execution.field_provider import (
    PoweredFieldProviderView,
    validate_powered_provider_view,
)
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_rejected_atomically
from tests.support.recursive_field_images import (
    completed_provider_input_setup,
    completed_provider_setup,
    field_image_application_setup,
    provider_absorption_setup,
    recursive_field_image_setup,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID


def test_powered_provider_view_is_sealed_scoped_and_observable() -> None:
    (
        ledger,
        _unused_source_binding,
        _unused_signature_binding,
        _unused_geometry_binding,
        _unused_action_binding,
        _,
        _unused_adapter_binding,
        _unused_executor_binding,
        _unused_incoming_binding,
        application,
    ) = field_image_application_setup()
    view = application.provider_view()

    assert validate_powered_provider_view(view, ledger)
    assert application.provider_point(view, 0) == 0
    assert application.provider_active_width(view) == 2
    with pytest.raises(TypeError):
        PoweredFieldProviderView(
            view.image,
            view.action,
            view.source,
            view.geometry,
            view.signature,
            view.incoming,
            view.interface,
            view.output,
            view.extent_bound,
            application,
            object(),
        )


def test_powered_provider_view_rejects_foreign_application_before_observation() -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        _,
        _unused_adapter_binding,
        executor,
        incoming,
        first,
    ) = field_image_application_setup()
    second = executor.application(action, source, geometry, signature, incoming)
    view = first.provider_view()
    assert_rejected_atomically(
        ledger,
        lambda: second.provider_point(view, 0),
        ValueError,
        match="another application",
    )


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("orientation", True),
        ("orientation", 2),
        ("phase", True),
        ("phase", 0.0),
        ("phase", 1 << 100),
        ("phase_count", True),
        ("phase_count", 1.0),
        ("phase_count", 0),
        ("phase_count", 65),
    ),
)
def test_provider_geometry_rejects_unbounded_numeric_aliases_before_interning(
    field: Literal["orientation", "phase", "phase_count"],
    value: bool | float,
) -> None:
    ledger, _, _, _, action, images, adapter, _ = recursive_field_image_setup((0, 1))
    providers = ProviderAbsorptionArena(
        ledger,
        images.sources,
        validate_output=images.validate_output,
        validate_bound_output=images.validate_output,
        validate_interface=images.interfaces.resolve,
        validate_bound_interface=images.interfaces.resolve,
        validate_action=images.validate_action,
        validate_boundary=lambda _value: None,
        observe=lambda _output, _coordinate, _left, _right: 0,
    )
    record = ProviderAction(adapter.output, adapter.interface, action, 0, 0, 1)
    object.__setattr__(record, field, value)
    assert_rejected_atomically(
        ledger, lambda: providers.intern(record), (TypeError, ValueError)
    )
    snapshot = providers.audit_snapshot()
    assert not snapshot.nodes and not snapshot.keys


def test_provider_semantic_key_excludes_source_and_bound_recursive_output() -> None:
    _, providers, provider, binding = provider_absorption_setup()
    record = providers.resolve(provider)
    assert set(record.__dataclass_fields__) == {
        "output",
        "interface",
        "action",
        "orientation",
        "phase",
        "phase_count",
    }
    assert "source" not in record.__dataclass_fields__
    assert binding.output != record.output
    assert type(binding.interface) is type(record.interface)
    assert binding in providers.audit_snapshot().bindings
    providers.clear_observations()
    assert not providers.audit_snapshot().bindings
    assert providers.resolve(provider) is record


def test_provider_occurrence_may_bind_validated_completed_image_atomically() -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        images,
        adapter,
        _unused_executor_binding,
        image,
        providers,
        provider,
        binding,
    ) = completed_provider_setup()
    assert binding.image == image
    inputs = ProviderImageInputArena(providers, images)
    assert isinstance(source, SourceCellID)
    root = inputs.bind(binding, source, 2)
    left, right = inputs.children(root)
    assert inputs.resolve(left).level == inputs.resolve(right).level == 0
    assert (
        inputs.resolve(left).active_extent == inputs.resolve(right).active_extent == 1
    )
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    assert not audit_field_image_payloads(ledger).invalid
    expected_action = action

    class CompletedAdapter:
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
            assert geometry.owner is images.geometries.owner
            return signature

        def compile_leaf(
            self,
            complete: FieldCellActionID,
            consumer: FieldCellActionID,
            provider: ProviderImageInput,
            geometry: FieldGeometryID,
            signature: PortSignatureID,
        ) -> FieldImageCandidate:
            raise AssertionError("warm completed parent compiled a leaf")

        def join(
            self,
            complete: FieldCellActionID,
            provider: ProviderImageInput,
            left: FieldImageID,
            right: FieldImageID,
            geometry: FieldGeometryID,
            signature: PortSignatureID,
        ) -> FieldImageCandidate:
            raise AssertionError("warm completed parent descended to children")

    completed = ProviderFieldImageExecutor(
        providers,
        inputs,
        images,
        CompletedAdapter(),
    )
    # The original image was published for an unscoped occurrence. Reuse for
    # an active two-cell input requires its own exact occurrence publication.
    assert (
        images.publish(
            ImageRequestKey(action, source, geometry, signature, 2),
            images.resolve(image),
        )
        == image
    )
    assert completed.image(action, root, geometry) == image
    before = ledger.snapshot()
    foreign = FieldImageID(ArenaToken("foreign-image"), image.kind, image.local_id)
    with pytest.raises(ValueError):
        providers.bind(
            provider,
            source,
            adapter.output,
            adapter.interface,
            foreign,
        )
    assert ledger.snapshot() == before


def test_provider_active_extent_is_occurrence_authority_not_semantic_action() -> None:
    ledger, source, signature, geometry, action, images, adapter, executor = (
        recursive_field_image_setup(
            (0, 1),
        )
    )
    assert isinstance(source, SourceCellID)
    image = executor.image(action, source, geometry, signature)
    scoped_key = ImageRequestKey(action, source, geometry, signature, 1)
    assert images.probe(scoped_key) is None
    with pytest.raises(ValueError, match="not published"):
        images.validate_occurrence(image, source, action, 1)
    with pytest.raises(ValueError, match="active extent"):
        images.probe(ImageRequestKey(action, source, geometry, signature, True))
    with pytest.raises(ValueError, match="active extent"):
        images.probe(ImageRequestKey(action, source, geometry, signature, 3))

    providers = ProviderAbsorptionArena(
        ledger,
        images.sources,
        validate_output=images.validate_output,
        validate_bound_output=images.validate_output,
        validate_interface=images.interfaces.resolve,
        validate_bound_interface=images.interfaces.resolve,
        validate_action=images.validate_action,
        validate_boundary=lambda _value: None,
        observe=lambda _output, _coordinate, _left, _right: 0,
        validate_image=images.resolve,
        validate_image_occurrence=images.validate_occurrence,
    )
    provider = providers.intern(
        ProviderAction(adapter.output, adapter.interface, action, 0, 0, 1)
    )
    assert_rejected_atomically(
        ledger,
        lambda: providers.bind(
            provider, source, adapter.output, adapter.interface, image, active_extent=1
        ),
        ValueError,
        match="not published",
    )

    # One semantic image may serve both occurrences only after each exact
    # source/extent binding has been separately published.
    assert images.publish(scoped_key, images.resolve(image)) == image
    scoped = providers.bind(
        provider,
        source,
        adapter.output,
        adapter.interface,
        image,
        active_extent=1,
    )
    assert scoped.active_extent == 1
    inputs = ProviderImageInputArena(providers, images)
    scoped_input = inputs.bind(scoped, source, 1)
    assert inputs.resolve(scoped_input).request.active_extent == 1
    # A scoped parent does not silently authorize its children. The split
    # fails without publishing any partial child binding, then succeeds once
    # both exact child extents have been admitted separately.
    before_split = ledger.snapshot()
    before_bindings = len(providers.audit_snapshot().bindings)
    with pytest.raises(ValueError, match="not published"):
        inputs.children(scoped_input)
    assert ledger.snapshot() == before_split
    assert len(providers.audit_snapshot().bindings) == before_bindings
    left_source, right_source = images.sources.children(source)
    left_image, right_image = images.children(image)
    for child_source, child_image, child_extent in (
        (left_source, left_image, 1),
        (right_source, right_image, 0),
    ):
        child_record = images.resolve(child_image)
        child_signature = images.resolve_interface(child_record.interface).signature
        assert (
            images.publish(
                ImageRequestKey(
                    action,
                    child_source,
                    child_record.geometry,
                    child_signature,
                    child_extent,
                ),
                child_record,
            )
            == child_image
        )
    left_input, right_input = inputs.children(scoped_input)
    assert inputs.resolve(left_input).active_extent == 1
    assert inputs.resolve(right_input).active_extent == 0
    with pytest.raises(ValueError, match="differs from its completed image"):
        inputs.bind(scoped, source, 2)

    forged = replace(scoped, active_extent=0)
    with pytest.raises(ValueError, match="not published"):
        providers.validate_occurrence(forged)


def test_provider_occurrence_rejects_mismatched_completed_image_before_warm_hit() -> (
    None
):
    (
        ledger,
        source,
        signature,
        _unused_geometry_binding,
        _unused_action_binding,
        images,
        adapter,
        _unused_executor_binding,
        image,
        providers,
        provider,
        valid,
    ) = completed_provider_setup()
    assert isinstance(source, SourceCellID)
    assert (
        providers.bind(
            provider,
            source,
            adapter.output,
            adapter.interface,
            image,
        )
        == valid
    )

    assert isinstance(images.interfaces, DiamondQuotientArena)
    quotient = images.interfaces.resolve(adapter.interface)
    admissible = images.interfaces.interface(signature).admissible
    mismatched_interface = images.interfaces.intern(
        signature,
        replace(quotient.components, activity=admissible),
    )
    before = assert_rejected_atomically(
        ledger,
        lambda: providers.bind(
            provider, source, adapter.output, mismatched_interface, image
        ),
        ValueError,
        match="differs from its completed image",
    )
    assert tuple(providers.audit_snapshot().bindings) == (valid,)

    child = images.children(image)[0]
    child_record = images.resolve(child)
    with pytest.raises(ValueError, match="not published"):
        providers.bind(
            provider,
            source,
            child_record.output,
            child_record.interface,
            child,
        )
    assert ledger.snapshot() == before
    assert tuple(providers.audit_snapshot().bindings) == (valid,)


def test_provider_binding_eviction_invalidates_warm_image_input_children() -> None:
    ledger, _, providers, inputs, root = completed_provider_input_setup()
    children = inputs.children(root)
    assert all(inputs.resolve(child).level == 0 for child in children)
    providers.clear_observations()
    assert_rejected_atomically(
        ledger, lambda: inputs.children(root), ValueError, match="stale"
    )


def test_provider_child_batch_rejects_second_image_before_any_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, images, providers, inputs, root = completed_provider_input_setup()
    parent = inputs.resolve(root)
    _, right_image = images.children(parent.image)
    original = images.validate_binding

    def reject_second(request: ImageRequestKey, image: FieldImageID) -> None:
        if image == right_image:
            raise ValueError("invalid second child occurrence")
        return original(request, image)

    monkeypatch.setattr(images, "validate_binding", reject_second)
    before = ledger.snapshot()
    binding_count = len(providers.audit_snapshot().bindings)
    with pytest.raises(ValueError, match="second child"):
        inputs.children(root)
    assert ledger.snapshot() == before
    assert len(providers.audit_snapshot().bindings) == binding_count


@pytest.mark.parametrize("change", ("extent", "level", "source", "request"))
def test_provider_input_revalidates_published_context_before_resolution(
    change: str,
) -> None:
    ledger, images, _providers, inputs, root = completed_provider_input_setup()
    record = inputs.resolve(root)
    left, _ = inputs.sources.children(record.source)
    if change == "extent":
        object.__setattr__(record, "active_extent", 1)
    elif change == "level":
        object.__setattr__(record, "level", 0)
    elif change == "source":
        object.__setattr__(record, "source", left)
    else:
        object.__setattr__(record, "request", replace(record.request, source=left))
    assert_rejected_atomically(ledger, lambda: inputs.resolve(root), ValueError)
    # The completed image is still live: rejecting the altered input is not
    # accidentally just a cache miss or an evicted image.
    images.resolve(record.image)


def test_provider_input_rejects_revoked_image_binding_before_warm_hit() -> None:
    ledger, images, _providers, inputs, root = completed_provider_input_setup()
    record = inputs.resolve(root)
    assert images.probe(record.request) == record.image
    images.clear_bindings()
    images.resolve(record.image)
    assert_rejected_atomically(
        ledger, lambda: inputs.resolve(root), ValueError, match="occurrence"
    )


def test_provider_cold_join_preserves_distinct_charts_of_a_shared_child(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Traversal regression, not a reverse temporal constructor proof."""
    ledger, images, providers, inputs, root = completed_provider_input_setup((0, 0))
    left, right = inputs.children(root)
    assert left == right
    record = inputs.resolve(root)
    action = record.request.action
    signature = record.request.signature
    calls: list[str] = []

    def child_geometry(parent: FieldGeometryID, side: int) -> FieldGeometryID:
        parent_record = images.geometries.resolve(parent)
        return images.geometries.intern(
            FieldGeometry(
                parent_record.spatial_level - 1, orientation=side, halo_left=1
            )
        )

    monkeypatch.setattr(images.geometries, "child", child_geometry)
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
            calls.append("leaf")
            prior = images.resolve(provider.image)
            return FieldImageCandidate(
                prior.interface, prior.output, FieldImageSummary(True, 0, 0, 1)
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
            assert complete == action and signature == expected_signature
            calls.append("join")
            assert images.resolve(left).geometry == child_geometry(geometry, 0)
            assert images.resolve(right).geometry == child_geometry(geometry, 1)
            assert left != right
            prior = images.resolve(provider.image)
            return FieldImageCandidate(
                prior.interface, prior.output, FieldImageSummary(True, 0, 1, 2)
            )

    executor = ProviderFieldImageExecutor(providers, inputs, images, Adapter())
    geometry = images.geometries.intern(FieldGeometry(1, halo_left=1))
    result = executor.image(action, root, geometry)
    assert calls == ["leaf", "leaf", "join"]
    visits = ledger.counters["provider_field_image_frame_visits"]
    assert visits == 4
    assert executor.image(action, root, geometry) == result
    assert calls == ["leaf", "leaf", "join"]
    assert ledger.counters["provider_field_image_frame_visits"] == visits
    _assert_provider_workspace_released(ledger)

    def rejected_join(*_args: object, **_kwargs: object) -> Never:
        raise ValueError("rejected parent publication")

    monkeypatch.setattr(executor.adapter, "join", rejected_join)
    other_geometry = images.geometries.intern(FieldGeometry(1, halo_left=2))
    with pytest.raises(ValueError, match="rejected parent"):
        executor.image(action, root, other_geometry)
    # Cached children still cost visits and temporary bindings; failed parent
    # work is visible, and all temporary reservations are released.
    assert ledger.counters["provider_field_image_frame_visits"] == visits + 4
    _assert_provider_workspace_released(ledger)


def test_fused_provider_uses_one_entry_response_and_validates_before_warm_hit() -> None:
    ledger, providers, provider, occurrence = provider_absorption_setup()

    class Strategy:
        def __init__(self) -> None:
            self.ledger = ledger
            self.points = 0
            self.widths = 0

        def point(
            self,
            binding: ProviderBindingKey,
            left: ProviderBoundary,
            right: ProviderBoundary,
            coordinate: int,
        ) -> int:
            assert isinstance(left, int) and isinstance(right, int)
            assert binding == occurrence
            self.points += 1
            return (coordinate + left + right) & 1

        def width(
            self, binding: ProviderBindingKey, left: object, right: object
        ) -> int:
            assert binding == occurrence
            self.widths += 1
            return providers.sources.binding_extent(binding.source)

    strategy = Strategy()
    fused = ProviderFusedTransfer(providers, strategy)
    binding = fused.bind(
        provider,
        occurrence.source,
        occurrence.output,
        occurrence.interface,
    )
    assert fused.point(binding, 0, 0, 0) == 0
    assert fused.point(binding, 0, 0, 0) == 0
    assert fused.point(binding, 0, 0, 1) == 1
    assert len(fused.audit_snapshot().points) == 1
    assert strategy.points == 2
    assert fused.width(binding, 0, 0) == 2
    assert fused.width(binding, 0, 0) == 2
    assert strategy.widths == 1
    providers.clear_observations()
    assert_rejected_atomically(
        ledger, lambda: fused.point(binding, 0, 0, 1), ValueError, match="not published"
    )


def test_fused_foreign_handle_rejects_before_wrapper_cache_probe(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, providers, provider, occurrence = provider_absorption_setup()

    class Strategy:
        def __init__(self) -> None:
            self.ledger = ledger

        def point(
            self,
            binding: ProviderBindingKey,
            left: ProviderBoundary,
            right: ProviderBoundary,
            coordinate: int,
        ) -> int:
            return 0

        def width(
            self,
            binding: ProviderBindingKey,
            left: ProviderBoundary,
            right: ProviderBoundary,
        ) -> int:
            return 2

    class PoisonedBindings(dict[FusedProviderBinding, None]):
        def __contains__(self, _key: object) -> Never:
            raise AssertionError("wrapper cache probed before scoped authority")

    fused = ProviderFusedTransfer(providers, Strategy())
    binding = fused.bind(
        provider,
        occurrence.source,
        occurrence.output,
        occurrence.interface,
    )
    foreign = type(provider)(
        ArenaToken("foreign-provider"), provider.kind, provider.local_id
    )
    bad_occurrence = replace(binding.occurrence, provider=foreign)
    bad_binding = replace(binding, occurrence=bad_occurrence)
    monkeypatch.setattr(
        fused, "_bindings", PoisonedBindings(fused.audit_snapshot().bindings)
    )
    assert_rejected_atomically(
        ledger,
        lambda: fused.point(bad_binding, 0, 0, 0),
        ValueError,
        match="different arena",
    )


@pytest.mark.parametrize("alias", (True, 0.0, 1.0))
def test_provider_integer_aliases_reject_before_warm_lookup_or_mutation(
    alias: bool | float,
) -> None:
    ledger, providers, provider, _ = provider_absorption_setup()
    forged = type(provider)(provider.owner, provider.kind, provider.local_id)
    object.__setattr__(forged, "local_id", alias)
    assert_rejected_atomically(
        ledger, lambda: providers.resolve(forged), ValueError, match="malformed"
    )


def test_provider_observation_releases_every_cached_entry_before_replacement() -> None:
    ledger, providers, _, binding = provider_absorption_setup()
    assert providers.point(binding, 0, 0, 0) == 0
    initial_snapshot = providers.audit_snapshot()
    assert ProviderPointKey(binding, 0, 0, 0) in initial_snapshot.points
    assert len(initial_snapshot.points) == 1
    assert providers.point(binding, 1, 0, 2) == 1
    replacement_snapshot = providers.audit_snapshot()
    inventory = ledger.inventory()[replacement_snapshot.point_owner]
    assert len(replacement_snapshot.points) == inventory.entries == 1
    ledger.evict_query_memos()
    final_snapshot = providers.audit_snapshot()
    assert not final_snapshot.bindings and not final_snapshot.points


@pytest.mark.parametrize("extent", (True, 2.0, 0, 1 << 100))
def test_provider_extent_forgery_rejects_before_observation(
    monkeypatch: pytest.MonkeyPatch, extent: bool | float
) -> None:
    (
        ledger,
        _unused_source_binding,
        _unused_signature_binding,
        _unused_geometry_binding,
        _unused_action_binding,
        _,
        adapter,
        _unused_executor_binding,
        _unused_incoming_binding,
        application,
    ) = field_image_application_setup()
    view = application.provider_view()
    forged = replace(view)
    object.__setattr__(forged, "extent_bound", extent)

    def forbidden(*args: object) -> None:
        pytest.fail("forged provider reached an observer")

    monkeypatch.setattr(adapter, "point_bound", forbidden)
    monkeypatch.setattr(adapter, "width_bound", forbidden)
    before = ledger.snapshot()
    assert not validate_powered_provider_view(forged, ledger)
    with pytest.raises(ValueError, match="extent"):
        application.provider_point(forged, 0)
    with pytest.raises(ValueError, match="extent"):
        application.provider_active_width(forged)
    assert ledger.snapshot() == before


def _assert_provider_workspace_released(ledger: ResourceLedger) -> None:
    assert ledger.counters["provider_field_image_evaluations"] == 3
    workspace = next(
        item for item in ledger.inventory() if item.role == "provider_image_workspace"
    )
    assert workspace.entries == workspace.nodes == 0
