"""Recursive field images separate source occurrences from semantic macrocells."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldGeometryID
from number_compiler.hashlife.execution.field_images import SourceBindingID
from tests.support.assertions import assert_rejected_atomically
from tests.support.recursive_field_images import field_image_application_setup

if TYPE_CHECKING:
    import number_compiler.hashlife.actions.field_actions
    import number_compiler.hashlife.execution.field_images
from collections.abc import Callable
from dataclasses import fields, replace
from typing import TYPE_CHECKING, Literal, Never, TypedDict, TypeVar, cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
)
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometry,
)
from number_compiler.hashlife.execution.field_capabilities import (
    validate_field_image_application,
)
from number_compiler.hashlife.execution.field_executor import (
    FieldImageCandidate,
    ParentObservation,
    RecursiveFieldImageExecutor,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    FieldImageSemanticKey,
    FieldImageSummary,
    ImageRequestKey,
    RecursiveFieldImageArena,
    SourceForestID,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList
from tests.support.recursive_field_images import (
    FieldTransferPortID,
    RecursiveImageTestAdapter,
    SecondDomainArena,
    field_transfer_setup,
    provider_absorption_setup,
    recursive_field_image_setup,
)


class _ArenaArguments(TypedDict):
    action_owner: ArenaToken
    output_owner: ArenaToken
    action_kind: str
    output_kind: str


class _SummaryArguments(TypedDict):
    activity: bool
    first_active: int | None
    last_active: int | None
    extent: int
    growth: int
    terminated: bool


HandleT = TypeVar("HandleT")


def _probe(
    resolve: Callable[[HandleT], object], handle: HandleT
) -> Callable[[], object]:
    return lambda: resolve(handle)


def test_application_observes_parent_before_realizing_images(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, root, signature, geometry, action, images, adapter, executor = (
        recursive_field_image_setup()
    )
    incoming = ArenaHandle(adapter.port_owner, "test-image-port", 0)

    def observe_point(*_args: object) -> ParentObservation:
        return ParentObservation(1)

    def observe_width(*_args: object) -> ParentObservation:
        return ParentObservation(7, True)

    adapter.observe_parent_point = observe_point
    adapter.observe_parent_width = observe_width
    application = executor.application(
        action,
        root,
        geometry,
        signature,
        incoming,
    )

    def forbidden_image(*_args: object) -> Never:
        raise AssertionError("parent observation realized a field image")

    monkeypatch.setattr(type(executor), "image", forbidden_image)
    assert application.point(0) == 1
    assert application.active_width() == 7
    assert images.retained_images == 0
    assert ledger.counters["field_image_parent_observation_requests"] == 2
    assert ledger.counters["field_image_parent_observation_evaluations"] == 1
    assert ledger.counters["field_image_parent_observation_early_hits"] == 1


def test_parent_observation_metrics_follow_the_observer_memo_probe() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, root, signature, geometry, action, _, adapter, executor = (
        recursive_field_image_setup()
    )
    incoming = ArenaHandle(adapter.port_owner, "test-image-port", 0)
    memo: dict[int, int] = {}

    def observe(
        *args: object,
    ) -> ParentObservation:
        coordinate = args[-1]
        assert isinstance(coordinate, int)
        early_hit = coordinate in memo
        memo[coordinate] = 1
        return ParentObservation(1, early_hit)

    adapter.observe_parent_point = observe
    application = executor.application(
        action,
        root,
        geometry,
        signature,
        incoming,
    )
    assert application.point(0) == application.point(0) == 1
    report = collect_ledger_metrics(ledger)
    assert report.field_image_parent_observation_requests == 2
    assert report.field_image_parent_observation_evaluations == 1
    assert report.field_image_parent_observation_early_hits == 1


@pytest.mark.parametrize(
    ("field", "value", "error"),
    (
        ("action_owner", True, TypeError),
        ("output_owner", 0, TypeError),
        ("action_kind", False, ValueError),
        ("action_kind", "", ValueError),
        ("output_kind", 1.0, ValueError),
        ("output_kind", "", ValueError),
    ),
)
def test_image_arena_rejects_owner_and_sort_aliases_atomically(
    field: Literal["action_kind", "action_owner", "output_kind", "output_owner"],
    value: Literal[""] | bool | float,
    error: type[Exception],
) -> None:
    ledger, _, signature, _, _, images, _, _ = recursive_field_image_setup()
    arguments: dict[str, object] = {
        "action_owner": ArenaToken("other-field-actions"),
        "output_owner": ArenaToken("other-field-outputs"),
        "action_kind": "field-cell-action",
        "output_kind": "coordinate-output-morphism",
    }
    arguments[field] = value
    assert_rejected_atomically(
        ledger,
        lambda: RecursiveFieldImageArena(
            ledger,
            images.sources,
            images.geometries,
            images.interfaces,
            signature_owner=images.interfaces.owner,
            action_validate=lambda _value: None,
            output_validate=lambda _value: None,
            signature_for=lambda _action, _geometry: signature,
            **cast(_ArenaArguments, arguments),
        ),
        error,
    )


def test_image_arena_rejects_partial_authority_before_registration() -> None:
    ledger, _, _signature, _, _, images, adapter, _ = recursive_field_image_setup()
    assert_rejected_atomically(
        ledger,
        lambda: RecursiveFieldImageArena(
            ledger,
            images.sources,
            images.geometries,
            images.interfaces,
            signature_owner=images.interfaces.owner,
            action_owner=adapter.action.owner,
            output_owner=adapter.output.owner,
            action_validate=adapter.validate_action,
            output_validate=adapter.validate_output,
            signature_for=adapter.signature,
            action_authority=adapter,
        ),
        ValueError,
        match="supplied together",
    )


def test_parent_request_is_probed_before_descendants_and_warm_hit_skips_work() -> None:
    ledger, source, signature, geometry, action, _, adapter, executor = (
        recursive_field_image_setup()
    )
    first = executor.image(action, source, geometry, signature)
    calls = adapter.leaf_calls, adapter.join_calls
    before_visits = ledger.counters.get("source_leaf_visits", 0)
    second = executor.image(action, source, geometry, signature)
    assert first == second
    assert (adapter.leaf_calls, adapter.join_calls) == calls
    assert ledger.counters.get("source_leaf_visits", 0) == before_visits
    assert ledger.counters["field_image_binding_early_hits"] >= 1


def test_phase_is_bounded_by_finite_port_admission_but_coordinates_stay_exact() -> None:
    huge_level = 1 << 100
    geometry = FieldGeometry(huge_level, phase=(1 << 64) - 1, phase_count=1 << 64)
    assert geometry.spatial_level == huge_level
    with pytest.raises(ValueError, match="phase"):
        FieldGeometry(0, phase=1 << 100, phase_count=1 << 101)


def test_query_eviction_preserves_canonical_field_image_ids() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    image, record = _completed_image(executor, action, source, geometry, signature)

    ledger.evict_query_memos()

    assert images.resolve(image) == record
    assert images.retained_bindings == 0
    rebuilt_binding = executor.image(action, source, geometry, signature)
    assert rebuilt_binding == image
    assert images.resolve(rebuilt_binding) == record


def test_nonleaf_image_cannot_relabel_a_complete_word_as_an_opaque_leaf() -> None:
    _, source, signature, geometry, action, _unused_images_binding, _, executor = (
        recursive_field_image_setup()
    )
    _unused_image_binding, record = _completed_image(
        executor, action, source, geometry, signature
    )
    assert record.level > 0
    with pytest.raises(ValueError, match="recursive child references"):
        FieldImageRecord(
            record.level,
            None,
            None,
            record.interface,
            record.output,
            record.geometry,
            record.summary,
        )


def test_non_power_of_two_forest_publishes_balanced_recursive_image() -> None:
    ledger, source, signature, geometry, action, images, adapter, executor = (
        recursive_field_image_setup(
            (0, 1, 0, 1, 0, 1),
        )
    )
    assert type(source) is SourceForestID
    image, record = _completed_image(executor, action, source, geometry, signature)
    assert record.left is not None and record.right is not None
    left, right = images.children(image)
    assert images.resolve(left).level < record.level
    assert images.resolve(right).level < record.level
    assert adapter.forest_calls > 0
    assert all(
        not isinstance(value, (tuple, list, bytes, bytearray))
        for value in (
            record.left,
            record.right,
            record.interface,
            record.output,
            record.geometry,
        )
    )
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    assert not audit_field_image_payloads(ledger).invalid


def test_warm_forest_parent_hits_before_children_and_composition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, source, signature, geometry, action, _, adapter, executor = (
        recursive_field_image_setup(
            (0, 1, 0, 1, 0, 1),
        )
    )
    first = executor.image(action, source, geometry, signature)
    calls = adapter.leaf_calls, adapter.join_calls, adapter.forest_calls

    def poisoned(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm forest parent descended into construction")

    monkeypatch.setattr(adapter, "leaf", poisoned)
    monkeypatch.setattr(adapter, "join", poisoned)
    monkeypatch.setattr(adapter, "forest", poisoned)
    before = ledger.counters.get("source_leaf_visits", 0)
    assert executor.image(action, source, geometry, signature) == first
    assert calls[2] > 0
    assert ledger.counters.get("source_leaf_visits", 0) == before


def test_runtime_issued_application_is_lazy_and_marker_cannot_forge_it() -> None:
    (
        ledger,
        _unused_source_binding,
        _unused_signature_binding,
        _unused_geometry_binding,
        _unused_action_binding,
        images,
        _unused_adapter_binding,
        _unused_executor_binding,
        _unused_incoming_binding,
        application,
    ) = field_image_application_setup()
    assert images.retained_images == images.retained_bindings == 0
    assert validate_field_image_application(application, ledger)
    assert application.point(0) == 0
    assert application.active_width() == 2
    assert application.retained_entries() == images.retained_bindings


def test_image_application_rejects_foreign_port_before_warm_image_probe() -> None:
    (
        ledger,
        _unused_source_binding,
        _unused_signature_binding,
        _unused_geometry_binding,
        _unused_action_binding,
        _images,
        _unused_adapter_binding,
        _unused_executor_binding,
        _unused_incoming_binding,
        application,
    ) = field_image_application_setup()
    assert application.point(0) == 0
    requests = ledger.counters.get("field_image_binding_requests", 0)
    object.__setattr__(
        application,
        "incoming",
        ArenaHandle(ArenaToken("foreign-port"), "test-image-port", 0),
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="different arena"):
        application.point(0)
    assert ledger.counters.get("field_image_binding_requests", 0) == requests
    assert ledger.snapshot() == before

    class Marker:
        is_algebraic_field_action_executor = True

    assert not validate_field_image_application(Marker(), ledger)


def test_equal_complete_leaf_behavior_shares_one_recursive_image() -> None:
    _, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    executor.image(action, source, geometry, signature)
    left, right = images.sources.children(source)

    child_geometry = images.geometries.child(geometry, 0)
    first = images.probe(ImageRequestKey(action, left, child_geometry, signature))
    second = images.probe(ImageRequestKey(action, right, child_geometry, signature))
    assert first is not None and first == second
    assert images.retained_images == 2  # one shared leaf plus one parent


def test_field_image_metrics_match_the_owned_arena_and_interface_population() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    executor.image(action, source, geometry, signature)
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    report = collect_ledger_metrics(ledger)
    assert report.field_image_nodes == images.retained_images == 2
    assert report.new_canonical_field_images_published == images.retained_images
    assert report.field_interface_nodes == report.diamond_quotient_nodes == 1
    assert report.resource_accounting_mismatch == 0
    assert report.resource_audit_unknown_payloads == 0
    # The fixture intentionally uses synthetic action/output owners; the
    # population counters remain independently observable despite that failed
    # production-authority audit.
    assert report.forbidden_future_payloads > 0


def test_field_image_records_have_no_exact_future_payload_slots() -> None:
    from number_compiler.hashlife.execution.field_images import FieldImageRecord

    names = {field.name for field in fields(FieldImageRecord)}
    assert names == {
        "level",
        "left",
        "right",
        "interface",
        "output",
        "geometry",
        "summary",
    }
    assert names.isdisjoint({"digits", "rows", "tail", "coefficients", "offset"})


@pytest.mark.parametrize("kind", ("image", "provider", "transfer", "output"))
def test_unallocated_semantic_id_rejects_before_the_node_store(
    monkeypatch: pytest.MonkeyPatch, kind: str
) -> None:
    if kind == "image":
        ledger, _, _, _, _, image_arena, _, _ = recursive_field_image_setup()
        arena: object = image_arena
        probe = _probe(
            image_arena.resolve,
            image_arena.scoped_handle(image_arena.audit_snapshot().next_id),
        )
    elif kind == "provider":
        ledger, provider_arena, _, _ = provider_absorption_setup()
        arena = provider_arena
        probe = _probe(
            provider_arena.resolve,
            provider_arena.scoped_handle(provider_arena.audit_snapshot().next_id),
        )
    elif kind == "transfer":
        ledger, _, _, _, _, _, _, transfer_arena, _ = field_transfer_setup()
        arena = transfer_arena
        probe = _probe(
            transfer_arena.resolve,
            transfer_arena.scoped_handle(transfer_arena.audit_snapshot().next_id),
        )
    else:
        ledger = ResourceLedger()
        tiles = TileArena(ledger)
        arena = tiles
        probe = _probe(
            tiles.resolve,
            TileID(tiles.owner, "canonical-tile", tiles.audit_snapshot().next_tile),
        )

    class Unreachable(dict[object, object]):
        def __getitem__(self, key: object) -> None:
            pytest.fail("unallocated semantic ID reached the node store")

        def get(self, key: object, default: object = None) -> None:
            pytest.fail("unallocated semantic ID reached the node store")

    before = ledger.snapshot()
    with monkeypatch.context() as patch:
        patch.setattr(arena, "_nodes", Unreachable())
        with pytest.raises(ValueError, match="allocated range"):
            probe()
    assert ledger.snapshot() == before


def test_field_image_semantic_key_excludes_source_action_and_proof_occurrences() -> (
    None
):
    _, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    executor.image(action, source, geometry, signature)
    semantic = next(iter(images.audit_snapshot().keys))
    names = set(semantic.__dataclass_fields__)
    assert names == {
        "level",
        "left",
        "right",
        "interface",
        "output",
        "geometry",
        "summary",
    }
    assert not any(
        token in name
        for name in names
        for token in (
            "source",
            "action",
            "proof",
            "generation",
            "coordinate",
            "position",
            "trajectory",
        )
    )


def test_payload_audit_reconstructs_image_interner_keys_instead_of_trusting_them() -> (
    None
):
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    executor.image(action, source, geometry, signature)
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    semantic, local_id = next(iter(images.audit_snapshot().keys.items()))
    corrupted = replace(
        semantic,
        output=replace(semantic.output, local_id=semantic.output.local_id + 1),
    )
    keys = cast(
        LedgerDict[FieldImageSemanticKey, int],
        object.__getattribute__(images, "_keys"),
    )
    keys[corrupted] = keys.pop(semantic)
    audit = audit_field_image_payloads(ledger)
    assert (images.audit_snapshot().key_owner, id(corrupted)) in audit.invalid
    assert local_id < images.retained_images


def test_payload_audit_rejects_forward_references_in_source_cell_dag() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    executor.image(action, source, geometry, signature)
    from number_compiler.resources.field_image_payload_audit import (
        audit_field_image_payloads,
    )

    root = images.sources.resolve(source)
    nodes = images.sources.audit_snapshot().nodes
    assert isinstance(nodes, LedgerList)
    raw_nodes = cast(
        list[object],
        object.__getattribute__(nodes, "_data"),
    )
    raw_nodes[source.local_id] = replace(root, left=source.local_id)
    audit = audit_field_image_payloads(ledger)
    assert (
        images.sources.audit_snapshot().node_owner,
        id(images.sources.audit_snapshot().nodes[source.local_id]),
    ) in audit.invalid


@pytest.mark.parametrize("alias", (True, 0.0, 1.0))
def test_wrong_sort_action_rejects_before_binding_mutation(alias: bool | float) -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    forged = FieldCellActionID(action.owner, action.kind, action.local_id)
    object.__setattr__(forged, "local_id", alias)
    assert_rejected_atomically(
        ledger,
        lambda: executor.image(forged, source, geometry, signature),
        (TypeError, ValueError),
    )
    assert images.retained_bindings == 0


def test_foreign_image_action_rejects_before_adapter_and_binding_probe() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    request_count = ledger.counters.get("field_image_binding_requests", 0)

    def poison(_value: object) -> Never:
        raise AssertionError("foreign image action reached family validation")

    assert type(executor.adapter) is RecursiveImageTestAdapter
    object.__setattr__(images, "_action_validate", poison)
    foreign = FieldCellActionID(
        ArenaToken("foreign-image-actions"),
        action.kind,
        action.local_id,
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="different arena"):
        executor.image(foreign, source, geometry, signature)
    with pytest.raises(ValueError, match="different arena"):
        executor.application(
            foreign,
            source,
            geometry,
            signature,
            ArenaHandle(executor.adapter.port_owner, "test-image-port", 0),
        )
    assert ledger.counters.get("field_image_binding_requests", 0) == request_count
    assert ledger.snapshot() == before
    assert images.retained_images == images.retained_bindings == 0


def test_republication_with_different_complete_behavior_is_rejected() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    image = executor.image(action, source, geometry, signature)

    key = ImageRequestKey(action, source, geometry, signature)
    original = images.resolve(image)
    assert isinstance(original.summary, FieldImageSummary)
    conflicting = replace(
        original,
        summary=replace(original.summary, growth=original.summary.growth + 1),
    )
    assert_rejected_atomically(
        ledger,
        lambda: images.publish(key, conflicting),
        ValueError,
        match="different semantic result",
    )


def test_foreign_child_image_rejects_before_binding_lookup_or_mutation() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    _unused_image_binding, original = _completed_image(
        executor, action, source, geometry, signature
    )
    assert original.left is not None
    foreign_owner = ArenaToken("foreign-images")
    foreign_left = FieldImageID(
        foreign_owner,
        original.left.kind,
        original.left.local_id,
    )
    assert original.right is not None
    foreign_right = FieldImageID(
        foreign_owner,
        original.right.kind,
        original.right.local_id,
    )
    corrupted = replace(original, left=foreign_left, right=foreign_right)

    assert_rejected_atomically(
        ledger,
        lambda: images.publish(
            ImageRequestKey(action, source, geometry, signature), corrupted
        ),
        ValueError,
    )


def test_indirect_temporal_witness_cycle_rejects_without_publication() -> None:
    ledger, source, signature, geometry, action, images, adapter, _ = (
        recursive_field_image_setup()
    )
    left, _ = images.sources.children(source)
    leaf_geometry = images.geometries.child(geometry, 0)
    other = FieldCellActionID(action.owner, action.kind, 1)
    root_action = action

    class CyclicAdapter(RecursiveImageTestAdapter):
        def validate_action(
            self,
            action: number_compiler.hashlife.actions.field_actions.FieldCellActionID,
        ) -> None:
            if type(action) is not FieldCellActionID or action not in (
                root_action,
                other,
            ):
                raise ValueError("foreign field action")

        def action_children(
            self,
            action: number_compiler.hashlife.actions.field_actions.FieldCellActionID,
        ) -> tuple[
            FieldCellActionID,
            FieldCellActionID,
        ]:
            self.validate_action(action)
            return (
                (other, other) if action == root_action else (root_action, root_action)
            )

    cyclic_adapter = CyclicAdapter(
        action,
        adapter.interface,
        adapter.output,
        images.sources,
    )
    cyclic_adapter.signature_id = signature
    cyclic_authority = SecondDomainArena(
        ledger,
        action.owner,
        adapter.output.owner,
        signature,
        action_kind=action.kind,
        output_kind=adapter.output.kind,
        action_size=2,
    )
    cyclic_images = RecursiveFieldImageArena(
        ledger,
        images.sources,
        images.geometries,
        images.interfaces,
        action_owner=action.owner,
        output_owner=adapter.output.owner,
        signature_owner=images.interfaces.owner,
        action_validate=cyclic_authority.validate_action,
        output_validate=cyclic_authority.validate_output,
        signature_for=cyclic_authority.signature,
        action_authority=cyclic_authority,
        output_authority=cyclic_authority,
        signature_authority=cyclic_authority,
        action_kind=action.kind,
        output_kind=adapter.output.kind,
        signature_kind=images.interfaces.signature_kind,
    )
    cyclic = RecursiveFieldImageExecutor(
        images.sources,
        cyclic_images,
        cyclic_adapter,
    )
    before_entries, before_nodes = ledger.entries, ledger.nodes
    with pytest.raises(ValueError, match="cyclic field-action construction witness"):
        cyclic.image(action, left, leaf_geometry, signature)
    assert (ledger.entries, ledger.nodes) == (before_entries, before_nodes)
    assert images.retained_images == images.retained_bindings == 0


def test_image_adapter_candidate_requires_the_exact_complete_record_type() -> None:
    ledger, source, signature, geometry, action, images, adapter, _ = (
        recursive_field_image_setup()
    )

    class DuckAdapter(RecursiveImageTestAdapter):
        def leaf(
            self,
            action: number_compiler.hashlife.actions.field_actions.FieldCellActionID,
            source: number_compiler.hashlife.execution.field_images.SourceCellID,
            geometry: number_compiler.hashlife.actions.field_actions.FieldGeometryID,
        ) -> FieldImageCandidate:
            valid = super().leaf(action, source, geometry)

            class Duck:
                interface = valid.interface
                output = valid.output
                summary = valid.summary

            return cast(FieldImageCandidate, Duck())

    duck = DuckAdapter(action, adapter.interface, adapter.output)
    duck.signature_id = signature
    object.__setattr__(images, "_action_validate", duck.validate_action)
    executor = RecursiveFieldImageExecutor(images.sources, images, duck)
    leaf, _ = images.sources.children(source)
    leaf_geometry = images.geometries.child(geometry, 0)
    before = ledger.snapshot()
    with pytest.raises(TypeError, match="incomplete candidate"):
        executor.image(action, leaf, leaf_geometry, signature)
    assert ledger.snapshot().entries == before.entries
    assert images.retained_images == images.retained_bindings == 0


def test_query_eviction_releases_bindings_but_keeps_semantic_images_strong() -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    first = executor.image(action, source, geometry, signature)
    retained = images.retained_images
    ledger.evict_query_memos()
    assert images.retained_images == retained
    assert images.retained_bindings == 0
    first_summary = images.resolve(first).summary
    assert isinstance(first_summary, FieldImageSummary)
    assert first_summary.extent == 2
    inventory = {
        item.role: item
        for item in ledger.inventory()
        if item.role in {"field_image", "field_image_interner", "spatial_binding"}
    }
    assert inventory["spatial_binding"].entries == 0
    assert inventory["spatial_binding"].observed_entries == 0
    assert inventory["field_image"].entries == retained
    assert inventory["field_image_interner"].entries == retained
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    assert collect_ledger_metrics(ledger).resource_accounting_mismatch == 0
    second = executor.image(action, source, geometry, signature)
    assert second == first
    second_summary = images.resolve(second).summary
    assert isinstance(second_summary, FieldImageSummary)
    assert second_summary.extent == 2


def test_recursive_image_callbacks_cannot_hide_future_words_or_affine_b() -> None:
    from number_compiler.resources.callback_payload_audit import (
        audit_callback_future_payloads,
    )

    ledger, _, _, _, _, images, _, _ = recursive_field_image_setup()
    whole_word = (1 << 255) + 1
    affine_b = (1 << 192) + 3

    def retained_validator(_reference: object) -> int:
        return whole_word ^ affine_b

    object.__setattr__(images, "_output_validate", retained_validator)
    assert audit_callback_future_payloads(ledger)


@pytest.mark.parametrize("alias", (True, 0.0, 1.0))
def test_image_integer_aliases_and_foreign_sorts_reject_without_mutation(
    alias: bool | float,
) -> None:
    ledger, source, signature, geometry, action, images, _, executor = (
        recursive_field_image_setup()
    )
    valid = executor.image(action, source, geometry, signature)
    before = ledger.snapshot()
    forged = FieldImageID(valid.owner, valid.kind, valid.local_id)
    object.__setattr__(forged, "local_id", alias)
    with pytest.raises(ValueError, match="malformed"):
        images.resolve(forged)
    foreign = FieldImageID(ArenaToken("foreign-image"), valid.kind, valid.local_id)
    with pytest.raises(ValueError, match="different arena"):
        images.resolve(foreign)
    wrong_kind = FieldImageID(valid.owner, "field-transfer", valid.local_id)
    with pytest.raises(ValueError, match="different arena or node kind"):
        images.resolve(wrong_kind)
    assert ledger.snapshot() == before


def test_foreign_request_ids_reject_before_adapter_or_warm_cache_lookup() -> None:
    (
        ledger,
        source,
        signature,
        geometry,
        action,
        images,
        adapter,
        transfers,
        executor,
    ) = field_transfer_setup()
    executor.transfer(action, source, geometry, signature)
    request_count = ledger.counters.get("field_transfer_binding_requests", 0)

    def poison(_value: object) -> Never:
        raise AssertionError("foreign ID reached family validation")

    object.__setattr__(transfers, "_action_validate", poison)
    foreign = FieldCellActionID(
        ArenaToken("foreign-actions"),
        action.kind,
        action.local_id,
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="different arena"):
        executor.transfer(foreign, source, geometry, signature)
    with pytest.raises(ValueError, match="different arena"):
        executor.application(
            foreign,
            source,
            geometry,
            signature,
            FieldTransferPortID(adapter.port_owner, "test-boundary", 0),
        )
    assert ledger.counters.get("field_transfer_binding_requests", 0) == request_count
    assert ledger.snapshot() == before
    assert images.retained_images == 0


def test_foreign_source_rejects_before_other_request_range_lookups() -> None:
    (
        ledger,
        _,
        signature,
        geometry,
        action,
        _,
        _,
        transfers,
        executor,
    ) = field_transfer_setup()
    _, foreign_source, _, _, _, _, _, _ = recursive_field_image_setup()

    def poison(_value: object) -> Never:
        raise AssertionError("foreign source triggered action range validation")

    object.__setattr__(transfers, "_action_validate", poison)
    assert_rejected_atomically(
        ledger,
        lambda: executor.transfer(action, foreign_source, geometry, signature),
        ValueError,
        match="different arena",
    )


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("first_active", True),
        ("last_active", 0.0),
        ("extent", True),
        ("growth", 0.0),
        ("activity", 1),
        ("terminated", 0),
    ),
)
def test_field_image_summary_rejects_numeric_aliases(
    field: Literal[
        "activity", "extent", "first_active", "growth", "last_active", "terminated"
    ],
    value: bool | float,
) -> None:

    values: dict[str, object] = {
        "activity": True,
        "first_active": 0,
        "last_active": 0,
        "extent": 1,
        "growth": 0,
        "terminated": False,
    }
    values[field] = value
    with pytest.raises((TypeError, ValueError)):
        FieldImageSummary(**cast(_SummaryArguments, values))


def _completed_image(
    executor: RecursiveFieldImageExecutor[RecursiveImageTestAdapter],
    action: FieldCellActionID,
    source: SourceBindingID,
    geometry: FieldGeometryID,
    signature: PortSignatureID,
) -> tuple[FieldImageID, FieldImageRecord]:
    image = executor.image(action, source, geometry, signature)
    return image, executor.images.resolve(image)
