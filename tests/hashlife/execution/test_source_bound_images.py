from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass, replace
from typing import cast

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
    SourceImageApplyKey,
    SourceImageRecord,
    SourceImageRelativeApplication,
    SourceImageRelativeKey,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.source_image_seals import (
    PublicationSeal,
    TypedPayloadKey,
    publication_seal,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.stores import LedgerDict, LedgerList
from tests.support.source_bound_images import (
    DecimalImageAction,
    DecimalImageAdapter,
    assert_budget_refusal,
    one_image,
    source_audit,
    source_image_runtime,
)


def _assert_source_image_workspace_empty(ledger: ResourceLedger) -> None:
    entry = next(
        row for row in ledger.inventory() if row.role == "source_image_workspace"
    )
    assert entry.entries == entry.nodes == 0


def _publication_snapshot(
    ledger: ResourceLedger,
    binding: SourceImageBinding,
    payload: object,
    failure_prefix: object | None,
    provenance: tuple[str, object, object | None],
) -> PublicationSeal:
    return publication_seal(
        (binding, payload, failure_prefix, provenance),
        ledger,
    )


class _AuditedDecimalAdapter(DecimalImageAdapter):
    def __init__(self, ledger: ResourceLedger, *, reject: bool = False) -> None:
        super().__init__(ledger)
        self.binding_audits = 0
        self.reject_binding = reject

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: object,
        failure_prefix: object | None,
    ) -> None:
        self.binding_audits += 1
        if (
            self.reject_binding
            or failure_prefix is not None
            or binding.family != self.family
            or binding.semantic_version != self.semantic_version
            or type(binding.source) is not int
            or type(binding.action) is not DecimalImageAction
            or type(payload) is not int
        ):
            raise ValueError("invalid decimal source image binding")


def test_composite_applies_after_to_the_exact_before_image_and_reuses_it() -> None:
    ledger, core, adapter = source_image_runtime()
    action = DecimalImageAction((1, 2, 3, 4))
    image = core.apply(adapter, 0, action)
    view = core.view(image)
    assert view.payload == 1234
    assert view.binding.source == 0
    assert view.binding.action == action
    assert view.binding.boundary_ports == (0, 1)
    assert adapter.primitive_calls == 4
    before = ledger.snapshot()
    assert core.apply(adapter, 0, action) == image
    after = ledger.snapshot()
    assert adapter.primitive_calls == 4
    assert after.entries == before.entries
    assert after.nodes == before.nodes
    _assert_source_image_workspace_empty(ledger)
    workspace_snapshot = core.audit_snapshot().workspace
    assert (
        dict(ledger.iter_containers())[workspace_snapshot.owner]
        is workspace_snapshot.store_identity
    )
    assert ledger.is_factory_container(workspace_snapshot.store_identity)
    assert not tuple(
        violation
        for violation in audit_execution_ownership(ledger).violations
        if "._workspace" in violation.path
    )
    assert ledger.counters["source_image_chronological_compositions"] == 3


def test_projection_is_demanded_once_and_never_becomes_action_identity() -> None:
    _, core, adapter = source_image_runtime()
    image = core.apply(adapter, 7, DecimalImageAction((8, 9)))
    demand = SourceImageDemand("value")
    first = core.projection(adapter, image, demand)
    second = core.projection(adapter, image, demand)
    assert first == second == SourceImageProjection(789)
    assert adapter.projection_calls == 1
    assert type(first) is SourceImageProjection and type(image) is SourceImageID


def test_projection_cache_distinguishes_boolean_and_integer_parameters() -> None:
    class TypedProjection(DecimalImageAdapter):
        def project(
            self, image: SourceImageView, demand: SourceImageDemand
        ) -> SourceImageProjection:
            self.projection_calls += 1
            return SourceImageProjection(
                11 if type(demand.parameters[0]) is bool else 22
            )

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = TypedProjection(ledger)
    core.register(adapter)
    image = core.apply(adapter, 7, DecimalImageAction((8,)))
    boolean = SourceImageDemand("value", (True,))
    integer = SourceImageDemand("value", (1,))
    assert core.projection(adapter, image, boolean).value == 11
    assert core.projection(adapter, image, integer).value == 22
    assert core.projection(adapter, image, boolean).value == 11
    assert adapter.projection_calls == 2
    assert ledger.counters["source_image_projection_publications"] == 2
    assert ledger.counters["source_image_projection_hits"] == 1
    assert not source_audit(ledger, core).invalid


def test_optional_family_binding_audit_runs_once_without_runtime_work() -> None:
    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = _AuditedDecimalAdapter(ledger)
    core.register(adapter)
    image = core.apply(adapter, 7, DecimalImageAction((8,)))
    before = ledger.snapshot().counters

    audit = source_audit(ledger, core)

    assert audit.valid(image)
    assert adapter.binding_audits == len(core.audit_snapshot().nodes)
    assert ledger.snapshot().counters == before
    core.dispose()


def test_optional_family_binding_audit_rejects_bad_record() -> None:
    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = _AuditedDecimalAdapter(ledger, reject=True)
    core.register(adapter)
    image = core.apply(adapter, 7, DecimalImageAction((8,)))

    audit = source_audit(ledger, core)

    assert adapter.binding_audits == len(core.audit_snapshot().nodes)
    assert not audit.valid(image)
    assert audit.invalid
    core.dispose()


def test_typed_demand_hashes_shared_descriptor_dags_without_expansion() -> None:
    def shared(levels: int, leaf: int | bool) -> object:
        result: object = leaf
        for _ in range(levels):
            result = (result, result)
        return result

    first = SourceImageDemand("value", (shared(50, 1),))
    equal = SourceImageDemand("value", (shared(50, 1),))
    different = SourceImageDemand("value", (shared(50, True),))
    assert first == equal
    assert hash(first) == hash(equal)
    assert first != different


def test_origin_cache_distinguishes_boolean_and_integer_sources() -> None:
    class TypedSource(DecimalImageAdapter):
        def validate_source(self, source: object) -> None:
            if type(source) not in (bool, int):
                raise ValueError("invalid source")

        def admit_source(self, source: object) -> SourceImageCandidate:
            return SourceImageCandidate(11 if type(source) is bool else 22, 0)

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = TypedSource(ledger)
    core.register(adapter)
    boolean = core.origin(adapter, True)
    integer = core.origin(adapter, 1)
    assert boolean != integer
    assert core.view(boolean).payload == 11
    assert core.view(integer).payload == 22
    assert core.origin(adapter, True) == boolean
    assert core.origin(adapter, 1) == integer
    assert ledger.counters["source_image_origin_publications"] == 2
    assert ledger.counters["source_image_origin_hits"] == 2
    assert not source_audit(ledger, core).invalid


def test_application_cache_distinguishes_boolean_and_integer_actions() -> None:
    class TypedAction:
        family = "test-typed-action"
        semantic_version = "test-typed-action-v1"

        def __init__(self, ledger: ResourceLedger) -> None:
            self.ledger = ledger
            self.primitive_calls = 0

        def validate_source(self, source: object) -> None:
            if type(source) is not int or source < 0:
                raise ValueError("invalid source")

        def validate_action(self, action: object) -> None:
            if type(action) not in (bool, int):
                raise ValueError("invalid action")

        def validate_payload(self, payload: object) -> None:
            if type(payload) is not int or payload < 0:
                raise ValueError("invalid payload")

        def identity_action(self, source: object) -> int:
            return 0

        def action_children(self, action: object) -> None:
            self.validate_action(action)

        def compose_actions(self, before: object, after: object) -> object:
            self.validate_action(before)
            self.validate_action(after)
            return after

        def apply_primitive(
            self, action: object, source: SourceImageView
        ) -> SourceImageCandidate:
            self.primitive_calls += 1
            return SourceImageCandidate(11 if type(action) is bool else 22, 1)

        def admit_source(self, source: object) -> SourceImageCandidate:
            self.validate_source(source)
            if type(source) is not int:
                raise AssertionError("typed action source was not an integer")
            return SourceImageCandidate(source, 0)

        def compose_chronological(
            self,
            action: object,
            source: SourceImageView,
            before: SourceImageView,
            after: SourceImageView,
        ) -> SourceImageCandidate:
            return SourceImageCandidate(after.payload, after.binding.extent)

        def admitted_input_key(self, action: object, source: SourceImageView) -> None:
            return None

        def transport_reuse(
            self,
            action: object,
            cached_source: SourceImageView,
            cached_result: SourceImageView,
            source: SourceImageView,
        ) -> SourceImageCandidate:
            raise AssertionError("typed action test has no relative reuse")

        def project(
            self, image: SourceImageView, demand: SourceImageDemand
        ) -> SourceImageProjection:
            return SourceImageProjection(image.payload)

        def first_failure(self, image: SourceImageView) -> None:
            return None

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = TypedAction(ledger)
    core.register(adapter)
    boolean = core.apply(adapter, 7, True)
    integer = core.apply(adapter, 7, 1)
    assert boolean != integer
    assert core.view(boolean).payload == 11
    assert core.view(integer).payload == 22
    assert adapter.primitive_calls == 2
    assert ledger.counters["source_image_primitive_applications"] == 2
    origin = core.origin(adapter, 7)
    with pytest.raises(ValueError, match="application binding was altered"):
        core.validate_application_binding(
            adapter,
            SourceImageApplyKey((adapter.family, adapter.semantic_version), origin, 1),
            boolean,
        )
    assert not source_audit(ledger, core).invalid


def test_active_action_stack_distinguishes_boolean_and_integer_ids() -> None:
    ledger, core, _ = source_image_runtime()
    boolean = ("test-decimal", "test-decimal-v1", True)
    integer = ("test-decimal", "test-decimal-v1", 1)
    workspace = core.audit_snapshot().workspace
    store = ledger.registered_container(workspace.owner)
    assert isinstance(store, LedgerDict)
    boolean_key = (
        "active",
        (boolean[0], boolean[1], TypedPayloadKey(boolean[2])),
    )
    integer_key = (
        "active",
        (integer[0], integer[1], TypedPayloadKey(integer[2])),
    )
    ledger.reserve(workspace.owner, entries=2, nodes=2)
    store[boolean_key] = None
    assert boolean_key in workspace.entries
    assert integer_key not in workspace.entries
    store[integer_key] = None
    assert integer_key in workspace.entries
    del store[boolean_key]
    assert integer_key in workspace.entries
    del store[integer_key]
    assert not workspace.entries
    ledger.release(workspace.owner, entries=2, nodes=2)


def test_relative_cache_distinguishes_boolean_and_integer_inputs() -> None:
    class TypedRelative(DecimalImageAdapter):
        def admitted_input_key(
            self, action: object, source: SourceImageView
        ) -> bool | int:
            return True if source.payload == 7 else 1

        def transport_reuse(
            self,
            action: object,
            cached_source: SourceImageView,
            cached_result: SourceImageView,
            source: SourceImageView,
        ) -> SourceImageCandidate:
            raise AssertionError("different typed relative inputs reused an effect")

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = TypedRelative(ledger)
    core.register(adapter)
    action = DecimalImageAction((8,))
    assert core.view(core.apply(adapter, 7, action)).payload == 78
    assert core.view(core.apply(adapter, 8, action)).payload == 88
    assert adapter.primitive_calls == 2
    assert ledger.counters.get("source_image_relative_transfer_hits", 0) == 0
    assert ledger.counters["source_image_relative_transfer_publications"] == 2
    assert not source_audit(ledger, core).invalid


class _TransactionalDecimal(DecimalImageAdapter):
    """Track adapter records that must roll back with failed scheduler commits."""

    def __init__(self, ledger: ResourceLedger) -> None:
        super().__init__(ledger)
        self.records: list[str] = []

    @contextmanager
    def composite_transaction(self) -> Generator[None, None, None]:
        checkpoint = len(self.records)
        try:
            yield
        except BaseException:
            del self.records[checkpoint:]
            raise

    def apply_primitive(
        self, action: object, source: SourceImageView
    ) -> SourceImageCandidate:
        self.records.append("primitive")
        return super().apply_primitive(action, source)

    def transport_reuse(
        self,
        action: object,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        self.records.append("relative")
        return super().transport_reuse(action, cached_source, cached_result, source)


def test_primitive_adapter_records_roll_back_when_scheduler_publication_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = _TransactionalDecimal(ledger)
    core.register(adapter)
    core.origin(adapter, 0)
    before = ledger.snapshot()

    def reject_publication(*_args: object, **_kwargs: object) -> SourceImageID:
        raise RuntimeError("injected scheduler publication failure")

    monkeypatch.setattr(core, "publish_application_result", reject_publication)
    with pytest.raises(RuntimeError, match="injected scheduler publication failure"):
        core.apply(adapter, 0, DecimalImageAction((8,)))

    assert adapter.records == []
    assert not core.audit_snapshot().applications
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_relative_adapter_records_roll_back_when_scheduler_publication_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = _TransactionalDecimal(ledger)
    core.register(adapter)
    core.apply(adapter, 0, DecimalImageAction((8,)))
    records_before = tuple(adapter.records)
    applications_before = len(core.audit_snapshot().applications)

    def reject_second_source(
        key: SourceImageApplyKey,
        source: object,
        cumulative_action: object,
        candidate: SourceImageCandidate,
        *,
        relative_key: SourceImageRelativeKey | None,
    ) -> SourceImageID:
        if source == 9:
            raise RuntimeError("injected relative publication failure")
        raise AssertionError("unexpected source in the injected publication test")

    monkeypatch.setattr(core, "publish_application_result", reject_second_source)
    with pytest.raises(RuntimeError, match="injected relative publication failure"):
        core.apply(adapter, 9, DecimalImageAction((8,)))

    assert tuple(adapter.records) == records_before
    assert len(core.audit_snapshot().applications) == applications_before
    assert ledger.counters.get("source_image_relative_transfer_hits", 0) == 0


@pytest.mark.parametrize("demanded_first", [False, True])
def test_complete_image_constructor_precedes_child_traversal(
    demanded_first: bool,
) -> None:
    class CompleteAdapter(DecimalImageAdapter):
        def apply_composite(
            self,
            action: object,
            source: SourceImageView,
            demand: SourceImageDemand | None,
        ) -> SourceImageCandidate:
            assert demand is None or demand.name == "last-digit"
            assert action == DecimalImageAction((8, 9))
            assert source.payload == 7
            return SourceImageCandidate(789, 1, (1, 0), radix=10)

        def apply_primitive(
            self,
            action: object,
            source: SourceImageView,
        ) -> SourceImageCandidate:
            raise AssertionError("complete-image construction descended to a child")

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = CompleteAdapter(ledger)
    core.register(adapter)
    action, demand = DecimalImageAction((8, 9)), SourceImageDemand("last-digit")
    if demanded_first:
        image = core.apply_demanded(adapter, 7, action, demand)
        repeated = core.apply(adapter, 7, action)
    else:
        image = core.apply(adapter, 7, action)
        repeated = core.apply_demanded(adapter, 7, action, demand)
    assert repeated == image
    assert ledger.counters["source_image_application_hits"] == 1
    assert core.view(image).payload == 789
    assert len(core.audit_snapshot().nodes) == 2  # Origin and final image only.
    assert adapter.projection_calls == 0
    assert core.projection(adapter, repeated, SourceImageDemand("value")).value == 789
    assert core.first_failure(adapter, repeated) is None
    kind = "demanded_composite" if demanded_first else "composite"
    assert ledger.counters[f"source_image_{kind}_applications"] == 1
    assert ledger.counters.get("source_image_primitive_applications", 0) == 0


def test_powered_repetition_reuses_relative_transfer_not_cumulative_endpoint() -> None:
    ledger, core, adapter = source_image_runtime()
    action = DecimalImageAction((1,) * 32)
    image = core.apply(adapter, 0, action)
    assert core.view(image).payload == int("1" * 32)
    assert adapter.primitive_calls == 1
    assert ledger.counters["source_image_relative_transfer_hits"] >= 5


@pytest.mark.parametrize("damage", ("origin", "application", "relative", "orphan"))
def test_payload_audit_rejects_redirected_or_orphaned_memo_publications(
    damage: str,
) -> None:
    ledger, core, adapter = source_image_runtime()
    core.apply(adapter, 0, DecimalImageAction((1, 2, 3, 4)))
    core.apply(adapter, 9, DecimalImageAction((5,)))
    assert not source_audit(ledger, core).invalid
    snapshot = core.audit_snapshot()
    if damage == "origin":
        first, second = tuple(snapshot.origins.items())
        origin_store = cast(
            LedgerDict[tuple[tuple[str, str], TypedPayloadKey], SourceImageID],
            snapshot.origin_store,
        )
        origin_store[first[0]] = second[1]
    elif damage == "application":
        first_application, second_application = tuple(snapshot.applications.items())[:2]
        application_store = cast(
            LedgerDict[SourceImageApplyKey, SourceImageID], snapshot.application_store
        )
        application_store[first_application[0]] = second_application[1]
    elif damage == "relative":
        first_relative, second_relative = tuple(snapshot.relative.items())[:2]
        relative_store = cast(
            LedgerDict[SourceImageRelativeKey, SourceImageRelativeApplication],
            snapshot.relative_store,
        )
        relative_store[first_relative[0]] = second_relative[1]
    else:
        orphaned_application_store = cast(
            LedgerDict[SourceImageApplyKey, SourceImageID], snapshot.application_store
        )
        orphaned_application_store.pop(next(iter(snapshot.applications)))
    assert source_audit(ledger, core).invalid


@pytest.mark.parametrize("replacement", (9, False))
def test_origin_provenance_rejects_reflected_typed_key_change(
    replacement: object,
) -> None:
    ledger, core, adapter = source_image_runtime()
    core.apply(adapter, 0, DecimalImageAction((1,)))
    assert not source_audit(ledger, core).invalid
    origin_key = next(iter(core.audit_snapshot().origins))
    typed_source = origin_key[1]
    object.__setattr__(typed_source, "value", replacement)
    assert source_audit(ledger, core).invalid


def test_payload_audit_rejects_forged_seal_and_stale_image() -> None:
    ledger, core, _, image, record = one_image()
    forged = _publication_snapshot(
        ledger,
        record.binding,
        record.payload,
        record.failure_prefix,
        record.publication_provenance,
    )
    snapshot = core.audit_snapshot()
    store = cast(LedgerList[SourceImageRecord], snapshot.node_store)
    store[image.local_id] = replace(record, publication_snapshot=forged)
    assert source_audit(ledger, core).invalid
    core.clear()
    assert not source_audit(ledger, core).valid(image)


def test_payload_audit_passes_failure_prefix_to_family_binding_auditor() -> None:
    ledger, core, _, image, record = one_image()
    failure_prefix = 7
    seal = _publication_snapshot(
        ledger,
        record.binding,
        record.payload,
        failure_prefix,
        record.publication_provenance,
    )
    snapshot = core.audit_snapshot()
    store = cast(LedgerList[SourceImageRecord], snapshot.node_store)
    store[image.local_id] = replace(
        record,
        failure_prefix=failure_prefix,
        publication_snapshot=seal,
    )
    audit = source_audit(ledger, core)
    assert (snapshot.node_owner, id(store[image.local_id])) in audit.invalid


def test_foreign_adapter_image_and_forged_binding_are_rejected() -> None:
    ledger, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1,)))
    other_ledger = ResourceLedger()
    other = DecimalImageAdapter(other_ledger)
    other_core = SourceBoundSchedulerCore(other_ledger)
    other_core.register(other)
    with pytest.raises(ValueError, match="different arena"):
        other_core.view(image)
    record = core.resolve(image)
    snapshot = core.audit_snapshot()
    store = ledger.registered_container(snapshot.node_owner)
    assert isinstance(store, LedgerList)
    store[image.local_id] = replace(
        record,
        binding=replace(record.binding, family="forged-family"),
    )
    with pytest.raises(ValueError, match="publication record was altered"):
        core.projection(adapter, image, SourceImageDemand("value"))


@pytest.mark.parametrize("field", ("extent", "boundary_ports", "action", "payload"))
def test_same_family_image_record_mutation_is_rejected(field: str) -> None:
    ledger, core, adapter, image, record = one_image()
    if field == "payload":
        poisoned = replace(record, payload=99)
    elif field == "extent":
        poisoned = replace(record, binding=replace(record.binding, extent=999))
    elif field == "boundary_ports":
        poisoned = replace(
            record, binding=replace(record.binding, boundary_ports=(9, 9))
        )
    else:
        poisoned = replace(
            record, binding=replace(record.binding, action=DecimalImageAction((9,)))
        )
    snapshot = core.audit_snapshot()
    store = ledger.registered_container(snapshot.node_owner)
    assert isinstance(store, LedgerList)
    store[image.local_id] = poisoned
    with pytest.raises(ValueError, match="publication record was altered"):
        core.projection(adapter, image, SourceImageDemand("value"))


def test_record_cannot_replace_its_data_and_self_carried_seal() -> None:
    ledger, core, _unused_adapter_binding, image, record = one_image()
    binding = replace(record.binding, extent=999)
    forged_seal = publication_seal((binding, record.payload, None), ledger)
    snapshot = core.audit_snapshot()
    store = ledger.registered_container(snapshot.node_owner)
    assert isinstance(store, LedgerList)
    store[image.local_id] = replace(
        record, binding=binding, publication_snapshot=forged_seal
    )
    with pytest.raises(ValueError, match="publication record was altered"):
        core.view(image)


def test_projection_cannot_replace_its_value_and_self_carried_seal() -> None:
    ledger, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1,)))
    demand = SourceImageDemand("value")
    core.projection(adapter, image, demand)
    key = image, demand
    snapshot = core.audit_snapshot()
    record = snapshot.projections[key]
    projection = replace(record.projection, value=999)
    forged_seal = publication_seal((image, demand, projection), ledger)
    store = ledger.registered_container(snapshot.projection_owner)
    assert isinstance(store, LedgerDict)
    store[key] = replace(
        record, projection=projection, publication_snapshot=forged_seal
    )
    with pytest.raises(ValueError, match="projection record was altered"):
        core.projection(adapter, image, demand)


def test_failure_descent_requires_a_recorded_minimum_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, core, adapter = source_image_runtime()
    failed = core.apply(adapter, 0, DecimalImageAction((1, 2, 3)))
    assert core.first_failure(adapter, failed) == (2, 123)
    healthy = core.apply(adapter, 0, DecimalImageAction((4,)))
    assert core.first_failure(adapter, healthy) is None

    def fabricated_failure(_image: SourceImageView) -> tuple[int, int]:
        return (0, 4)

    monkeypatch.setattr(adapter, "first_failure", fabricated_failure)
    with pytest.raises(ValueError, match="fabricated failure"):
        core.first_failure(adapter, healthy)


def test_in_place_frozen_binding_mutation_is_detected_on_warm_projection() -> None:
    _, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1,)))
    demand = SourceImageDemand("value")
    core.projection(adapter, image, demand)
    object.__setattr__(core.resolve(image).binding, "extent", 999)
    with pytest.raises(ValueError, match="publication record was altered"):
        core.projection(adapter, image, demand)


def test_in_place_frozen_projection_mutation_is_detected() -> None:
    _, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1,)))
    demand = SourceImageDemand("value")
    projected = core.projection(adapter, image, demand)
    object.__setattr__(projected, "value", 999)
    with pytest.raises(ValueError, match="projection record was altered"):
        core.projection(adapter, image, demand)


def test_warm_projection_rechecks_adapter_authority_before_cache_hit() -> None:
    class RevocableAdapter(DecimalImageAdapter):
        def __init__(self, ledger: ResourceLedger) -> None:
            super().__init__(ledger)
            self.revoked = False

        def validate_payload(self, payload: object) -> None:
            super().validate_payload(payload)
            if self.revoked:
                raise ValueError("payload authority was revoked")

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = RevocableAdapter(ledger)
    core.register(adapter)
    image = core.apply(adapter, 0, DecimalImageAction((1,)))
    demand = SourceImageDemand("value")
    assert core.projection(adapter, image, demand).value == 1
    assert adapter.projection_calls == 1
    adapter.revoked = True
    with pytest.raises(ValueError, match="payload authority was revoked"):
        core.projection(adapter, image, demand)
    assert adapter.projection_calls == 1


def test_first_failure_survives_a_later_successful_primitive() -> None:
    _, core, adapter = source_image_runtime()
    failed = core.apply(adapter, 0, DecimalImageAction((1, 2, 3, 4)))
    assert core.view(failed).payload == 1234
    assert core.first_failure(adapter, failed) == (2, 1234)


def test_indirect_action_cycle_is_rejected_and_workspace_is_released(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, core, adapter = source_image_runtime()
    first, second = DecimalImageAction((1, 2)), DecimalImageAction((3, 4))

    def cyclic(action: object) -> tuple[DecimalImageAction, DecimalImageAction] | None:
        if action == first:
            return second, DecimalImageAction(())
        if action == second:
            return first, DecimalImageAction(())
        return None

    monkeypatch.setattr(adapter, "action_children", cyclic)

    def cyclic_compose(before: object, _after: object) -> DecimalImageAction:
        assert isinstance(before, DecimalImageAction)
        return first if before == second else second

    monkeypatch.setattr(adapter, "compose_actions", cyclic_compose)
    with pytest.raises(ValueError, match="cycle"):
        core.apply(adapter, 0, first)
    _assert_source_image_workspace_empty(ledger)
    workspace_snapshot = core.audit_snapshot().workspace
    assert not workspace_snapshot.frames and not workspace_snapshot.values
    assert not tuple(
        violation
        for violation in audit_execution_ownership(ledger).violations
        if "._workspace" in violation.path
    )


def test_mutable_hash_objects_are_not_admitted_as_semantic_keys() -> None:
    _, core, adapter = source_image_runtime()

    class MutableHash:
        def __hash__(self) -> int:
            return 1

    with pytest.raises(TypeError, match="structural immutable"):
        core.apply(adapter, MutableHash(), DecimalImageAction((1,)))


def test_cyclic_or_large_inline_descriptors_must_be_interned() -> None:
    _, core, adapter = source_image_runtime()

    @dataclass(frozen=True, slots=True)
    class Cyclic:
        child: object | None = None

    cyclic = Cyclic()
    object.__setattr__(cyclic, "child", cyclic)
    with pytest.raises(ValueError, match="reference cycle"):
        core.apply(adapter, cyclic, DecimalImageAction((1,)))
    with pytest.raises(ValueError, match="intern it in an arena"):
        core.apply(adapter, tuple(range(128)), DecimalImageAction((1,)))


def test_budget_refusal_does_not_publish_an_orphan_image() -> None:
    # Adapter registration consumes one entry.  The origin needs two more
    # entries atomically (node and binding), so this request must fail cleanly.
    ledger, core, adapter = source_image_runtime(max_nodes=8, max_entries=2)
    assert_budget_refusal(ledger, core, adapter)
    snapshot = core.audit_snapshot()
    assert len(snapshot.nodes) == len(snapshot.origins) == 0


def test_workspace_budget_refusal_releases_its_factory_store() -> None:
    ledger, core, adapter = source_image_runtime()
    core.origin(adapter, 0)
    ledger.max_cache_entries = ledger.entries
    assert_budget_refusal(ledger, core, adapter)
    workspace = core.audit_snapshot().workspace
    assert not workspace.running and not workspace.entries
    assert not workspace.frames and not workspace.values


def test_handle_subclasses_cannot_alias_the_image_sort() -> None:
    _, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1,)))

    @dataclass(frozen=True, slots=True)
    class ForgedImage(SourceImageID):
        pass

    forged = ForgedImage(image.owner, image.kind, image.local_id)
    with pytest.raises(TypeError, match="source-bound image"):
        core.view(forged)


def test_clear_invalidates_handles_and_dispose_releases_adapter() -> None:
    ledger, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1, 2)))
    core.projection(adapter, image, SourceImageDemand("value"))
    seal_row = next(
        row for row in ledger.inventory() if row.role == "source_image_publication_seal"
    )
    assert seal_row.entries > 0 and seal_row.nodes > 0
    assert seal_row.accounting_delta == 0
    core.clear()
    with pytest.raises(ValueError, match="different arena"):
        core.view(image)
    assert all(
        row.entries == row.nodes == 0
        for row in ledger.inventory()
        if row.role
        in {
            "source_image",
            "source_image_origin",
            "source_image_application",
            "source_image_projection",
            "source_image_publication_seal",
            "source_image_relative_transfer",
            "source_image_workspace",
        }
    )
    second = core.apply(adapter, 3, DecimalImageAction((4,)))
    assert core.view(second).payload == 34
    core.dispose()
    with pytest.raises(ValueError, match="disposed"):
        core.apply(adapter, 0, DecimalImageAction((1,)))
    adapter_row = next(
        row for row in ledger.inventory() if row.role == "source_image_adapter"
    )
    assert adapter_row.entries == 0


def test_payload_audit_rejects_malformed_registered_adapter_without_callbacks() -> None:
    ledger, core, adapter = source_image_runtime()
    core.apply(adapter, 0, DecimalImageAction((1,)))
    object.__setattr__(adapter, "validate_payload", None)
    before = ledger.snapshot()
    try:
        assert source_audit(ledger, core).invalid
        assert ledger.snapshot() == before
    finally:
        core.dispose()
