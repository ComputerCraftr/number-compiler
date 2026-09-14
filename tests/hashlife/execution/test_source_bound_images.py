from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.source_image_seals import publication_seal
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class _Action:
    digits: tuple[int, ...]


class _DecimalAdapter:
    family = "test-decimal"
    semantic_version = "test-decimal-v1"

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.primitive_calls = 0
        self.projection_calls = 0

    def validate_source(self, source: object) -> None:
        if type(source) is not int or source < 0:
            raise ValueError("invalid decimal source")

    def validate_action(self, action: object) -> None:
        if type(action) is not _Action or any(
            type(digit) is not int or not 0 <= digit < 10 for digit in action.digits
        ):
            raise ValueError("invalid decimal action")

    def validate_payload(self, payload: object) -> None:
        if type(payload) is not int or payload < 0:
            raise ValueError("invalid decimal payload")

    def identity_action(self, _source: object) -> _Action:
        return _Action(())

    def action_children(self, action: object) -> tuple[_Action, _Action] | None:
        self.validate_action(action)
        assert isinstance(action, _Action)
        if len(action.digits) <= 1:
            return None
        split = len(action.digits) // 2
        return _Action(action.digits[:split]), _Action(action.digits[split:])

    def compose_actions(self, before: object, after: object) -> _Action:
        self.validate_action(before)
        self.validate_action(after)
        assert isinstance(before, _Action) and isinstance(after, _Action)
        return _Action(before.digits + after.digits)

    def admit_source(self, source: object) -> SourceImageCandidate:
        self.validate_source(source)
        assert isinstance(source, int)
        return SourceImageCandidate(source, 1, (0, 0), radix=10)

    def apply_primitive(
        self, action: object, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert isinstance(action, _Action) and len(action.digits) == 1
        assert isinstance(source.payload, int)
        previous = source.binding.action
        assert isinstance(previous, _Action)
        self.primitive_calls += 1
        value = source.payload * 10 + action.digits[0]
        failure = source.failure_prefix
        if failure is None and value == 123:
            failure = len(previous.digits)
        return SourceImageCandidate(
            value,
            1,
            (value % 2, value % 3),
            radix=10,
            failure_prefix=failure,
        )

    def compose_chronological(
        self,
        action: object,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert before.binding.source == source.binding.source
        return SourceImageCandidate(
            after.payload,
            after.binding.extent,
            after.binding.boundary_ports,
            after.binding.orientation,
            after.binding.radix,
            after.binding.precision,
            after.failure_prefix,
        )

    def admitted_input_key(
        self, action: object, source: SourceImageView
    ) -> object | None:
        self.validate_action(action)
        # Decimal append has one relative transfer law for every exact action.
        assert isinstance(source.payload, int)
        return 0

    def transport_reuse(
        self,
        action: object,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert isinstance(action, _Action)
        assert isinstance(source.payload, int)
        # This adapter only admits relative reuse for a one-digit source state.
        value = source.payload
        for digit in action.digits:
            value = value * 10 + digit
        assert cached_source.binding.source == cached_result.binding.source
        return SourceImageCandidate(
            value,
            cached_result.binding.extent,
            (value % 2, value % 3),
            cached_result.binding.orientation,
            cached_result.binding.radix,
            cached_result.binding.precision,
            cached_result.failure_prefix,
        )

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.projection_calls += 1
        if demand.name != "value":
            raise ValueError("unsupported projection")
        return SourceImageProjection(image.payload)

    def first_failure(self, image: SourceImageView) -> object | None:
        return (
            None
            if image.failure_prefix is None
            else (image.failure_prefix, image.payload)
        )


def _runtime(
    *, max_nodes: int | None = None, max_entries: int | None = None
) -> tuple[ResourceLedger, SourceBoundSchedulerCore, _DecimalAdapter]:
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=max_entries)
    core = SourceBoundSchedulerCore(ledger)
    adapter = _DecimalAdapter(ledger)
    core.register(adapter)
    return ledger, core, adapter


def test_composite_applies_after_to_the_exact_before_image_and_reuses_it() -> None:
    ledger, core, adapter = _runtime()
    action = _Action((1, 2, 3, 4))
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
    workspace = next(
        row for row in ledger.inventory() if row.role == "source_image_workspace"
    )
    assert workspace.entries == workspace.nodes == 0
    assert ledger.counters["source_image_chronological_compositions"] == 3


def test_projection_is_demanded_once_and_never_becomes_action_identity() -> None:
    _, core, adapter = _runtime()
    image = core.apply(adapter, 7, _Action((8, 9)))
    demand = SourceImageDemand("value")
    first = core.projection(adapter, image, demand)
    second = core.projection(adapter, image, demand)
    assert first == second == SourceImageProjection(789)
    assert adapter.projection_calls == 1
    assert type(first) is SourceImageProjection and type(image) is SourceImageID


def test_powered_repetition_reuses_relative_transfer_not_cumulative_endpoint() -> None:
    ledger, core, adapter = _runtime()
    action = _Action((1,) * 32)
    image = core.apply(adapter, 0, action)
    assert core.view(image).payload == int("1" * 32)
    assert adapter.primitive_calls == 1
    assert ledger.counters["source_image_relative_transfer_hits"] >= 5


def test_foreign_adapter_image_and_forged_binding_are_rejected() -> None:
    _, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    other_ledger = ResourceLedger()
    other = _DecimalAdapter(other_ledger)
    other_core = SourceBoundSchedulerCore(other_ledger)
    other_core.register(other)
    with pytest.raises(ValueError, match="different arena"):
        other_core.view(image)
    record = core.resolve(image)
    core._nodes[image.local_id] = replace(
        record,
        binding=replace(record.binding, family="forged-family"),
    )
    with pytest.raises(ValueError, match="publication record was altered"):
        core.projection(adapter, image, SourceImageDemand("value"))


@pytest.mark.parametrize("field", ("extent", "boundary_ports", "action", "payload"))
def test_same_family_image_record_mutation_is_rejected(field: str) -> None:
    _, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    record = core.resolve(image)
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
            record, binding=replace(record.binding, action=_Action((9,)))
        )
    core._nodes[image.local_id] = poisoned
    with pytest.raises(ValueError, match="publication record was altered"):
        core.projection(adapter, image, SourceImageDemand("value"))


def test_record_cannot_replace_its_data_and_self_carried_seal() -> None:
    ledger, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    record = core.resolve(image)
    binding = replace(record.binding, extent=999)
    forged_seal = publication_seal((binding, record.payload, None), ledger)
    core._nodes[image.local_id] = replace(
        record, binding=binding, publication_snapshot=forged_seal
    )
    with pytest.raises(ValueError, match="publication record was altered"):
        core.view(image)


def test_projection_cannot_replace_its_value_and_self_carried_seal() -> None:
    ledger, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    demand = SourceImageDemand("value")
    core.projection(adapter, image, demand)
    key = image, demand
    record = core._projections[key]
    projection = replace(record.projection, value=999)
    forged_seal = publication_seal((image, demand, projection), ledger)
    core._projections[key] = replace(
        record, projection=projection, publication_snapshot=forged_seal
    )
    with pytest.raises(ValueError, match="projection record was altered"):
        core.projection(adapter, image, demand)


def test_failure_descent_requires_a_recorded_minimum_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, core, adapter = _runtime()
    failed = core.apply(adapter, 0, _Action((1, 2, 3)))
    assert core.first_failure(adapter, failed) == (2, 123)
    healthy = core.apply(adapter, 0, _Action((4,)))
    assert core.first_failure(adapter, healthy) is None
    monkeypatch.setattr(adapter, "first_failure", lambda _image: (0, 4))
    with pytest.raises(ValueError, match="fabricated failure"):
        core.first_failure(adapter, healthy)


def test_in_place_frozen_binding_mutation_is_detected_on_warm_projection() -> None:
    _, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    demand = SourceImageDemand("value")
    core.projection(adapter, image, demand)
    object.__setattr__(core.resolve(image).binding, "extent", 999)
    with pytest.raises(ValueError, match="publication record was altered"):
        core.projection(adapter, image, demand)


def test_in_place_frozen_projection_mutation_is_detected() -> None:
    _, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    demand = SourceImageDemand("value")
    projected = core.projection(adapter, image, demand)
    object.__setattr__(projected, "value", 999)
    with pytest.raises(ValueError, match="projection record was altered"):
        core.projection(adapter, image, demand)


def test_first_failure_survives_a_later_successful_primitive() -> None:
    _, core, adapter = _runtime()
    failed = core.apply(adapter, 0, _Action((1, 2, 3, 4)))
    assert core.view(failed).payload == 1234
    assert core.first_failure(adapter, failed) == (2, 1234)


def test_indirect_action_cycle_is_rejected_and_workspace_is_released(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, core, adapter = _runtime()
    first, second = _Action((1, 2)), _Action((3, 4))

    def cyclic(action: object) -> tuple[_Action, _Action] | None:
        if action == first:
            return second, _Action(())
        if action == second:
            return first, _Action(())
        return None

    monkeypatch.setattr(adapter, "action_children", cyclic)

    def cyclic_compose(before: object, _after: object) -> _Action:
        assert isinstance(before, _Action)
        return first if before == second else second

    monkeypatch.setattr(adapter, "compose_actions", cyclic_compose)
    with pytest.raises(ValueError, match="cycle"):
        core.apply(adapter, 0, first)
    workspace = next(
        row for row in ledger.inventory() if row.role == "source_image_workspace"
    )
    assert workspace.entries == workspace.nodes == 0


def test_mutable_hash_objects_are_not_admitted_as_semantic_keys() -> None:
    _, core, adapter = _runtime()

    class MutableHash:
        def __hash__(self) -> int:
            return 1

    with pytest.raises(TypeError, match="structural immutable"):
        core.apply(adapter, MutableHash(), _Action((1,)))


def test_cyclic_or_large_inline_descriptors_must_be_interned() -> None:
    _, core, adapter = _runtime()

    @dataclass(frozen=True, slots=True)
    class Cyclic:
        child: object | None = None

    cyclic = Cyclic()
    object.__setattr__(cyclic, "child", cyclic)
    with pytest.raises(ValueError, match="reference cycle"):
        core.apply(adapter, cyclic, _Action((1,)))
    with pytest.raises(ValueError, match="intern it in an arena"):
        core.apply(adapter, tuple(range(128)), _Action((1,)))


def test_budget_refusal_does_not_publish_an_orphan_image() -> None:
    # Adapter registration consumes one entry.  The origin needs two more
    # entries atomically (node and binding), so this request must fail cleanly.
    ledger, core, adapter = _runtime(max_nodes=8, max_entries=2)
    before = ledger.snapshot()
    with pytest.raises(Exception, match="budget exceeded"):
        core.apply(adapter, 0, _Action((1,)))
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert len(core._nodes) == len(core._origins) == 0


def test_handle_subclasses_cannot_alias_the_image_sort() -> None:
    _, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))

    @dataclass(frozen=True, slots=True)
    class ForgedImage(SourceImageID):
        pass

    forged = ForgedImage(image.owner, image.kind, image.local_id)
    with pytest.raises(TypeError, match="source-bound image"):
        core.view(forged)


def test_clear_invalidates_handles_and_dispose_releases_adapter() -> None:
    ledger, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1, 2)))
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
    second = core.apply(adapter, 3, _Action((4,)))
    assert core.view(second).payload == 34
    core.dispose()
    with pytest.raises(ValueError, match="disposed"):
        core.apply(adapter, 0, _Action((1,)))
    adapter_row = next(
        row for row in ledger.inventory() if row.role == "source_image_adapter"
    )
    assert adapter_row.entries == 0
