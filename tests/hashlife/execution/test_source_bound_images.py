from __future__ import annotations

from dataclasses import dataclass, replace
from typing import cast

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
    _ApplyKey,
)
from number_compiler.hashlife.execution.source_image_seals import publication_seal
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.source_bound_payload_audit import (
    audit_source_bound_payloads,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.source_bound_images import (
    _Action,
    _DecimalAdapter,
    _runtime,
    _source_audit,
    assert_budget_refusal,
    one_image,
)


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
    assert dict(ledger.iter_containers())[core._workspace_owner] is (
        core._workspace._storage
    )
    assert ledger.is_factory_container(core._workspace._storage)
    assert not tuple(
        violation
        for violation in audit_execution_ownership(ledger).violations
        if "._workspace" in violation.path
    )
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


def test_projection_cache_distinguishes_boolean_and_integer_parameters() -> None:
    class TypedProjection(_DecimalAdapter):
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
    image = core.apply(adapter, 7, _Action((8,)))
    boolean = SourceImageDemand("value", (True,))
    integer = SourceImageDemand("value", (1,))
    assert core.projection(adapter, image, boolean).value == 11
    assert core.projection(adapter, image, integer).value == 22
    assert core.projection(adapter, image, boolean).value == 11
    assert adapter.projection_calls == 2
    assert ledger.counters["source_image_projection_publications"] == 2
    assert ledger.counters["source_image_projection_hits"] == 1
    assert not _source_audit(ledger, core).invalid


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
    class TypedSource(_DecimalAdapter):
        def validate_source(self, source: object) -> None:
            if type(source) not in (bool, int):
                raise ValueError("invalid source")

        def admit_source(self, source: object) -> SourceImageCandidate:
            return SourceImageCandidate(11 if type(source) is bool else 22, 0)

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = TypedSource(ledger)
    core.register(adapter)
    boolean = core._origin(adapter, True)
    integer = core._origin(adapter, 1)
    assert boolean != integer
    assert core.view(boolean).payload == 11
    assert core.view(integer).payload == 22
    assert core._origin(adapter, True) == boolean
    assert core._origin(adapter, 1) == integer
    assert ledger.counters["source_image_origin_publications"] == 2
    assert ledger.counters["source_image_origin_hits"] == 2
    assert not _source_audit(ledger, core).invalid


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

        def identity_action(self, _source: object) -> int:
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
            return SourceImageCandidate(cast(int, source), 0)

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
    origin = core._origin(adapter, 7)
    with pytest.raises(ValueError, match="application binding was altered"):
        core._validate_application_binding(
            adapter,
            _ApplyKey((adapter.family, adapter.semantic_version), origin, 1),
            boolean,
        )
    assert not _source_audit(ledger, core).invalid


def test_active_action_stack_distinguishes_boolean_and_integer_ids() -> None:
    ledger, core, _ = _runtime()
    active = core._workspace
    boolean = ("test-decimal", "test-decimal-v1", True)
    integer = ("test-decimal", "test-decimal-v1", 1)
    ledger.reserve(core._workspace_owner, entries=2, nodes=2)
    active.add_active(boolean)
    assert active.contains_active(boolean)
    assert not active.contains_active(integer)
    active.add_active(integer)
    assert active.contains_active(integer)
    active.remove_active(boolean)
    assert active.contains_active(integer)
    active.remove_active(integer)
    assert not active.contains_active(integer)
    assert len(active) == 0
    ledger.release(core._workspace_owner, entries=2, nodes=2)


def test_relative_cache_distinguishes_boolean_and_integer_inputs() -> None:
    class TypedRelative(_DecimalAdapter):
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
    action = _Action((8,))
    assert core.view(core.apply(adapter, 7, action)).payload == 78
    assert core.view(core.apply(adapter, 8, action)).payload == 88
    assert adapter.primitive_calls == 2
    assert ledger.counters.get("source_image_relative_transfer_hits", 0) == 0
    assert ledger.counters["source_image_relative_transfer_publications"] == 2
    assert not _source_audit(ledger, core).invalid


@pytest.mark.parametrize("demanded_first", [False, True])
def test_complete_image_constructor_precedes_child_traversal(
    demanded_first: bool,
) -> None:
    class CompleteAdapter(_DecimalAdapter):
        def apply_composite(
            self,
            action: object,
            source: SourceImageView,
            demand: SourceImageDemand | None,
        ) -> SourceImageCandidate:
            assert demand is None or demand.name == "last-digit"
            assert action == _Action((8, 9))
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
    action, demand = _Action((8, 9)), SourceImageDemand("last-digit")
    if demanded_first:
        image = core.apply_demanded(adapter, 7, action, demand)
        repeated = core.apply(adapter, 7, action)
    else:
        image = core.apply(adapter, 7, action)
        repeated = core.apply_demanded(adapter, 7, action, demand)
    assert repeated == image
    assert ledger.counters["source_image_application_hits"] == 1
    assert core.view(image).payload == 789
    assert len(core._nodes) == 2  # Original source and final image only.
    assert adapter.projection_calls == 0
    assert core.projection(adapter, repeated, SourceImageDemand("value")).value == 789
    assert core.first_failure(adapter, repeated) is None
    kind = "demanded_composite" if demanded_first else "composite"
    assert ledger.counters[f"source_image_{kind}_applications"] == 1
    assert ledger.counters.get("source_image_primitive_applications", 0) == 0


def test_powered_repetition_reuses_relative_transfer_not_cumulative_endpoint() -> None:
    ledger, core, adapter = _runtime()
    action = _Action((1,) * 32)
    image = core.apply(adapter, 0, action)
    assert core.view(image).payload == int("1" * 32)
    assert adapter.primitive_calls == 1
    assert ledger.counters["source_image_relative_transfer_hits"] >= 5


@pytest.mark.parametrize("damage", ("origin", "application", "relative", "orphan"))
def test_payload_audit_rejects_redirected_or_orphaned_memo_publications(
    damage: str,
) -> None:
    ledger, core, adapter = _runtime()
    core.apply(adapter, 0, _Action((1, 2, 3, 4)))
    core.apply(adapter, 9, _Action((5,)))
    assert not _source_audit(ledger, core).invalid
    if damage == "origin":
        first, second = tuple(core._origins.items())
        core._origins[first[0]] = second[1]
    elif damage == "application":
        first_application, second_application = tuple(core._applications.items())[:2]
        core._applications[first_application[0]] = second_application[1]
    elif damage == "relative":
        first_relative, second_relative = tuple(core._relative.items())[:2]
        core._relative[first_relative[0]] = second_relative[1]
    else:
        core._applications.pop(next(iter(core._applications)))
    assert _source_audit(ledger, core).invalid


@pytest.mark.parametrize("replacement", (9, False))
def test_origin_provenance_rejects_reflected_typed_key_change(
    replacement: object,
) -> None:
    ledger, core, adapter = _runtime()
    core.apply(adapter, 0, _Action((1,)))
    assert not _source_audit(ledger, core).invalid
    origin_key = next(iter(core._origins))
    typed_source = origin_key[1]
    object.__setattr__(typed_source, "value", replacement)
    assert _source_audit(ledger, core).invalid


def test_payload_audit_rejects_forged_seal_and_stale_image() -> None:
    ledger, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    record = core._nodes[image.local_id]
    forged = publication_seal(
        (
            record.binding,
            record.payload,
            record.failure_prefix,
            record.publication_provenance,
        ),
        ledger,
    )
    core._nodes[image.local_id] = replace(record, publication_snapshot=forged)
    assert _source_audit(ledger, core).invalid
    core.clear()
    assert not _source_audit(ledger, core).valid(image)


def test_prime_source_payload_audit_is_read_only_at_the_work_limit() -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
        PrimeSuccessorImageAdapter,
        PrimeSuccessorSource,
    )

    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        action = arena.prefix(11)
        image = core.apply_demanded(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            action,
            SourceImageDemand("rank-before", (11,)),
        )
        core.projection(adapter, image, SourceImageDemand("rank-before", (11,)))
        dag.max_work = dag.work
        before, work = dag.ledger.snapshot(), dag.work
        report = audit_registered_payloads(dag.ledger)
        after = dag.ledger.snapshot()
        assert (
            report.forbidden_future_payloads,
            report.unbounded_future_integers,
            report.unknown_payloads,
        ) == (0, 0, 0)
        assert after == before
        assert dag.work == work
    finally:
        core.dispose()
        arena.close()
        dag.close()


@pytest.mark.parametrize("damage", ("node-width", "node-child", "container"))
def test_prime_source_payload_audit_rejects_forged_arena_ownership(
    damage: str,
) -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
        PrimeSuccessorImageAdapter,
        PrimeSuccessorSource,
    )

    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        core.apply(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            arena.prefix(11),
        )
        containers = dict(dag.ledger.iter_containers())
        if damage == "node-width":
            object.__setattr__(arena._nodes[2], "width", 99)
        elif damage == "node-child":
            composite = next(
                node for node in arena._nodes.values() if node.before is not None
            )
            object.__setattr__(composite, "before", arena.descriptor_id)
        else:
            containers[arena._nodes.owner] = object()
        audit = audit_source_bound_payloads(dag.ledger, (core,), containers)
        assert audit.invalid
    finally:
        core.dispose()
        arena.close()
        dag.close()


def test_prime_source_payload_audit_rejects_replaced_adapter_arena() -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
        PrimeSuccessorImageAdapter,
        PrimeSuccessorSource,
    )

    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    foreign_dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    foreign = PrimeSuccessorActionArena(foreign_dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        core.apply(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            arena.prefix(7),
        )
        adapter.arena = foreign
        audit = _source_audit(dag.ledger, core)
        assert audit.invalid
    finally:
        adapter.arena = arena
        core.dispose()
        arena.close()
        foreign.close()
        dag.close()
        foreign_dag.close()


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
    _, core, adapter, image, record = one_image()
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
    ledger, core, _unused_adapter_binding, image, record = one_image()
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


def test_warm_projection_rechecks_adapter_authority_before_cache_hit() -> None:
    class RevocableAdapter(_DecimalAdapter):
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
    image = core.apply(adapter, 0, _Action((1,)))
    demand = SourceImageDemand("value")
    assert core.projection(adapter, image, demand).value == 1
    assert adapter.projection_calls == 1
    adapter.revoked = True
    with pytest.raises(ValueError, match="payload authority was revoked"):
        core.projection(adapter, image, demand)
    assert adapter.projection_calls == 1


def test_public_reverse_warm_projection_validates_binding_before_cache_hit() -> None:
    term = ReverseAddPoweredTerm(196, 2)
    expected = term.digit(0)
    before_hits = term._ledger.counters.get("source_image_projection_hits", 0)
    original = term.seed
    term.seed = original + 1
    try:
        with pytest.raises(ValueError, match="binding changed"):
            term.digit(0)
        assert (
            term._ledger.counters.get("source_image_projection_hits", 0) == before_hits
        )
    finally:
        term.seed = original
    assert term.digit(0) == expected


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
    assert not core._workspace.frames and not core._workspace.values
    assert not tuple(
        violation
        for violation in audit_execution_ownership(ledger).violations
        if "._workspace" in violation.path
    )


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
    assert_budget_refusal(ledger, core, adapter)
    assert len(core._nodes) == len(core._origins) == 0


def test_workspace_budget_refusal_releases_its_factory_store() -> None:
    ledger, core, adapter = _runtime()
    core._origin(adapter, 0)
    ledger.max_cache_entries = ledger.entries
    assert_budget_refusal(ledger, core, adapter)
    assert not core._workspace.running and not core._workspace
    assert not core._workspace.frames and not core._workspace.values


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


def test_payload_audit_rejects_malformed_registered_adapter_without_callbacks() -> None:
    ledger, core, adapter = _runtime()
    core.apply(adapter, 0, _Action((1,)))
    key = next(iter(core._adapters))
    core._adapters[key] = cast(SourceBoundImageAdapter, object())
    before = ledger.snapshot()
    try:
        assert _source_audit(ledger, core).invalid
        assert ledger.snapshot() == before
    finally:
        core.dispose()


@pytest.mark.parametrize("damage", ("fresh-prime", "forbidden-residues", "port-count"))
def test_prime_descriptor_authority_and_port_extent_are_immutable(damage: str) -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
        PrimeSuccessorImageAdapter,
        PrimeSuccessorSource,
    )

    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 11)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        action = arena.prefix(1)
        core.apply(adapter, PrimeSuccessorSource(arena.descriptor_id, 0), action)
        if damage == "fresh-prime":
            # Both fresh-prime phases on the old period are 1; phase checks alone
            # cannot distinguish the admitted successor 11 from the later 19.
            assert 210 % 11 == 210 % 19 == 1
            object.__setattr__(arena.descriptor, "fresh_prime", 19)
        elif damage == "forbidden-residues":
            object.__setattr__(arena.descriptor, "forbidden_residues", (2,))
        else:
            effect = arena.port_effect(arena.base, 0)
            too_many = arena.descriptor.parent_period + 1
            object.__setattr__(effect, "parent_survivors", too_many)
            object.__setattr__(
                effect, "surviving_values", too_many - effect.deleted_survivors
            )
        before, work = dag.ledger.snapshot(), dag.work
        assert _source_audit(dag.ledger, core).invalid
        assert dag.ledger.snapshot() == before
        assert dag.work == work
        if damage != "port-count":
            with pytest.raises(
                ValueError, match="descriptor lost its source authority"
            ):
                arena.node(action)
    finally:
        core.dispose()
        arena.close()
        dag.close()
