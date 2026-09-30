"""Independent audits for canonical tile actions and demanded result pins."""

from __future__ import annotations

from dataclasses import replace
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    ReverseFrobeniusPlan,
    ReverseGrowthRunCertificate,
)
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.actions.tile_action_algebra import (
    PrimitiveTileAction as _Action,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.execution.tile_fused_kernel import LeafProductKey
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
    LocalInterfaceID,
)
from number_compiler.hashlife.observation.tile_projection import (
    LazyProjection,
    import_exact_source,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    CompletedInterfaceResult,
    FusedInterfaceKey,
    PoweredInterfaceKey,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileArena
from number_compiler.resources.field_image_payload_audit import (
    audit_field_image_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.support.assertions import assert_rejected_atomically


def _runtime(
    base: int = 2,
) -> tuple[ResourceLedger, PrimitiveTileKernelAdapter, TileScheduler, LazyProjection]:
    ledger = ResourceLedger()
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    tiles = TileArena(ledger)
    kernels = DiamondKernelArena(ledger)
    adapter = PrimitiveTileKernelAdapter(tiles, kernels, quotients)
    action = adapter.admit(BaseBlockEffect(base))
    results = CompletedResultArena(
        tiles,
        quotients,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    scheduler = TileScheduler(tiles, results, adapter)
    effect = BaseBlockEffect(base)
    source = ExactSource(
        (1, 0, 1),
        base,
        blank=effect.blank,
        extent=4,
        alphabet_size=effect.blank,
    )
    projection = LazyProjection(
        scheduler,
        action,
        source,
        SourceGeometry(ledger, source),
        adapter.alphabet(action),
        adapter.initial_ports(action),
        adapter.wiring(action),
    )
    return ledger, adapter, scheduler, projection


def test_tile_runtime_inventory_approves_real_action_and_demand_pin() -> None:
    ledger, _, scheduler, projection = _runtime()
    try:
        projection.point(0)
        assert scheduler._pins
        _assert_payload_clean(ledger)
    finally:
        projection.close()


def test_leaf_inventory_rejects_orphan_reverse_admission_without_executing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.interfaces import (
        tile_reverse_functions as reverse_ports,
    )

    ledger, adapter, _scheduler, projection = _runtime()
    removed = {}
    try:
        projection.point(0)
        forward = next(
            key for key in adapter._leaf_records if type(key) is LeafProductKey
        )
        interface = adapter._leaf_records[forward]
        for key, value in tuple(adapter._leaf_records.items()):
            if type(key) is LeafProductKey and value == interface:
                removed[key] = adapter._leaf_records.pop(key)

        def forbidden(*_args: object) -> Never:
            raise AssertionError("inventory executed a semantic function")

        monkeypatch.setattr(reverse_ports, "reverse_leaf_components", forbidden)
        monkeypatch.setattr(adapter, "_leaf_components", forbidden)
        monkeypatch.setattr(adapter.bits, "evaluate", forbidden)
        before = ledger.snapshot()
        audit = audit_field_image_payloads(ledger)
        assert (adapter._leaf_owner, id(interface)) in audit.invalid
        assert ledger.snapshot() == before
    finally:
        adapter._leaf_records.update(removed)
        projection.close()


@pytest.mark.parametrize("squared", (False, True))
@pytest.mark.parametrize("completed", (False, True))
def test_tile_runtime_metrics_are_read_only_for_open_and_completed_applications(
    squared: bool,
    completed: bool,
) -> None:
    ledger, adapter, scheduler, projection = _runtime()
    extra = None
    try:
        application = projection._application
        if squared:
            action = adapter.power(application.action, 2)
            extra = scheduler.application(
                action,
                application.source,
                adapter.initial_ports(action),
                adapter.wiring(action),
            )
            application = extra
        if completed:
            application.complete()
        before = ledger.snapshot()
        metrics = collect_ledger_metrics(ledger)
        assert metrics.resource_audit_complete == 1
        assert metrics.canonical_parent_identity_entries == sum(
            record.left is not None and record.right is not None
            for record in adapter.tiles._nodes.values()
        )
        assert metrics.canonical_parent_identity_entries > 0
        assert ledger.snapshot() == before
    finally:
        if extra is not None:
            extra.close()
        projection.close()


def test_tile_runtime_inventory_rejects_action_signature_substitution() -> None:
    ledger, adapter, _, projection = _runtime()
    original = adapter._actions[0]
    try:
        other = adapter.admit(BaseBlockEffect(3))
        adapter._actions[0] = _Action(
            original.kernel,
            adapter.signature_for(other),
        )
        before = ledger.entries, ledger.nodes, ledger.inventory()
        with pytest.raises(ValueError, match="signature|another record"):
            adapter.admit(BaseBlockEffect(2))
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == before
        audit = audit_field_image_payloads(ledger)
        assert (adapter._action_owner, id(adapter._actions[0])) in audit.invalid
    finally:
        adapter._actions[0] = original
        projection.close()


def test_tile_runtime_inventory_recomputes_reverse_frobenius_product() -> None:
    ledger, adapter, _, projection = _runtime(10)
    action = adapter.power(projection._application.action, 2)
    original = adapter._actions[action.local_id]
    try:
        plan = original.reverse_frobenius
        assert plan is not None
        assert plan == ReverseFrobeniusPlan.for_steps(
            maximum_classes=8,
            bits=5,
            steps=2,
            growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
        )
        forged_certificate = replace(
            original,
            reverse_frobenius=replace(
                plan,
                growth_certificate=ReverseGrowthRunCertificate.for_base(10),
            ),
        )
        adapter._actions[action.local_id] = forged_certificate
        certificate_audit = audit_field_image_payloads(ledger)
        assert (
            adapter._action_owner,
            id(forged_certificate),
        ) in certificate_audit.invalid
        forged = replace(
            original,
            reverse_frobenius=ReverseFrobeniusPlan.for_steps(
                maximum_classes=8,
                bits=5,
                steps=3,
                growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
            ),
        )
        adapter._actions[action.local_id] = forged
        audit = audit_field_image_payloads(ledger)
        assert (adapter._action_owner, id(forged)) in audit.invalid
    finally:
        adapter._actions[action.local_id] = original
        projection.close()


def test_warm_action_validation_rejects_mutated_shared_growth_certificate() -> None:
    _ledger, adapter, _, projection = _runtime(10)
    action = adapter.power(projection._application.action, 2)
    certificate = DECIMAL_REVERSE_GROWTH_CERTIFICATE
    try:
        for name, invalid in (
            ("version", "forged-growth-law"),
            ("base", 10.0),
            ("base", True),
            ("maximum_consecutive_growth", 3.0),
        ):
            original = getattr(certificate, name)
            object.__setattr__(certificate, name, invalid)
            try:
                with pytest.raises(ValueError, match="growth certificate"):
                    adapter.validate_action(action)
            finally:
                object.__setattr__(certificate, name, original)
    finally:
        projection.close()


def test_tile_runtime_inventory_rejects_mutated_reverse_observation_metadata() -> None:
    ledger, _adapter, scheduler, projection = _runtime(3)
    application = projection._application
    engine = CausalTileEngine(scheduler)
    try:
        engine._run(
            CausalFrame(
                "reverse_interface",
                (application.action, application.source, *application.ports),
            ),
            tile_result=False,
        )
        key = next(
            key
            for key in scheduler.results._memo
            if type(key) is CausalInterfaceKey
            and key.observation == "reverse-output-carry"
        )
        result = scheduler.results._memo[key]
        assert type(result) is CompletedInterfaceResult
        assert result.bound_reverse_output is not None
        before = ledger.snapshot()

        object.__setattr__(key, "observation", "interface")
        try:
            audit = audit_field_image_payloads(ledger)
            assert (scheduler.results._memo_owner, id(key)) in audit.invalid
            assert ledger.snapshot() == before
        finally:
            object.__setattr__(key, "observation", "reverse-output-carry")

        output = result.bound_reverse_output
        object.__setattr__(result, "bound_reverse_output", None)
        try:
            corrupted = ledger.snapshot()
            audit = audit_field_image_payloads(ledger)
            assert (scheduler.results._memo_owner, id(key)) in audit.invalid
            assert ledger.snapshot() == corrupted
        finally:
            object.__setattr__(result, "bound_reverse_output", output)
        assert ledger.snapshot() == before
    finally:
        engine._release_workspace()
        projection.close()


def test_reverse_frobenius_plan_compilation_does_not_claim_executed_algebra() -> None:
    ledger, adapter, _, projection = _runtime(10)
    try:
        adapter.power(projection._application.action, 8)
        report = collect_ledger_metrics(ledger)
        assert report.reverse_frobenius_plan_compositions > 0
        assert report.reverse_frobenius_retained_component_nodes == sum(
            1 + len(record.reverse_frobenius.sectors)
            for record in adapter._actions.values()
            if record.reverse_frobenius is not None
        )
        assert report.resource_accounting_mismatch == 0
        action_inventory = next(
            item
            for item in report.resource_inventory
            if item.owner == adapter._action_owner
        )
        assert action_inventory.nodes == action_inventory.observed_nodes
        assert report.radial_action_operations == 0
        assert report.innovation_action_operations == 0
        assert report.source_annihilations == 0
    finally:
        projection.close()


def test_annihilated_frobenius_sectors_do_not_erase_exact_source_binding() -> None:
    ledger, adapter, scheduler, projection = _runtime(10)
    application = projection._application
    powered = adapter.power(application.action, 64)
    extra = scheduler.application(
        powered,
        application.source,
        adapter.initial_ports(powered),
        adapter.wiring(powered),
    )
    try:
        plan = adapter._action(powered).reverse_frobenius
        assert plan is not None and plan.all_source_sectors_annihilated
        assert extra.source == application.source
        assert not audit_field_image_payloads(ledger).invalid
        payloads = audit_registered_payloads(ledger)
        assert payloads.forbidden_future_payloads == 0
        assert payloads.unknown_payloads == 0
    finally:
        extra.close()
        projection.close()


def test_tile_runtime_inventory_rejects_bool_application_pin_alias() -> None:
    ledger, _, scheduler, projection = _runtime()
    try:
        projection.point(0)
        binding, lease = next(iter(scheduler._pins.items()))
        application, key = binding
        scheduler._pins.pop(binding)
        forged = (False, key)
        scheduler._pins[forged] = lease
        audit = audit_field_image_payloads(ledger)
        assert (scheduler._pin_owner, id(forged)) in audit.invalid
        scheduler._pins.pop(forged)
        scheduler._pins[(application, key)] = lease
    finally:
        projection.close()


def test_tile_runtime_inventory_rejects_closed_retained_result_lease() -> None:
    ledger, _, scheduler, projection = _runtime()
    try:
        projection.point(0)
        binding, lease = next(iter(scheduler._pins.items()))
        assert type(lease) is ResultLease
        object.__setattr__(lease, "_closed", True)
        audit = audit_field_image_payloads(ledger)
        assert (scheduler._pin_owner, id(binding)) in audit.invalid
        object.__setattr__(lease, "_closed", False)
    finally:
        projection.close()


def test_result_admission_rejects_action_with_another_tile_alphabet_before_warm_lookup() -> (
    None
):
    ledger, adapter, _, projection = _runtime()
    try:
        projection.point(0)
        action = projection._application.action
        kernel = adapter.kernels.kernel(adapter._action(action).kernel)
        wrong_alphabet = adapter.tiles.intern_alphabet(
            TileAlphabet(
                kernel.blank + 1,
                kernel.blank,
                kernel.base,
                max(1, kernel.blank.bit_length()),
                "unrelated-symbol-interpretation",
                "v1",
            )
        )
        wrong_tile = adapter.tiles.leaf(wrong_alphabet, 1)
        try:
            key = PoweredInterfaceKey(
                action,
                wrong_tile.tile,
                projection._application.wiring,
            )
            results = adapter._require_results()
            before = ledger.snapshot()
            with pytest.raises(ValueError, match="tile alphabet differs"):
                results.publish_interface(
                    key,
                    next(
                        k
                        for k in adapter._leaf_records
                        if isinstance(k, LocalInterfaceID)
                    ),
                )
            with pytest.raises(ValueError, match="tile alphabet differs"):
                results.lookup_interface(key)
            assert ledger.snapshot() == before
            audit = audit_field_image_payloads(ledger)
            assert not audit.invalid
        finally:
            wrong_tile.close()
    finally:
        projection.close()


def test_fused_memo_rejects_unsupported_primitive_action_before_warm_lookup() -> None:
    ledger, adapter, _, projection = _runtime()
    try:
        projection.point(0)
        application = projection._application
        key = FusedInterfaceKey(
            application.action,
            application.source,
            application.ports,
            application.wiring,
        )
        result = next(
            k for k in adapter._leaf_records if isinstance(k, LocalInterfaceID)
        )
        before = ledger.snapshot()
        with pytest.raises(
            UnsupportedInterfaceError, match="no bounded fused primitive-pair"
        ):
            adapter._require_results().lookup_fused_interface(key)
        with pytest.raises(
            UnsupportedInterfaceError, match="no bounded fused primitive-pair"
        ):
            adapter._require_results().publish_fused_interface(key, result)
        after = ledger.snapshot()
        assert (
            after.entries,
            after.nodes,
            after.peak_entries,
            after.peak_nodes,
            after.inventory,
        ) == (
            before.entries,
            before.nodes,
            before.peak_entries,
            before.peak_nodes,
            before.inventory,
        )
    finally:
        projection.close()


def test_completed_result_rejects_output_with_another_tile_alphabet() -> None:
    ledger, adapter, _, projection = _runtime()
    wrong_tile = None
    try:
        application = projection._application
        completed = application.complete()
        kernel = adapter.kernels.kernel(adapter._action(application.action).kernel)
        wrong_alphabet = adapter.tiles.intern_alphabet(
            TileAlphabet(
                kernel.blank + 1,
                kernel.blank,
                kernel.base,
                max(1, kernel.blank.bit_length()),
                "unrelated-output-interpretation",
                "v1",
            )
        )
        wrong_tile = adapter.tiles.leaf(wrong_alphabet, 1)
        ledger.evict_query_memos()
        key = PoweredResultKey(
            application.action,
            application.source,
            application.ports,
            application.wiring,
        )
        wrong = replace(
            completed,
            output=wrong_tile.tile,
            relative_extent=adapter.tiles.resolve(wrong_tile.tile).extent,
        )
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="tile alphabet differs"):
            adapter._require_results().publish(key, wrong)
        after = ledger.snapshot()
        assert (
            after.entries,
            after.nodes,
            after.peak_entries,
            after.peak_nodes,
            after.inventory,
        ) == (
            before.entries,
            before.nodes,
            before.peak_entries,
            before.peak_nodes,
            before.inventory,
        )
    finally:
        if wrong_tile is not None:
            wrong_tile.close()
        projection.close()


def test_application_result_lease_survives_query_memo_eviction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, scheduler, projection = _runtime()
    try:
        expected = projection.point(0)
        projection._application.complete()
        ledger.evict_query_memos()

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm application replayed tile construction")

        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(scheduler, "point", forbidden)
        assert projection.point(0) == expected
        assert not audit_field_image_payloads(ledger).invalid
        assert audit_registered_payloads(ledger).unknown_payloads == 0
    finally:
        projection.close()


@pytest.mark.parametrize("forged", (True, 999))
def test_primitive_action_warm_interner_rejects_integer_alias_or_stale_id(
    forged: object,
) -> None:
    ledger, adapter, _, projection = _runtime()
    try:
        action = projection._application.action
        kernel = adapter._action(action).kernel
        record = adapter._action(action)
        adapter._action_keys[("power", kernel, 1, record.cocycle)] = cast(int, forged)
        before = ledger.entries, ledger.nodes, ledger.inventory()
        with pytest.raises((TypeError, ValueError)):
            adapter.admit(BaseBlockEffect(2))
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == before
    finally:
        projection.close()


@pytest.mark.parametrize("forged", (True, 0, 999))
def test_temporal_action_warm_interner_rejects_wrong_record_or_integer_alias(
    forged: object,
) -> None:
    ledger, adapter, _, projection = _runtime()
    try:
        primitive = projection._application.action
        composed = adapter.compose(primitive, primitive)
        key = primitive, primitive
        assert adapter._compositions[key] == composed.local_id
        adapter._compositions[key] = cast(int, forged)
        assert_rejected_atomically(
            ledger,
            lambda: adapter.compose(primitive, primitive),
            (TypeError, ValueError),
        )
    finally:
        projection.close()


def test_tile_runtime_inventory_validates_composed_action_dag_and_interner() -> None:
    ledger, adapter, _, projection = _runtime()
    try:
        primitive = projection._application.action
        composed = adapter.compose(primitive, primitive)
        assert adapter.power(primitive, 2) == composed
        left = adapter.compose(composed, primitive)
        right = adapter.compose(primitive, composed)
        assert left == right
        assert adapter.compose(primitive, composed) == right
        _assert_payload_clean(ledger)

        key = primitive, primitive
        adapter._compositions[key] = primitive.local_id
        audit = audit_field_image_payloads(ledger)
        assert any(owner == adapter._compose_owner for owner, _ in audit.invalid)
    finally:
        projection.close()


def test_tile_runtime_inventory_validates_retained_causal_task_payloads() -> None:
    ledger, _, scheduler, projection = _runtime()
    tasks = scheduler._causal_tasks
    action = projection._open().action
    memo_key = ("advance_symbol", (action, 0, 0, 0))
    active_key = ("advance_symbol", (action, 1, 0, 0))
    try:
        tasks.begin(memo_key)
        tasks.finish(memo_key, 0)
        tasks.begin(active_key)
        before = ledger.snapshot()
        assert not audit_field_image_payloads(ledger).invalid
        assert ledger.snapshot() == before

        tasks.memo[memo_key] = object()
        forged_memo = ledger.snapshot()
        assert (
            tasks.memo_owner,
            id(tasks.memo[memo_key]),
        ) in audit_field_image_payloads(ledger).invalid
        assert ledger.snapshot() == forged_memo

        tasks.memo[memo_key] = 0
        tasks.active[active_key] = cast(bool, 1)
        forged_active = ledger.snapshot()
        assert (
            tasks.active_owner,
            id(tasks.active[active_key]),
        ) in audit_field_image_payloads(ledger).invalid
        assert ledger.snapshot() == forged_active
    finally:
        tasks.clear()
        projection.close()


def test_sparse_legacy_source_geometry_is_canonical_tile_content() -> None:
    ledger = ResourceLedger(max_nodes=1000, max_cache_entries=1000)
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(TileAlphabet(3, 2, 2, 2, "collatz-binary", "v1"))
    digits = tuple(1 if position in (1, 7, 26) else 0 for position in range(27))
    source = ExactSource(digits, 2, blank=2, extent=64, alphabet_size=2)
    lease = import_exact_source(
        source,
        SourceGeometry(ledger, source),
        tiles,
        alphabet,
    )
    try:
        root = tiles.resolve(lease.tile)
        assert root.width == 64
        assert root.extent == 27
        assert tuple(
            position
            for position in range(root.extent)
            if tiles.point(lease.tile, position)
        ) == (1, 7, 26)
        assert not audit_field_image_payloads(ledger).invalid
    finally:
        lease.close()


def _assert_payload_clean(ledger: ResourceLedger) -> None:
    assert not audit_field_image_payloads(ledger).invalid
    payloads = audit_registered_payloads(ledger)
    assert (
        payloads.forbidden_future_payloads,
        payloads.unbounded_future_integers,
        payloads.unknown_payloads,
    ) == (0, 0, 0)
