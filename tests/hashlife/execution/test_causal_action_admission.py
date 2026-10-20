"""Run admission remains exact across causal execution and cleanup."""

from dataclasses import replace
from typing import TYPE_CHECKING, TypeGuard, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    FrobeniusSectorSourceBound,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.tile_action_algebra import PrimitiveTileAction
from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    AdvanceSymbolFrame,
    AnchorFrame,
    CausalTaskFrame,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_admission import admit_run_actions
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_directed_transfer_memo import (
    lookup_prepared_directed_transfer,
    prepare_canonical_admission,
    prepare_directed_transfer_with_admission,
)
from number_compiler.hashlife.tiles.tile_result_records import DirectedTransferKey
from number_compiler.resources.causal_workspace import CausalActionAdmission
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.stores import LedgerDict
from tests.support.causal_frames import run_causal_frame
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.resources.causal_workspace import CausalTaskWorkspace


def _causal_tasks(scheduler: TileScheduler) -> CausalTaskWorkspace:
    return scheduler.audit_causal_owners().tasks


def _is_primitive_action_store(
    value: object,
) -> TypeGuard[LedgerDict[int, PrimitiveTileAction]]:
    if type(value) is not LedgerDict:
        return False
    entries = cast(LedgerDict[object, object], value)
    return all(
        type(key) is int and type(action) is PrimitiveTileAction
        for key, action in entries.items()
    )


def _primitive_action_store(
    adapter: PrimitiveTileKernelAdapter,
) -> LedgerDict[int, PrimitiveTileAction]:
    snapshot = adapter.audit_snapshot()
    store = snapshot.ledger.registered_container(snapshot.action_owner)
    if id(store) != snapshot.action_store_identity or not _is_primitive_action_store(
        store
    ):
        raise AssertionError("primitive action audit lost its registered store")
    return store


def _advance_one_symbol(engine: CausalTileEngine, action: FieldCellActionID) -> int:
    """Run the admitted one-symbol action used by mutation regressions."""
    result = run_causal_frame(
        engine,
        AdvanceSymbolFrame((action, 0, 0, 1)),
        tile_result=False,
    )
    if type(result) is not int:
        raise TypeError("one-symbol advance returned a non-integer state")
    return result


def _assert_admission_released(scheduler: TileScheduler) -> None:
    """Check the complete task and admission cleanup contract after a run."""
    tasks = _causal_tasks(scheduler)
    snapshot = tasks.audit_snapshot()
    assert not tasks.action_pending
    assert not tasks.action_admitted
    assert snapshot.action_admission is None
    assert snapshot.run_token is None
    assert not tasks.frames
    assert not tasks.values


def test_final_admission_rejects_callback_action_mutation_and_cleans_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    record = _primitive_action_store(adapter)[action.local_id]
    original = PrimitiveKernel.advance

    def poisoned_advance(
        kernel: PrimitiveKernel,
        side: BoundarySide,
        state: int,
        symbol: int,
    ) -> int:
        result = original(kernel, side, state, symbol)
        _primitive_action_store(adapter)[action.local_id] = replace(
            record, repetitions=2
        )
        return result

    monkeypatch.setattr(PrimitiveKernel, "advance", poisoned_advance)
    try:
        with pytest.raises(ValueError, match="inconsistent metadata"):
            _advance_one_symbol(engine, action)
        assert ledger.counters["tile_causal_action_final_validation_visits"] == 1
        _assert_admission_released(scheduler)
    finally:
        _primitive_action_store(adapter)[action.local_id] = record


def test_detached_admission_snapshot_rejects_signature_redirection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, _adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    original = PrimitiveKernel.advance

    def redirect_snapshot(
        kernel: PrimitiveKernel,
        side: BoundarySide,
        state: int,
        symbol: int,
    ) -> int:
        result = original(kernel, side, state, symbol)
        snapshot = _causal_tasks(scheduler).action_admitted[action]
        _causal_tasks(scheduler).action_admitted[action] = (
            *snapshot[:-1],
            not snapshot[-1],
        )
        return result

    monkeypatch.setattr(PrimitiveKernel, "advance", redirect_snapshot)
    with pytest.raises(ValueError, match="metadata changed"):
        _advance_one_symbol(engine, action)
    _assert_admission_released(scheduler)


def test_detached_admission_snapshot_rejects_integer_alias() -> None:
    _ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    tasks = _causal_tasks(scheduler)
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    snapshot = tasks.action_admitted[action]
    tasks.action_admitted[action] = (*snapshot[:2], False, *snapshot[3:])
    try:
        with pytest.raises(ValueError, match="handle changed"):
            tasks.admitted_action_metadata(token, adapter, action)
        audit = audit_registered_payloads(scheduler.ledger)
        assert audit.forbidden_future_payloads > 0
    finally:
        tasks.action_admitted[action] = snapshot
        tasks.clear_action_admission(token)
        tasks.end_run(run)


def test_action_admission_snapshot_nodes_are_released_after_success() -> None:
    ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    before = ledger.snapshot()
    engine = CausalTileEngine(scheduler)
    assert _advance_one_symbol(engine, action) == adapter.primitive_law(action).advance(
        BoundarySide.LEFT, 0, 1
    )
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert ledger.counters["tile_causal_action_admission_visits"] == 1
    assert ledger.counters["tile_causal_action_final_validation_visits"] == 1


def test_action_admission_budget_failure_releases_partial_snapshots() -> None:
    ledger, _tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    action = adapter.power(primitive, 4)
    before = ledger.snapshot()
    ledger.max_nodes = ledger.nodes + 53
    engine = CausalTileEngine(scheduler)
    with pytest.raises(BlockContextBudgetExceeded, match="node budget"):
        _advance_one_symbol(engine, action)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    _assert_admission_released(scheduler)


def test_stale_and_foreign_action_admission_leases_are_rejected() -> None:
    _ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    tasks = _causal_tasks(scheduler)
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    tasks.clear_action_admission(token)
    tasks.end_run(run)
    with pytest.raises(RuntimeError, match="not active"):
        tasks.admitted_action_metadata(token, adapter, action)

    _other_ledger, _other_tiles, other_adapter, other_action, other_scheduler = (
        make_tile_runtime(BaseBlockEffect(3))
    )
    other_tasks = _causal_tasks(other_scheduler)
    other_run = other_tasks.begin_run()
    other_token = admit_run_actions(
        other_adapter, other_tasks, other_scheduler.ledger, other_action
    )
    try:
        with pytest.raises((ValueError, RuntimeError), match="outside|another|active"):
            tasks.admitted_action_metadata(other_token, adapter, action)
    finally:
        other_tasks.clear_action_admission(other_token)
        other_tasks.end_run(other_run)


def test_final_validation_runs_on_a_causal_task_memo_hit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    action = adapter.power(primitive, 4)
    children = adapter.action_record(action).children
    assert children is not None
    child = children[0]
    engine = CausalTileEngine(scheduler)
    object.__setattr__(engine, "_hold_workspace", True)
    initial = engine.initial_state(action, 0)

    def frame() -> CausalTaskFrame:
        return AnchorFrame((action, 0, initial))

    record = _primitive_action_store(adapter)[child.local_id]
    try:
        run_causal_frame(engine, frame(), tile_result=False)
        memo_hits = ledger.counters.get("tile_causal_task_memo_hits", 0)
        original = _causal_tasks(scheduler).validate_admitted_actions

        def poison_before_final(
            token: CausalActionAdmission, authority: PrimitiveTileKernelAdapter
        ) -> None:
            _primitive_action_store(adapter)[child.local_id] = replace(
                record,
                repetitions=record.repetitions + 1,
            )
            original(token, authority)

        monkeypatch.setattr(
            _causal_tasks(scheduler),
            "validate_admitted_actions",
            poison_before_final,
        )
        with pytest.raises(ValueError, match="composition witness is inconsistent"):
            run_causal_frame(engine, frame(), tile_result=False)
        assert ledger.counters["tile_causal_task_memo_hits"] == memo_hits + 1
    finally:
        _primitive_action_store(adapter)[child.local_id] = record
        object.__setattr__(engine, "_hold_workspace", False)
        engine.release_workspace()


def test_callback_mutation_cannot_publish_a_directed_parent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    record = _primitive_action_store(adapter)[action.local_id]
    original = PrimitiveKernel.advance
    calls = 0

    def poison_first_leaf(
        kernel: PrimitiveKernel,
        side: BoundarySide,
        state: int,
        symbol: int,
    ) -> int:
        nonlocal calls
        result = original(kernel, side, state, symbol)
        calls += 1
        if calls == 1:
            _primitive_action_store(adapter)[action.local_id] = replace(
                record, repetitions=2
            )
        return result

    monkeypatch.setattr(PrimitiveKernel, "advance", poison_first_leaf)
    try:
        with make_tile_from_symbols(tiles, adapter, action, (0, 1, 2, 3)) as source:
            engine = CausalTileEngine(scheduler)
            with pytest.raises(ValueError, match="metadata changed"):
                run_causal_frame(
                    engine,
                    AdvanceFrame(
                        (
                            action,
                            0,
                            0,
                            BoundaryTileView(source.tile, 0, 4),
                        ),
                    ),
                    tile_result=False,
                )
            assert not any(
                type(key) is DirectedTransferKey
                for key in scheduler.results.audit_snapshot().memo
            )
    finally:
        _primitive_action_store(adapter)[action.local_id] = record


def test_prepared_directed_request_expires_with_its_run_admission() -> None:
    _ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with make_tile_from_symbols(tiles, adapter, action, (0, 1)) as source:
        tasks = _causal_tasks(scheduler)
        run = tasks.begin_run()
        token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
        admission = prepare_canonical_admission(
            scheduler.results,
            action,
            0,
            action_admission=token,
        )
        request = prepare_directed_transfer_with_admission(
            scheduler.results,
            DirectedTransferKey(
                action,
                source.tile,
                0,
                0,
                admission.wiring,
            ),
            admission,
        )
        tasks.clear_action_admission(token)
        tasks.end_run(run)
        with pytest.raises(RuntimeError, match="not active"):
            lookup_prepared_directed_transfer(scheduler.results, request)


def test_transient_action_replacement_is_rejected_before_metadata_use() -> None:
    _ledger, _tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    power2 = adapter.compose(primitive, primitive)
    power3 = adapter.compose(primitive, power2)
    action = adapter.compose(power2, power2)
    root = adapter.compose(action, power3)
    engine = CausalTileEngine(scheduler)
    record = _primitive_action_store(adapter)[action.local_id]
    tasks = _causal_tasks(scheduler)
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, root)
    object.__setattr__(engine, "_action_admission_token", token)
    try:
        _primitive_action_store(adapter)[action.local_id] = replace(
            record, children=(primitive, power3)
        )
        assert _primitive_action_store(adapter)[action.local_id] != record
        try:
            with pytest.raises(ValueError, match="metadata changed after admission"):
                engine.child_actions(action)
        finally:
            _primitive_action_store(adapter)[action.local_id] = record
    finally:
        object.__setattr__(engine, "_action_admission_token", None)
        tasks.clear_action_admission(token)
        tasks.end_run(run)
    assert _primitive_action_store(adapter)[action.local_id] is record
    assert _causal_tasks(scheduler).audit_snapshot().action_admission is None
    assert _causal_tasks(scheduler).audit_snapshot().run_token is None


def test_transient_reverse_sector_integer_alias_is_rejected_before_use(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(10))
    engine = CausalTileEngine(scheduler)
    record = _primitive_action_store(adapter)[action.local_id]
    plan = record.reverse_frobenius
    assert plan is not None
    sector = plan.sectors[0]
    assert type(sector) is FrobeniusSectorSourceBound
    original = PrimitiveKernel.advance

    def mutate_then_restore(
        kernel: PrimitiveKernel,
        side: BoundarySide,
        state: int,
        symbol: int,
    ) -> int:
        object.__setattr__(sector, "classes", True)
        try:
            engine.action_cocycle(action)
        finally:
            object.__setattr__(sector, "classes", 1)
        return original(kernel, side, state, symbol)

    monkeypatch.setattr(PrimitiveKernel, "advance", mutate_then_restore)
    with pytest.raises(ValueError, match="metadata changed after admission"):
        run_causal_frame(
            engine,
            AdvanceSymbolFrame((action, 0, 0, 1)),
            tile_result=False,
        )
    assert sector.classes == 1
    assert _causal_tasks(scheduler).audit_snapshot().action_admission is None


def test_transient_reverse_sector_list_is_rejected_before_use() -> None:
    _ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(10))
    engine = CausalTileEngine(scheduler)
    plan = _primitive_action_store(adapter)[action.local_id].reverse_frobenius
    assert plan is not None
    sectors = plan.sectors
    tasks = _causal_tasks(scheduler)
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    object.__setattr__(engine, "_action_admission_token", token)
    try:
        object.__setattr__(plan, "sectors", list(sectors))
        try:
            with pytest.raises(TypeError, match="immutable reverse sectors"):
                engine.action_cocycle(action)
        finally:
            object.__setattr__(plan, "sectors", sectors)
    finally:
        object.__setattr__(engine, "_action_admission_token", None)
        tasks.clear_action_admission(token)
        tasks.end_run(run)
    assert plan.sectors is sectors


def test_live_inventory_authenticates_every_action_admission_lease_field() -> None:
    ledger, _tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    tasks = _causal_tasks(scheduler)
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, ledger, action)
    assert type(token) is CausalActionAdmission
    try:
        clean = audit_registered_payloads(ledger)
        assert clean == type(clean)(0, 0, 0)
        for field in ("_seal", "_workspace", "_run"):
            original = getattr(token, field)
            object.__setattr__(token, field, object())
            try:
                audit = audit_registered_payloads(ledger)
                assert audit.forbidden_future_payloads > 0
            finally:
                object.__setattr__(token, field, original)
        foreign = CausalActionAdmission(tasks, run, adapter)
        object.__setattr__(tasks, "_action_admission_token", foreign)
        try:
            audit = audit_registered_payloads(ledger)
            assert audit.forbidden_future_payloads > 0
        finally:
            object.__setattr__(tasks, "_action_admission_token", token)
    finally:
        tasks.clear_action_admission(token)
        tasks.end_run(run)
