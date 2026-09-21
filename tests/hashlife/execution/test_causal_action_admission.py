"""Run admission remains exact across causal execution and cleanup."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    FrobeniusSectorSourceBound,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_admission import admit_run_actions
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_directed_transfer_memo import (
    _prepare_canonical_admission,
    _prepare_directed_transfer_with_admission,
    lookup_prepared_directed_transfer,
)
from number_compiler.hashlife.tiles.tile_result_records import DirectedTransferKey
from number_compiler.resources.causal_workspace import CausalActionAdmission
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


def test_final_admission_rejects_callback_action_mutation_and_cleans_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    record = adapter._actions[action.local_id]
    original = PrimitiveKernel.advance

    def poisoned_advance(
        kernel: PrimitiveKernel,
        side: BoundarySide,
        state: int,
        symbol: int,
    ) -> int:
        result = original(kernel, side, state, symbol)
        adapter._actions[action.local_id] = replace(record, repetitions=2)
        return result

    monkeypatch.setattr(PrimitiveKernel, "advance", poisoned_advance)
    try:
        with pytest.raises(ValueError, match="inconsistent metadata"):
            engine._run(
                CausalFrame("advance_symbol", (action, 0, 0, 1)),
                tile_result=False,
            )
        assert ledger.counters["tile_causal_action_final_validation_visits"] == 1
        assert not scheduler._causal_tasks.action_pending
        assert not scheduler._causal_tasks.action_admitted
        assert scheduler._causal_tasks._action_admission_token is None
        assert scheduler._causal_tasks._run_token is None
        assert not scheduler._causal_tasks.frames
        assert not scheduler._causal_tasks.values
    finally:
        adapter._actions[action.local_id] = record


def test_detached_admission_snapshot_rejects_signature_redirection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, _adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    original = PrimitiveKernel.advance

    def redirect_snapshot(
        kernel: PrimitiveKernel,
        side: BoundarySide,
        state: int,
        symbol: int,
    ) -> int:
        result = original(kernel, side, state, symbol)
        snapshot = scheduler._causal_tasks.action_admitted[action]
        scheduler._causal_tasks.action_admitted[action] = (
            *snapshot[:-1],
            not snapshot[-1],
        )
        return result

    monkeypatch.setattr(PrimitiveKernel, "advance", redirect_snapshot)
    with pytest.raises(ValueError, match="metadata changed"):
        engine._run(
            CausalFrame("advance_symbol", (action, 0, 0, 1)),
            tile_result=False,
        )
    assert not scheduler._causal_tasks.action_admitted
    assert scheduler._causal_tasks._action_admission_token is None
    assert scheduler._causal_tasks._run_token is None


def test_detached_admission_snapshot_rejects_integer_alias() -> None:
    _ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    tasks = scheduler._causal_tasks
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
    ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    before = ledger.snapshot()
    engine = CausalTileEngine(scheduler)
    assert engine._run(
        CausalFrame("advance_symbol", (action, 0, 0, 1)),
        tile_result=False,
    ) == adapter.primitive_law(action).advance(BoundarySide.LEFT, 0, 1)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert ledger.counters["tile_causal_action_admission_visits"] == 1
    assert ledger.counters["tile_causal_action_final_validation_visits"] == 1


def test_action_admission_budget_failure_releases_partial_snapshots() -> None:
    ledger, _tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    before = ledger.snapshot()
    ledger.max_nodes = ledger.nodes + 53
    engine = CausalTileEngine(scheduler)
    with pytest.raises(BlockContextBudgetExceeded, match="node budget"):
        engine._run(
            CausalFrame("advance_symbol", (action, 0, 0, 1)),
            tile_result=False,
        )
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert not scheduler._causal_tasks.action_pending
    assert not scheduler._causal_tasks.action_admitted
    assert scheduler._causal_tasks._action_admission_token is None
    assert scheduler._causal_tasks._run_token is None


def test_stale_and_foreign_action_admission_leases_are_rejected() -> None:
    _ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    tasks.clear_action_admission(token)
    tasks.end_run(run)
    with pytest.raises(RuntimeError, match="not active"):
        tasks.admitted_action_metadata(token, adapter, action)

    _other_ledger, _other_tiles, other_adapter, other_action, other_scheduler = (
        _runtime(BaseBlockEffect(3))
    )
    other_tasks = other_scheduler._causal_tasks
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
    ledger, _tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    children = adapter._action_record(action).children
    assert children is not None
    child = children[0]
    engine = CausalTileEngine(scheduler)
    engine._hold_workspace = True
    initial = engine._initial(action, 0)

    def frame() -> CausalFrame:
        return CausalFrame("anchor", (action, 0, initial))

    record = adapter._actions[child.local_id]
    try:
        engine._run(frame(), tile_result=False)
        memo_hits = ledger.counters.get("tile_causal_task_memo_hits", 0)
        original = scheduler._causal_tasks.validate_admitted_actions

        def poison_before_final(
            token: object, authority: PrimitiveTileKernelAdapter
        ) -> None:
            adapter._actions[child.local_id] = replace(
                record,
                repetitions=record.repetitions + 1,
            )
            original(token, authority)

        monkeypatch.setattr(
            scheduler._causal_tasks,
            "validate_admitted_actions",
            poison_before_final,
        )
        with pytest.raises(ValueError, match="composition witness is inconsistent"):
            engine._run(frame(), tile_result=False)
        assert ledger.counters["tile_causal_task_memo_hits"] == memo_hits + 1
    finally:
        adapter._actions[child.local_id] = record
        engine._hold_workspace = False
        engine._release_workspace()


def test_callback_mutation_cannot_publish_a_directed_parent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    record = adapter._actions[action.local_id]
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
            adapter._actions[action.local_id] = replace(record, repetitions=2)
        return result

    monkeypatch.setattr(PrimitiveKernel, "advance", poison_first_leaf)
    try:
        with _tile(tiles, adapter, action, (0, 1, 2, 3)) as source:
            engine = CausalTileEngine(scheduler)
            with pytest.raises(ValueError, match="metadata changed"):
                engine._run(
                    CausalFrame(
                        "advance",
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
                type(key) is DirectedTransferKey for key in scheduler.results._memo
            )
    finally:
        adapter._actions[action.local_id] = record


def test_prepared_directed_request_expires_with_its_run_admission() -> None:
    _ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 1)) as source:
        tasks = scheduler._causal_tasks
        run = tasks.begin_run()
        token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
        admission = _prepare_canonical_admission(
            scheduler.results,
            action,
            0,
            action_admission=token,
        )
        request = _prepare_directed_transfer_with_admission(
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
    _ledger, _tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    power2 = adapter.compose(primitive, primitive)
    power3 = adapter.compose(primitive, power2)
    action = adapter.compose(power2, power2)
    root = adapter.compose(action, power3)
    engine = CausalTileEngine(scheduler)
    record = adapter._actions[action.local_id]
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, root)
    engine._action_admission_token = token
    try:
        adapter._actions[action.local_id] = replace(
            record, children=(primitive, power3)
        )
        assert adapter._actions[action.local_id] != record
        adapter._action_record(action)
        try:
            with pytest.raises(ValueError, match="metadata changed after admission"):
                engine._children(action)
        finally:
            adapter._actions[action.local_id] = record
    finally:
        engine._action_admission_token = None
        tasks.clear_action_admission(token)
        tasks.end_run(run)
    assert adapter._actions[action.local_id] is record
    assert scheduler._causal_tasks._action_admission_token is None
    assert scheduler._causal_tasks._run_token is None


def test_transient_reverse_sector_integer_alias_is_rejected_before_use(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(10))
    engine = CausalTileEngine(scheduler)
    record = adapter._actions[action.local_id]
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
            engine._cocycle(action)
        finally:
            object.__setattr__(sector, "classes", 1)
        return original(kernel, side, state, symbol)

    monkeypatch.setattr(PrimitiveKernel, "advance", mutate_then_restore)
    with pytest.raises(ValueError, match="metadata changed after admission"):
        engine._run(
            CausalFrame("advance_symbol", (action, 0, 0, 1)),
            tile_result=False,
        )
    assert sector.classes == 1
    assert scheduler._causal_tasks._action_admission_token is None


def test_transient_reverse_sector_list_is_rejected_before_use() -> None:
    _ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(10))
    engine = CausalTileEngine(scheduler)
    plan = adapter._actions[action.local_id].reverse_frobenius
    assert plan is not None
    sectors = plan.sectors
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    engine._action_admission_token = token
    try:
        object.__setattr__(plan, "sectors", list(sectors))
        try:
            with pytest.raises(TypeError, match="immutable reverse sectors"):
                engine._cocycle(action)
        finally:
            object.__setattr__(plan, "sectors", sectors)
    finally:
        engine._action_admission_token = None
        tasks.clear_action_admission(token)
        tasks.end_run(run)
    assert plan.sectors is sectors


def test_live_inventory_authenticates_every_action_admission_lease_field() -> None:
    ledger, _tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    tasks = scheduler._causal_tasks
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
        foreign = CausalActionAdmission(tasks, run)
        tasks._action_admission_token = foreign
        try:
            audit = audit_registered_payloads(ledger)
            assert audit.forbidden_future_payloads > 0
        finally:
            tasks._action_admission_token = token
    finally:
        tasks.clear_action_admission(token)
        tasks.end_run(run)
