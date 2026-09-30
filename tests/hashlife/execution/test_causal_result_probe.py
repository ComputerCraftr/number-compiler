"""Atomic causal probes validate authority before touching result storage."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal_admission import admit_run_actions
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    causal_result_key,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from tests.support.tile_kernel import _runtime, _runtime_source, _tile


def test_atomic_probe_rejects_malformed_key_before_memo_access(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    source = _tile(tiles, adapter, action, (0,))
    original_getitem = LedgerDict.__getitem__

    def forbidden_getitem(self: LedgerDict[object, object], key: object) -> object:
        if self is scheduler.results._memo:
            raise AssertionError(f"malformed causal key reached result memo: {key!r}")
        return original_getitem(self, key)

    try:
        monkeypatch.setattr(LedgerDict, "__getitem__", forbidden_getitem)
        left, right = adapter.initial_ports(action)
        with pytest.raises(ValueError, match="port|state|domain"):
            probe_causal_result(
                scheduler.results,
                action,
                source.tile,
                PrimitiveCausalPorts(left, right + 10_000),
                adapter.wiring(action),
                action_admission=token,
            )
    finally:
        source.close()
        tasks.clear_action_admission(token)
        tasks.end_run(run)


def test_atomic_probe_rejects_changed_admitted_action_before_memo_access(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, scheduler.ledger, action)
    source = _tile(tiles, adapter, action, (0,))
    record = adapter._actions[action.local_id]
    ports = adapter.initial_ports(action)
    wiring = adapter.wiring(action)
    original_getitem = LedgerDict.__getitem__

    def forbidden_getitem(self: LedgerDict[object, object], key: object) -> object:
        if self is scheduler.results._memo:
            raise AssertionError(f"changed action reached result memo: {key!r}")
        return original_getitem(self, key)

    try:
        monkeypatch.setattr(LedgerDict, "__getitem__", forbidden_getitem)
        adapter._actions[action.local_id] = replace(
            record,
            repetitions=record.repetitions + 1,
        )
        with pytest.raises(ValueError, match="metadata changed"):
            probe_causal_result(
                scheduler.results,
                action,
                source.tile,
                PrimitiveCausalPorts(*ports),
                wiring,
                action_admission=token,
            )
    finally:
        adapter._actions[action.local_id] = record
        source.close()
        tasks.clear_action_admission(token)
        tasks.end_run(run)


def test_public_causal_lookup_retains_deep_action_validation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        _runtime_source(BaseBlockEffect(3), (0,))
    )
    key = causal_result_key(
        scheduler.results,
        action,
        source.tile,
        PrimitiveCausalPorts(*adapter.initial_ports(action)),
        adapter.wiring(action),
    )
    original = PrimitiveTileKernelAdapter.validate_action
    validations = 0

    def counted(
        authority: PrimitiveTileKernelAdapter,
        candidate: FieldCellActionID,
    ) -> None:
        nonlocal validations
        validations += 1
        original(authority, candidate)

    try:
        monkeypatch.setattr(PrimitiveTileKernelAdapter, "validate_action", counted)
        assert lookup_causal_result(scheduler.results, key) is None
        assert validations > 0
    finally:
        source.close()


def test_probe_counter_failure_precedes_lookup_and_acquires_no_lease(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, ledger, action)
    source = _tile(tiles, adapter, action, (0,))
    ports = adapter.initial_ports(action)
    wiring = adapter.wiring(action)
    original_bump = ResourceLedger.bump
    original_getitem = LedgerDict.__getitem__
    memo_accessed = False
    leases_before = len(tiles._leases)

    def fail_probe_counter(
        owner: ResourceLedger,
        counter: str,
        amount: int = 1,
    ) -> None:
        if owner is ledger and counter == "tile_causal_result_probe_requests":
            raise RuntimeError("injected probe counter failure")
        original_bump(owner, counter, amount)

    def observe_getitem(self: LedgerDict[object, object], key: object) -> object:
        nonlocal memo_accessed
        if self is scheduler.results._memo:
            memo_accessed = True
        return original_getitem(self, key)

    try:
        monkeypatch.setattr(ResourceLedger, "bump", fail_probe_counter)
        monkeypatch.setattr(LedgerDict, "__getitem__", observe_getitem)
        with pytest.raises(RuntimeError, match="injected probe counter failure"):
            probe_causal_result(
                scheduler.results,
                action,
                source.tile,
                PrimitiveCausalPorts(*ports),
                wiring,
                action_admission=token,
            )
        assert not memo_accessed
        assert len(tiles._leases) == leases_before
    finally:
        source.close()
        tasks.clear_action_admission(token)
        tasks.end_run(run)
