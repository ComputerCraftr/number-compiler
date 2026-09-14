"""Execution cache hits retain admission while avoiding a repeated key proof."""

from dataclasses import replace

import pytest

from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from tests.hashlife.tiles.test_tile_scheduler import _runtime
from tests.support.tile_results import _setup


def test_scheduler_lookup_admits_key_once_on_cold_and_warm_paths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime = _runtime()
    try:
        action = runtime.actions.action(0)
        key = runtime.scheduler._key(action, runtime.root.tile, (0,), runtime.wiring)
        original = runtime.scheduler.results._validate_key
        calls: list[PoweredResultKey] = []

        def counted(request: PoweredResultKey) -> None:
            calls.append(request)
            original(request)

        monkeypatch.setattr(runtime.scheduler.results, "_validate_key", counted)
        assert runtime.scheduler._lookup_execution_key(key) is None
        assert calls == [key]
        held = runtime.scheduler.complete(
            action, runtime.root.tile, (0,), runtime.wiring
        )
        try:
            calls.clear()
            warm = runtime.scheduler._lookup_execution_key(key)
            assert warm is not None
            try:
                assert calls == [key]
                assert warm.result == held.result
            finally:
                warm.close()
        finally:
            held.close()
    finally:
        runtime.close()


def test_context_rejection_precedes_warm_cache_access() -> None:
    ledger, _, _, results, source, target, key, result = _setup()
    held = results.publish(key, result)
    try:
        before = ledger.snapshot()

        def reject(request: PoweredResultKey) -> None:
            assert request == key
            raise ValueError("execution context rejected")

        with pytest.raises(ValueError, match="execution context rejected"):
            results.lookup(key, validate_context=reject)
        after = ledger.snapshot()
        assert (after.entries, after.nodes, after.inventory) == (
            before.entries,
            before.nodes,
            before.inventory,
        )
        for counter in ("completed_result_requests", "completed_result_early_hits"):
            assert after.counters.get(counter, 0) == before.counters.get(counter, 0)
    finally:
        held.close()
        target.close()
        source.close()


def test_context_hook_cannot_bypass_key_admission() -> None:
    _, _, _, results, source, target, key, _ = _setup()
    calls: list[PoweredResultKey] = []
    try:
        with pytest.raises(ValueError, match="finite domain"):
            results.lookup(replace(key, ports=(99,)), validate_context=calls.append)
        assert not calls
    finally:
        target.close()
        source.close()


def test_public_application_rejects_context_before_using_a_warm_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime = _runtime()
    action = runtime.actions.action(0)
    held = runtime.scheduler.complete(action, runtime.root.tile, (0,), runtime.wiring)
    application = runtime.scheduler.application(
        action, runtime.root.tile, (0,), runtime.wiring
    )
    try:

        def reject(*_args: object) -> None:
            raise ValueError("execution wiring revoked")

        with monkeypatch.context() as patch:
            patch.setattr(runtime.adapter, "validate_wiring", reject)
            with pytest.raises(ValueError, match="execution wiring revoked"):
                runtime.scheduler.application(
                    action, runtime.root.tile, (0,), runtime.wiring
                )
            with pytest.raises(ValueError, match="execution wiring revoked"):
                application._cached_root()
    finally:
        application.close()
        held.close()
        runtime.close()
