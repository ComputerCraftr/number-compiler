"""Failed reverse-index snapshots never strand publication reservations."""

from __future__ import annotations

from collections.abc import Callable
from typing import Never

import pytest

from number_compiler.hashlife.tiles.tile_behavior_memo import (
    publish_behavior_classification,
    reserve_behavior_publication,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger
from tests.hashlife.tiles.test_tile_behavior_memo import _binding
from tests.support.tile_results import _setup, fused_setup


def _assert_snapshot_failure(
    monkeypatch: pytest.MonkeyPatch,
    ledger: ResourceLedger,
    results: CompletedResultArena,
    operation: Callable[[], object],
    *,
    baseline: LedgerSnapshot | None = None,
) -> None:
    before = ledger.snapshot() if baseline is None else baseline
    memo, reverse, variants = (
        dict(results._memo),
        dict(results._reverse),
        dict(results._variants),
    )
    references, leases = dict(results.tiles._refs), dict(results.tiles._leases)

    def fail_snapshot(*_args: object) -> Never:
        raise RuntimeError("injected reverse snapshot failure")

    with monkeypatch.context() as patch:
        patch.setattr(type(results), "reverse_snapshot", fail_snapshot)
        with pytest.raises(RuntimeError, match="injected reverse snapshot"):
            operation()
    after = ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert (dict(results._memo), dict(results._reverse), dict(results._variants)) == (
        memo,
        reverse,
        variants,
    )
    assert (dict(results.tiles._refs), dict(results.tiles._leases)) == (
        references,
        leases,
    )


@pytest.mark.parametrize(
    "fused", (False, True), ids=("completed-result", "fused-interface")
)
def test_snapshot_failure_precedes_result_reservations(
    monkeypatch: pytest.MonkeyPatch, fused: bool
) -> None:
    if fused:
        ledger, _, _, results, input_lease, output_lease, key, result, fused_key = (
            fused_setup(publish=False)
        )

        def operation() -> object:
            return results.publish_fused_interface(fused_key, result.outgoing)
    else:
        ledger, _, _, results, input_lease, output_lease, key, result = _setup()

        def operation() -> object:
            return results.publish(key, result)

    try:
        _assert_snapshot_failure(monkeypatch, ledger, results, operation)
    finally:
        output_lease.close()
        input_lease.close()


@pytest.mark.parametrize("supplied", (False, True), ids=("internal", "supplied"))
def test_behavior_snapshot_failure_releases_issued_reservation(
    monkeypatch: pytest.MonkeyPatch, supplied: bool
) -> None:
    ledger, _adapter, results, source, key, behavior = _binding()
    before = ledger.snapshot()
    reservation = (
        reserve_behavior_publication(results, key.request) if supplied else None
    )
    try:
        _assert_snapshot_failure(
            monkeypatch,
            ledger,
            results,
            lambda: publish_behavior_classification(
                results, key, behavior, reservation=reservation
            ),
            baseline=before,
        )
        assert ledger.counters["future_behavior_publication_failures"] == 1
        if reservation is not None:
            assert not reservation._open
            retained = ledger.entries, ledger.nodes
            reservation.close()
            assert (ledger.entries, ledger.nodes) == retained
        assert (
            publish_behavior_classification(results, key, behavior).behavior == behavior
        )
    finally:
        if reservation is not None:
            reservation.close()
        source.close()
