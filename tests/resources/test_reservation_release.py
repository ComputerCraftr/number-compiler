"""Partial scratch release preserves per-reservation ownership and retryability."""

from typing import NoReturn

import pytest

from number_compiler.resources.ledger import LedgerReservation, ResourceLedger


def test_partial_release_cannot_consume_a_neighbour_reservation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("shared-scratch", "WORKSPACE")
    first = LedgerReservation(ledger, owner)
    second = LedgerReservation(ledger, owner)
    with first, second:
        first.reserve(entries=2, nodes=5)
        second.reserve(entries=3, nodes=7)
        first.release(entries=1, nodes=3)
        assert (ledger.entries, ledger.nodes) == (4, 9)
        for entries, nodes in ((2, 0), (0, 3)):
            with pytest.raises(ValueError, match="this reservation"):
                first.release(entries=entries, nodes=nodes)
            assert (ledger.entries, ledger.nodes) == (4, 9)
        with pytest.raises((TypeError, ValueError)):
            first.release(entries=True)
        with pytest.raises((TypeError, ValueError)):
            first.release(nodes=-1)
        foreign = ResourceLedger()
        with pytest.raises(RuntimeError, match="foreign"):
            foreign.release_for_reservation(first, entries=1)
        first.release(entries=1, nodes=2)
        assert (ledger.entries, ledger.nodes) == (3, 7)
    assert (ledger.entries, ledger.nodes) == (0, 0)
    with pytest.raises(RuntimeError, match="closed"):
        first.release()


def test_failed_partial_release_keeps_its_charge_for_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("retryable-scratch", "WORKSPACE")

    def refuse_release(
        self: ResourceLedger, owner: int, entries: int = 0, nodes: int = 0
    ) -> NoReturn:
        raise RuntimeError("injected release failure")

    with LedgerReservation(ledger, owner) as reservation:
        reservation.reserve(entries=2, nodes=6)
        with monkeypatch.context() as patch:
            patch.setattr(ResourceLedger, "release", refuse_release)
            with pytest.raises(RuntimeError, match="injected"):
                reservation.release(entries=1, nodes=3)
        assert (ledger.entries, ledger.nodes) == (2, 6)
        reservation.release(entries=1, nodes=3)
        assert (ledger.entries, ledger.nodes) == (1, 3)
    assert (ledger.entries, ledger.nodes) == (0, 0)
