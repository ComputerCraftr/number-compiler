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


@pytest.mark.parametrize("close", (False, True))
def test_committed_release_failure_cannot_spend_neighbour_credit(
    monkeypatch: pytest.MonkeyPatch, close: bool
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("post-commit-release", "WORKSPACE")
    first = LedgerReservation(ledger, owner)
    second = LedgerReservation(ledger, owner)
    first.reserve(entries=2, nodes=5)
    second.reserve(entries=3, nodes=7)
    original = ResourceLedger.release

    def release_then_raise(
        self: ResourceLedger, owner: int, entries: int = 0, nodes: int = 0
    ) -> NoReturn:
        original(self, owner, entries=entries, nodes=nodes)
        raise RuntimeError("post-commit release failure")

    with monkeypatch.context() as patch:
        patch.setattr(ResourceLedger, "release", release_then_raise)
        with pytest.raises(RuntimeError, match="post-commit"):
            if close:
                first.close()
            else:
                first.release(entries=1, nodes=3)
    assert ledger.account_usage(owner) == ((3, 7) if close else (4, 9))
    with pytest.raises(ValueError, match="this reservation"):
        first.release(entries=1 if close else 2)
    first.close()
    first.close()
    assert ledger.account_usage(owner) == (3, 7)
    second.close()
    assert (ledger.entries, ledger.nodes) == (0, 0)


def test_committed_reserve_failure_remains_owned_for_cleanup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("post-commit-reserve", "WORKSPACE")
    original = ResourceLedger.reserve

    def reserve_then_raise(
        self: ResourceLedger, owner: int, entries: int = 0, nodes: int = 0
    ) -> NoReturn:
        original(self, owner, entries=entries, nodes=nodes)
        raise RuntimeError("post-commit reserve failure")

    with LedgerReservation(ledger, owner) as reservation:
        with monkeypatch.context() as patch:
            patch.setattr(ResourceLedger, "reserve", reserve_then_raise)
            with pytest.raises(RuntimeError, match="post-commit"):
                reservation.reserve(entries=2, nodes=5)
        assert ledger.account_usage(owner) == (2, 5)
    assert (ledger.entries, ledger.nodes) == (0, 0)


@pytest.mark.parametrize("into_reservation", (False, True))
def test_committed_transfer_failure_preserves_charge_ownership(
    monkeypatch: pytest.MonkeyPatch, into_reservation: bool
) -> None:
    from collections.abc import Iterable

    ledger = ResourceLedger()
    owner = ledger.register("transfer-scratch", "WORKSPACE")
    other = ledger.register("transfer-retained", "CACHE")
    original = ResourceLedger.reassign_many

    def transfer_then_raise(
        self: ResourceLedger,
        releases: Iterable[tuple[int, int, int]],
        reservations: Iterable[tuple[int, int, int]],
    ) -> NoReturn:
        original(self, releases, reservations)
        raise RuntimeError("post-commit transfer failure")

    with LedgerReservation(ledger, owner) as reservation:
        if into_reservation:
            ledger.reserve(other, entries=2, nodes=5)
        else:
            reservation.reserve(entries=2, nodes=5)
        with monkeypatch.context() as patch:
            patch.setattr(ResourceLedger, "reassign_many", transfer_then_raise)
            with pytest.raises(RuntimeError, match="post-commit"):
                if into_reservation:
                    reservation.transfer_from(other, entries=2, nodes=5)
                else:
                    reservation.transfer_to(other, entries=2, nodes=5)
        assert ledger.account_usage(owner) == ((2, 5) if into_reservation else (0, 0))
    assert ledger.account_usage(owner) == (0, 0)
    if not into_reservation:
        assert ledger.account_usage(other) == (2, 5)
        ledger.release(other, entries=2, nodes=5)
    assert (ledger.entries, ledger.nodes) == (0, 0)
