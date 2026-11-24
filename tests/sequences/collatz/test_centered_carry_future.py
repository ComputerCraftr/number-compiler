"""The bounded carry event consumes one source and ordered integer inlets."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.dyadic_unit_phase import DyadicUnitPhase
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.sequences.collatz.centered_carry_future import (
    CenteredCarryFuture,
)
from number_compiler.sequences.collatz.future_carry_bellman import (
    centered_carry_signal,
    first_simultaneous_even_carries,
)


def _literal(
    source: int, cuts: tuple[int, ...], horizon: int, *, corrected: bool = False
) -> int | None:
    for tick in range(1, horizon + 1):
        if all(
            (
                (
                    base**tick * ((source + 1) % (1 << cut))
                    + ((-(1 << tick)) % (1 << cut) if corrected and base == 3 else 0)
                )
                >> cut
            )
            % 2
            == 0
            for base in (3, 5, 15)
            for cut in cuts
        ):
            return tick
    return None


@pytest.mark.parametrize("source", (3, 7, 15, 31, 63, 127, 255, 1023, 1535))
@pytest.mark.parametrize("cuts", ((0,), (1, 3), (7, 1, 7), (4, 12)))
def test_same_time_carries_match_independent_integer_oracle(
    source: int, cuts: tuple[int, ...]
) -> None:
    centered = source + 1
    headroom = (centered & -centered).bit_length() - 1
    for horizon in range(headroom + 1):
        ledger = ResourceLedger()
        signal = centered_carry_signal(source, cuts, horizon=horizon, ledger=ledger)
        assert signal.hits.homogeneous == _literal(source, cuts, horizon)
        assert signal.hits.corrected == _literal(source, cuts, horizon, corrected=True)
        literal = source
        for _ in range(horizon):
            assert literal & 1
            literal = (3 * literal + 1) // 2
        assert signal.numerator_bits == max(cuts) + 1
        assert signal.numerator_residue == (literal << horizon) % (
            1 << signal.numerator_bits
        )
        assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError, match="headroom"):
        first_simultaneous_even_carries(
            source, cuts, horizon=headroom + 1, ledger=ResourceLedger()
        )


def test_valuation_covered_cuts_need_no_phase_storage() -> None:
    future = CenteredCarryFuture.from_normalized_source(127, 8)

    def forbid_reservation(_bits: int) -> None:
        raise AssertionError("valuation-covered cuts constructed a phase walk")

    hits = future.first_same_time_even(
        (0, 2, 7),
        horizon=7,
        max_phase_states=1,
        reserve_bits=forbid_reservation,
        include_correction=True,
    )
    assert hits.homogeneous == hits.corrected == 1


def test_valuation_covered_source_skips_joint_phase_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid(*_args: object, **_kwargs: object) -> DyadicUnitPhase:
        raise AssertionError("valuation-covered cuts constructed a joint phase")

    monkeypatch.setattr(DyadicUnitPhase, "from_exponent", forbid)
    for source, cuts, horizon in ((127, (0, 2, 7), 7), (15, (4,), 1)):
        ledger = ResourceLedger()
        signal = centered_carry_signal(source, cuts, horizon=horizon, ledger=ledger)
        assert signal.hits.homogeneous == _literal(source, cuts, horizon)
        assert signal.hits.corrected == _literal(source, cuts, horizon, corrected=True)
        assert signal.numerator_residue == (3**horizon * (source + 1) - 2**horizon) % (
            1 << (max(cuts) + 1)
        )
        assert ledger.entries == ledger.nodes == 0
        with pytest.raises(ValueError, match="headroom"):
            centered_carry_signal(source, cuts, horizon=horizon + 7, ledger=ledger)


def test_phase_precision_is_checked_at_source_admission() -> None:
    with pytest.raises(ValueError, match="dyadic phase precision"):
        CenteredCarryFuture.from_normalized_source(7, 16388)


def test_signal_failed_reservation_close_is_retried_during_disposal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    original_close = LedgerReservation.close
    attempts = 0

    def fail_once(reservation: LedgerReservation) -> None:
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            raise RuntimeError("injected carry reservation close failure")
        original_close(reservation)

    monkeypatch.setattr(LedgerReservation, "close", fail_once)
    with pytest.raises(RuntimeError, match="carry reservation close failure"):
        centered_carry_signal(11, (2, 3), horizon=2, ledger=ledger)
    assert attempts == 2
    assert ledger.nodes == ledger.entries == 0
    assert ledger.inventory()[-1].disposed


def test_signal_persistent_close_failure_keeps_retired_reservation_retryable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()

    def fail_close(_reservation: LedgerReservation) -> None:
        raise RuntimeError("injected persistent carry close failure")

    with monkeypatch.context() as fault:
        fault.setattr(LedgerReservation, "close", fail_close)
        with pytest.raises(RuntimeError, match="persistent carry close failure"):
            centered_carry_signal(11, (2, 3), horizon=2, ledger=ledger)
    account = ledger.inventory()[-1]
    assert account.nodes > 0 and not account.disposed
    ledger.mark_disposed(account.owner)
    assert ledger.nodes == ledger.entries == 0
    assert ledger.inventory()[-1].disposed
