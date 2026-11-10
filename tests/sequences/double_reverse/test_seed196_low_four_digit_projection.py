"""The seed-196 finite low-band helper matches literal physical iterates."""

from __future__ import annotations

from typing import NoReturn

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import LedgerReservation
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_digit_affine import (
    Seed196BandPhase,
    Seed196BandSheet,
    Seed196TwoBaseBand,
    seed196_low_four_digits_at_even_generation,
)
from tests.support.reverse_add_source_data import iterate_double_reverse


@pytest.mark.parametrize("generation", range(16, 66, 2))
def test_seed196_low_four_digit_helper_matches_physical_orbit(
    generation: int,
) -> None:
    expected = iterate_double_reverse(196, generation) % 10_000
    with DoubleReverseTerm(196, generation, max_steps=generation) as term:
        assert seed196_low_four_digits_at_even_generation(generation) == expected
        assert [term.digit(position) for position in range(4)] == [
            (expected // (10**position)) % 10 for position in range(4)
        ]


def test_seed196_low_band_helper_matches_4096_step_physical_orbit() -> None:
    generation = 4096
    expected = iterate_double_reverse(196, generation) % 10_000
    action = Seed196TwoBaseBand.at_even_generation(generation)
    assert action.low_four == expected


def test_seed196_digit_projection_avoids_endpoint_and_releases_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    generation = 1024
    expected = iterate_double_reverse(196, generation) % 10_000

    def fail_endpoint(_term: DoubleReverseTerm) -> NoReturn:
        raise AssertionError("low-band digit query prepared the full endpoint")

    def fail_stencil(_term: DoubleReverseTerm, _position: int) -> NoReturn:
        raise AssertionError("low-band digit query built a pointed stencil")

    monkeypatch.setattr(DoubleReverseTerm, "endpoint_root", fail_endpoint)
    monkeypatch.setattr(DoubleReverseTerm, "pointed_stencil", fail_stencil)
    with DoubleReverseTerm(
        196, generation, max_steps=generation, max_state_bits=30_000
    ) as term:
        before = (term.resource_ledger.entries, term.resource_ledger.nodes)
        actual = [term.digit(position) for position in range(4)]
        after = (term.resource_ledger.entries, term.resource_ledger.nodes)
        assert actual == [(expected // (10**position)) % 10 for position in range(4)]
        assert after == before
        assert term.metrics()["double_reverse_low_band_projections"] == 4
        assert term.metrics()["double_reverse_low_band_operand_bits"] > 0


def test_seed196_digit_projection_refuses_scratch_before_work_without_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    generation = 16
    original_reserve = LedgerReservation.reserve
    refused = False

    def refuse_once(
        reservation: LedgerReservation, *, entries: int = 0, nodes: int = 0
    ) -> None:
        nonlocal refused
        if not refused and entries == 1 and nodes == 1:
            refused = True
            raise BlockContextBudgetExceeded("injected low-band scratch refusal")
        original_reserve(reservation, entries=entries, nodes=nodes)

    monkeypatch.setattr(LedgerReservation, "reserve", refuse_once)
    with DoubleReverseTerm(196, generation, max_steps=generation) as term:
        before = (term.resource_ledger.entries, term.resource_ledger.nodes)
        with pytest.raises(BlockContextBudgetExceeded, match="injected low-band"):
            term.digit(0)
        assert refused
        assert (term.resource_ledger.entries, term.resource_ledger.nodes) == before
        assert term.metrics()["double_reverse_low_band_projections"] == 0


def test_seed196_low_band_keeps_conservative_full_state_bit_admission() -> None:
    generation = 1024
    expected = iterate_double_reverse(196, generation) % 10
    with DoubleReverseTerm(
        196, generation, max_steps=generation, max_state_bits=2_000
    ) as term:
        assert term.estimated_bit_length > term.max_state_bits
        assert term.digit(0) == expected
        assert term.metrics()["double_reverse_low_band_projections"] == 0


def test_low_band_rejects_source_width_metadata_tampering() -> None:
    with DoubleReverseTerm(196, 16, max_state_bits=54) as term:
        assert term.estimated_bit_length > term.max_state_bits
        term.source_digits = ()
        with pytest.raises(ValueError, match="source binding changed"):
            term.digit(0)
        assert term.metrics()["double_reverse_low_band_projections"] == 0


def test_seed196_low_band_controls_keep_class_and_pair_phase_distinct() -> None:
    entry = Seed196TwoBaseBand.entry()
    assert entry.phase is Seed196BandPhase.ENTRY
    assert entry.sheet is Seed196BandSheet.PHASE_ZERO
    assert entry.next_pair().sheet is Seed196BandSheet.AFTER_FIRST_PAIR
    assert entry.next_pair().next_pair().phase is Seed196BandPhase.FIRST


@pytest.mark.parametrize("generation", (14, 15, 17))
def test_seed196_low_band_rejects_unadmitted_generations(generation: int) -> None:
    with pytest.raises(ValueError):
        Seed196TwoBaseBand.at_even_generation(generation)


@pytest.mark.parametrize(
    ("seed", "generation", "position"),
    ((196, 17, 0), (196, 20, 4), (168, 20, 0)),
)
def test_low_band_fallback_keeps_other_digit_requests_exact(
    seed: int, generation: int, position: int
) -> None:
    expected = (iterate_double_reverse(seed, generation) // (10**position)) % 10
    with DoubleReverseTerm(seed, generation, max_steps=generation) as term:
        assert term.digit(position) == expected


@pytest.mark.parametrize("mutation", ("seed", "generation", "budget"))
def test_low_band_rejects_mutated_source_or_ledger_binding(mutation: str) -> None:
    with DoubleReverseTerm(196, 20) as term:
        if mutation == "seed":
            term.seed = 197
        elif mutation == "generation":
            term.generation = 18
        else:
            term.resource_ledger.max_cache_entries = 0
        with pytest.raises(ValueError, match="source binding changed|binding changed"):
            term.digit(0)
