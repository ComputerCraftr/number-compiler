"""Bulk phase reads validate the retained source chain once per batch."""

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.sequences.reverse_add.q19_border_control import (
    CertifiedBorderGrowth,
)
from number_compiler.sequences.reverse_add.temporal_carry_phase import (
    CertifiedCarryWord,
)
from tests.support.reverse_add_carry_fixture import source_196_generation_79_border


def _word(certificate: CertifiedBorderGrowth) -> CertifiedCarryWord:
    first = certificate.temporal_ring_bank(start=0, duration=4, positions=(0, 1, 2))
    second = certificate.temporal_ring_bank(start=4, duration=5, positions=(0, 1, 2))
    return first.conditional_carry_word().then(second.conditional_carry_word())


def test_phase_batch_matches_issued_objects_and_validates_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with source_196_generation_79_border() as (
        _value,
        _ledger,
        _owner,
        certificate,
    ):
        word = _word(certificate)
        repeated = word.conditional_power(10**9)
        ticks = tuple(i * 7 for i in range(500))
        expected = tuple(word.phases[tick % word.duration] for tick in ticks)
        original = CertifiedCarryWord.validate
        visits = 0

        def counted(self: CertifiedCarryWord) -> None:
            nonlocal visits
            visits += 1
            return original(self)

        monkeypatch.setattr(CertifiedCarryWord, "validate", counted)
        observed = repeated.phase_batch(ticks)
        assert observed == expected
        assert all(a is b for a, b in zip(observed, expected, strict=True))
        assert visits == 1
        assert repeated.phase_batch(()) == ()
        assert visits == 2


def test_phase_batch_rejects_bad_coordinates_mutation_and_stale_owner() -> None:
    with source_196_generation_79_border() as (
        _value,
        _ledger,
        _owner,
        certificate,
    ):
        word = _word(certificate)
        repeated = word.conditional_power(1000)
        with pytest.raises(IndexError):
            repeated.phase_batch((0, repeated.duration))
        with pytest.raises(IndexError):
            repeated.phase_batch((True,))
        with pytest.raises(TypeError):
            repeated.phase_batch(cast(tuple[int, ...], [0, 1]))
        phase = word.phases[0]
        original = phase.middle_wire
        object.__setattr__(phase, "middle_wire", replace(original, pair_domains=()))
        try:
            with pytest.raises(ValueError):
                repeated.phase_batch((0, 1))
            with pytest.raises(ValueError):
                repeated.phase(0)
        finally:
            object.__setattr__(phase, "middle_wire", original)
    with pytest.raises(ValueError):
        repeated.phase_batch((0,))
