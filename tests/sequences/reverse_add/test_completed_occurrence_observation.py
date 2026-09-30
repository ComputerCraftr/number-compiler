"""Completed reverse occurrences answer queries without rebuilding history."""

from __future__ import annotations

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveOccurrence,
    ReverseRecursiveTemporalCutover,
)

_D4_DIGITS = (3, 8, 7, 3, 1)


class _ForbiddenSourceDigits:
    def __iter__(self) -> Never:
        raise AssertionError("completed occurrence reread original source digits")

    def __len__(self) -> Never:
        raise AssertionError("completed occurrence measured original source digits")

    def __getitem__(self, _index: object) -> Never:
        raise AssertionError("completed occurrence indexed original source digits")


def _completed_cutover() -> tuple[
    ReverseRecursiveTemporalCutover, ReverseRecursiveOccurrence
]:
    source_digits = tuple(int(character) for character in reversed("196"))
    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), source_digits, base=10, maximum_steps=8
    )
    return cutover, cutover.pair_image(4)


@pytest.mark.parametrize("first_demand", ("width", "point", "stream"))
def test_completed_demands_do_not_read_the_seed(
    monkeypatch: pytest.MonkeyPatch, first_demand: str
) -> None:
    cutover, occurrence = _completed_cutover()
    monkeypatch.setattr(cutover, "source_digits", _ForbiddenSourceDigits())

    if first_demand == "width":
        assert cutover.width(occurrence) == len(_D4_DIGITS)
    elif first_demand == "point":
        assert cutover.digit(occurrence, 0) == _D4_DIGITS[0]
    else:
        assert tuple(cutover.iter_digits(occurrence)) == _D4_DIGITS


def test_completed_demands_do_not_recompile_temporal_history(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover, occurrence = _completed_cutover()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("completed query rebuilt a temporal occurrence")

    # These are the live chronology/construction entry points. Once the
    # occurrence is published, observations should only inspect its image.
    monkeypatch.setattr(cutover, "pair_image", forbidden)
    monkeypatch.setattr(cutover, "apply_to_occurrence", forbidden)
    monkeypatch.setattr(cutover, "square_occurrence", forbidden)
    monkeypatch.setattr(cutover.adapter, "_compile", forbidden)

    temporal_counters = (
        "reverse_recursive_occurrence_publications",
        "reverse_recursive_provider_applications",
        "reverse_recursive_source_relative_squares",
    )
    before = {name: cutover.ledger.counters.get(name, 0) for name in temporal_counters}
    assert cutover.width(occurrence) == len(_D4_DIGITS)
    assert cutover.digit(occurrence, 0) == _D4_DIGITS[0]
    assert tuple(cutover.iter_digits(occurrence)) == _D4_DIGITS
    assert {
        name: cutover.ledger.counters.get(name, 0) for name in temporal_counters
    } == before


@pytest.mark.parametrize("demand", ("width", "point", "stream"))
def test_public_demands_reject_forged_temporal_duration(demand: str) -> None:
    cutover, occurrence = _completed_cutover()
    forged = replace(occurrence, temporal_steps=occurrence.temporal_steps + 1)

    with pytest.raises(ValueError):
        if demand == "width":
            cutover.width(forged)
        elif demand == "point":
            cutover.digit(forged, 0)
        else:
            tuple(cutover.iter_digits(forged))
