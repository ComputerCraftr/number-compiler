"""Completed reverse occurrences answer queries without rebuilding history."""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import replace
from types import GeneratorType
from typing import Never

import pytest

from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveOccurrence,
    ReverseRecursiveTemporalCutover,
)

_D4_DIGITS = (3, 8, 7, 3, 1)


def _assert_d4_demands(
    cutover: ReverseRecursiveTemporalCutover, occurrence: ReverseRecursiveOccurrence
) -> None:
    assert cutover.width(occurrence) == len(_D4_DIGITS)
    assert cutover.digit(occurrence, 0) == _D4_DIGITS[0]
    assert tuple(cutover.iter_digits(occurrence)) == _D4_DIGITS


class _TrackedOutputIterator:
    def __init__(
        self,
        values: tuple[int, ...],
        *,
        failure: BaseException | None = None,
        close_failure: BaseException | None = None,
    ) -> None:
        self.values = values
        self.failure = failure
        self.close_failure = close_failure
        self.closed = False
        self.close_count = 0
        self.position = 0

    def __iter__(self) -> _TrackedOutputIterator:
        return self

    def __next__(self) -> int:
        if self.position < len(self.values):
            value = self.values[self.position]
            self.position += 1
            return value
        failure = self.failure
        self.failure = None
        if failure is not None:
            raise failure
        raise StopIteration

    def close(self) -> None:
        self.closed = True
        self.close_count += 1
        if self.close_failure is not None:
            raise self.close_failure


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


def _cutover_with_observed_pair_stream(
    monkeypatch: pytest.MonkeyPatch,
    *,
    values: tuple[int, ...],
    failure: BaseException | None = None,
    close_failure: BaseException | None = None,
) -> tuple[
    ReverseRecursiveTemporalCutover,
    ReverseRecursiveOccurrence,
    _TrackedOutputIterator,
]:
    cutover, occurrence = _completed_cutover()
    stream = _TrackedOutputIterator(
        values,
        failure=failure,
        close_failure=close_failure,
    )
    monkeypatch.setattr(
        cutover.outputs,
        "iter_observe_range",
        lambda *_args, **_kwargs: stream,
    )
    return cutover, occurrence, stream


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
    _assert_d4_demands(cutover, occurrence)
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


def test_point_early_return_closes_pair_output_iterator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover, occurrence, stream = _cutover_with_observed_pair_stream(
        monkeypatch,
        values=(18, 18, 18, 18, 9),
    )

    assert cutover.digit(occurrence, 0) == 8
    assert stream.closed
    assert stream.close_count == 1


def test_public_stream_cancellation_closes_pair_output_iterator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover, occurrence, stream = _cutover_with_observed_pair_stream(
        monkeypatch,
        values=(18, 18, 18, 18, 9),
    )

    digits = cutover.iter_digits(occurrence)
    assert next(digits) == 8
    digits.close()
    assert stream.closed
    assert stream.close_count == 1


def test_pair_stream_exception_closes_source_and_preserves_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_error = ValueError("pair stream failure")
    cutover, occurrence, stream = _cutover_with_observed_pair_stream(
        monkeypatch,
        values=(9,),
        failure=original_error,
        close_failure=RuntimeError("cleanup failure"),
    )

    with pytest.raises(ValueError, match="pair stream failure") as error:
        cutover.width(occurrence)
    assert error.value is original_error
    assert stream.closed
    assert stream.close_count == 1


def test_complete_width_query_closes_pair_output_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover, occurrence, stream = _cutover_with_observed_pair_stream(
        monkeypatch,
        values=(18, 18, 18, 18),
    )

    assert cutover.width(occurrence) == 5
    assert stream.closed
    assert stream.close_count == 1


@pytest.mark.parametrize("demand", ("point", "stream"))
def test_cancelled_real_pair_stream_releases_charged_frames(
    monkeypatch: pytest.MonkeyPatch,
    demand: str,
) -> None:
    cutover, occurrence = _completed_cutover()
    outputs = cutover.outputs
    original = outputs.iter_observe_range
    streams: list[Generator[int, None, None]] = []

    def retain_stream(
        output: CoordinateOutputMorphismID,
        start: int,
        stop: int,
        left: object,
        right: object,
    ) -> Generator[int, None, None]:
        stream = original(output, start, stop, left, right)
        streams.append(stream)
        return stream

    monkeypatch.setattr(outputs, "iter_observe_range", retain_stream)
    if demand == "point":
        assert cutover.digit(occurrence, 0) == _D4_DIGITS[0]
    else:
        digits = cutover.iter_digits(occurrence)
        assert next(digits) == _D4_DIGITS[0]
        digits.close()

    assert streams
    for stream in streams:
        assert isinstance(stream, GeneratorType)
        assert stream.gi_frame is None
    assert not outputs._stream_frames
    stream_resources = tuple(
        item
        for item in outputs.ledger.inventory()
        if item.owner == outputs._stream_owner
    )
    assert len(stream_resources) == 1
    assert stream_resources[0].entries == stream_resources[0].nodes == 0
    assert stream_resources[0].accounting_delta == 0


def test_width_point_and_stream_reuse_the_same_admitted_extent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover, occurrence = _completed_cutover()
    try:
        assert cutover.width(occurrence) == len(_D4_DIGITS)
        descents = cutover.ledger.counters["reverse_recursive_pair_width_descents"]

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("repeated exact extent discovery")

        with monkeypatch.context() as patch:
            patch.setattr(cutover.outputs, "observe_extent", forbidden)
            _assert_d4_demands(cutover, occurrence)
            assert (
                cutover.ledger.counters["reverse_recursive_pair_width_descents"]
                == descents
            )
            later = cutover.pair_image(8)
            with pytest.raises(AssertionError, match="repeated exact extent"):
                cutover.pair_width(later)
        assert cutover.ledger.counters["reverse_recursive_pair_width_failures"] == 1
        assert cutover.pair_width(later) == 6  # D8 terminal carry supplies digit seven.
        assert cutover.ledger.counters["reverse_recursive_pair_width_publications"] == 2
        with pytest.raises(ValueError):
            cutover.pair_width(replace(occurrence, _authority=object()))
        assert cutover._pair_widths.owner in cutover.ledger.evict_query_memos()
        # Query eviction discards the extent memo, not publication authority.
        # Re-answer from the same occurrence without reapplying its action.
        with monkeypatch.context() as patch:
            patch.setattr(cutover, "pair_image", forbidden)
            patch.setattr(cutover, "apply_to_occurrence", forbidden)
            assert cutover.pair_width(occurrence) == 4
            _assert_d4_demands(cutover, occurrence)
        assert cutover.ledger.counters["reverse_recursive_pair_width_publications"] == 3
    finally:
        cutover.dispose()
    with pytest.raises(ValueError, match="disposed"):
        cutover.pair_width(occurrence)
    with pytest.raises(RuntimeError, match="disposed"):
        len(cutover._pair_widths)
