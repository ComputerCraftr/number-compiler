"""Detect inconsistent local records when a Collatz cylinder is reused."""

from collections.abc import MutableMapping
from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
    CollatzDyadicOccurrence,
)


def _normalized_prefix(source: int, width: int) -> tuple[int, int]:
    current = source
    odd_symbols = 0
    for _ in range(width):
        if current & 1:
            current = (3 * current + 1) // 2
            odd_symbols += 1
        else:
            current //= 2
    return current, odd_symbols


def test_same_cylinder_duplicate_is_admitted_across_compatible_high_fibers() -> None:
    source = 27
    width = 8
    endpoint, odd_symbols = _normalized_prefix(source, width)
    other_source = source + (5 << width)
    other_endpoint, other_odd_symbols = _normalized_prefix(other_source, width)
    assert other_odd_symbols == odd_symbols

    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger) as macros:
        assert macros.remember(source, width, odd_symbols, endpoint)
        retained = macros.lookup(source, width)
        assert retained is not None
        assert retained.apply(other_source) == other_endpoint

        operand_work_before = ledger.counters.get("collatz_hashlife_operand_bits", 0)
        assert not macros.remember(
            other_source, width, other_odd_symbols, other_endpoint
        )
        assert ledger.counters["collatz_hashlife_operand_bits"] > operand_work_before
        assert ledger.counters["collatz_hashlife_occurrence_admission_rejections"] == 0


def test_duplicate_rejects_a_well_formed_but_wrong_published_endpoint() -> None:
    source = 27
    width = 8
    endpoint, odd_symbols = _normalized_prefix(source, width)
    multiplier = 3**odd_symbols
    correct_origin = endpoint - multiplier * (source >> width)
    forged_origin = (correct_origin + 1) % multiplier
    assert forged_origin != correct_origin

    forged = CollatzDyadicOccurrence(
        width,
        source & ((1 << width) - 1),
        odd_symbols,
        forged_origin,
        multiplier,
    )
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger) as macros:
        macros._publish(forged, source >> width)
        with pytest.raises(ValueError, match="disagrees with the new endpoint"):
            macros.remember(source, width, odd_symbols, endpoint)

        counters = ledger.counters
        assert counters["collatz_hashlife_occurrence_admission_rejections"] == 1
        assert counters["collatz_hashlife_failed_work"] == 1
        assert counters["collatz_hashlife_occurrence_publications"] == 1


def test_duplicate_does_not_treat_a_malformed_cached_value_as_a_miss() -> None:
    source = 27
    width = 8
    endpoint, odd_symbols = _normalized_prefix(source, width)
    key = (width, source & ((1 << width) - 1))

    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger) as macros:
        cast(MutableMapping[tuple[int, int], object], macros.occurrences)[key] = None
        with pytest.raises(ValueError, match="record is malformed"):
            macros.remember(source, width, odd_symbols, endpoint)

        assert macros.occurrences[key] is None
        assert ledger.counters["collatz_hashlife_occurrence_admission_rejections"] == 1
