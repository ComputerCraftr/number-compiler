"""Exhaustive binary jet and spatial response evidence, explicitly opt-in."""

import json
from collections.abc import Callable

import pytest

from devtools.proofs.collatz_harmonic_probe import (
    death,
    phase_normalization,
    spatial,
    temporal,
)


@pytest.mark.parametrize("chunk", range(16))
def test_all_odd_sixteen_bit_harmonic_identities(
    chunk: int, record_testsuite_property: Callable[[str, object], None]
) -> None:
    result = temporal(chunk)
    assert result["sources"] == 2048
    record_testsuite_property(f"collatz_temporal_chunk_{chunk}", json.dumps(result))


def test_complete_spatial_response_projection(
    record_testsuite_property: Callable[[str, object], None],
) -> None:
    result = spatial()
    assert result["length_counts"] == [5, 17, 53, 161, 485, 1457, 3752, 7568]
    record_testsuite_property("collatz_spatial_response", json.dumps(result))


def test_all_residual_phase_deaths() -> None:
    assert death()["phase_sequences"] == 7776


def test_exact_extent_is_not_part_of_harmonic_action_identity() -> None:
    assert phase_normalization() == {
        "occurrence_extents": 32,
        "wire_action_ids": 8,
        "output_action_ids": 4,
        "wire_potential_reuses": 24,
        "output_potential_reuses": 28,
    }
