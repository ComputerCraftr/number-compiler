from __future__ import annotations

import pytest

from devtools.experiments.power_numbers.radix64_mirror_refinement import (
    refinement_corpus_audit,
    single_coefficient_search,
    temporal_mirror_audit,
)


pytestmark = pytest.mark.validation


def test_radix64_fifth_residue_refines_the_72_row_corpus() -> None:
    audit = refinement_corpus_audit()
    assert len(audit.rows) == 72
    assert all(row.exact for row in audit.rows)
    assert audit.fifth_residue_classes == 16
    assert audit.legacy_false_positives == 1
    assert audit.legacy_false_negatives == 0
    assert audit.refined_false_positives == 0
    assert audit.refined_false_negatives == 0
    assert {
        (row.family, row.parameter): row.fifth_residue_classes
        for row in audit.class_counts
    } == {
        ("fermat", 4): 2,
        ("fermat", 5): 4,
        ("fermat", 6): 3,
        ("fermat", 7): 4,
        ("fermat", 9): 4,
        ("mersenne", 11): 4,
        ("mersenne", 13): 2,
        ("mersenne", 17): 2,
        ("mersenne", 19): 2,
        ("mersenne", 23): 3,
        ("mersenne", 29): 6,
        ("mersenne", 31): 2,
        ("mersenne", 37): 4,
        ("mersenne", 43): 8,
        ("mersenne", 47): 6,
        ("mersenne", 53): 7,
        ("mersenne", 61): 2,
    }

    m53_false_positive = next(
        row
        for row in audit.rows
        if row.source.sheet.parameter == 53
        and row.source.orientations == (1, 1, -1)
    )
    assert m53_false_positive.source.projection.vanishes
    assert m53_false_positive.dense_fifth == 13
    assert m53_false_positive.fifth.residue == 13


def test_fifth_mod16_is_the_unique_minimum_single_coefficient_witness() -> None:
    audit = single_coefficient_search()
    assert (audit.position_start, audit.position_stop) == (0, 10)
    assert (audit.modulus_bits_start, audit.modulus_bits_stop) == (1, 12)
    assert audit.search_order == "modulus-bits-then-coefficient-position"
    assert audit.minimum_modulus_bits == 4
    assert tuple(
        (row.position, row.modulus_bits) for row in audit.minimum_witnesses
    ) == ((5, 4),)
    assert (8, 5) in {
        (row.position, row.modulus_bits) for row in audit.all_witnesses
    }


@pytest.mark.parametrize(
    ("family", "parameter", "depths", "last_level", "partial"),
    (
        ("fermat", 4, (11,), 14, False),
        ("fermat", 5, (1, 1), 4, False),
        ("fermat", 9, (6, 1), 9, True),
        ("mersenne", 11, (0, 0), 3, False),
        ("mersenne", 13, (11,), 14, False),
        ("mersenne", 29, (0, 0, 1), 4, False),
    ),
)
def test_temporal_rows_use_common_depth_orientations_through_the_audit_horizon(
    family: str,
    parameter: int,
    depths: tuple[int, ...],
    last_level: int,
    partial: bool,
) -> None:
    audit = temporal_mirror_audit(family, parameter)
    assert audit.local_depths == depths
    assert audit.last_level == last_level
    assert audit.partial_factor_sheet is partial
    assert len(audit.rows) == last_level
    assert all(row.exact for row in audit.rows)
    for level, row in enumerate(audit.rows, start=1):
        assert row.source.orientations == tuple(
            1 if depth >= level else -1 for depth in depths
        )
        assert row.fifth.vanishes == (level <= min(depths))
    assert next(
        level for level, row in enumerate(audit.rows, start=1) if not row.fifth.vanishes
    ) == min(depths) + 1
