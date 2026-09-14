from __future__ import annotations

import pytest

from devtools.experiments.power_numbers.five_bit_support import (
    assembled_factor_truth_corpus,
    assembled_local_support_corpus,
    dense_folded_square_differential,
    incomplete_factor_evidence,
    minimum_bit_audit,
    packet_collisions,
    partial_f9_first_hole_audit,
    temporal_first_hole_audit,
    unrestricted_m53_counterexample,
)

pytestmark = pytest.mark.validation


def test_five_bit_packet_matches_full_folded_convolution() -> None:
    rows = assembled_local_support_corpus()
    assert len(rows) == 64
    assert all(dense_folded_square_differential(row).exact for row in rows)
    assert all(row.matches_sheet_all_pass for row in rows)


def test_minimum_bits_are_measured_on_the_assembled_corpus() -> None:
    audit = minimum_bit_audit()
    assert audit.corpus_rows == 64
    # The partial F9 local sheet is the needed adversary: neither arbitrary
    # packet-bit deletion nor a smaller pair of 2-power moduli classifies this
    # assembled corpus.  This remains a bounded corpus result.
    assert audit.minimum_bits == 5
    assert audit.sufficient_masks == ((0, 1, 2, 3, 4),)
    assert audit.minimum_power_modulus_bits == 5
    assert audit.sufficient_power_moduli == ((2, 3), (3, 2))


@pytest.mark.parametrize("parameter", (43, 47))
def test_large_mersenne_factor_sheets_are_noninjective(parameter: int) -> None:
    collisions = packet_collisions("mersenne", parameter)
    assert collisions
    assert all(row.left_orientations != row.right_orientations for row in collisions)
    assert any(
        row.left_dense_coefficients != row.right_dense_coefficients
        for row in collisions
    )


@pytest.mark.parametrize(
    ("family", "parameter", "expected_hole"),
    (
        ("fermat", 4, 12),
        ("fermat", 5, 2),
        ("mersenne", 11, 1),
        ("mersenne", 13, 12),
        ("mersenne", 29, 1),
    ),
)
def test_packet_detects_the_factor_truth_first_hole(
    family: str, parameter: int, expected_hole: int
) -> None:
    audit = temporal_first_hole_audit(family, parameter)
    assert audit.first_hole_level == expected_hole
    assert audit.exact
    assert audit.rows[-1].orientations != (1,) * len(audit.local_depths)


def test_partial_f9_sheet_detects_only_its_supplied_first_hole() -> None:
    audit = partial_f9_first_hole_audit()
    assert audit.local_depths == (6, 1)
    assert audit.first_hole_level == 2
    assert audit.exact
    assert not audit.rows[-1].sheet.complete_factorization
    assert audit.rows[-1].sheet.source == "supplied-partial-divisor-truth"


def test_partial_f9_divisors_remain_outside_the_factor_sheet_corpus() -> None:
    boundary = incomplete_factor_evidence()
    assert len(boundary) == 1
    assert boundary[0].excluded_family == "fermat"
    assert boundary[0].excluded_parameter == 9
    assert boundary[0].divisors_verified
    assert not boundary[0].complete_factorization
    assert boundary[0].status == "unverified-requested-case"
    assert all(
        not (row.sheet.family == "fermat" and row.sheet.parameter == 9)
        for row in assembled_factor_truth_corpus()
    )


def test_unrestricted_m53_sheet_has_a_zero_packet_false_positive() -> None:
    counterexample = unrestricted_m53_counterexample()
    row = counterexample.row
    assert row.sheet.modulus == (1 << 53) - 1
    assert row.orientations == (1, 1, -1)
    assert row.defect == 4_573_151_866_567_653
    assert row.projection.packet.canonical_key == (0, 0)
    assert row.projection.vanishes
    assert not row.all_pass
    assert counterexample.nontrivial_defect_gcd == 441_650_591
    dense = dense_folded_square_differential(row)
    assert dense.exact
    assert (dense.dense_r1, dense.dense_r2) == (12, 16)
    assert counterexample.local_depths == (1, 0, 0)
    admitted = {
        tuple(1 if depth >= level else -1 for depth in counterexample.local_depths)
        for level in range(1, max(counterexample.local_depths) + 2)
    }
    assert row.orientations not in admitted
    assert counterexample.status == "unrestricted-sheet-generalization-failure"
