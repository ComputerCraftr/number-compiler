from devtools.experiments.power_numbers.multiplication_consumer_congruence import (
    carrier_binary_closure_audits,
    multiplication_consumer_congruence_audits,
    multiplication_preflight_audits,
)


def test_existing_bounded_carriers_are_multiplicative_but_not_additive() -> None:
    rows = carrier_binary_closure_audits()
    assert {(row.family, row.parameter) for row in rows} == {
        ("fermat", 2),
        ("fermat", 3),
        ("mersenne", 5),
        ("mersenne", 7),
    }
    for row in rows:
        assert row.multiplication_closed
        assert row.multiplication_witness is None
        assert not row.addition_closed
        assert row.addition_witness is not None
        assert row.addition_witness.first_target != row.addition_witness.second_target


def test_consumer_partition_is_refined_to_exact_multiplication_congruence() -> None:
    expected = {
        ("fermat", 2): (3, 3),
        ("fermat", 3): (13, 17),
        ("mersenne", 5): (15, 16),
        ("mersenne", 7): (52, 64),
    }
    for row in multiplication_consumer_congruence_audits():
        assert (row.initial_consumer_classes, row.stable_classes) == expected[
            (row.family, row.parameter)
        ]
        assert row.multiplication_well_defined
        assert row.multiplication_cells_examined == row.carrier_classes**2
        assert (
            row.refinement_cells_examined
            == (row.refinement_rounds + 1) * row.carrier_classes**2
        )
        assert row.quotient_verification_cells == row.carrier_classes**2
        if row.initial_multiplication_conflicts:
            assert row.refinement_rounds > 0
            assert row.first_refinement_witness is not None
        else:
            assert row.refinement_rounds == 1
            assert row.first_refinement_witness is None
        assert not row.addition_available
        assert not row.scheduler_promotion_safe
        if row.quotient_table_published:
            assert row.noninjective
            assert row.quotient_multiplication_table is not None
            assert row.quotient_square_table == tuple(
                row.quotient_multiplication_table[i][i]
                for i in range(row.stable_classes)
            )
        else:
            assert not row.noninjective
            assert row.quotient_multiplication_table is None
            assert row.quotient_square_table is None


def test_large_carriers_fail_closed_before_cartesian_refinement() -> None:
    rows = {
        (row.family, row.parameter): row for row in multiplication_preflight_audits()
    }
    for key in (("fermat", 4), ("mersenne", 11), ("mersenne", 13)):
        row = rows[key]
        assert not row.refinement_admitted
        assert row.cartesian_cells > row.refinement_cell_budget
        assert row.addition_witness.first_target != row.addition_witness.second_target
        assert "orbit" in row.multiplication_congruence_method
