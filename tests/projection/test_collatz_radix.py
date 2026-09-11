import pytest

from number_compiler.projection.collatz_orbits.binary import collatz_orbit_formulas
from number_compiler.sequences.collatz.radix import collatz_orbit_formulas_ternary


@pytest.mark.validation  # Complete 111-step binary/ternary formula orbits.
def test_ternary_collatz_formula_matches_binary_canonical_orbit() -> None:
    _a2, binary = collatz_orbit_formulas(
        27, max_steps=111, stop_at_one=False, materialize_values=True
    )
    _a3, ternary = collatz_orbit_formulas_ternary(
        27, max_steps=111, stop_at_one=False, materialize_values=True
    )
    assert [row.value for row in ternary] == [row.value for row in binary]
    # The radix-3 representation is not cosmetic: 3*n+1 is a structural shift,
    # and the concrete seed-27 formula DAG is substantially smaller.
    assert ternary[-1].formula_nodes < binary[-1].formula_nodes // 2


def test_ternary_odd_branch_uses_division_remainder_monoid_not_multiply_carry_monoid() -> (
    None
):
    _arena, rows = collatz_orbit_formulas_ternary(
        27, max_steps=1, stop_at_one=False, materialize_values=True
    )
    odd = rows[1]
    assert odd.branch == "multiply_3_add_1_radix_shift"
    assert odd.value == 82
    assert odd.transducer_states == 2
    assert odd.transition_monoid_size == 2
