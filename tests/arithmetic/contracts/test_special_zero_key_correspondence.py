"""Numeric regressions tying the zero-key obstruction to production objects.

The source-text check is an audit anchor, not extraction of Isabelle code into Python.
"""

from pathlib import Path

from devtools.proofs.oracles.special_primality import pepin_test
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.arithmetic.polynomials.primary_carry_jet import PrimaryCarryJet


ROOT = Path(__file__).resolve().parents[3]


def test_m11_zero_key_numeric_regression_agrees_with_arithmetic_tile() -> None:
    theory = (
        ROOT
        / "devtools/proofs/isabelle/etale/Mersenne_Zero_Key_Counterexample.thy"
    ).read_text()
    assert '"primary_root_key False 11 m11_zero_carry =' in theory
    assert '(False, -1, (14, 5))' in theory

    spec = ArithmeticTileSpec.mersenne(11)
    _, key = ArithmeticTile.from_value(spec, 0).step_with_primary_carry_jet()
    assert spec.modulus == 2047 == 23 * 89
    assert (key.deck_branch, key.seam_carry, key.jet) == (
        0,
        -1,
        PrimaryCarryJet(14, 5),
    )


def test_one_step_fermat_zero_key_does_not_determine_primality() -> None:
    f4_spec = ArithmeticTileSpec.fermat(1 << 4)
    f5_spec = ArithmeticTileSpec.fermat(1 << 5)
    _, f4_key = ArithmeticTile.from_value(
        f4_spec, 0
    ).step_with_primary_carry_jet()
    _, f5_key = ArithmeticTile.from_value(
        f5_spec, 0
    ).step_with_primary_carry_jet()
    zero_key = (
        0,
        0,
        PrimaryCarryJet(0, 0),
    )
    assert (f4_key.deck_branch, f4_key.seam_carry, f4_key.jet) == zero_key
    assert (f5_key.deck_branch, f5_key.seam_carry, f5_key.jet) == zero_key
    assert f5_spec.modulus == 4_294_967_297 == 641 * 6_700_417
    assert pepin_test(4).passes
    assert not pepin_test(5).passes
