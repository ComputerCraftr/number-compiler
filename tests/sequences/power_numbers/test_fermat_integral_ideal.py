"""Bounded unit checks for authenticated Fermat integral ideal witnesses."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from devtools.verification.emit_fermat_ideal_certificate import emit
from devtools.verification.fermat_integral_ideal_reference import (
    FermatIntegralIdealWitness,
    SourceCoefficientBudgetExceeded,
)
from devtools.verification.verify_fermat_ideal_certificate import verify
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.signed_weighted_carry import (
    SignedCarryBudgetExceeded,
    WeightedCarryBlock,
    WideSignedCarryAction,
)


def test_weighted_signed_carry_composition_and_repeat_are_exact() -> None:
    left = WeightedCarryBlock(1, -3)
    right = WeightedCarryBlock(1, 5)
    joined = left.then(right, max_length=64)
    for incoming in range(-8, 9):
        direct = (5 + ((-3 + incoming) // 2)) // 2
        assert joined.apply(incoming) == direct
    repeated = left.power(31, max_length=64)
    assert repeated.length == 31
    assert repeated.value == -3 * ((1 << 31) - 1)


def test_signed_carry_handles_large_coefficients_in_a_repeated_slp() -> None:
    arena = SLPArena()
    coefficient = (1 << 20_480) + 319
    block = arena.concat(arena.terminal(-coefficient), arena.terminal(coefficient))
    root = arena.repeat(block, 5)
    action = WideSignedCarryAction(arena, root, sign=-1)
    assert action.width == 10
    assert action.verify_cochain()
    assert action.residue == action.block.value % 1025
    assert tuple(row[0] for row in action.demand((0, 1, 2, 9))) == (0, 1, 2, 9)


def test_signed_carry_rejects_width_and_integer_budgets_before_summary() -> None:
    arena = SLPArena()
    root = arena.word((1 << 500, 0, 0, 0))
    with pytest.raises(SignedCarryBudgetExceeded, match="width exceeds budget"):
        WideSignedCarryAction(arena, root, sign=-1, max_width=3)
    with pytest.raises(SignedCarryBudgetExceeded, match="weighted integer budget"):
        WideSignedCarryAction(arena, root, sign=-1, max_weighted_bits=100)


def test_signed_carry_demand_rejects_oversized_positions_before_hashing() -> None:
    arena = SLPArena()
    action = WideSignedCarryAction(arena, arena.word((1, 2)), sign=-1)
    positions = cast(tuple[int, ...], ([], [], []))
    with pytest.raises(ValueError, match="exceeds action width"):
        action.demand(positions)


def test_signed_carry_demand_validates_positions_before_duplicate_set() -> None:
    arena = SLPArena()
    action = WideSignedCarryAction(arena, arena.word((1, 2)), sign=-1)
    with pytest.raises(IndexError):
        action.demand(cast(tuple[int, ...], ([], [])))


def test_bounded_reference_f2_witness_authenticates_integral_pepin_identity() -> None:
    witness = FermatIntegralIdealWitness.from_source(2)
    assert witness.verify()
    assert witness.terminal
    assert witness.terminal_result() == "PRIME"
    assert witness.terminal_ideal_member()
    assert witness.signed_digits == (-1,) + (0,) * (witness.width - 1)
    assert witness.carries[-1] == -witness.carries[0]
    assert witness.exponent + 1 == 9


def test_source_checker_rejects_forged_fold_carry_and_prime_label() -> None:
    witness = FermatIntegralIdealWitness.from_source(2)
    changed_fold = list(witness.folded)
    changed_fold[2] += 1
    assert not replace(witness, folded=tuple(changed_fold)).verify()

    changed_carries = list(witness.carries)
    changed_carries[2] += 1
    assert not replace(witness, carries=tuple(changed_carries)).verify()

    changed_digits = list(witness.signed_digits)
    changed_digits[0] = 0
    counterfeit = replace(witness, signed_digits=tuple(changed_digits))
    assert not counterfeit.verify()
    with pytest.raises(ValueError, match="unauthenticated"):
        counterfeit.terminal_result()


def test_terminal_projection_validates_index_before_computing_terminal_width() -> None:
    forged = FermatIntegralIdealWitness.from_source(2)
    object.__setattr__(forged, "index", 10**9)
    with pytest.raises(ValueError, match="unauthenticated"):
        forged.terminal_result()


@pytest.mark.parametrize("field", ("folded", "carries", "signed_digits"))
def test_witness_rejects_oversized_vectors_before_scanning_elements(
    field: str,
) -> None:
    witness = FermatIntegralIdealWitness.from_source(1)
    expected_length = witness.width + int(field == "carries")
    oversized = (False,) * (expected_length + 1)
    folded = oversized if field == "folded" else witness.folded
    carries = oversized if field == "carries" else witness.carries
    signed_digits = oversized if field == "signed_digits" else witness.signed_digits

    with pytest.raises(ValueError, match="vector lengths do not match"):
        FermatIntegralIdealWitness(
            witness.index,
            witness.level,
            folded,
            carries,
            signed_digits,
        )


def test_bounded_certificate_emitter_and_independent_verifier_round_trip(
    tmp_path: Path,
) -> None:
    path = tmp_path / "fermat.json"
    assert emit(2, path) == "PRIME"
    report = verify(path)
    assert report["status"] == "PRIME"
    assert report["source_recomputed"] is True
    assert report["modular_squarings"] == 0

    payload = path.read_text()
    path.write_text(
        payload.replace("exact-integer-binomial-negacyclic-fold-v1", "forged")
    )
    with pytest.raises(
        ValueError, match="unauthenticated Fermat integral ideal witness"
    ):
        verify(path)


def test_nonterminal_and_overbudget_sources_do_not_issue_prime_results() -> None:
    partial = FermatIntegralIdealWitness.from_source(4, level=2)
    assert partial.verify()
    assert not partial.terminal
    with pytest.raises(ValueError, match="terminal"):
        partial.terminal_result()

    with pytest.raises(SourceCoefficientBudgetExceeded, match="term budget"):
        FermatIntegralIdealWitness.from_source(5)
