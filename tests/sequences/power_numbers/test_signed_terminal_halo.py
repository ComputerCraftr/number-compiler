"""Exact signed carry-birth/H5 → primary halo regression tests.

The finite source rows in these tests are independent truth-oracle labels;
the production construction must not infer their missing next forcing term
from the unwrapped Walsh, pivot, or CRT packet.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest

from devtools.verification.fermat_integral_ideal_reference import (
    FermatIntegralIdealWitness,
)
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.signed_weighted_carry import WideSignedCarryAction
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.signed_terminal_halo import (
    compose_four_exact_birth_observations,
    demand_signed_birth_window,
)


def _carry_action_from_coefficients(
    coefficients: tuple[int, ...], *, sign: int
) -> WideSignedCarryAction:
    arena = SLPArena()
    return WideSignedCarryAction(arena, arena.word(coefficients), sign=sign)


def _cyclic_source_square_coefficients(value: int, width: int) -> tuple[int, ...]:
    bits = [(value >> i) & 1 for i in range(width)]
    out = [0] * width
    out[0] -= 2
    for i, a in enumerate(bits):
        if a:
            for j, b in enumerate(bits):
                if b:
                    out[(i + j) % width] += 1
    return tuple(out)


@pytest.mark.parametrize("index", (3, 4))
def test_actual_fermat_five_source_births_are_nilpotent_and_source_checked(
    index: int,
) -> None:
    width = 1 << index
    terminal = width - 1
    witnesses = tuple(
        FermatIntegralIdealWitness.from_source(index, level=t)
        for t in range(terminal - 4, terminal + 1)
    )
    assert all(w.verify() for w in witnesses)
    sources = tuple(
        _carry_action_from_coefficients(w.folded, sign=-1) for w in witnesses
    )
    for witness, source in zip(witnesses, sources):
        assert tuple(source.carry_at(j) for j in range(width + 1)) == witness.carries
    composed = compose_four_exact_birth_observations(sources)
    assert composed.result.source_annihilated
    assert composed.result.apply((9, 7)) == composed.endpoint_birth_jet
    assert not composed.source_authenticated
    # The terminal remainder and normalized unit are determined by the actual
    # authenticated source, not by inventing an extra Moore state.
    modulus = (1 << width) + 1
    residue = sources[-1].residue
    unit = ((residue - 1) * pow(2, -(terminal + 2), modulus)) % modulus
    assert unit == 1


def test_mersenne_cyclic_signed_birth_h5_and_seam() -> None:
    for source_value, expected in ((194, 4870), (4870, 3953), (3953, 5970)):
        action = _carry_action_from_coefficients(
            _cyclic_source_square_coefficients(source_value, 13), sign=1
        )
        assert action.residue == expected
        row = demand_signed_birth_window(action, start=0, length=13)
        assert row.birth_parity_mask == row.carry_parity_mask
        assert row.carries[-1] == action.carry_at(13)
        assert action.carry_at(13) == action.c0
        assert row.first_halo_carries == tuple(
            action.carry_at(j) for j in (1, 2, 3, 5, 6)
        )


def test_walsh_birth_is_not_a_source_or_prime_certificate() -> None:
    true_coefficients = _cyclic_source_square_coefficients(4870, 13)
    honest = _carry_action_from_coefficients(true_coefficients, sign=1)
    forged = _carry_action_from_coefficients((0,) * 13, sign=1)
    assert demand_signed_birth_window(forged, length=13).birth_parity_mask == 0
    assert demand_signed_birth_window(honest, length=13).birth_parity_mask != 0
    # A fake current output and a real current output are both syntactically
    # valid signed folds. Their H5 packets must not authorize source equality.
    assert (
        FermatNumberSpec(4)
        .demand_joint_three_power_quotient(15, ((2, 8), (3, 5), (5, 5)), moving_width=0)
        .terminal_status
        == "UNKNOWN"
    )


def test_source_halo_guards_refuse_wrong_length_and_walsh_tampering() -> None:
    action = _carry_action_from_coefficients((3, 1, -2, 0, 4, 2, 0, 0), sign=-1)
    window = demand_signed_birth_window(action, length=8)
    with pytest.raises(ValueError, match="parity"):
        replace(window, birth_parity_mask=window.birth_parity_mask ^ 1)
    with pytest.raises(TypeError, match="h5"):
        changes: dict[str, object] = {
            "h5": demand_signed_birth_window(action, length=3).h5
        }
        unchecked_replace = cast(Callable[..., object], replace)
        unchecked_replace(window, **changes)
    with pytest.raises(ValueError, match="five exact"):
        compose_four_exact_birth_observations((action,) * 4)
    with pytest.raises(ValueError, match="width"):
        demand_signed_birth_window(action, start=1, length=8)


def test_no_unverified_birth_can_issue_prime_status() -> None:
    action = _carry_action_from_coefficients((0,) * 16, sign=-1)
    window = demand_signed_birth_window(action, length=16)
    assert not hasattr(window, "terminal_status")
    assert not hasattr(window, "prime")
    assert not hasattr(window, "source_authenticated")


def test_h5_zero_kernel_is_not_generic_fermat_primality() -> None:
    zero = _carry_action_from_coefficients((0,) * 16, sign=-1)
    minus_one = _carry_action_from_coefficients((-1,) + (0,) * 15, sign=-1)
    zero_h5 = demand_signed_birth_window(zero, length=16).h5
    minus_one_h5 = demand_signed_birth_window(minus_one, length=16).h5
    assert zero_h5 == minus_one_h5
    assert zero.residue == 0 and minus_one.residue == (1 << 16)
    assert zero_h5.phi2 == zero_h5.phi3_a == zero_h5.phi3_b == 0
    # The restricted Fermat support-orientation theorem must authenticate a
    # nonzero terminal distinction; a generic zero H5 cannot supply it.


@pytest.mark.parametrize(("exponent", "terminal_zero"), ((11, False), (13, True)))
def test_mersenne_signed_fold_audit_reference_is_explicitly_sequential(
    exponent: int, terminal_zero: bool
) -> None:
    # Research oracle only: these p-2 source-fold applications are EXACTLY
    # Lucas-Lehmer work in cyclic digit coordinates, not a temporal shortcut.
    from number_compiler.sequences.power_numbers.numbers import MersenneNumberSpec

    value = 4
    for _ in range(exponent - 2):
        source = _carry_action_from_coefficients(
            _cyclic_source_square_coefficients(value, exponent), sign=1
        )
        window = MersenneNumberSpec(exponent).project_signed_fold_birth_window(
            source, length=exponent
        )
        assert window.carries[-1] == source.c0
        value = source.residue
    assert (value == 0) is terminal_zero


def test_family_seam_and_width_guards_cannot_cross_sources() -> None:
    from number_compiler.sequences.power_numbers.numbers import MersenneNumberSpec

    source_16 = _carry_action_from_coefficients((0,) * 16, sign=-1)
    source_13 = _carry_action_from_coefficients((0,) * 13, sign=1)
    assert (
        FermatNumberSpec(4).project_signed_fold_birth_window(source_16, length=16).sign
        == -1
    )
    assert (
        MersenneNumberSpec(13)
        .project_signed_fold_birth_window(source_13, length=13)
        .sign
        == 1
    )
    with pytest.raises(ValueError, match="Fermat"):
        FermatNumberSpec(4).project_signed_fold_birth_window(source_13, length=13)
    with pytest.raises(ValueError, match="Mersenne"):
        MersenneNumberSpec(13).project_signed_fold_birth_window(source_16, length=13)
