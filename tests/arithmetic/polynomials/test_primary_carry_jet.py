from random import Random

import pytest

from number_compiler.arithmetic.carry.carry_normalization import (
    linear_normalization_fields,
)
from number_compiler.arithmetic.polynomials.primary_carry_jet import (
    PrimaryCarryJet,
    PrimaryEtaleCarryJetTransducer,
)


def direct_jet(values: tuple[int, ...]) -> PrimaryCarryJet:
    return PrimaryCarryJet(
        sum(v * (-1) ** i for i, v in enumerate(values)),
        sum(i * v * (-1) ** (i - 1) for i, v in enumerate(values) if i),
    )


def test_full_response_composition_and_normalization_basis() -> None:
    rng = Random(196)
    for length in range(1, 25):
        coefficients = tuple(rng.randrange(4) for _ in range(length))
        t = PrimaryEtaleCarryJetTransducer.from_coefficients(
            coefficients, incoming_min=0, incoming_max=3
        )
        for split in range(length + 1):
            left = PrimaryEtaleCarryJetTransducer.from_coefficients(
                coefficients[:split], incoming_min=0, incoming_max=3
            )
            right = PrimaryEtaleCarryJetTransducer.from_coefficients(
                coefficients[split:], incoming_min=0, incoming_max=3
            )
            composed = left.then(right)
            for incoming in range(4):
                digits, carries = linear_normalization_fields(
                    coefficients, base=2, boundary_in=incoming
                )
                outgoing, jet = t.response(incoming)
                assert composed.response(incoming) == (outgoing, jet)
                assert outgoing == carries[-1]
                assert jet == direct_jet(tuple(carries[1:]))
                defect = jet.normalization_defect(
                    length=length, incoming=incoming, outgoing=outgoing
                )
                assert defect == direct_jet(
                    tuple(a - b for a, b in zip(coefficients, digits, strict=True))
                )
                assert (
                    PrimaryCarryJet.from_normalization_defect(
                        defect, length=length, incoming=incoming, outgoing=outgoing
                    )
                    == jet
                )
                assert jet.marker_parities == (
                    sum(carries[1:]) % 2,
                    sum((i + 1) * c for i, c in enumerate(carries[1:])) % 2,
                )
                q = carries[1:]
                assert jet.harmonic_mod2 == (sum(q[::2]) % 2, sum(q[1::2]) % 2)


def test_binary_power_and_seam_admission() -> None:
    atom = PrimaryEtaleCarryJetTransducer.from_coefficients(
        (2, 1, 0), incoming_min=0, incoming_max=3
    )
    for n in (0, 1, 2, 17, 64):
        powered = atom.power_block(n)
        expanded = PrimaryEtaleCarryJetTransducer.from_coefficients(
            (2, 1, 0) * n, incoming_min=0, incoming_max=3
        )
        assert powered.transducer.canonical_key == expanded.transducer.canonical_key
        assert powered.transducer.compositions <= 2 * n.bit_length()
    assert atom.seam_key(deck_branch=0, seam_carry=0).jet == atom.response(0)[1]
    with pytest.raises(ValueError, match="fixed point"):
        atom.seam_key(deck_branch=0, seam_carry=3)


def test_negacyclic_seam_uses_an_anti_fixed_carry() -> None:
    t = PrimaryEtaleCarryJetTransducer.from_coefficients(
        (-3, 4), incoming_min=-4, incoming_max=4
    )
    assert t.response(-1)[0] == 1
    assert (
        t.seam_key(deck_branch=0, seam_carry=-1, boundary_sign=-1).jet
        == t.response(-1)[1]
    )
    with pytest.raises(ValueError, match="fixed point"):
        t.seam_key(deck_branch=0, seam_carry=-1, boundary_sign=1)


def test_signed_fermat_deck_is_derived_from_the_full_response() -> None:
    from number_compiler.arithmetic.carry.carry_normalization import (
        RadixCarryBlock,
        normalization_carry_boundaries,
        normalize_negacyclic_block,
    )

    for length in range(1, 17):
        coefficients = (0,) * (length - 1) + (2,)
        normal = normalize_negacyclic_block(
            RadixCarryBlock.from_coefficients(coefficients, base=2)
        )
        assert normal.exceptional_minus_one
        t = PrimaryEtaleCarryJetTransducer.from_coefficients(
            coefficients, incoming_min=-2, incoming_max=2
        )
        key = t.seam_key(
            deck_branch=1,
            seam_carry=normal.boundary_in,
            boundary_sign=-1,
            exceptional_minus_one=True,
        )
        carries = normalization_carry_boundaries(coefficients, normal)
        assert key.jet == direct_jet(tuple(carries[1:]))
        assert key.jet.normalization_defect(
            length=length, incoming=normal.boundary_in, outgoing=normal.boundary_out
        ) == direct_jet(tuple(a + int(i == 0) for i, a in enumerate(coefficients)))
        with pytest.raises(ValueError):
            t.seam_key(deck_branch=0, seam_carry=normal.boundary_in, boundary_sign=-1)
    invalid = PrimaryEtaleCarryJetTransducer.from_coefficients(
        (1, 1), incoming_min=-2, incoming_max=2
    )
    with pytest.raises(ValueError, match="does not certify"):
        invalid.seam_key(
            deck_branch=1, seam_carry=-1, boundary_sign=-1, exceptional_minus_one=True
        )


def test_sign_deck_is_independent_of_the_signed_output_chart() -> None:
    t = PrimaryEtaleCarryJetTransducer.from_coefficients(
        (0, 0, 1, 0), incoming_min=-1, incoming_max=1
    )
    first = t.seam_key(deck_branch=0, seam_carry=0, boundary_sign=-1)
    second = t.seam_key(deck_branch=1, seam_carry=0, boundary_sign=-1)
    assert first.jet == second.jet
    assert first != second


@pytest.mark.parametrize(
    "family,width", [("fermat", 4), ("fermat", 8), ("mersenne", 7)]
)
def test_tile_key_matches_independent_fold_and_carry(family: str, width: int) -> None:
    from number_compiler.arithmetic.polynomials.arithmetic_tile import (
        ArithmeticTile,
        ArithmeticTileSpec,
    )

    spec = ArithmeticTileSpec(family, width)
    n = spec.modulus
    for defect in range(n):
        # Independent exact definition supplied for the orientation experiment.
        def digits(value: int) -> tuple[int, ...]:
            if family == "fermat" and value == 1 << width:
                return (-1,) + (0,) * (width - 1)
            return tuple((value >> i) & 1 for i in range(width))

        chosen = min(
            (defect, (-defect) % n),
            key=lambda v: (sum(x != 0 for x in digits(v)), v),
        )
        word = digits(chosen)
        field = [0] * width
        for i, a in enumerate(word):
            for j, b in enumerate(word):
                field[(i + j) % width] += (
                    a * b * spec.boundary_sign ** ((i + j) // width)
                )
        field[0] += spec.addend
        value = sum(a << i for i, a in enumerate(field))
        residue = value % n
        out = digits(residue)
        output_value = sum(a << i for i, a in enumerate(out))
        seam = spec.boundary_sign * ((value - output_value) // n)
        carry = seam
        carries: list[int] = []
        for a, r in zip(field, out, strict=True):
            assert (a + carry - r) % 2 == 0
            carry = (a + carry - r) // 2
            carries.append(carry)
        assert carry == spec.boundary_sign * seam
        step, key = ArithmeticTile.from_value(
            spec, defect
        ).step_with_primary_carry_jet()
        assert key.deck_branch == int(chosen != defect)
        assert key.seam_carry == seam
        assert key.jet == direct_jet(tuple(carries))
        assert step.tile.residue == residue


@pytest.mark.parametrize("width", [3, 5, 7, 9, 11, 13, 15])
def test_mersenne_root_zero_section_needs_only_deck_and_seam(width: int) -> None:
    from number_compiler.arithmetic.polynomials.arithmetic_tile import (
        ArithmeticTile,
        ArithmeticTileSpec,
    )

    spec = ArithmeticTileSpec.mersenne(width)
    _, zero = ArithmeticTile.from_value(spec, 0).step_with_primary_carry_jet()
    assert (zero.deck_branch, zero.seam_carry) == (0, -1)
    for defect in range(spec.modulus):
        if defect * (defect + 2) % spec.modulus:
            continue
        _, key = ArithmeticTile.from_value(spec, defect).step_with_primary_carry_jet()
        assert ((key.deck_branch, key.seam_carry) == (0, -1)) == (defect == 0)
