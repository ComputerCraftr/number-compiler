import pytest

from number_compiler.arithmetic.fields.integer_congruence import (
    Congruence,
    affine_preimage,
)
from number_compiler.sequences.prime.set import (
    canonical_multiplicative_lane_basis,
    smallest_factor,
)
from number_compiler.sequences.prime.wheel_cyclotomic import (
    PrimeWheelExtensionIndex,
    build_prime_wheel_cyclotomic_automaton,
)


def test_ordered_wheel_reuses_one_admitted_congruence_solution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0

    def counted(
        target: Congruence, *, gain: int, offset: int, denominator: int
    ) -> Congruence | None:
        nonlocal calls
        calls += 1
        return affine_preimage(
            target, gain=gain, offset=offset, denominator=denominator
        )

    monkeypatch.setattr(
        "number_compiler.sequences.prime.wheel_cyclotomic.affine_preimage", counted
    )
    index = PrimeWheelExtensionIndex.build(
        (6, 4, 2, 4, 2, 4, 6, 2), old_modulus=30, new_prime=7
    )
    assert calls == 1
    assert (
        tuple(
            tuple(
                position
                for position, residue in enumerate(index.old_residues)
                if (30 * copy + residue) % 7 == 0
            )
            for copy in range(7)
        )
        == index.deletion_positions
    )


def test_cyclotomic_wheel_field_groups_exactly_classify_finite_block() -> None:
    start, length = 9_999_993, 256
    basis = canonical_multiplicative_lane_basis(start, length)
    automaton = build_prime_wheel_cyclotomic_automaton(basis.lanes)
    assert automaton.lane_count == len(basis.lanes)
    assert len(automaton.groups) < len(basis.lanes)
    assert automaton.state_bits > 0
    for index in range(length):
        prime, _calls = automaton.classify_index(index)
        assert prime == (smallest_factor(start + 2 * index) is None)


def test_cyclotomic_wheel_advance_is_random_access_group_action() -> None:
    start, length = 999_993, 128
    basis = canonical_multiplicative_lane_basis(start, length)
    automaton = build_prime_wheel_cyclotomic_automaton(basis.lanes)
    zero = automaton.zero()
    a = automaton.advance(zero, 17)
    b = automaton.advance(automaton.advance(zero, 5), 12)
    assert a == b
    assert a.index == 17
    assert automaton.classify_state(a) == automaton.classify_index(17)


@pytest.mark.parametrize("modulus", (2, 4, 6, 7, 11))
def test_powered_phase_rotation_matches_chronological_composition(
    modulus: int,
) -> None:
    from number_compiler.sequences.prime.wheel_cyclotomic import PrimeWheelPhaseBlock

    for shift in range(modulus):
        block = PrimeWheelPhaseBlock.gap(shift, prime=modulus, alpha=1)
        expected = PrimeWheelPhaseBlock.identity(modulus, 1)
        for exponent in range(2 * modulus + 1):
            actual = block.power_block(exponent)
            assert actual.phase_histogram() == expected.phase_histogram()
            assert actual.phase_shift == expected.phase_shift
            assert actual.length == expected.length
            assert actual.compositions == 0
            expected = expected.then(block)


def test_large_phase_power_uses_orbit_quotient(monkeypatch: pytest.MonkeyPatch) -> None:
    from number_compiler.sequences.prime.wheel_cyclotomic import PrimeWheelPhaseBlock

    block = PrimeWheelPhaseBlock.gap(3, prime=7, alpha=1)

    def forbid_then(*_args: object) -> None:
        pytest.fail("phase power reconstructed a composition history")

    monkeypatch.setattr(PrimeWheelPhaseBlock, "then", forbid_then)
    exponent = 10**100
    result = block.power_block(exponent)
    assert sum(result.phase_histogram()) == exponent
    assert result.phase_shift == 3 * exponent % 7
    with pytest.raises(TypeError):
        block.power_block(True)
    with pytest.raises(ValueError):
        block.power_block(-1)
