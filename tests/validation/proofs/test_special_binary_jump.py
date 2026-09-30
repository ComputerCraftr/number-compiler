from devtools.verification.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    build_fermat_binary_jump,
    build_fermat_carrier_proof_uncached,
    build_mersenne_binary_jump,
    fermat_radix_orbit_representative,
    mersenne_sign_representative,
)
from devtools.verification.oracles.special_power_reference import (
    bounded_binary_target_jump,
)
from number_compiler.arithmetic.functions.finite_unary import (
    UnaryPowerArena,
    UnaryTransitionEffect,
)


def _fermat_target(index: int, steps: int) -> bool:
    width = 1 << index
    modulus = (1 << width) + 1
    value = 3
    for _ in range(steps):
        value = value * value % modulus
    return value == modulus - 1


def _mersenne_target(exponent: int, steps: int) -> bool:
    modulus = (1 << exponent) - 1
    value = 4 % modulus
    for _ in range(steps):
        value = (value * value - 2) % modulus
    return value == 0


def test_finite_unary_power_is_extensional_and_binary() -> None:
    primitive = (1, 2, 3, 0)
    arena = UnaryPowerArena(primitive)
    node = arena.power(1_000_003)
    assert node.effect.classes == 4
    assert arena.composition_operations <= 2 * (1_000_003).bit_length()
    # Extensional interning: the order-four permutation has period four.
    assert arena.power(4).effect == UnaryTransitionEffect.identity(4)


def test_carrier_artifact_reuses_frozen_semantics_and_retains_a_cold_builder() -> None:
    cold = build_fermat_carrier_proof_uncached(3)
    first = _fermat_carrier_proof(3)
    second = _fermat_carrier_proof(3, max_width=32)
    assert cold == first == second
    assert first is second
    assert cold is not first


def test_mersenne_sign_representative_is_exact_phi_p_mod2_partition() -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
        CyclotomicDigitBlock,
    )

    for p in (5, 7):
        modulus = (1 << p) - 1
        by_sign: dict[int, set[int]] = {}
        by_phi: dict[tuple[int, ...], set[int]] = {}
        for state in range(modulus):
            sign = mersenne_sign_representative(state, p)
            phi = CyclotomicDigitBlock.from_coefficients(
                digits_lsd(state, 2, p),
                order=p,
                modulus=2,
                length=p,
            ).residue
            by_sign.setdefault(sign, set()).add(state)
            by_phi.setdefault(phi, set()).add(state)
        assert {frozenset(group) for group in by_sign.values()} == {
            frozenset(group) for group in by_phi.values()
        }


def test_mersenne_phi2_carrier_minimizes_to_exact_order_depth_classes() -> None:
    for p, carrier, classes in ((5, 16, 5), (7, 64, 7), (11, 1024, 3), (13, 4096, 13)):
        program = build_mersenne_binary_jump(p)
        assert program.carrier_classes == carrier
        assert program.quotient_classes == classes
        assert program.quotient_state_bits == (classes - 1).bit_length()
        assert program.offset == 0
        assert program.construction_is_exhaustive
        assert not program.scalable_construction
        for steps in range(p + 3):
            result = program.apply(steps)
            assert result.target == _mersenne_target(p, steps)
            assert result.specialization_raw_squarings == 0
            assert result.construction_compositions <= 2 * max(1, steps.bit_length())


def test_fermat_radix_orbit_is_exact_negacyclic_root_action() -> None:
    for n in (2, 3, 4):
        width = 1 << n
        modulus = (1 << width) + 1
        order = 2 * width
        for source in (1, 3, 5, modulus - 1):
            rep = fermat_radix_orbit_representative(source, n)
            value = source % modulus
            orbit = []
            for _ in range(order):
                orbit.append(value)
                value = 2 * value % modulus
            assert value == source % modulus
            assert rep == min(orbit)


def test_fermat_delayed_radix_residual_minimizes_and_jumps_without_replay() -> None:
    expected = {
        2: (3, 2),
        3: (17, 5),
        4: (2049, 12),
    }
    for n, (carrier, classes) in expected.items():
        program = build_fermat_binary_jump(n)
        assert program.carrier_classes == carrier
        assert program.quotient_classes == classes
        assert program.offset == n + 1
        assert program.construction_is_exhaustive
        assert not program.scalable_construction
        width = 1 << n
        for steps in range(width + 3):
            result = program.apply(steps)
            assert result.target == _fermat_target(n, steps)
            if steps < program.offset:
                assert result.specialization_raw_squarings == steps
            else:
                assert result.specialization_raw_squarings == 0
                assert result.construction_compositions <= 2 * max(
                    1, (steps - program.offset).bit_length()
                )


def test_target_horizon_uses_real_binary_jump_not_raw_recurrence() -> None:
    f4 = build_fermat_binary_jump(4)
    f = f4.apply((1 << 4) - 1)
    assert f.target is True  # F4 = 65537 is prime.
    assert f.specialization_raw_squarings == 0
    assert f.quotient_steps == 10
    assert f4.quotient_classes == 12

    m13 = build_mersenne_binary_jump(13)
    m = m13.apply(11)
    assert m.target is True
    assert m.specialization_raw_squarings == 0
    assert m13.quotient_classes == 13


def test_explicit_oracle_can_apply_bounded_target_jump_to_power_program() -> None:
    from devtools.verification.special_power_monoid import (
        build_special_power_program,
    )

    f = bounded_binary_target_jump(build_special_power_program("fermat", 4, 15))
    assert f.target and f.specialization_raw_squarings == 0
    m = bounded_binary_target_jump(build_special_power_program("mersenne", 13, 11))
    assert m.target and m.specialization_raw_squarings == 0
