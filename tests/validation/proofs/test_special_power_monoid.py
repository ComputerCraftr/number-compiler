from devtools.verification.oracles.special_power_reference import (
    apply_special_power_reference,
)
from devtools.verification.oracles.special_primality import (
    lucas_lehmer_test,
    pepin_test,
)
from devtools.verification.special_power_monoid import (
    build_special_power_program,
)
from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
from number_compiler.sequences.power_numbers.two_primary_clock import (
    mersenne_norm_one_multiply,
)


def _fermat_reference(index: int, source: int, steps: int) -> int:
    width = 1 << index
    modulus = (1 << width) + 1
    value = source % modulus
    for _ in range(steps):
        value = value * value % modulus
    return value


def _mersenne_reference(exponent: int, source: int, steps: int) -> int:
    modulus = (1 << exponent) - 1
    value = source % modulus
    for _ in range(steps):
        value = (value * value - 2) % modulus
    return value


def test_powered_operator_is_the_shared_quadratic_morphism_without_arena_provenance() -> (
    None
):
    for steps in (0, 1, 2, 3, 37, 1_000_003):
        program = build_special_power_program("fermat", 4, steps)
        assert program.steps == steps
        assert isinstance(program.operator, QuadraticPower)
        assert program.operator.depth == steps
        assert program.canonical_key == ("special-power-program", "fermat", 4, steps)
        assert program.construction_compositions <= 2 * max(1, steps.bit_length())
        assert not hasattr(program, "node")
        assert not hasattr(program, "arena_nodes")


def test_raw_specialization_regenerates_intermediate_state_but_charges_every_squaring() -> (
    None
):
    for index in (1, 2, 3):
        width = 1 << index
        for steps in range(width):
            program = build_special_power_program("fermat", index, steps)
            for source in (0, 1, 2, 3, min((1 << width), 17)):
                application = apply_special_power_reference(program, source)
                assert application.value == _fermat_reference(index, source, steps)
                assert application.nonlinear_squarings == steps
                assert program.raw_specialization_lower_bound == steps
                assert program.fast_raw_exact is False

    for exponent in (3, 5, 7):
        for steps in range(exponent):
            program = build_special_power_program("mersenne", exponent, steps)
            for source in (0, 1, 2, 4, 7):
                application = apply_special_power_reference(program, source)
                assert application.value == _mersenne_reference(exponent, source, steps)
                assert application.nonlinear_squarings == steps
                assert program.raw_specialization_lower_bound == steps
                assert program.fast_raw_exact is False


def test_fermat_prime_domain_powered_image_rank_matches_exhaustive_map() -> None:
    for index in (2, 3):
        width = 1 << index
        modulus = (1 << width) + 1
        values = tuple(range(modulus))
        for steps in range(width + 1):
            program = build_special_power_program("fermat", index, steps)
            assert len(set(values)) == program.prime_domain_image_classes()
            values = tuple(value * value % modulus for value in values)


def test_mersenne_prime_norm_one_trace_powered_image_rank_matches_exhaustive_subgroup() -> (
    None
):
    for exponent in (5, 7):
        modulus = (1 << exponent) - 1
        generator = (2, 1)
        units: list[tuple[int, int]] = []
        value = (1, 0)
        for _ in range(1 << exponent):
            units.append(value)
            value = mersenne_norm_one_multiply(value, generator, modulus)
        assert value == (1, 0)
        assert len(set(units)) == 1 << exponent

        for steps in range(exponent + 1):
            traces = {2 * a % modulus for a, _b in units}
            program = build_special_power_program("mersenne", exponent, steps)
            assert len(traces) == program.prime_domain_image_classes()
            units = [mersenne_norm_one_multiply(unit, unit, modulus) for unit in units]


def test_primality_paths_use_monoid_but_do_not_misreport_operator_construction_as_execution() -> (
    None
):
    f4 = pepin_test(4)
    assert f4.passes
    assert f4.squarings == f4.raw_specialization_squarings == 15
    assert f4.operator_compositions < f4.raw_specialization_squarings
    assert f4.powered_image_classes == 3

    m13 = lucas_lehmer_test(13)
    assert m13.passes
    assert m13.iterations == m13.raw_specialization_squarings == 11
    assert m13.operator_compositions < m13.raw_specialization_squarings
    assert m13.powered_image_classes == 3
