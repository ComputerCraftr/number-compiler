from number_compiler.arithmetic.fields.morphism_core import (
    AffineCocycle,
    DyadicAffineCocycle,
    QuadraticPower,
    binary_power,
    trace_square,
)
from number_compiler.arithmetic.polynomials.polynomial import trace_square_polynomial


def test_binary_power_uses_shared_logarithmic_composition() -> None:
    out = binary_power(3, 13, identity=0, compose=lambda a, b: a + b)
    assert out.value == 39
    assert out.compositions == 6


def test_affine_cocycle_composition_order() -> None:
    first = AffineCocycle(3, 1)
    second = AffineCocycle(5, 7)
    composed = first.then(second, multiply=lambda a, b: a * b, add=lambda a, b: a + b)
    assert composed == AffineCocycle(15, 12)
    assert composed.apply(
        11, multiply=lambda a, b: a * b, add=lambda a, b: a + b
    ) == second.apply(
        first.apply(11, multiply=lambda a, b: a * b, add=lambda a, b: a + b),
        multiply=lambda a, b: a * b,
        add=lambda a, b: a + b,
    )


def test_dyadic_affine_square_matches_self_composition() -> None:
    block = DyadicAffineCocycle(9, 17, 5)
    assert block.square() == block.then(block)
    powered = block.power(9)
    direct = DyadicAffineCocycle.identity()
    for _ in range(9):
        direct = direct.then(block)
    assert powered.value == direct
    assert powered.compositions < 9


def test_quadratic_power_unifies_multiplicative_and_trace_coordinates() -> None:
    q = QuadraticPower.atom().power(7)
    assert q.value.depth == 7
    modulus = 127
    y = 11
    u = (y + pow(y, -1, modulus)) % modulus
    y2 = q.value.apply_multiplicative(y, modulus)
    u2 = q.value.apply_trace(u, modulus)
    assert u2 == (y2 + pow(y2, -1, modulus)) % modulus


def test_trace_square_polynomial_is_196_real_cyclotomic_doubling() -> None:
    # u=x-2, so u^2-2 = x^2-4x+2 = P8(x).
    p8 = trace_square_polynomial((-2, 1))
    assert p8 == (2, -4, 1)
    assert trace_square_polynomial(p8) == (2, -16, 20, -8, 1)
    assert trace_square(4) == 14


def test_lazy_lowering_cache_materializes_once_per_canonical_key() -> None:
    from number_compiler.arithmetic.fields.morphism_core import LazyLoweringCache

    cache: LazyLoweringCache[tuple[str, int], tuple[str, int]] = LazyLoweringCache()
    calls = 0

    def lower() -> tuple[str, int]:
        nonlocal calls
        calls += 1
        return ("large-carrier", 7)

    first = cache.get_or_lower(("morphism", 7), lower)
    second = cache.get_or_lower(("morphism", 7), lower)
    assert first is second
    assert calls == 1
    assert cache.misses == 1 and cache.hits == 1 and cache.size == 1
