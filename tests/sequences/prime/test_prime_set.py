from number_compiler.sequences.prime.set import (
    AdditiveTranslation,
    MultiplicativeSetOperator,
    PrimeBlockSummary,
    composite_convolution,
    project_odd_prime_block,
)


def test_multiplicative_convolution_is_exact_without_prime_table() -> None:
    primes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}
    for n in range(2, 31):
        assert composite_convolution(n) == (n not in primes)


def test_symbolic_translation_is_additive_monoid() -> None:
    op = MultiplicativeSetOperator.at(123)
    assert op.translate(17).translate(29) == op.translate(46)
    symbolic = AdditiveTranslation.power_of_two(1_000_000)
    huge = op.translate(symbolic)
    assert huge.operator_nodes == 1
    assert huge.description_bits < 128
    doubled = symbolic.then(symbolic)
    assert doubled.pow2_exponents == (1_000_001,)


def test_prime_summary_monoid() -> None:
    a = PrimeBlockSummary(4, 1, 2)
    b = PrimeBlockSummary(3, 2, 0)
    c = PrimeBlockSummary(5, 0, None)
    assert a.then(b) == PrimeBlockSummary(7, 3, 2)
    assert a.then(b).then(c) == a.then(b.then(c))


def test_prime_projection_reproduces_first_hole_and_canonical_lane_counts() -> None:
    p = 9_999_991
    expected = {
        16: (40, 17),
        64: (132, 54),
        256: (429, 150),
        1024: (1071, 317),
        4096: (1581, 446),
    }
    for length, (natural, canonical) in expected.items():
        projection = project_odd_prime_block(p + 2, length)
        assert projection.natural_lanes == natural
        assert len(projection.canonical_lanes) == canonical
    projection = project_odd_prime_block(p + 2, 64)
    assert projection.summary.first == 13
    assert p + 2 + 2 * projection.summary.first == 10_000_019


def test_prime_projection_discovers_irreducible_factor_basis() -> None:
    projection = project_odd_prime_block(9_999_993, 4096)
    factors = [lane.factor for lane in projection.canonical_lanes]
    assert 3 in factors and 5 in factors and 7 in factors
    assert 9 not in factors and 15 not in factors and 21 not in factors
    # No retained lane is dominated by an earlier retained period.
    for i, lane in enumerate(projection.canonical_lanes):
        for prior in projection.canonical_lanes[:i]:
            assert not (
                lane.factor % prior.factor == 0
                and lane.phase % prior.factor == prior.phase
            )


def test_canonical_u64_prime_predicate_handles_strong_pseudoprime_regression() -> None:
    from number_compiler.sequences.prime.set import is_prime_u64

    assert is_prime_u64(2) and is_prime_u64(4_294_967_291)
    assert not is_prime_u64(1)
    assert not is_prime_u64(341_550_071_728_321)
    assert not is_prime_u64((1 << 64) - 1)
