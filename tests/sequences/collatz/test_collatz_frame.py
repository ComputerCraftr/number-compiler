from typing import cast

import pytest

from number_compiler.arithmetic.automata.program_word import (
    from_runs,
    from_values,
    iter_runs,
)
from number_compiler.arithmetic.fields.adic_morphism import PadicRadialQuotient
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.collatz.frame import (
    CollatzFixedPointPadicFrame,
    CollatzFutureValuationRoot,
    CollatzTwoValuationFrameSummary,
    collatz_affine_suffix_valuations_value,
    collatz_affine_suffix_valuations_word,
    collatz_radix4_frame_factorization,
    collatz_two_valuation_frame_value,
    collatz_two_valuation_frame_word,
    fixed_frame_future_collision,
    strip_radix4_fixed_point_word,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.collatz.root_germs import (
    PadicAngularBoundaryGerm,
    RationalPadicRootGerm,
)


@pytest.mark.parametrize("precision", (True, 1.0, 0, 41))
def test_fixed_point_frame_rejects_aliased_or_unbounded_precision(
    precision: object,
) -> None:
    error = TypeError if type(precision) is not int else ValueError
    with pytest.raises(error):
        CollatzFixedPointPadicFrame(cast(int, precision), 0, 0)


@pytest.mark.parametrize("value", (True, 3.0))
def test_fixed_point_frame_rejects_aliased_source_values(value: object) -> None:
    with pytest.raises(TypeError):
        CollatzFixedPointPadicFrame.from_odd_value(
            cast("int", value),
            precision=8,
        )


@pytest.mark.parametrize(
    ("power", "constant", "error"),
    (
        (True, 1, TypeError),
        (2.0, 1, TypeError),
        (41, 1, ValueError),
        (2, True, TypeError),
        (2, 1 << 65, ValueError),
    ),
)
def test_rational_root_rejects_numeric_aliases_and_unbounded_limbs(
    power: object,
    constant: object,
    error: type[Exception],
) -> None:
    with pytest.raises(error):
        RationalPadicRootGerm(cast(int, power), cast(int, constant))


@pytest.mark.parametrize("bits", (True, 1.0, 0, 65))
def test_rational_root_residue_rejects_aliased_or_unbounded_precision(
    bits: object,
) -> None:
    root = RationalPadicRootGerm(2, 4)
    error = TypeError if type(bits) is not int else ValueError
    with pytest.raises(error):
        root.root_residue(cast(int, bits))


@pytest.mark.parametrize("alias", (True, 1.0))
def test_collatz_frame_helpers_reject_numeric_aliases(alias: object) -> None:
    with pytest.raises(TypeError):
        collatz_radix4_frame_factorization(cast(int, alias))
    with pytest.raises(TypeError):
        CollatzFutureValuationRoot(cast(int, alias))
    with pytest.raises(TypeError):
        CollatzFutureValuationRoot(0).root_residue(cast(int, alias))
    with pytest.raises(TypeError):
        collatz_two_valuation_frame_value(cast(int, alias))
    with pytest.raises(TypeError):
        collatz_affine_suffix_valuations_value(
            cast("int", alias),
            1,
        )
    with pytest.raises(TypeError):
        collatz_affine_suffix_valuations_value(
            3,
            cast("int", alias),
        )


def _v2(n: int) -> int:
    return (n & -n).bit_length() - 1


@pytest.mark.validation
def test_radix4_fixed_point_frames_are_exact_and_do_not_affect_successor() -> None:
    """Exhaust the 16-bit odd source domain for the fixed-frame theorem."""
    for n in range(1, 65536, 2):
        frame = collatz_radix4_frame_factorization(n)
        direct = accelerated_odd_collatz(n)
        assert frame.valuation == direct.valuation
        assert frame.successor == direct.target
        # Exact fixed-point decomposition n=S_q+4^q*m.
        sentinel = (4**frame.frame_depth - 1) // 3
        assert n == sentinel + 4**frame.frame_depth * frame.tail
        assert frame.local_shift in (0, 1)


def test_radix4_frame_prefix_is_pure_gauge_for_accelerated_target() -> None:
    for tail in range(128):
        if tail and (tail & 3) == 1:
            continue
        local = _v2(3 * tail + 1)
        assert local in (0, 1)
        target = (3 * tail + 1) >> local
        for q in range(8):
            n = (4**q - 1) // 3 + 4**q * tail
            if n <= 0 or not (n & 1):
                continue
            frame = collatz_radix4_frame_factorization(n)
            assert frame.tail == tail
            assert frame.local_shift == local
            assert frame.successor == target


def test_future_valuation_roots_have_exact_period_three_radix4_expansions() -> None:
    for t, period in ((0, (0, 3, 1)), (1, (3, 0, 2))):
        root = CollatzFutureValuationRoot(t)
        assert root.radix4_period == period
        packed = sum(d * 4**i for i, d in enumerate(period))
        # Repeating period value is packed/(1-4^3) = -(3+2^t)/9.
        assert 9 * packed == -(3 + (1 << t)) * (1 - 4**3)
        for digits_count in range(1, 12):
            bits = 2 * digits_count
            residue = sum(period[i % 3] * 4**i for i in range(digits_count))
            assert residue == root.root_residue(bits)


def test_rational_root_germ_matches_direct_valuation_across_growing_denominators() -> (
    None
):
    for h in range(1, 8):
        p = 3**h
        for constant in (1, max(1, p // 3), p // 2, p - 1):
            root = RationalPadicRootGerm(h, constant)
            for value in range(300):
                numerator = p * value + constant
                assert root.valuation_from_integer(value) == _v2(numerator)
                assert root.valuation_from_digits(digits_lsd(value, 4)) == _v2(
                    numerator
                )


def test_rational_root_germ_skips_million_digit_constant_run_without_period_table() -> (
    None
):
    # c=3^(h-1) makes -c/3^h exactly -1/3 = ...111_4 for every h.
    h = 20
    root = RationalPadicRootGerm(h, 3 ** (h - 1))
    word = from_runs(((1, 1_000_000), (3, 1)))
    mismatch, suffix = root.first_mismatch_word(word)
    assert mismatch.matched_quarters == 1_000_000
    assert mismatch.source_digit == 3
    assert mismatch.root_digit == 1
    assert mismatch.valuation_bits == 2_000_001
    assert suffix.length == 0


def test_padic_angular_boundary_rewrites_normalized_discrepancy_as_affine_suffix() -> (
    None
):
    root = RationalPadicRootGerm(2, 4)  # -4/9
    for value in range(2000):
        word = from_values(digits_lsd(value, 4))
        mismatch, suffix = root.first_mismatch_word(word)
        angular = PadicAngularBoundaryGerm.from_mismatch(root, mismatch)
        suffix_value = 0
        pos = 0
        for digit, count in iter_runs(suffix):
            for _ in range(count):
                suffix_value += digit * 4**pos
                pos += 1
        direct = (9 * value + 4) >> mismatch.valuation_bits
        assert direct & 1
        assert angular.multiplier * suffix_value + angular.offset == direct


@pytest.mark.validation
def test_periodic_future_root_summary_predicts_next_collatz_valuation_without_successor_scan() -> (
    None
):
    """Check the future-root law over the complete 50,000-state fixture."""
    for n in range(1, 50000, 2):
        frame = collatz_radix4_frame_factorization(n)
        root = CollatzFutureValuationRoot(frame.local_shift)
        tail_digits = digits_lsd(frame.tail, 4)
        via_digits = root.next_valuation_from_digits(tail_digits)
        via_integer = root.next_valuation_from_tail(frame.tail)
        direct = _v2(3 * frame.successor + 1)
        assert via_digits == via_integer == direct


def test_future_root_uses_symbolic_rational_germ_not_periodic_runtime_summary() -> None:
    word = from_runs(((0, 1), (3, 1), (1, 1), (2, 1_000_000)))
    root = CollatzFutureValuationRoot(0)
    # First three digits agree with -4/9; the next source digit 2 differs from
    # the root digit 0.  The million-digit tail is never expanded.
    mismatch, _suffix = root.rational_root.first_mismatch_word(word)
    assert mismatch.matched_quarters == 3
    assert mismatch.valuation_bits == 7
    assert root.next_valuation_from_word(word) == 7


def test_strip_fixed_point_word_removes_one_canonical_sentinel_run() -> None:
    word = from_runs(((1, 1_000_000), (3, 2), (0, 5)))
    q, tail = strip_radix4_fixed_point_word(word)
    assert q == 1_000_000
    assert tail.length == 7
    assert tail.run_count == 2
    q0, same = strip_radix4_fixed_point_word(from_runs(((3, 2), (0, 5))))
    assert q0 == 0 and same.length == 7


def test_three_adic_fixed_frame_projection_removes_q_and_reconstructs_successor_residue() -> (
    None
):
    for precision in (2, 4, 8):
        modulus = 3**precision
        for n in range(1, 5000, 2):
            factor = collatz_radix4_frame_factorization(n)
            direct = CollatzFixedPointPadicFrame.from_odd_value(n, precision=precision)
            assert direct.local_shift == factor.local_shift
            assert direct.tail_residue == factor.tail % modulus
            assert direct.successor_residue == factor.successor % modulus
            radial = PadicRadialQuotient(3, precision, precision, None, n % modulus, 0)
            via_radial = CollatzFixedPointPadicFrame.from_radial_quotient(
                radial,
                factor.valuation,
            )
            assert via_radial == direct
            next_k = _v2(3 * factor.successor + 1)
            recentered = direct.recenter(next_k)
            expected = CollatzFixedPointPadicFrame.from_odd_value(
                factor.successor,
                precision=precision,
            )
            assert recentered == expected


def test_every_finite_three_adic_fixed_frame_has_a_symbolic_future_valuation_collision() -> (
    None
):
    for precision in (1, 2, 4, 8, 12, 16):
        m1, m2, k1, k2 = fixed_frame_future_collision(precision)
        modulus = 3**precision
        assert m1 % modulus == m2 % modulus
        assert m1 % 4 == m2 % 4 == 3
        assert (k1, k2) == (4, 1)
        f1 = CollatzFixedPointPadicFrame.from_odd_value(m1, precision=precision)
        f2 = CollatzFixedPointPadicFrame.from_odd_value(m2, precision=precision)
        assert f1.canonical_key == f2.canonical_key
        assert _v2(3 * accelerated_odd_collatz(m1).target + 1) == 4
        assert _v2(3 * accelerated_odd_collatz(m2).target + 1) == 1


@pytest.mark.validation
def test_affine_suffix_germ_projects_many_collatz_steps_without_successor_digit_words() -> (
    None
):
    """Compare ten-event germs over the complete 10,000-state fixture."""
    for n in range(1, 10000, 2):
        valuations, germ = collatz_affine_suffix_valuations_value(n, 10)
        value = n
        expected = []
        for _ in range(10):
            step = accelerated_odd_collatz(value)
            expected.append(step.valuation)
            value = step.target
        assert valuations == tuple(expected)
        if germ.multiplier == 0:
            assert germ.offset == value


def test_affine_suffix_germ_generalizes_fixed_frame_on_million_digit_source() -> None:
    q = 1_000_000
    word = from_runs(((1, q), (3, 1)))
    valuations, germ = collatz_affine_suffix_valuations_word(word, 2)
    assert valuations == (2 * q + 1, 4)
    # Both root mismatches consume the source symbolically; no million-digit
    # successor word survives in the execution state.
    assert germ.suffix.length == 0
    assert germ.multiplier == 0
    assert germ.offset == 1


def test_canonical_compiler_exposes_only_the_two_fixed_future_root_sectors_in_diagnostics() -> (
    None
):
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.api.sequence_types import CollatzSequenceSpec

    compiler = CanonicalSequenceCompiler()
    diag = compiler.compile_diagnostic(CollatzSequenceSpec(27, max_steps=64))
    assert tuple(root.local_shift for root in diag.future_valuation_roots) == (0, 1)
    assert tuple(root.radix4_period for root in diag.future_valuation_roots) == (
        (0, 3, 1),
        (3, 0, 2),
    )
    prod = compiler.compile(CollatzSequenceSpec(27, max_steps=8), diagnostics=False)
    assert not prod.future_valuation_roots


@pytest.mark.validation
def test_two_valuation_frame_projects_two_accelerated_branch_depths_without_successor_word() -> (
    None
):
    """Exhaust the 16-bit odd domain for the two-event frame summary."""
    for n in range(1, 65536, 2):
        summary = collatz_two_valuation_frame_value(n)
        first = accelerated_odd_collatz(n)
        second_k = _v2(3 * first.target + 1)
        assert isinstance(summary, CollatzTwoValuationFrameSummary)
        assert summary.current_valuation == first.valuation
        assert summary.next_valuation == second_k
        assert (
            summary.current_valuation == 2 * summary.frame_depth + summary.local_shift
        )


def test_two_valuation_frame_word_handles_large_fixed_point_runs_symbolically() -> None:
    # n has one million low radix-4 digits equal to the -1/3 sentinel followed
    # by tail digit 3.  The current valuation is therefore 2q+1.  The future
    # root for local sector 1 starts with 3, then sees implicit/explicit zero;
    # the result is finite and obtained without expanding the run.
    q = 1_000_000
    word = from_runs(((1, q), (3, 1)))
    summary = collatz_two_valuation_frame_word(word)
    assert summary.frame_depth == q
    assert summary.local_shift == 1
    assert summary.current_valuation == 2 * q + 1
    assert summary.next_valuation == 4
    assert summary.canonical_future_key == (
        "collatz-two-valuation-fixed-frame",
        1,
        4,
    )


def test_affine_suffix_germ_streams_directly_into_lazy_event_morphisms() -> None:
    from devtools.verification.collatz_frame_projection import (
        collatz_affine_suffix_event_power_value,
    )
    from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
    from number_compiler.sequences.collatz.power import CollatzEventArena

    source = 27
    value = source
    for _ in range(32):
        value = accelerated_odd_collatz(value).target
    arena = CollatzEventArena()
    projection = collatz_affine_suffix_event_power_value(source, 32, arena=arena)
    assert projection.events == 32
    assert arena.apply_exact(projection.root, source) == value
    assert projection.target.logical_steps == 32
    metrics = arena.metrics(projection.root)
    assert metrics["events"] == 32
    assert metrics["cocycle_materializations"] == 0


def test_million_digit_frame_to_two_event_dag_does_not_expand_valuation_or_affine_offset() -> (
    None
):
    from devtools.verification.collatz_frame_projection import (
        collatz_affine_suffix_event_power_word,
    )
    from number_compiler.arithmetic.automata.program_word import from_runs
    from number_compiler.sequences.collatz.power import CollatzEventArena

    q = 1_000_000
    word = from_runs(((1, q), (3, 1)))
    arena = CollatzEventArena()
    projection = collatz_affine_suffix_event_power_word(word, 2, arena=arena)
    metrics = arena.metrics(projection.root)
    assert projection.events == 2
    assert projection.root.effect.shift == 2 * q + 5  # valuations 2q+1 and 4
    assert metrics["operator_nodes"] <= 3
    assert metrics["operator_description_bits"] < 128
    assert metrics["cocycle_materializations"] == 0


def test_germ_transition_cache_normalizes_matching_frame_before_boundary_generation() -> (
    None
):
    from devtools.verification.collatz_frame_projection import (
        collatz_affine_suffix_event_power_word,
    )
    from number_compiler.arithmetic.automata.program_word import from_runs
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
    from number_compiler.sequences.collatz.power import CollatzEventArena

    cache = CollatzGermTransitionCache()
    arena = CollatzEventArena()
    small = from_runs(((1, 100), (3, 1)))
    huge = from_runs(((1, 1_000_000), (3, 1)))

    first = collatz_affine_suffix_event_power_word(
        small,
        2,
        arena=arena,
        transition_cache=cache,
    )
    after_first = cache.metrics()
    second = collatz_affine_suffix_event_power_word(
        huge,
        2,
        arena=arena,
        transition_cache=cache,
    )
    after_second = cache.metrics()

    assert first.root.effect.shift == 205
    assert second.root.effect.shift == 2_000_005
    assert first.target.multiplier == second.target.multiplier == 0
    assert first.target.offset == second.target.offset == 1
    # The second source differs in a million-scale gauge depth, but both of its
    # transition lookups hit canonical algebraic state before event creation.
    assert after_first["canonical_misses"] == 2
    assert after_second["canonical_misses"] == 2
    assert (after_second["canonical_hits"] + after_second["event_power_jump_hits"]) >= 2
    assert after_second["raw_states"] > after_second["canonical_states"]
    assert after_second["normalized_quarters"] >= 1_000_000


def test_valuation_projection_uses_same_upstream_transition_cache() -> None:
    from number_compiler.arithmetic.automata.program_word import from_runs
    from number_compiler.sequences.collatz.frame import (
        collatz_affine_suffix_valuations_word,
    )
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache

    cache = CollatzGermTransitionCache()
    a = from_runs(((1, 7), (3, 1)))
    b = from_runs(((1, 700_000), (3, 1)))
    va, ta = collatz_affine_suffix_valuations_word(a, 2, transition_cache=cache)
    misses = cache.misses
    vb, tb = collatz_affine_suffix_valuations_word(b, 2, transition_cache=cache)
    assert va == (15, 4)
    assert vb == (1_400_001, 4)
    assert ta.multiplier == tb.multiplier == 0
    assert ta.offset == tb.offset == 1
    assert cache.misses == misses
    assert cache.hits >= 2


def test_shared_binary_lift_powers_normalized_collatz_germs_exactly() -> None:
    from number_compiler.arithmetic.automata.program_word import from_values
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.sequences.collatz.frame import CollatzAffineSuffixGerm
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache

    seed = 27
    germ = CollatzAffineSuffixGerm.from_word(from_values(digits_lsd(seed, 4)))
    direct_cache = CollatzGermTransitionCache()
    direct = germ
    valuation_sum = 0
    for _ in range(32):
        advance = direct_cache.advance(direct)
        valuation_sum += advance.valuation
        direct = advance.target

    powered_cache = CollatzGermTransitionCache()
    powered = powered_cache.advance_many(germ, 32)
    assert powered.target.algebraic_key == direct.algebraic_key
    assert powered.target.logical_steps == 32
    assert powered.valuation_sum == valuation_sum

    fixed = CollatzAffineSuffixGerm(0, 1, from_values((1,)), 7)
    huge = powered_cache.advance_many(fixed, 1 << 20)
    assert huge.target.multiplier == 0 and huge.target.offset == 1
    assert huge.target.logical_steps == 7 + (1 << 20)
    assert huge.valuation_sum == 2 * (1 << 20)
    assert huge.lift_metrics.step_evaluations < 64


def test_event_projection_uses_shared_binary_lift_weight_without_valuation_replay() -> (
    None
):
    from devtools.verification.collatz_frame_projection import (
        collatz_affine_suffix_event_power_word,
    )
    from number_compiler.arithmetic.automata.program_word import from_values
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
    from number_compiler.sequences.collatz.power import CollatzEventArena

    arena = CollatzEventArena()
    cache = CollatzGermTransitionCache()
    events = 1 << 20
    projected = collatz_affine_suffix_event_power_word(
        from_values((1,)),
        events,
        arena=arena,
        transition_cache=cache,
    )
    metrics = arena.metrics(projected.root)
    assert projected.target.multiplier == 0
    assert projected.target.offset == 1
    assert projected.target.logical_steps == events
    assert metrics["events"] == events
    assert metrics["shift"] == 2 * events
    assert metrics["operator_nodes"] <= events.bit_length()
    assert metrics["cocycle_materializations"] == 0
    assert cache.metrics()["event_power_jump_hits"] > 0
