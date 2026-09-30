from __future__ import annotations

import ast
import itertools
from collections.abc import Callable
from pathlib import Path
from typing import Never, cast

import pytest

import number_compiler
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzSequenceSpec,
    FermatSequenceSpec,
    MersenneSequenceSpec,
    PrimeBlockSequenceSpec,
    ReverseAddSequenceSpec,
)
from number_compiler.arithmetic.contracts.block_effect import _effect_key, _state_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
from tests.support.special_theorem_assertions import assert_unknown_resolution


@pytest.mark.parametrize(
    "spec",
    (
        lambda: ReverseAddSequenceSpec(cast(int, 1.0), 10, 1),
        lambda: ReverseAddSequenceSpec(1, True, 1),
        lambda: ReverseAddSequenceSpec(1, 10, cast(int, 1.0)),
        lambda: CollatzSequenceSpec(True, 2, 1),
        lambda: CollatzSequenceSpec(1, cast(int, 2.0), 1),
        lambda: CollatzSequenceSpec(1, 2, False),
        lambda: PrimeBlockSequenceSpec(cast(int, 3.0), 1),
        lambda: PrimeBlockSequenceSpec(3, True),
        lambda: PrimeBlockSequenceSpec(3, 1, random_access=cast(bool, 1)),
        lambda: FermatSequenceSpec((0, True)),
        lambda: FermatSequenceSpec((0,), test_through=cast(int, 1.0)),
        lambda: MersenneSequenceSpec((2, cast(int, 3.0))),
        lambda: MersenneSequenceSpec((2,), test_through=True),
    ),
)
def test_sequence_specs_reject_integer_aliases(spec: Callable[[], object]) -> None:
    with pytest.raises(TypeError):
        spec()


def _reverse_int(value: int, base: int) -> int:
    digits = digits_lsd(value, base)
    out = 0
    for digit in digits:
        out = out * base + digit
    return out


def _reverse_add_values(seed: int, base: int, steps: int) -> tuple[int, ...]:
    out = [int(seed)]
    for _ in range(steps):
        out.append(out[-1] + _reverse_int(out[-1], base))
    return tuple(out)


def test_sequence_compiler_uses_semantic_spec_keys_and_reuses_exact_result() -> None:
    compiler = CanonicalSequenceCompiler()
    spec = ReverseAddSequenceSpec(196, 10, 4)
    first = compiler.compile(spec)
    second = compiler.compile(ReverseAddSequenceSpec(196, 10, 4))
    assert first is second
    assert compiler.cache_size == 1
    assert spec.canonical_key == ("reverse_add", 196, 10, 4)
    with pytest.raises(ValueError):
        FermatSequenceSpec((2, 1))
    with pytest.raises(ValueError):
        MersenneSequenceSpec((5, 3))


def test_special_source_cache_identity_ignores_legacy_theorem_policy() -> None:
    compiler = CanonicalSequenceCompiler()
    f0 = compiler.compile(FermatSequenceSpec((4,), test_through=0))
    f99 = compiler.compile(FermatSequenceSpec((4,), test_through=99))
    assert f0 is f99 and f0.spec.test_through == 0
    assert (
        FermatSequenceSpec((4,), test_through=0).canonical_key
        == FermatSequenceSpec((4,), test_through=99).canonical_key
    )

    m0 = compiler.compile(MersenneSequenceSpec((13,), test_through=0))
    m99 = compiler.compile(MersenneSequenceSpec((13,), test_through=99))
    assert m0 is m99 and m0.spec.test_through == 0
    assert (
        MersenneSequenceSpec((13,), test_through=0).canonical_key
        == MersenneSequenceSpec((13,), test_through=99).canonical_key
    )
    assert compiler.cache_size == 2 and compiler.theorem_cache_size == 0


def test_block_cache_state_and_operator_keys_do_not_alias_numeric_namespaces() -> None:
    class Context:
        node_id = 1

    assert _state_key(1) != _state_key(Context())
    # Construction order differs, semantic operator identity does not.
    a = BaseBlockEffect(10)
    b = BaseBlockEffect(10)
    assert a.node_id != b.node_id
    assert _effect_key(a) == _effect_key(b) == ("base_block", 10)


def test_production_compiler_import_graph_excludes_tests_bench_release_and_analysis_probes() -> (
    None
):
    path = Path(number_compiler.__file__).with_name("api") / "sequence_compiler.py"
    tree = ast.parse(path.read_text())
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module.lstrip("."))
        elif isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
    forbidden = {"tests", "bench", "research", "release", "prime_encoding_analysis"}
    assert not any(name.split(".")[0] in forbidden for name in imported)
    assert not hasattr(number_compiler, "trial_factor")


@pytest.mark.parametrize("seed", [1, 195, 196, 197])
@pytest.mark.parametrize("base", [2, 3, 4, 5, 7, 8, 10, 12, 16])
def test_reverse_add_seed_base_matrix_compiles_exact_radix_values(
    seed: int, base: int
) -> None:
    steps = 4
    got = CanonicalSequenceCompiler().compile_diagnostic(
        ReverseAddSequenceSpec(seed, base, steps)
    )
    want = _reverse_add_values(seed, base, steps)
    assert tuple(term.value for term in got.terms) == want
    assert all(term.radix == base for term in got.terms)
    assert tuple(got.growths) == tuple(
        len(digits_lsd(b, base)) - len(digits_lsd(a, base))
        for a, b in itertools.pairwise(want)
    )


def test_fermat_and_mersenne_are_actual_symbolic_radix_compilations_not_materialized_bitmaps() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    fermat = compiler.compile_diagnostic(
        FermatSequenceSpec((0, 1, 5, 12), test_through=5)
    )
    f12 = fermat.terms[-1]
    assert f12.number_bits == 4097
    assert f12.radix_word.width == 4097
    assert f12.radix_word.runs == 3
    assert f12.radix_word.word_description_bits < 128
    assert f12.radix_word.value is None
    f5 = fermat.terms[2]
    assert f5.primality is None
    assert (f5.projection_method, f5.factor_witness) == ("deferred", None)
    assert f5.radix_word.factored_projection is None and f5.source_guard is None
    assert f5.digit_projection is None
    lazy_f5 = compiler.resolve_special_theorem("fermat", 5)
    assert lazy_f5.projection_method.startswith("terminal-threshold:")
    assert lazy_f5.factor_witness is None
    primality = assert_unknown_resolution(lazy_f5)
    assert not primality.scalable_construction
    assert lazy_f5.source_guard.failure_bit is None

    mersenne = compiler.compile_diagnostic(
        MersenneSequenceSpec((11, 13, 15, 8191), test_through=31)
    )
    m8191 = mersenne.terms[-1]
    assert m8191.number_bits == 8191
    assert m8191.radix_word.width == 8191
    assert m8191.radix_word.runs == 1
    assert m8191.radix_word.word_description_bits < 64
    assert m8191.primality is None  # explicitly not hidden behind the compact word
    m15 = next(term for term in mersenne.terms if term.exponent == 15)
    assert m15.composite_exponent_factor is None and m15.projection_method == "deferred"
    lazy_m15 = compiler.resolve_special_theorem("mersenne", 15)
    assert lazy_m15.composite_exponent_factor is not None
    m13 = next(term for term in mersenne.terms if term.exponent == 13)
    assert m13.primality is None and m13.source_guard is None
    assert (
        compiler.resolve_special_theorem("mersenne", 13).source_guard.failure_bit
        is None
    )


def test_prime_and_collatz_use_same_compiler_without_cross_family_state_aliasing() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    prime = compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, 64))
    collatz2 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 2, 32))
    collatz3 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 3, 32))
    assert prime.decision.summary.first == 13
    assert prime.decision.summary.count > 0
    assert collatz2.terms[-1].value == collatz3.terms[-1].value
    assert collatz2.spec.canonical_key != collatz3.spec.canonical_key
    assert compiler.cache_size == 3


def test_collatz_composite_radix_local_compiler_beats_binary_and_ternary_on_seed27() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    c2 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 2, 200))
    c3 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 3, 200))
    c6 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 6, 200))
    c12 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 12, 200))
    assert (
        c2.terms[-1].value
        == c3.terms[-1].value
        == c6.terms[-1].value
        == c12.terms[-1].value
        == 1
    )
    n2 = max(t.formula_nodes for t in c2.terms)
    n3 = max(t.formula_nodes for t in c3.terms)
    n6 = max(t.formula_nodes for t in c6.terms)
    assert n6 < n3 < n2
    assert all(
        b in {"seed", "divide_2_local", "multiply_3_add_1_local"} for b in c6.branches
    )


def test_fermat_mersenne_binary_words_reinterpret_as_cross_radix_cyclotomic_words() -> (
    None
):
    from number_compiler.sequences.power_numbers.numbers import (
        fermat_radix_reinterpretation,
        mersenne_radix_reinterpretation,
    )

    compiler = CanonicalSequenceCompiler()
    f = compiler.compile_diagnostic(
        FermatSequenceSpec((3,), test_through=0, reinterpret_radices=(2, 3, 5, 6))
    )
    ft = f.terms[0]
    assert {t.radix for t in ft.reinterpretations} == {3, 5, 6}
    for t in ft.reinterpretations:
        spec = fermat_radix_reinterpretation(3, t.radix)
        assert spec.cyclotomic_order == 16
        assert spec.materialize() == pow(t.radix, 8) + 1
        assert t.width == 9 and t.runs == 3
    m = compiler.compile_diagnostic(
        MersenneSequenceSpec((5,), test_through=0, reinterpret_radices=(2, 3, 5, 6))
    )
    mt = m.terms[0]
    assert {t.radix for t in mt.reinterpretations} == {3, 5, 6}
    for t in mt.reinterpretations:
        spec = mersenne_radix_reinterpretation(5, t.radix)
        assert spec.cyclotomic_order == 5
        assert spec.materialize() == sum(t.radix**i for i in range(5))
        assert t.width == 5 and t.runs == 1


def test_prime_compiler_exposes_work_optimized_residual_divisor_quotient() -> None:
    prime = CanonicalSequenceCompiler().compile_diagnostic(
        PrimeBlockSequenceSpec(9_999_993, 4096)
    )
    assert (prime.decision.summary_count, prime.decision.summary_first) == (503, 13)
    assert prime.decision.base_period == (4, 8)
    assert prime.decision.domain_size == 4096
    assert prime.decision.lane_transform_checks > 0
    assert prime.decision.canonical_lanes == 446
    assert prime.decision.primary_jet is None
    assert prime.decision.wheel_cyclotomic is not None
    assert prime.automaton is not None
    assert prime.automaton.cyclotomic_group_count == len(
        prime.decision.wheel_cyclotomic.groups
    )


def test_special_theorem_query_leaves_unproved_special_cases_unknown() -> None:
    compiler = CanonicalSequenceCompiler()
    fermat = compiler.compile_diagnostic(
        FermatSequenceSpec((5,), test_through=5)
    ).terms[0]
    assert (fermat.projection_method, fermat.factor_witness) == ("deferred", None)
    assert fermat.primality is None and fermat.digit_projection is None
    assert compiler.theorem_cache_size == 0

    f5 = compiler.resolve_special_theorem("fermat", 5)
    assert f5.projection_method.startswith("terminal-threshold:")
    assert f5.factor_witness is None
    assert_unknown_resolution(f5)
    assert f5.source_guard.failure_bit is None

    raw = compiler.compile_diagnostic(
        MersenneSequenceSpec((11, 23, 31), test_through=31)
    ).terms
    assert all(term.projection_method == "deferred" for term in raw)
    assert all(term.primality is None and term.factor_witness is None for term in raw)
    m11 = compiler.resolve_special_theorem("mersenne", 11)
    m23 = compiler.resolve_special_theorem("mersenne", 23)
    m31 = compiler.resolve_special_theorem("mersenne", 31)
    assert all(
        row.projection_method.startswith("terminal-threshold:")
        for row in (m11, m23, m31)
    )
    assert m11.factor_witness is m23.factor_witness is m31.factor_witness is None
    for row in (m11, m23, m31):
        assert row.primality is not None
        assert row.primality.status == "unknown"
        assert row.primality.specialization_raw_squarings == 0
        assert not row.primality.decided and row.primality.target_depth is None
        assert not row.primality.scalable_construction
        assert row.source_guard.failure_bit is None


def test_unused_factor_limit_is_not_part_of_default_theorem_cache_identity() -> None:
    compiler = CanonicalSequenceCompiler()
    a = compiler.resolve_special_theorem(
        "fermat",
        4,
        factor_limit=17,
        use_terminal_certificate=False,
    )
    b = compiler.resolve_special_theorem(
        "fermat",
        4,
        factor_limit=99991,
        use_terminal_certificate=False,
    )
    assert a is b
    assert compiler.theorem_cache_size == 1
    assert a.projection_method == "deferred"


def test_special_source_compile_never_calls_factor_or_certificate_hot_paths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.certificate as special_certificate
    import number_compiler.sequences.power_numbers.numbers as special_numbers
    from number_compiler.api import sequence_terms
    from number_compiler.arithmetic.fields import congruence_automaton

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("theorem work reached raw special-source compiler")

    monkeypatch.setattr(sequence_terms, "factored_word_projection", forbidden)
    monkeypatch.setattr(special_certificate, "fermat_depth_certificate", forbidden)
    monkeypatch.setattr(special_certificate, "mersenne_depth_certificate", forbidden)
    monkeypatch.setattr(
        special_numbers, "mersenne_composite_exponent_factor", forbidden
    )
    monkeypatch.setattr(
        congruence_automaton.FactoredPrimeAutomaton,
        "build",
        classmethod(lambda cls, *args, **kwargs: forbidden()),
    )

    compiler = CanonicalSequenceCompiler()
    for diagnostics in (False, True):
        compile_one = compiler.compile_diagnostic if diagnostics else compiler.compile
        f2, f4, f5 = compile_one(FermatSequenceSpec((2, 4, 5), test_through=5)).terms
        m13, m15, m31 = compile_one(
            MersenneSequenceSpec((13, 15, 31), test_through=31)
        ).terms
        for term in (*(f2, f4, f5), *(m13, m15, m31)):
            assert term.primality is None
            assert term.projection_method == "deferred"
            assert term.factor_witness is None
            assert term.source_guard is None
            assert term.radix_word.factored_projection is None
        assert m15.composite_exponent_factor is None
    assert compiler.theorem_cache_size == 0


def test_lazy_factored_residue_projection_powers_runs_without_expansion() -> None:
    compiler = CanonicalSequenceCompiler()
    fermat = compiler.compile_diagnostic(FermatSequenceSpec((5, 12), test_through=0))
    assert all(term.radix_word.factored_projection is None for term in fermat.terms)
    f5 = compiler.resolve_special_theorem(
        "fermat",
        5,
        use_factor_projection=True,
        use_terminal_certificate=False,
    )
    f12 = compiler.resolve_special_theorem(
        "fermat",
        12,
        use_factor_projection=True,
        use_terminal_certificate=False,
    )
    assert f5.factored_projection is not None
    assert f5.factored_projection.noncoprime_groups >= 1
    assert f12.factored_projection is not None
    assert f12.factored_projection.morphism_compositions <= 2 * (4097).bit_length() + 8

    mersenne = compiler.compile_diagnostic(
        MersenneSequenceSpec((23, 8191), test_through=0)
    )
    assert all(term.radix_word.factored_projection is None for term in mersenne.terms)
    m23 = compiler.resolve_special_theorem(
        "mersenne",
        23,
        use_factor_projection=True,
        use_terminal_certificate=False,
    )
    m8191 = compiler.resolve_special_theorem(
        "mersenne",
        8191,
        use_factor_projection=True,
        use_terminal_certificate=False,
    )
    assert (
        m23.factored_projection is not None
        and m23.factored_projection.noncoprime_groups >= 1
    )
    assert m8191.factored_projection is not None
    assert (
        m8191.factored_projection.morphism_compositions <= 2 * (8191).bit_length() + 8
    )


def test_prime_uses_cyclotomic_wheel_instead_of_default_output_jet_while_other_diagnostics_keep_jets() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    reverse = compiler.compile_diagnostic(ReverseAddSequenceSpec(196, 10, 4))
    collatz = compiler.compile_diagnostic(CollatzSequenceSpec(27, 6, 32))
    prime = compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, 256))
    fermat = compiler.compile_diagnostic(
        FermatSequenceSpec((5,), test_through=0, reinterpret_radices=(2, 6))
    )
    mersenne = compiler.compile_diagnostic(
        MersenneSequenceSpec((31,), test_through=0, reinterpret_radices=(2, 6))
    )

    assert all(term.primary_jet is not None for term in reverse.terms)
    assert all(term.primary_jet is not None for term in collatz.terms)
    assert prime.decision.primary_jet is None
    assert prime.decision.primary_jet_compositions == 0
    assert prime.automaton is not None
    assert (
        prime.automaton.start_primary_jet is None
        and prime.automaton.first_primary_jet is None
    )
    assert prime.automaton is not None
    assert prime.automaton.cyclotomic_group_count > 0
    assert prime.automaton is not None
    assert prime.automaton.cyclotomic_state_bits < prime.automaton.total_group_bits
    assert prime.automaton is not None
    assert prime.automaton.selected_random_access == "cyclotomic"
    assert fermat.terms[0].radix_word.primary_jet is not None
    assert fermat.terms[0].reinterpretations[0].primary_jet is not None
    assert mersenne.terms[0].radix_word.primary_jet is not None
    assert mersenne.terms[0].reinterpretations[0].primary_jet is not None


def test_collatz_radix18_uses_same_local_multiply_divide_compiler_without_new_state() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    c6 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 6, 200))
    c18 = compiler.compile_diagnostic(CollatzSequenceSpec(27, 18, 200))
    assert c6.terms[-1].value == c18.terms[-1].value == 1
    assert all(
        branch in {"seed", "divide_2_local", "multiply_3_add_1_local"}
        for branch in c18.branches
    )
    assert max(t.formula_nodes for t in c6.terms) < max(
        t.formula_nodes for t in c18.terms
    )


def test_collatz_compiler_attaches_one_canonical_raw_field_theorem_quotient() -> None:
    compiled = CanonicalSequenceCompiler().compile_diagnostic(
        CollatzSequenceSpec(27, 6, 200)
    )
    q = compiled.raw_field_quotient
    assert q is not None
    assert (q.radix, q.sentinel_digit) == (4, 1)
    assert (q.odd_steps, q.valuation_sum) == (41, 70)
    assert (q.increase_symbols, q.nonincreasing_symbols) == (24, 17)
    assert q.valuation_digit_checks == 61
    assert q.stripped_digits == 21
    assert q.scalar_carry_peak <= 2
    # The theorem interface stores aggregate quotient metrics, not digit/carry vectors.
    assert not any(
        name in q.__dataclass_fields__ for name in ("digits", "carries", "coefficients")
    )


def test_reduced_growth_and_valuation_itineraries_are_not_retained_as_parallel_state() -> (
    None
):
    from number_compiler.api.sequence_types import (
        CollatzCompilation,
        ReverseAddCompilation,
    )

    reverse = CanonicalSequenceCompiler().compile_diagnostic(
        ReverseAddSequenceSpec(196, 10, 64)
    )
    assert "growths" not in ReverseAddCompilation.__dataclass_fields__
    assert reverse.carry_reset_max_bits == 0
    from devtools.verification import exact_oracle
    from devtools.verification.sequence_diagnostics import with_carry_diagnostics

    with exact_oracle():
        proof = with_carry_diagnostics(reverse)
    assert reverse.growth_state_max_bits < proof.carry_reset_max_bits
    assert reverse.carry_reset_max_bits == 0
    assert len(reverse.growths) == 64

    collatz = CanonicalSequenceCompiler().compile_diagnostic(
        CollatzSequenceSpec(27, 2, 200)
    )
    assert not hasattr(CollatzCompilation, "valuation_symbols")
    assert (
        collatz.valuation_projection is not None
        and collatz.raw_field_quotient is not None
    )
    assert (
        collatz.valuation_projection.odd_steps
        == collatz.raw_field_quotient.odd_steps
        == 41
    )
    assert (
        collatz.valuation_projection.valuation_sum
        == collatz.raw_field_quotient.valuation_sum
        == 70
    )
    assert collatz.valuation_state_classes < collatz.valuation_projection.odd_steps


def test_special_compiler_does_not_retain_a_second_prime_domain_depth_state() -> None:
    from number_compiler.api.sequence_types import (
        FermatCompiledTerm,
        MersenneCompiledTerm,
    )

    assert "cyclotomic_character" not in FermatCompiledTerm.__dataclass_fields__
    assert "cyclotomic_character" not in MersenneCompiledTerm.__dataclass_fields__


def test_default_semantic_compile_omits_diagnostic_parallel_views() -> None:
    compiler = CanonicalSequenceCompiler()

    reverse = compiler.compile(ReverseAddSequenceSpec(196, 10, 16))
    assert all(
        term.value is None and term.primary_jet is None and term.runs == 0
        for term in reverse.terms
    )
    assert reverse.live_rows_average is None
    assert reverse.live_rows_max is None
    assert reverse.live_carry_bits_ratio is None
    assert reverse.carry_reset_max_bits == 0
    assert not reverse.cyclotomic_memory_max
    assert not reverse.cyclotomic_radial_modes

    collatz = compiler.compile(CollatzSequenceSpec(27, 6, 200))
    assert all(
        term.value is None and term.primary_jet is None and term.runs == 0
        for term in collatz.terms
    )
    assert collatz.branches == ()
    assert collatz.raw_field_quotient is None
    assert collatz.valuation_projection is None
    assert collatz.normalized_padic_radial is None

    prime = compiler.compile(PrimeBlockSequenceSpec(9_999_993, 256))
    assert prime.automaton is None
    assert prime.translation_sensitivity is None
    assert prime.wheel_automaton is None
    assert prime.decision.primary_jet is None
    assert prime.decision.primary_jet_compositions == 0
    assert prime.decision.summary_count > 0

    fermat = compiler.compile(
        FermatSequenceSpec((4,), test_through=4, reinterpret_radices=(2,))
    )
    f4 = fermat.terms[0]
    assert f4.radix_word.primary_jet is None
    assert f4.shifted_sensitivity is None and f4.digit_projection is None
    assert f4.primality is None and f4.source_guard is None
    assert f4.projection_method == "deferred" and f4.factor_witness is None
    assert fermat.spec.test_through == 0

    mersenne = compiler.compile(
        MersenneSequenceSpec((13,), test_through=13, reinterpret_radices=(2,))
    )
    m13 = mersenne.terms[0]
    assert m13.radix_word.primary_jet is None
    assert m13.successor_sensitivity is None and m13.digit_projection is None
    assert m13.primality is None and m13.source_guard is None
    assert m13.projection_method == "deferred" and m13.factor_witness is None
    assert m13.composite_exponent_factor is None
    assert mersenne.spec.test_through == 0


def test_semantic_and_diagnostic_compilations_have_distinct_cache_identity() -> None:
    compiler = CanonicalSequenceCompiler()
    spec = ReverseAddSequenceSpec(196, 10, 8)
    semantic = compiler.compile(spec)
    diagnostic = compiler.compile_diagnostic(spec)
    assert semantic is compiler.compile(spec)
    assert diagnostic is compiler.compile_diagnostic(spec)
    assert semantic is not diagnostic
    assert compiler.cache_size == 2
    assert all(term.value is None for term in semantic.terms)
    assert all(term.value is not None for term in diagnostic.terms)


def test_factored_prime_automaton_build_is_canonical_across_family_compilers() -> None:
    from number_compiler.arithmetic.fields.congruence_automaton import (
        FactoredPrimeAutomaton,
    )

    a = FactoredPrimeAutomaton.build(1000)
    b = FactoredPrimeAutomaton.build(1000)
    c = FactoredPrimeAutomaton.build(1000, word_bits=62)
    assert a is b is c
    assert FactoredPrimeAutomaton.build(999) is not a


def test_prime_random_access_is_demand_driven_cyclotomic_wheel_from_same_lane_scan() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    prime = compiler.compile(PrimeBlockSequenceSpec(9_999_993, 128, random_access=True))
    assert prime.automaton is None  # packed comparison is diagnostic only
    assert prime.wheel_automaton is prime.decision.wheel_cyclotomic
    assert prime.wheel_automaton is not None
    first = prime.decision.summary.first
    assert first is not None and prime.wheel_automaton.classify_index(first)[0]


def test_collatz_compilation_exposes_one_self_branching_successor_not_an_itinerary() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    collatz = compiler.compile(CollatzSequenceSpec(27, 2, 64))
    assert collatz.successor_morphism_key == ("collatz-piecewise-morphism", 2)
    assert collatz.branches == ()


def test_default_special_theorem_fails_closed_without_factor_or_recurrence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import congruence_automaton

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "default theorem path exceeded classical recurrence budget"
        )

    monkeypatch.setattr(
        congruence_automaton.FactoredPrimeAutomaton,
        "build",
        classmethod(lambda cls, *args, **kwargs: forbidden()),
    )
    compiler = CanonicalSequenceCompiler()
    f4 = compiler.resolve_special_theorem("fermat", 4)
    m13 = compiler.resolve_special_theorem("mersenne", 13)
    assert f4.primality is not None
    assert f4.primality.status == "unknown"
    assert f4.primality.specialization_raw_squarings == 0
    assert not f4.primality.decided and f4.primality.target_depth is None
    assert f4.source_guard.failure_bit is None
    assert m13.primality is not None
    assert m13.primality.status == "unknown"
    assert m13.primality.specialization_raw_squarings == 0
    assert not m13.primality.decided and m13.primality.target_depth is None
    assert m13.source_guard.failure_bit is None
    assert f4.factored_projection is None and m13.factored_projection is None


def test_fermat_source_extent_stays_algebraic_for_huge_index(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
    from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec

    original = DyadicExtent.materialize

    def forbidden(self: DyadicExtent, *, max_power: int = 1_000_000) -> int:
        if self.power >= 100_000:
            raise AssertionError("huge Fermat extent was materialized")
        return original(self, max_power=max_power)

    monkeypatch.setattr(DyadicExtent, "materialize", forbidden)
    n = 1_000_000
    term = (
        CanonicalSequenceCompiler()
        .compile(
            FermatSequenceSpec((n,), test_through=0, reinterpret_radices=(2, 3, 10))
        )
        .terms[0]
    )
    assert term.number_bits == DyadicExtent(n, 1)
    assert term.cyclotomic_order == DyadicExtent(n + 1)
    assert term.radix_word.width == DyadicExtent(n, 1)
    assert term.radix_word.runs == 3
    assert term.radix_word.word_description_bits < 256
    assert all(view.width == DyadicExtent(n, 1) for view in term.reinterpretations)
    # Rejected materialization must compare the symbolic boundary first rather
    # than constructing the million-bit exponent just to discover it is over budget.
    with pytest.raises(ValueError):
        FermatNumberSpec(n).materialize(max_bits=1024)
    # Canonicalize the only tiny overlapping dyadic forms so hash/equality agree.
    assert DyadicExtent(0, 1) == DyadicExtent(1)
    assert hash(DyadicExtent(0, 1)) == hash(DyadicExtent(1))
