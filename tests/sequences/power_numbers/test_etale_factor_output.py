import pytest

from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.sequences.power_numbers.etale_factor import (
    fermat_additive_etale_frobenius_probe,
    mersenne_additive_etale_frobenius_probe,
)


@pytest.mark.parametrize("p,factor", [(11, 23), (23, 47), (83, 167), (131, 263)])
def test_exact_coefficient_factor_leaks(p: int, factor: int) -> None:
    probe = mersenne_additive_etale_frobenius_probe(p)
    assert probe.nontrivial_gcds == (factor,)
    assert probe.candidate_modulus % factor == 0
    assert probe.composite_witness and not probe.prime_certificate
    assert probe.factor_enumeration == 0
    assert probe.ring_multiplications > p
    compiler = CanonicalSequenceCompiler()
    # The optional factor proves composite without a primality recurrence.
    assert not compiler.resolve_special_theorem("mersenne", p).decided
    result = compiler.resolve_special_theorem("mersenne", p, collect_etale_factor=True)
    assert result.factor_witness == factor
    assert result.etale_ring_multiplications == probe.ring_multiplications
    assert (
        compiler.resolve_special_theorem("mersenne", p, collect_etale_factor=True)
        is result
    )


def test_unrequested_factor_probe_never_runs_for_unknown(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.etale_factor as owner

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("unresolved compact query ran a ring power")

    monkeypatch.setattr(owner, "mersenne_additive_etale_frobenius_probe", forbidden)
    result = CanonicalSequenceCompiler().resolve_special_theorem(
        "mersenne", 13, allow_classical_ceiling=False
    )
    assert not result.decided
    assert result.factor_witness is None and result.etale_ring_multiplications == 0


def test_prime_controls_and_fermat_composites() -> None:
    for p in (5, 7, 13, 31):
        probe = mersenne_additive_etale_frobenius_probe(p)
        assert not probe.composite_witness and not probe.prime_certificate
        assert not probe.nontrivial_gcds
    for n in (3, 4, 5, 6):
        fermat_probe = fermat_additive_etale_frobenius_probe(n)
        assert fermat_probe.composite_witness == (n >= 5)
        assert not fermat_probe.prime_certificate


def test_composite_exponent_factor_survives_constraint_only_result() -> None:
    compiler = CanonicalSequenceCompiler()
    assert compiler.resolve_special_theorem("mersenne", 12).decided
    result = compiler.resolve_special_theorem("mersenne", 12, collect_etale_factor=True)
    assert result.composite_exponent_factor is not None
    assert result.composite_exponent_factor.exponent == 2
    assert result.etale_ring_multiplications == 0


def test_unknown_factor_cache_does_not_mask_a_later_proof() -> None:
    compiler = CanonicalSequenceCompiler()
    result = compiler.resolve_special_theorem(
        "mersenne",
        11,
        collect_etale_factor=True,
        allow_classical_ceiling=False,
        max_factor_products=0,
    )
    assert not result.decided
    assert compiler.resolve_special_theorem(
        "mersenne", 11, collect_etale_factor=True
    ).decided
    resolved = compiler.resolve_special_theorem(
        "mersenne", 11, collect_etale_factor=True, allow_classical_ceiling=False
    )
    assert resolved.decided and resolved.factor_witness == 23


def test_every_nontrivial_small_etale_root_prints_a_factor() -> None:
    from number_compiler.sequences.power_numbers.etale_factor import (
        factor_from_etale_root,
    )

    for modulus in range(3, 100):
        for defect in range(modulus):
            if defect * (defect + 2) % modulus:
                continue
            factor = factor_from_etale_root(modulus, defect)
            if defect not in (0, modulus - 2):
                assert factor is not None
            if factor is not None:
                assert 1 < factor < modulus
                assert modulus % factor == 0
    with pytest.raises(ValueError, match="not a quadratic"):
        factor_from_etale_root(2047, 1)
    with pytest.raises(ValueError, match="canonical"):
        factor_from_etale_root(2047, 2047)
    with pytest.raises(TypeError, match="exact integers"):
        factor_from_etale_root(2047, True)


def test_known_factor_prints_with_zero_new_product_budget(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import etale_factor

    compiler = CanonicalSequenceCompiler()
    result = compiler.resolve_special_theorem("mersenne", 11, collect_etale_factor=True)
    assert result.factor_witness == 23

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("already available factor triggered another ring power")

    monkeypatch.setattr(etale_factor, "_quadratic_power_pair", forbidden)
    reused = compiler.resolve_special_theorem(
        "mersenne", 11, collect_etale_factor=True, max_factor_products=0
    )
    assert reused is result
    assert reused.primality is not None and reused.primality.status == "composite"
    assert reused.primality.specialization_raw_squarings == 0


def test_no_split_is_cached_without_becoming_a_prime_certificate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import etale_factor

    compiler = CanonicalSequenceCompiler()
    result = compiler.resolve_special_theorem("mersenne", 13, collect_etale_factor=True)
    assert not result.decided and result.factor_query_status == "no-split"

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("cached no-split result replayed the probe")

    monkeypatch.setattr(etale_factor, "_quadratic_power_pair", forbidden)
    assert (
        compiler.resolve_special_theorem("mersenne", 13, collect_etale_factor=True)
        is result
    )


@pytest.mark.parametrize("family,parameter", [("fermat", 5), ("mersenne", 11)])
def test_factor_enriches_cached_primality_without_terminal_reconstruction(
    family: str, parameter: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.power_numbers import theorem_query

    compiler = CanonicalSequenceCompiler()
    base = compiler.resolve_special_theorem(family, parameter)
    assert not base.decided
    expected = theorem_query.resolve_special_theorem(
        family, parameter, collect_etale_factor=True
    )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("factor demand repeated the cached terminal constructor")

    monkeypatch.setattr(theorem_query, "resolve_special_theorem", forbidden)
    refused = compiler.resolve_special_theorem(
        family, parameter, collect_etale_factor=True, max_factor_products=0
    )
    assert not refused.decided
    assert refused.factor_query_status == "product-budget-exceeded"
    result = compiler.resolve_special_theorem(
        family, parameter, collect_etale_factor=True
    )
    assert result == expected
    assert result.etale_ring_multiplications > 0
    if result.factor_witness is not None:
        candidate = (
            (1 << (1 << parameter)) + 1 if family == "fermat" else (1 << parameter) - 1
        )
        assert 1 < result.factor_witness < candidate
        assert candidate % result.factor_witness == 0
    else:
        assert result.factor_query_status == "no-split" and not result.decided
    assert not base.decided  # Witness enrichment does not mutate the cached result.
    with pytest.raises(ValueError, match="candidate exceeds"):
        compiler.resolve_special_theorem(
            family, parameter, collect_etale_factor=True, max_candidate_bits=1
        )


def test_factor_reuse_respects_terminal_policy(monkeypatch: pytest.MonkeyPatch) -> None:
    from number_compiler.sequences.power_numbers import theorem_query

    compiler = CanonicalSequenceCompiler()
    compiler.resolve_special_theorem("mersenne", 13, use_terminal_certificate=False)
    called = []
    original = theorem_query.resolve_special_theorem

    def observed(*args: object, **kwargs: object) -> None:
        called.append(True)
        raise RuntimeError("different policy requires its own constructor")

    monkeypatch.setattr(theorem_query, "resolve_special_theorem", observed)
    with pytest.raises(RuntimeError, match="different policy"):
        compiler.resolve_special_theorem("mersenne", 13, collect_etale_factor=True)
    assert called == [True]
    monkeypatch.setattr(theorem_query, "resolve_special_theorem", original)
