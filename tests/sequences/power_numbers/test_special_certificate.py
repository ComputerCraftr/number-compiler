from typing import Never, cast

import pytest

from number_compiler.sequences.power_numbers.certificate import (
    fermat_depth_certificate,
    mersenne_depth_certificate,
)


def test_demanded_depth_certificates_never_fall_back_from_missing_extractor() -> None:
    for n in (0, 1, 2):
        cert = fermat_depth_certificate(n)
        assert cert.status == "prime"
        assert cert.specialization_raw_squarings == 0
        assert cert.carrier_states_enumerated == 0
    # F3 is now proved directly by the square-root divisor bound.
    f3 = fermat_depth_certificate(3)
    assert f3.status == "prime"
    assert f3.method == "terminal-threshold:fermat-sqrt-divisor-lower-bound"
    for n in (4, 5):
        cert = fermat_depth_certificate(n)
        assert cert.status == "unknown"
        assert cert.method.startswith("terminal-threshold:")
        assert cert.specialization_raw_squarings == 0
        assert cert.carrier_states_enumerated == 0
        assert not cert.scalable_construction

    assert mersenne_depth_certificate(2).status == "prime"
    m3 = mersenne_depth_certificate(3)
    assert m3.status == "prime"
    assert m3.method == "terminal-threshold:explicit-small-mersenne"
    for p in (5, 7):
        cert = mersenne_depth_certificate(p)
        assert cert.status == "prime"
        assert cert.method == "terminal-threshold:mersenne-order-divisor-sqrt-bound"
        assert cert.specialization_raw_squarings == 0
        assert cert.carrier_states_enumerated == 0
    for p in (11, 13, 17):
        cert = mersenne_depth_certificate(p)
        assert cert.status == "unknown"
        assert cert.method.startswith("terminal-threshold:")
        assert cert.specialization_raw_squarings == 0
        assert cert.carrier_states_enumerated == 0
        assert not cert.scalable_construction
    # Composite exponents are still rejected by the cheap symbolic exponent theorem.
    assert mersenne_depth_certificate(9).status == "composite"


def test_prime_depth_metadata_is_attached_only_after_candidate_derived_target_proof() -> (
    None
):
    f2 = fermat_depth_certificate(2)
    f4 = fermat_depth_certificate(4)
    m13 = mersenne_depth_certificate(13)
    assert f2.target_depth == 0 and f2.quotient_classes == 2
    assert f4.target_depth is None and f4.quotient_classes == 0
    assert m13.target_depth is None and m13.quotient_classes == 0


def test_certificate_module_has_no_reference_classifier_dependency() -> None:
    from pathlib import Path

    import number_compiler.sequences.power_numbers.certificate as module

    text = Path(module.__file__).read_text()
    for forbidden in (
        "pepin_test",
        "lucas_lehmer_test",
        "is_prime_u64",
        "bounded_candidate_image_filtration",
        "smallest_factor",
        "oracle_support",
        "tropical_ghost_flux",
    ):
        assert forbidden not in text


def test_proved_pass_metadata_does_not_materialize_the_image_filtration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.two_primary_filtration as filtration

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("full image-rank tuples entered compact PASS metadata")

    monkeypatch.setattr(filtration, "pure_two_primary_image_filtration", forbidden)
    f4 = fermat_depth_certificate(4)
    m13 = mersenne_depth_certificate(13)
    assert (f4.status, f4.quotient_classes, f4.target_depth) == ("unknown", 0, None)
    assert (m13.status, m13.quotient_classes, m13.target_depth) == ("unknown", 0, None)


def test_no_classical_policy_returns_unknown_without_entering_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.proofs.oracles.classical_ceiling as ceiling
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("disabled classical ceiling was called")

    monkeypatch.setattr(ceiling, "fermat_classical_ceiling", forbidden)
    monkeypatch.setattr(ceiling, "mersenne_classical_ceiling", forbidden)
    compiler = CanonicalSequenceCompiler()
    f4 = compiler.resolve_special_theorem("fermat", 4, allow_classical_ceiling=False)
    m13 = compiler.resolve_special_theorem(
        "mersenne", 13, allow_classical_ceiling=False
    )
    assert not f4.decided and f4.primality is not None
    assert f4.primality.status == "unknown"
    assert f4.primality.specialization_raw_squarings == 0
    assert not m13.decided and m13.primality is not None
    assert m13.primality.status == "unknown"
    assert m13.primality.specialization_raw_squarings == 0


def test_no_classical_policy_preserves_independently_decided_branches() -> None:
    assert fermat_depth_certificate(3, allow_classical_ceiling=False).status == "prime"
    assert (
        mersenne_depth_certificate(7, allow_classical_ceiling=False).status == "prime"
    )
    assert (
        mersenne_depth_certificate(9, allow_classical_ceiling=False).status
        == "composite"
    )
    assert fermat_depth_certificate(4).status == "unknown"
    assert mersenne_depth_certificate(13).status == "unknown"


def test_public_pass_resolver_avoids_materialized_filtration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.two_primary_filtration as filtration
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("public PASS path materialized full filtration")

    monkeypatch.setattr(filtration, "pure_two_primary_image_filtration", forbidden)
    result = CanonicalSequenceCompiler().resolve_special_theorem("fermat", 3)
    assert result.decided and result.primality is not None
    assert result.primality.status == "prime"


def test_classical_policy_requires_literal_bool() -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.sequences.power_numbers.theorem_query import (
        resolve_special_theorem,
    )

    with pytest.raises(TypeError):
        fermat_depth_certificate(4, allow_classical_ceiling=cast(bool, 1))
    with pytest.raises(TypeError):
        resolve_special_theorem("fermat", 4, allow_classical_ceiling=cast(bool, 1))
    with pytest.raises(TypeError):
        CanonicalSequenceCompiler().resolve_special_theorem(
            "fermat",
            4,
            allow_classical_ceiling=cast(bool, 1),
        )


def test_mersenne_exponent_gate_uses_exact_u64_primality_without_factor_scan(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.numbers as special_numbers

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("least-factor scan entered boolean exponent gate")

    monkeypatch.setattr(special_numbers, "smallest_factor", forbidden)
    assert special_numbers.mersenne_exponent_is_prime(2_147_483_647)
    assert not special_numbers.mersenne_exponent_is_prime(2_147_483_645)


def test_direct_mersenne_certificate_rejects_unbounded_exponent_factor_search(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.numbers as special_numbers

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("unbounded exponent factor search entered certificate")

    monkeypatch.setattr(special_numbers, "smallest_factor", forbidden)
    unresolved = mersenne_depth_certificate(
        (1 << 64) + 13, max_candidate_bits=(1 << 64) + 20
    )
    assert unresolved.status == "unknown"
    assert unresolved.method == "exponent-gate-budget"
    assert not unresolved.scalable_construction

    even = mersenne_depth_certificate((1 << 64) + 2, max_candidate_bits=(1 << 64) + 20)
    assert even.status == "composite"
    assert even.method == "composite-exponent-small-factor"


def test_direct_special_certificates_reject_symbolic_width_before_large_shift() -> None:
    with pytest.raises(ValueError, match="candidate exceeds max_candidate_bits"):
        fermat_depth_certificate(1_000_000)
    with pytest.raises(ValueError, match="candidate exceeds max_candidate_bits"):
        mersenne_depth_certificate(1_000_001)


def test_removed_recurrence_policy_cannot_be_enabled_even_after_cache_hit() -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.sequences.power_numbers.theorem_query import (
        resolve_special_theorem,
    )

    compiler = CanonicalSequenceCompiler()
    assert compiler.resolve_special_theorem("fermat", 3).decided
    for resolve in (resolve_special_theorem, compiler.resolve_special_theorem):
        with pytest.raises(ValueError):
            resolve("fermat", 3, allow_classical_ceiling=True)
    for certify in (fermat_depth_certificate, mersenne_depth_certificate):
        with pytest.raises(ValueError):
            certify(3, allow_classical_ceiling=True)
