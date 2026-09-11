from typing import Never

import pytest

from number_compiler.sequences.power_numbers.certificate import (
    fermat_depth_certificate,
    mersenne_depth_certificate,
)


def test_demanded_depth_certificates_use_compact_terminal_then_classical_ceiling() -> (
    None
):
    for n in (0, 1, 2):
        cert = fermat_depth_certificate(n)
        assert cert.status == "prime"
        assert cert.specialization_raw_squarings == 0
        assert cert.carrier_states_enumerated == 0
    # F3 is now proved directly by the square-root divisor bound.
    f3 = fermat_depth_certificate(3)
    assert f3.status == "prime"
    assert f3.method == "terminal-threshold:fermat-sqrt-divisor-lower-bound"
    expected_fermat = {4: ("prime", 15), 5: ("composite", 31)}
    for n, (status, steps) in expected_fermat.items():
        cert = fermat_depth_certificate(n)
        assert cert.status == status
        assert cert.method == "classical-ceiling:pepin-target-pullback"
        assert cert.specialization_raw_squarings == steps == cert.modulus_bits - 2
        assert cert.carrier_states_enumerated == 0

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
    expected_mersenne = {11: "composite", 13: "prime", 17: "prime"}
    for p, status in expected_mersenne.items():
        cert = mersenne_depth_certificate(p)
        assert cert.status == status
        assert cert.method == "classical-ceiling:lucas-lehmer-target-pullback"
        assert cert.specialization_raw_squarings == p - 2 == cert.modulus_bits - 2
        assert cert.carrier_states_enumerated == 0
    # Composite exponents are still rejected by the cheap symbolic exponent theorem.
    assert mersenne_depth_certificate(9).status == "composite"


def test_prime_depth_metadata_is_attached_only_after_candidate_derived_target_proof() -> (
    None
):
    f2 = fermat_depth_certificate(2)
    f4 = fermat_depth_certificate(4)
    m13 = mersenne_depth_certificate(13)
    assert f2.target_depth == 0 and f2.quotient_classes == 2
    assert f4.target_depth is not None and f4.quotient_classes > 0
    assert m13.target_depth is not None and m13.quotient_classes > 0


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
    assert (f4.status, f4.quotient_classes, f4.target_depth) == ("prime", 12, 10)
    assert (m13.status, m13.quotient_classes, m13.target_depth) == ("prime", 13, 11)


def test_no_classical_policy_returns_unknown_without_entering_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.classical_ceiling as ceiling
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
    assert fermat_depth_certificate(4).status == "prime"
    assert mersenne_depth_certificate(13).status == "prime"


def test_public_pass_resolver_avoids_materialized_filtration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.two_primary_filtration as filtration
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("public PASS path materialized full filtration")

    monkeypatch.setattr(filtration, "pure_two_primary_image_filtration", forbidden)
    result = CanonicalSequenceCompiler().resolve_special_theorem("fermat", 4)
    assert result.decided and result.primality is not None
    assert result.primality.status == "prime"


def test_classical_policy_requires_literal_bool() -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.sequences.power_numbers.theorem_query import (
        resolve_special_theorem,
    )

    with pytest.raises(TypeError):
        fermat_depth_certificate(4, allow_classical_ceiling=1)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        resolve_special_theorem("fermat", 4, allow_classical_ceiling=1)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        CanonicalSequenceCompiler().resolve_special_theorem(
            "fermat",
            4,
            allow_classical_ceiling=1,  # type: ignore[arg-type]
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
