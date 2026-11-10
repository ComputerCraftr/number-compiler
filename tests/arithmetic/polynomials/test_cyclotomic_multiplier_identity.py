"""Multiplier identities forget derivations without forgetting their ring."""

from dataclasses import replace
from typing import NoReturn

import pytest

from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
    PowerTwoCyclotomicTransport,
    power_two_cyclotomic_radial_quotient,
    power_two_cyclotomic_transport,
)


@pytest.mark.parametrize("classes", (1, 2, 4))
@pytest.mark.parametrize("bits", (1, 3))
def test_multiplier_key_agrees_with_exact_action(classes: int, bits: int) -> None:
    by_action: dict[
        tuple[int, ...], tuple[str, int, int, int, tuple[int, ...] | None]
    ] = {}
    by_key: dict[
        tuple[str, int, int, int, tuple[int, ...] | None], tuple[int, ...]
    ] = {}
    for no_growth in range(5):
        for growth in range(13):
            action = power_two_cyclotomic_radial_quotient(
                classes, no_growth, growth, bits=bits
            )
            residue = action.multiplier_residue()
            key = action.canonical_key
            assert by_action.setdefault(residue, key) == key
            assert by_key.setdefault(key, residue) == residue


def test_zero_multiplier_keeps_ring_but_not_annihilation_provenance() -> None:
    exact = power_two_cyclotomic_radial_quotient(1, 0, 1, bits=4)
    modular = power_two_cyclotomic_radial_quotient(1, 4, 0, bits=4)
    assert exact.exact_zero and not modular.exact_zero
    assert exact.canonical_key == modular.canonical_key
    assert (
        exact.canonical_key
        != power_two_cyclotomic_radial_quotient(1, 5, 0, bits=5).canonical_key
    )
    assert (
        exact.canonical_key
        != power_two_cyclotomic_radial_quotient(2, 4, 0, bits=4).canonical_key
    )


def test_false_unit_cannot_issue_a_multiplier_identity() -> None:
    with pytest.raises(ValueError, match="exact multiplier"):
        PowerTwoCyclotomicRadialQuotient(2, 3, 0, 0, 0, 0, (0, 0))
    valid = power_two_cyclotomic_radial_quotient(2, 0, 0, bits=3)
    with pytest.raises(ValueError, match="exact multiplier"):
        replace(valid, unit_residue=(0, 0))
    object.__setattr__(valid, "unit_residue", (0, 0))
    with pytest.raises(ValueError, match="changed after validation"):
        valid.__post_init__()


def test_warm_unit_validation_does_not_recompute_polynomial(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    value = power_two_cyclotomic_radial_quotient(8, 0, 17, bits=9)

    def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("warm radial validation reconstructed its polynomial")

    monkeypatch.setattr(
        "number_compiler.arithmetic.polynomials.cyclotomic_transport._live_radial_unit",
        forbidden,
    )
    value.__post_init__()


def test_identity_never_constructs_an_unused_cyclotomic_block(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("identity constructed an unused ring")

    monkeypatch.setattr(
        "number_compiler.arithmetic.polynomials.cyclotomic_transport.CyclotomicRing",
        forbidden,
    )
    value = power_two_cyclotomic_radial_quotient(1024, 0, 0, bits=1)
    assert value.multiplier_residue() == (1,) + (0,) * 1023


def test_boolean_cannot_alias_cyclotomic_source_coordinates() -> None:
    with pytest.raises(TypeError, match="exact integers"):
        power_two_cyclotomic_radial_quotient(True, 0, 0, bits=3)
    with pytest.raises(TypeError, match="exact integers"):
        power_two_cyclotomic_transport(2, False, 0)


def test_false_annihilation_cannot_be_supplied_as_transport_metadata() -> None:
    with pytest.raises(ValueError, match="exact exponents"):
        PowerTwoCyclotomicTransport(2, 0, 0, 8, 0)
    with pytest.raises(ValueError, match="exact exponents"):
        PowerTwoCyclotomicTransport(2, 0, 0, 0, 0, True)
