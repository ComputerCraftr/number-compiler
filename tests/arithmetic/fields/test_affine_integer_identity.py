"""Algebraic runtime payloads reject Python numeric identity aliases."""

from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.fields.adic_morphism import (
    PadicAffineMorphism,
    PadicRadialQuotient,
    ValuationSensitivityMorphism,
    mersenne_successor_padic2,
    prime_translation_sensitivity,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power, modular_power


@pytest.mark.parametrize(
    "field", ("prime", "precision", "multiplier", "offset", "steps", "compositions")
)
@pytest.mark.parametrize("alias", (True, False, 1.0))
def test_padic_affine_rejects_numeric_aliases(field: str, alias: object) -> None:
    values: dict[str, object] = {
        "prime": 3,
        "precision": 4,
        "multiplier": 3,
        "offset": 1,
        "steps": 1,
        "compositions": 0,
    }
    values[field] = alias
    with pytest.raises(TypeError, match="exact integers"):
        PadicAffineMorphism(**cast(dict[str, int], values))


@pytest.mark.parametrize(
    "field",
    ("prime", "precision", "source_valuation", "source_unit", "innovation", "steps"),
)
@pytest.mark.parametrize("alias", (True, False, 1.0))
def test_padic_radial_rejects_numeric_aliases(field: str, alias: object) -> None:
    values: dict[str, object] = {
        "prime": 3,
        "precision": 4,
        "source_valuation": 1,
        "source_unit": 1,
        "innovation": 1,
        "steps": 1,
    }
    values[field] = alias
    with pytest.raises(TypeError, match="exact integers"):
        PadicRadialQuotient(**cast(dict[str, int], values))


@pytest.mark.parametrize(
    "field",
    ("prime", "precision", "scale", "increment", "logical_steps", "compositions"),
)
@pytest.mark.parametrize("alias", (True, False, 1.0))
def test_valuation_morphism_rejects_numeric_aliases(field: str, alias: object) -> None:
    values: dict[str, object] = {
        "prime": 2,
        "precision": 4,
        "scale": 1,
        "increment": 1,
        "logical_steps": 1,
        "compositions": 0,
    }
    values[field] = alias
    with pytest.raises(TypeError, match="exact integers"):
        ValuationSensitivityMorphism(**cast(dict[str, int], values))


def test_affine_observations_and_helpers_reject_numeric_aliases() -> None:
    affine = PadicAffineMorphism(3, 4, 3, 1)
    sensitivity = ValuationSensitivityMorphism(2, 4, 1, 1)
    for alias in (True, 1.0):
        with pytest.raises(TypeError, match="exact integer"):
            affine.apply(cast(int, alias))
        with pytest.raises(TypeError, match="exact integer"):
            sensitivity.apply(cast(int, alias))
        with pytest.raises(TypeError, match="exact integer"):
            mersenne_successor_padic2(cast(int, alias))
        with pytest.raises(TypeError, match="exact integer"):
            prime_translation_sensitivity(cast(int, alias), 4)


def test_shared_powering_rejects_boolean_float_integer_aliases() -> None:
    def compose(first: int, second: int) -> int:
        return first + second

    for alias in (True, False, 1.0):
        with pytest.raises(TypeError, match="exact integer"):
            binary_power(2, cast(int, alias), identity=0, compose=compose)
        with pytest.raises(TypeError, match="exact integers"):
            modular_power(2, cast(int, alias), 5)


def test_forged_affine_dataclass_is_revalidated_by_replace() -> None:
    valid = PadicAffineMorphism(3, 4, 3, 1)
    with pytest.raises(TypeError, match="exact integers"):
        replace(valid, steps=True)


@pytest.mark.parametrize(
    "factory",
    (
        lambda: PadicAffineMorphism(3, 41, 1, 0),
        lambda: PadicRadialQuotient(3, 41, 0, 1, 0),
        lambda: PadicAffineMorphism(1 << 63, 2, 1, 0),
    ),
)
def test_padic_runtime_payload_rejects_moduli_wider_than_one_limb(
    factory: Callable[[], object],
) -> None:
    with pytest.raises(ValueError, match="64-bit runtime limb"):
        factory()
