"""Wire conversion preserves exact values and never mutates cached packets."""

import math

import pytest

from number_compiler.api.json_output import json_integers


def test_serialization_copies_nested_packets_and_preserves_index_roles() -> None:
    original = {
        "index": {"encoding": "power10", "exponent": 3},
        "data": [1000, {"index": 1000}],
        "missing": None,
    }
    encoded = json_integers(original)
    assert encoded == original
    assert encoded is not original
    assert encoded["data"] is not original["data"]


def test_large_integer_encoding_is_exact() -> None:
    value = -(1 << 13000)
    encoded = json_integers({"value": value})["value"]
    assert isinstance(encoded, dict)
    assert encoded["encoding"] == "hex"
    assert int(str(encoded["value"]), 16) == value
    assert encoded["bits"] == value.bit_length()


@pytest.mark.parametrize("value", (math.nan, math.inf, -math.inf))
def test_nonfinite_measurements_are_not_valid_json(value: float) -> None:
    with pytest.raises(ValueError, match="finite"):
        json_integers({"measurement": value})


def test_serialization_does_not_invoke_object_rendering() -> None:
    class Undemanded:
        def __str__(self) -> str:
            raise AssertionError("unexpected rendering")

    with pytest.raises(TypeError, match="unsupported JSON"):
        json_integers({"value": Undemanded()})
