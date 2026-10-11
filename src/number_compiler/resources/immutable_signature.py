"""Exact-type checks for compact immutable scalar signatures."""

from __future__ import annotations

from typing import TypeAlias, cast

ScalarSignatureValue: TypeAlias = str | int | bool | None
ScalarSignature: TypeAlias = tuple[ScalarSignatureValue, ...]


def make_scalar_signature(values: tuple[object, ...]) -> ScalarSignature:
    if type(values) is not tuple or any(
        type(value) not in (str, int, bool, type(None)) for value in values
    ):
        raise TypeError("immutable signatures contain only exact scalar values")
    return cast(ScalarSignature, values)


def matches_scalar_signature(
    values: tuple[object, ...], signature: ScalarSignature
) -> bool:
    return (
        type(values) is tuple
        and len(values) == len(signature)
        and all(
            type(value) is type(expected) and value == expected
            for value, expected in zip(values, signature, strict=True)
        )
    )
