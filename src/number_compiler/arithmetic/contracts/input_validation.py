"""Exact integer admission shared by public inputs and resource boundaries."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TypeGuard, TypeVar, cast

_T = TypeVar("_T")


def is_object_dictionary(value: object) -> TypeGuard[dict[object, object]]:
    """Narrow the dictionary container without trusting its keys or values."""
    return isinstance(value, dict)


def is_object_list(value: object) -> TypeGuard[list[object]]:
    """Admit an exact list without trusting its element types."""
    return type(value) is list


def is_object_list_instance(value: object) -> TypeGuard[list[object]]:
    """Narrow a list payload while preserving admission of list subclasses."""
    return isinstance(value, list)


def string_keyed_mapping(value: object) -> Mapping[str, object] | None:
    """Validate external dictionary keys before exposing a read-only mapping."""
    if not is_object_dictionary(value):
        return None
    result: dict[str, object] = {}
    for raw_key, raw_item in value.items():
        if not isinstance(raw_key, str):
            return None
        item: object = raw_item
        result[raw_key] = item
    return result


def is_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    """Narrow tuple payloads without changing their runtime admission rule."""
    return isinstance(value, tuple)


def is_exact_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    """Admit an exact immutable tuple while leaving its members untrusted."""
    return type(value) is tuple


def is_exact_integer_tuple(value: object) -> TypeGuard[tuple[int, ...]]:
    """Admit an exact tuple containing only exact integers."""
    return is_exact_object_tuple(value) and all(type(item) is int for item in value)


def object_mapping(value: object) -> Mapping[object, object] | None:
    """Narrow a mapping without trusting the types of its keys or values."""
    if not isinstance(value, Mapping):
        return None
    return cast(Mapping[object, object], value)


def require_instance(value: object, expected: type[_T]) -> _T:
    """Admit a runtime instance while preserving the original TypeError args."""
    if not isinstance(value, expected):
        raise TypeError(type(value))
    return value


def is_runtime_instance(value: object, expected: type[_T]) -> TypeGuard[_T]:
    """Check untrusted runtime inputs, including callers that bypass annotations."""
    return isinstance(value, expected)


def is_mapping_instance(value: object) -> bool:
    """Preserve an isinstance check for ABC mappings without a class argument."""
    return isinstance(value, Mapping)


def is_exact_integer_in_range(
    value: object, lower: int = 0, upper: int | None = None
) -> bool:
    """Check an exact integer against an inclusive lower and exclusive upper bound."""
    return type(value) is int and value >= lower and (upper is None or value < upper)


def require_integer(
    value: object, name: str, minimum: int | None = None, maximum: int | None = None
) -> int:
    """Reject coercions that alias distinct requests before doing any work."""
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer")
    if (
        minimum is not None
        and value < minimum
        or maximum is not None
        and value > maximum
    ):
        if minimum is None:
            bound = f"<= {maximum}"
        elif maximum is None:
            bound = f">= {minimum}"
        else:
            bound = f"between {minimum} and {maximum}"
        raise ValueError(f"{name} must be {bound}")
    return value


def normalized_integer_pair(
    first: int, second: int, *, first_minimum: int = 0, second_minimum: int = 0
) -> tuple[int, int]:
    """Preserve legacy algebraic integer coercion and paired range diagnostics."""
    left, right = int(first), int(second)
    if left < first_minimum or right < second_minimum:
        raise ValueError((left, right))
    return left, right


__all__ = [
    "is_exact_object_tuple",
    "is_exact_integer_in_range",
    "is_exact_integer_tuple",
    "is_mapping_instance",
    "is_object_dictionary",
    "is_object_list",
    "is_object_list_instance",
    "is_object_tuple",
    "is_runtime_instance",
    "object_mapping",
    "require_instance",
    "require_integer",
    "string_keyed_mapping",
]


def normalized_odd_modulus(value: int, *, minimum: int = 3) -> int:
    """Admit legacy integer-coercing odd ring moduli with scalar diagnostics."""
    modulus = int(value)
    if modulus < minimum or not (modulus & 1):
        raise ValueError(modulus)
    return modulus
