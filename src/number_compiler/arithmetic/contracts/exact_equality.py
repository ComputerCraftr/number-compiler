"""Small exact comparators for immutable structural payloads."""

from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple


def extend_typed_tuple_pairs(
    pending: list[tuple[object, object]], left: object, right: object
) -> bool:
    """Append corresponding items when both values are equal-length tuples."""
    if type(left) is not tuple or type(right) is not tuple:
        return False
    left_items = cast(tuple[object, ...], left)
    right_items = cast(tuple[object, ...], right)
    if len(left_items) != len(right_items):
        return False
    pending.extend(zip(left_items, right_items, strict=True))
    return True


def typed_tuple_tree_equal(left: object, right: object) -> bool:
    """Compare nested tuples and typed scalar leaves without recursion."""
    pending = [(left, right)]
    while pending:
        first, second = pending.pop()
        if type(first) is not type(second):
            return False
        if is_exact_object_tuple(first):
            if not extend_typed_tuple_pairs(pending, first, second):
                return False
        elif first != second:
            return False
    return True


__all__ = ["extend_typed_tuple_pairs", "typed_tuple_tree_equal"]
