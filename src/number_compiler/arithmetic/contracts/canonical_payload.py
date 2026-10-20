"""Closed validation for bounded semantic interner keys.

Semantic identities are descriptive structure.  Numeric cache IDs, digit
payloads, and scoped handles belong in typed arena fields and cannot be hidden
inside an otherwise hashable construction key.
"""

from __future__ import annotations

from collections.abc import Hashable

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity


def validate_bounded_semantic_key(key: Hashable, *, max_units: int) -> None:
    """Reject untyped IDs and unbounded payloads before interner lookup."""
    if type(max_units) is not int or max_units < 1:
        raise ValueError("semantic-key capacity must be a positive exact integer")
    if isinstance(key, ArenaHandle) or type(key) in (bool, int, float):
        raise TypeError("semantic keys cannot be handles or scalar ID aliases")
    pending: list[object] = [key]
    units = 0
    while pending:
        value = pending.pop()
        units += 1
        if units > max_units:
            raise ValueError("semantic key exceeds the bounded canonical record limit")
        if isinstance(value, ArenaHandle):
            raise TypeError("semantic keys cannot contain scoped handles")
        if is_exact_object_tuple(value):
            pending.extend(value)
        elif isinstance(value, SemanticIdentity):
            value.__post_init__()
        elif isinstance(value, (str, bytes)):
            if len(value) > max_units:
                raise ValueError("semantic key embeds an unbounded scalar payload")
        elif type(value) in (int, bool, float):
            raise TypeError("semantic keys cannot contain scalar ID aliases")
        elif type(value) not in (str, bytes, type(None), SemanticIdentity):
            raise TypeError("semantic keys require canonical immutable structure")
    hash(key)


__all__ = ["validate_bounded_semantic_key"]
