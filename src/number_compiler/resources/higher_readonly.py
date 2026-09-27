"""Read-only schema calls used by retained higher-semantic audits."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import Any, cast


def audit_schema_call(schema: object, operation: str, *arguments: object) -> Any:
    """Prefer an authority's nonmemoizing audit operation when available."""
    method = getattr(schema, operation + "_readonly", None)
    if method is None:
        method = getattr(schema, operation, None)
    if not callable(method):
        raise TypeError("higher semantic schema lacks an audit operation")
    return cast(Callable[..., Any], method)(*arguments)


def audit_identity_index(mapping: object, record: object, index: int) -> bool:
    """Check an interner entry without mutating it, even after record corruption."""
    if not isinstance(mapping, Mapping):
        return False
    try:
        found = mapping.get(record)
        return type(found) is int and found == index
    except (KeyError, TypeError, AttributeError):
        return any(
            key is record and type(value) is int and value == index
            for key, value in mapping.items()
        )


__all__ = ["audit_identity_index", "audit_schema_call"]
