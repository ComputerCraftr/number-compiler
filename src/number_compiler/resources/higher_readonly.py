"""Read-only schema calls used by retained higher-semantic audits."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any, cast


def audit_schema_call(schema: object, operation: str, *arguments: object) -> Any:
    """Prefer an authority's nonmemoizing audit operation when available."""
    method = getattr(schema, operation + "_readonly", None)
    if method is None:
        method = getattr(schema, operation, None)
    if not callable(method):
        raise TypeError("higher semantic schema lacks an audit operation")
    return cast(Callable[..., Any], method)(*arguments)


__all__ = ["audit_schema_call"]
