"""Explicit exact arithmetic oracles, excluded from production observers.

These routines may construct complete intermediate fields, carry rows, and
lossless encodings. Their data structures are mathematical reference objects,
not bounded transfer summaries or production temporal state.
"""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from contextvars import ContextVar

from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)

_ORACLE_ACTIVE: ContextVar[bool] = ContextVar(
    "number_compiler_exact_oracle", default=False
)


class ExactOracleAccessForbidden(RuntimeError):
    """Exact reference execution needs an explicit oracle context."""


def require_exact_oracle() -> None:
    """Check before allocation, warm cache access, or zero-step shortcuts."""
    require_endpoint_construction()
    if not _ORACLE_ACTIVE.get():
        raise ExactOracleAccessForbidden(
            "exact reference APIs require 'with devtools.verification.exact_oracle()'"
        )


@contextmanager
def exact_oracle() -> Generator[None, None, None]:
    """Authorize exact reference computation outside any point/width request."""
    require_endpoint_construction()
    token = _ORACLE_ACTIVE.set(True)
    try:
        yield
    finally:
        _ORACLE_ACTIVE.reset(token)


__all__ = ["ExactOracleAccessForbidden", "exact_oracle", "require_exact_oracle"]
