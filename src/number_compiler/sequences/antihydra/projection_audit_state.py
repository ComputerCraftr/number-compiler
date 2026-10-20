"""Opaque exact-store identities for idle projection-owner audits."""

from __future__ import annotations

from typing import NamedTuple


class ProjectionStoreState(NamedTuple):
    owner: int
    attribute: str
    role: str
    store: object


class ProjectionCursorAuditState(NamedTuple):
    stores: tuple[ProjectionStoreState, ...]
    active: bool
    token_is_valid: bool


class ProjectionAdapterAuditState(NamedTuple):
    stores: tuple[ProjectionStoreState, ...]
    idle: bool
    token_is_valid: bool
