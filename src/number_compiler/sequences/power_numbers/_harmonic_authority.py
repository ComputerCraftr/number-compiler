"""Run-local integrity for finite harmonic source observations.

Producer modules keep their own private issuer and source checks.  This module
only snapshots bounded immutable packet values and binds them to an exact
record instance; it does not allocate a cache or a standalone resource ledger.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import fields, is_dataclass
from enum import Enum
from math import isnan
from typing import NamedTuple, cast
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.iterative_queries import (
    enter_ordered_children,
)

_MAX_SNAPSHOT_NODES = 100_000
_MAX_SNAPSHOT_BYTES = 16 * 1024 * 1024


class HarmonicIssuer(NamedTuple):
    """Private capability bound to one exact producer record type."""

    record_type: type[object]
    nonce: object


def new_harmonic_issuer(record_type: type[object]) -> HarmonicIssuer:
    if not isinstance(record_type, type):
        raise TypeError("harmonic issuer requires a record type")
    return HarmonicIssuer(record_type, object())


class _Token(NamedTuple):
    value_type: object
    value: object


class HarmonicSnapshot(NamedTuple):
    """Flat immutable payload snapshot with explicit retained-size bounds."""

    tokens: tuple[_Token, ...]
    retained_nodes: int
    retained_bytes: int


class _HarmonicSeal(NamedTuple):
    issuer: HarmonicIssuer
    record: ReferenceType[object]
    snapshot: HarmonicSnapshot


def _primitive_token(value: object) -> _Token | None:
    value_type = type(value)
    if value_type in (type(None), bool, int, str, bytes):
        return _Token(value_type, value)
    if value_type is float:
        floating = cast(float, value)
        return _Token(float, floating.hex() if isnan(floating) else floating)
    if isinstance(value, Enum):
        return _Token(value_type, value)
    return None


def _iter_tokens(payload: tuple[object, ...]) -> Iterator[_Token]:
    if type(payload) is not tuple:
        raise TypeError("harmonic payload must be a tuple")
    pending: list[tuple[object, bool]] = [(payload, False)]
    active: set[int] = set()
    scheduled = 1
    emitted = 0
    while pending:
        value, leaving = pending.pop()
        identity = id(value)
        if leaving:
            active.remove(identity)
            continue
        scheduled -= 1
        primitive = _primitive_token(value)
        if primitive is not None:
            if emitted + 1 + scheduled > _MAX_SNAPSHOT_NODES:
                raise ValueError("harmonic payload exceeds its snapshot budget")
            emitted += 1
            yield primitive
            continue
        if identity in active:
            raise ValueError("harmonic payload contains a reference cycle")
        if type(value) is tuple:
            children = value
            marker = _Token(tuple, len(children))
        elif is_dataclass(value) and not isinstance(value, type):
            parameters = getattr(type(value), "__dataclass_params__", None)
            if parameters is None or not parameters.frozen:
                raise TypeError("harmonic payload records must be frozen")
            definitions = fields(value)
            child_count = len(definitions)
            if (
                emitted + 1 + scheduled + child_count > _MAX_SNAPSHOT_NODES
                or len(pending) + 1 + child_count > _MAX_SNAPSHOT_NODES
            ):
                raise ValueError("harmonic payload exceeds its snapshot budget")
            names = tuple(item.name for item in definitions)
            children = tuple(getattr(value, name) for name in names)
            marker = _Token(type(value), child_count)
        else:
            raise TypeError("harmonic payload contains an unsupported value")
        child_count = len(children)
        if (
            emitted + 1 + scheduled + child_count > _MAX_SNAPSHOT_NODES
            or len(pending) + 1 + child_count > _MAX_SNAPSHOT_NODES
        ):
            raise ValueError("harmonic payload exceeds its snapshot budget")
        emitted += 1
        scheduled += child_count
        yield marker
        enter_ordered_children(pending, active, value, children)


def _token_size(token: _Token) -> int:
    value = token.value
    if type(value) is int:
        return 32 + max(1, (abs(value).bit_length() + 7) // 8)
    if type(value) is str:
        return 32 + 4 * len(value)
    if type(value) is bytes:
        return 32 + len(value)
    return 32


def snapshot_harmonic_payload(payload: tuple[object, ...]) -> HarmonicSnapshot:
    tokens: list[_Token] = []
    retained_bytes = 0
    for token in _iter_tokens(payload):
        tokens.append(token)
        retained_bytes += _token_size(token)
        if len(tokens) > _MAX_SNAPSHOT_NODES or retained_bytes > _MAX_SNAPSHOT_BYTES:
            raise ValueError("harmonic payload exceeds its snapshot budget")
    return HarmonicSnapshot(tuple(tokens), len(tokens), retained_bytes)


def harmonic_snapshot_matches(
    payload: tuple[object, ...], snapshot: HarmonicSnapshot
) -> bool:
    if type(snapshot) is not HarmonicSnapshot:
        return False
    try:
        emitted = 0
        retained_bytes = 0
        for token in _iter_tokens(payload):
            if emitted >= snapshot.retained_nodes or token != snapshot.tokens[emitted]:
                return False
            emitted += 1
            retained_bytes += _token_size(token)
            if retained_bytes > _MAX_SNAPSHOT_BYTES:
                return False
        return (
            emitted == snapshot.retained_nodes == len(snapshot.tokens)
            and retained_bytes == snapshot.retained_bytes
        )
    except (TypeError, ValueError):
        return False


def issue_harmonic(
    record: object,
    payload: tuple[object, ...],
    *,
    issuer: HarmonicIssuer,
) -> None:
    if type(issuer) is not HarmonicIssuer or type(record) is not issuer.record_type:
        raise TypeError("harmonic issuer does not own this record type")
    if getattr(record, "_issuer", None) is not None:
        raise ValueError("harmonic record has already been issued")
    seal = _HarmonicSeal(issuer, ref(record), snapshot_harmonic_payload(payload))
    object.__setattr__(record, "_issuer", seal)


def harmonic_verified(
    record: object,
    payload: tuple[object, ...],
    *,
    issuer: HarmonicIssuer,
) -> bool:
    seal = getattr(record, "_issuer", None)
    return (
        type(issuer) is HarmonicIssuer
        and type(record) is issuer.record_type
        and type(seal) is _HarmonicSeal
        and seal.issuer is issuer
        and seal.record() is record
        and harmonic_snapshot_matches(payload, seal.snapshot)
    )


def harmonic_payload(record: object) -> tuple[object, ...]:
    if not is_dataclass(record) or isinstance(record, type):
        raise TypeError("harmonic publication requires a data record")
    parameters = getattr(type(record), "__dataclass_params__", None)
    if parameters is None or not parameters.frozen:
        raise TypeError("harmonic publication requires a frozen data record")
    return tuple(getattr(record, f.name) for f in fields(record) if f.name != "_issuer")


__all__ = [
    "HarmonicIssuer",
    "HarmonicSnapshot",
    "harmonic_payload",
    "harmonic_snapshot_matches",
    "harmonic_verified",
    "issue_harmonic",
    "new_harmonic_issuer",
    "snapshot_harmonic_payload",
]
