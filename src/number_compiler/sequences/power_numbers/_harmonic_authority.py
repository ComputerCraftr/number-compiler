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
from typing import NamedTuple
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    require_instance,
)
from number_compiler.arithmetic.contracts.iterative_queries import (
    enter_ordered_children,
)

_MAX_SNAPSHOT_NODES = 100_000
_MAX_SNAPSHOT_BYTES = 16 * 1024 * 1024
_PRIMITIVE_TYPES = (type(None), bool, int, str, bytes, float)


class HarmonicIssuer(NamedTuple):
    """Private capability bound to one exact producer record type."""

    record_type: type[object]
    nonce: object


def new_harmonic_issuer(record_type: type[object]) -> HarmonicIssuer:
    require_instance(record_type, type)
    return HarmonicIssuer(record_type, object())


class _Token(NamedTuple):
    value_type: type[object]
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


def _primitive_value(value: object) -> object:
    if type(value) is float and isnan(value):
        return value.hex()
    return value


def _ordered_children(value: object, limit: int) -> tuple[object, ...]:
    children: tuple[object, ...]
    if isinstance(value, Enum):
        # Retaining the member itself would alias a changed arithmetic value.
        children = (value.name, value.value)
    elif is_exact_object_tuple(value):
        children = value
    elif is_dataclass(value) and not isinstance(value, type):
        parameters = getattr(type(value), "__dataclass_params__", None)
        if parameters is None or not parameters.frozen:
            raise TypeError("harmonic payload records must be frozen")
        definitions = fields(value)
        if len(definitions) > limit:
            raise ValueError("harmonic payload exceeds its snapshot budget")
        return tuple(getattr(value, item.name) for item in definitions)
    else:
        raise TypeError("harmonic payload contains an unsupported value")
    if len(children) > limit:
        raise ValueError("harmonic payload exceeds its snapshot budget")
    return children


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
        kind = type(value)
        if kind in _PRIMITIVE_TYPES:
            emitted += 1
            yield _Token(kind, _primitive_value(value))
            continue
        if identity in active:
            raise ValueError("harmonic payload contains a reference cycle")
        children = _ordered_children(
            value, _MAX_SNAPSHOT_NODES - 1 - max(emitted + scheduled, len(pending))
        )
        emitted += 1
        scheduled += len(children)
        yield _Token(kind, len(children))
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
    if (
        type(snapshot) is not HarmonicSnapshot
        or type(payload) is not tuple
        or type(snapshot.tokens) is not tuple
        or type(snapshot.retained_nodes) is not int
        or type(snapshot.retained_bytes) is not int
        or not 1
        <= snapshot.retained_nodes
        == len(snapshot.tokens)
        <= _MAX_SNAPSHOT_NODES
        or not 0 <= snapshot.retained_bytes <= _MAX_SNAPSHOT_BYTES
    ):
        return False
    # The issued stream fixes the complete traversal and all child arities.
    # Verification never generates a second token stream or trusts a prior hit.
    pending: list[object] = [payload]
    retained_bytes = 0
    try:
        for index, token in enumerate(snapshot.tokens):
            if not pending or type(token) is not _Token:
                return False
            value = pending.pop()
            kind = type(value)
            if kind is not token.value_type:
                return False
            if kind in _PRIMITIVE_TYPES:
                encoded = _primitive_value(value)
                if type(encoded) is not type(token.value) or encoded != token.value:
                    return False
            else:
                limit = snapshot.retained_nodes - index - 1 - len(pending)
                arity = token.value
                if type(arity) is not int or not 0 <= arity <= limit:
                    return False
                children = _ordered_children(value, arity)
                if len(children) != arity:
                    return False
                pending.extend(reversed(children))
            retained_bytes += _token_size(token)
            if retained_bytes > snapshot.retained_bytes:
                return False
        return not pending and retained_bytes == snapshot.retained_bytes
    except (AttributeError, TypeError, ValueError):
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
