"""Safe fingerprints for approved semantic effect keys during payload audits."""

from __future__ import annotations

from collections.abc import Callable
from functools import partial

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple

_MAX_EFFECT_KEY_NODES = 65_536


def _walk_effect_key(
    value: object,
    authorized_identity_ids: set[int] | None,
) -> tuple[tuple[tuple[object, ...], ...], set[int]] | None:
    if not is_exact_object_tuple(value):
        return None
    pending: list[tuple[object, bool]] = [(value, False)]
    tokens: list[tuple[object, ...]] = []
    identity_ids: set[int] = set()
    visited = 0
    while pending:
        part, closing = pending.pop()
        visited += 1
        if visited > _MAX_EFFECT_KEY_NODES:
            return None
        if closing:
            tokens.append(("tuple-end",))
        elif is_exact_object_tuple(part):
            children = part
            if visited + len(pending) + len(children) + 1 > _MAX_EFFECT_KEY_NODES:
                return None
            tokens.append(("tuple-start", len(children)))
            pending.append((children, True))
            pending.extend((child, False) for child in reversed(children))
        elif type(part) in (type(None), bool, int, float, str, bytes):
            tokens.append(("scalar", id(type(part)), part))
        elif authorized_identity_ids is None:
            identity_ids.add(id(part))
            tokens.append(("identity", id(type(part)), id(part)))
        elif id(part) in authorized_identity_ids:
            tokens.append(("identity", id(type(part)), id(part)))
        else:
            return None
    return tuple(tokens), identity_ids


def effect_key_snapshot(
    value: object,
) -> tuple[tuple[tuple[object, ...], ...], set[int]] | None:
    """Fingerprint a trusted key and retain IDs of its non-scalar leaves."""
    return _walk_effect_key(value, None)


def effect_key_fingerprint(
    value: object,
    *,
    authorized_identity_ids: set[int],
) -> tuple[tuple[object, ...], ...] | None:
    """Fingerprint a tuple key without hashing or comparing caller objects."""
    snapshot = _walk_effect_key(value, authorized_identity_ids)
    return None if snapshot is None else snapshot[0]


def approved_effect_key(
    value: object,
    *,
    approved_metadata: set[int],
    authorized_identity_ids: set[int],
    approved_fingerprints: set[tuple[tuple[object, ...], ...]],
) -> bool:
    """Check retained effect-key metadata against one completed audit inventory."""
    if id(value) in approved_metadata:
        return True
    if not is_exact_object_tuple(value):
        return False
    fingerprint = effect_key_fingerprint(
        value,
        authorized_identity_ids=authorized_identity_ids,
    )
    return fingerprint is not None and fingerprint in approved_fingerprints


def record_approved_effect_key(
    value: object,
    *,
    authorized_identity_ids: set[int],
    approved_fingerprints: set[tuple[tuple[object, ...], ...]],
) -> None:
    """Add one immutable key's safe fingerprint and retained identity leaves."""
    snapshot = effect_key_snapshot(value)
    if snapshot is None:
        return
    fingerprint, identity_ids = snapshot
    authorized_identity_ids.update(identity_ids)
    approved_fingerprints.add(fingerprint)


def approved_effect_key_checker(
    approved_metadata: set[int],
    authorized_identity_ids: set[int],
    approved_fingerprints: set[tuple[tuple[object, ...], ...]],
) -> Callable[[object], bool]:
    """Bind the mutable, audit-local approval sets to the key checker."""
    return partial(
        approved_effect_key,
        approved_metadata=approved_metadata,
        authorized_identity_ids=authorized_identity_ids,
        approved_fingerprints=approved_fingerprints,
    )
