"""Safe fingerprints for approved semantic effect keys during payload audits."""

from __future__ import annotations

_MAX_EFFECT_KEY_NODES = 65_536


def _walk_effect_key(
    value: object,
    authorized_identity_ids: set[int] | None,
) -> tuple[tuple[tuple[object, ...], ...], set[int]] | None:
    if type(value) is not tuple:
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
        elif type(part) is tuple:
            if visited + len(pending) + len(part) + 1 > _MAX_EFFECT_KEY_NODES:
                return None
            tokens.append(("tuple-start", len(part)))
            pending.append((part, True))
            pending.extend((child, False) for child in reversed(part))
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
