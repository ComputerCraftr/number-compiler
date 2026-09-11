"""Immutable semantic keys: digests accelerate lookup, exact structure decides it."""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256


@dataclass(frozen=True, slots=True, eq=False)
class SemanticIdentity:
    digest: str
    behavior: tuple[object, ...]

    def __post_init__(self) -> None:
        if type(self.digest) is not str or type(self.behavior) is not tuple:
            raise TypeError("semantic identity requires immutable digest and behavior")
        pending: list[tuple[object, bool]] = [(self, False)]
        active: set[int] = set()
        complete: set[int] = set()
        while pending:
            value, leaving = pending.pop()
            identity = id(value)
            if leaving:
                active.remove(identity)
                complete.add(identity)
                continue
            if identity in active:
                raise ValueError("semantic identity structure cannot be cyclic")
            if identity in complete:
                continue
            active.add(identity)
            pending.append((value, True))
            if type(value) is SemanticIdentity:
                if type(value.digest) is not str or type(value.behavior) is not tuple:
                    raise TypeError(
                        "semantic identity requires immutable digest and behavior"
                    )
                pending.append((value.behavior, False))
            elif type(value) is tuple:
                # Finite kernel tables contain many scalar cells. Validate
                # those in place; only containers need cycle/DAG work frames.
                for item in value:
                    kind = type(item)
                    if kind is tuple or kind is SemanticIdentity:
                        pending.append((item, False))
                    elif kind is int:
                        if item.bit_length() > 64:
                            raise ValueError(
                                "semantic identities cannot hide unbounded integer payloads"
                            )
                    elif kind not in (str, bytes, bool, type(None)):
                        raise TypeError(
                            "semantic identities cannot retain mutable or executable payloads"
                        )
            else:
                raise TypeError(
                    "semantic identities cannot retain mutable or executable payloads"
                )
        # A caller-supplied label is metadata, not identity authority.  Derive
        # the digest after validating the complete immutable behavior so equal
        # behavior cannot be split into distinct cache identities.
        canonical = sha256(repr(self.behavior).encode("utf-8")).hexdigest()
        object.__setattr__(self, "digest", canonical)

    def __hash__(self) -> int:
        return hash(self.digest)

    def __repr__(self) -> str:
        return f"SemanticIdentity({self.digest!r})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SemanticIdentity):
            return NotImplemented
        pending: list[tuple[object, object]] = [(self, other)]
        visited: set[tuple[int, int]] = set()
        while pending:
            left, right = pending.pop()
            if left is right:
                continue
            pair = id(left), id(right)
            if pair in visited:
                continue
            visited.add(pair)
            if isinstance(left, SemanticIdentity) and isinstance(
                right, SemanticIdentity
            ):
                if left.digest != right.digest:
                    return False
                pending.append((left.behavior, right.behavior))
            elif isinstance(left, tuple) and isinstance(right, tuple):
                if len(left) != len(right):
                    return False
                pending.extend(zip(left, right))
            elif type(left) is not type(right) or left != right:
                return False
        return True


__all__ = ["SemanticIdentity"]
