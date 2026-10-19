"""Immutable semantic keys: digests accelerate lookup, exact structure decides it."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from hashlib import sha256


class SemanticIdentityDomain(StrEnum):
    """Named construction domains for the shared semantic identity carrier.

    The constructor's first argument is a provenance label; the canonical
    digest is derived only from ``behavior``. Keeping these labels in an enum
    prevents call sites from inventing near-duplicate cache-domain strings
    without changing the serialized behavior or identity equality.
    """

    ANONYMOUS = ""
    ACTION_PROGRAM = "action-program"
    COMPOSED_BLOCK_DEFINITION = "composed-block-definition"
    PRIMITIVE_BEHAVIOR = "primitive-behavior"
    PRIMITIVE_BEHAVIOR_QUOTIENT = "primitive-behavior-quotient"
    PRIMITIVE_BEHAVIOR_TABLE = "primitive-behavior-table"
    PRIMITIVE_MACRO = "primitive-macro"
    REVERSE_ADD_SOURCE_CARRY = "reverse-add-source-carry-v1"
    REVERSE_ADD_PRIMITIVE_CYLINDER_CLAUSE = "reverse-add-primitive-cylinder-clause-v1"
    REVERSE_CENTERED_RADIAL_ACTION = "reverse-centered-radial-action-v1"
    REVERSE_COORDINATE_PROGRAM = "reverse-coordinate-program-v1"
    REVERSE_FIELD_OCCURRENCE = "reverse-field-occurrence"
    SEMANTIC_INTERFACE = "semantic-interface"
    TILE_INTERFACE = "tile-interface"


@dataclass(frozen=True, slots=True, eq=False, init=False)
class SemanticIdentity:
    digest: str
    behavior: tuple[object, ...]

    def __init__(
        self,
        digest: str | SemanticIdentityDomain,
        behavior: tuple[object, ...],
    ) -> None:
        # Call sites may supply a named construction domain. Normalize it at
        # this boundary before validation so the retained digest remains an
        # exact built-in string throughout the identity DAG.
        if type(digest) is SemanticIdentityDomain:
            digest = digest.value
        elif type(digest) is not str:
            raise TypeError("semantic identity domain must be a named enum or string")
        object.__setattr__(self, "digest", digest)
        object.__setattr__(self, "behavior", behavior)
        self.__post_init__()

    @classmethod
    def _from_validator(
        cls,
        digest: str | SemanticIdentityDomain,
        behavior: tuple[object, ...],
        validator: SemanticIdentityValidator,
    ) -> SemanticIdentity:
        """Construct an identity inside one caller-owned synchronous audit.

        This private path shares the audit's union-DAG work while still
        verifying and recording the newly constructed root. Public callers use
        the regular constructor, which always starts an independent audit.
        """
        if cls is not SemanticIdentity:
            raise TypeError("semantic identities cannot use a subclass constructor")
        if type(digest) is SemanticIdentityDomain:
            normalized_digest = digest.value
        elif type(digest) is str:
            normalized_digest = digest
        else:
            raise TypeError("semantic identity domain must be a named enum or string")
        if type(behavior) is not tuple:
            raise TypeError("semantic identity behavior must be an immutable tuple")
        if type(validator) is not SemanticIdentityValidator:
            raise TypeError("semantic identity construction requires an audit scope")
        identity = object.__new__(cls)
        object.__setattr__(identity, "digest", normalized_digest)
        object.__setattr__(identity, "behavior", behavior)
        canonical = validator._walk(identity, verify_root=False)
        object.__setattr__(identity, "digest", canonical)
        validator.validate(identity)
        return identity

    def __post_init__(self) -> None:
        """Derive the digest and validate the immutable behavior structure."""
        object.__setattr__(self, "digest", self._canonical_digest())

    def validate(self) -> None:
        """Recheck retained identity without repairing or mutating its digest."""
        validator = SemanticIdentityValidator()
        validator.validate(self)
        validator.finish()

    def _canonical_digest(self) -> str:
        validator = SemanticIdentityValidator()
        result = validator._walk(self, verify_root=False)
        validator.finish()
        return result

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
                pending.extend(zip(left, right, strict=True))
            elif type(left) is not type(right) or left != right:
                return False
        return True


class SemanticIdentityValidator:
    """Read-only validation of the union DAG during one synchronous audit.

    References prevent object-id reuse. No authority survives the audit:
    finish rechecks every identity's digest and immutable behavior reference.
    Tuple contents cannot mutate; nested identities are checked independently.
    """

    __slots__ = ("_digests", "_failed", "_identities", "_tuples")

    def __init__(self) -> None:
        self._tuples: dict[int, tuple[object, ...]] = {}
        self._digests: dict[int, bytes] = {}
        self._identities: dict[
            int, tuple[SemanticIdentity, str, tuple[object, ...]]
        ] = {}
        self._failed = False

    def validate(self, identity: SemanticIdentity) -> None:
        if self._failed:
            raise ValueError("semantic identity audit already failed")
        additions: list[tuple[bool, int]] = []
        succeeded = False
        try:
            self._walk(identity, verify_root=True, additions=additions)
            succeeded = True
        finally:
            if not succeeded:
                # Roll back only this candidate's new nodes. Scanning or copying
                # the whole committed DAG here would restore quadratic work.
                for is_tuple, node_id in additions:
                    if is_tuple:
                        self._tuples.pop(node_id, None)
                        self._digests.pop(node_id, None)
                    else:
                        self._identities.pop(node_id, None)

    def finish(self) -> None:
        if self._failed:
            raise ValueError("semantic identity audit already failed")
        for value, digest, behavior in self._identities.values():
            if (
                type(value.digest) is not str
                or value.digest != digest
                or value.behavior is not behavior
            ):
                self._failed = True
                raise ValueError("semantic identity changed during audit")

    def _discard(self) -> None:
        """Drop all candidate snapshots when their enclosing construction fails."""
        self._tuples.clear()
        self._digests.clear()
        self._identities.clear()
        self._failed = True

    def _walk(
        self,
        root: SemanticIdentity,
        *,
        verify_root: bool,
        additions: list[tuple[bool, int]] | None = None,
    ) -> str:
        pending: list[tuple[object, bool]] = [(root, False)]
        active: set[int] = set()
        while pending:
            value, leaving = pending.pop()
            identity = id(value)
            if leaving:
                active.remove(identity)
                if type(value) is tuple:
                    if additions is not None:
                        additions.append((True, identity))
                    self._digests[identity] = _tuple_digest(value, self._digests)
                    self._tuples[identity] = value
                elif type(value) is SemanticIdentity:
                    if value is not root or verify_root:
                        if value.digest != self._digests[id(value.behavior)].hex():
                            raise ValueError(
                                "semantic identity digest differs from its behavior"
                                if value is root
                                else "nested semantic identity has a forged digest"
                            )
                        if additions is not None:
                            additions.append((False, identity))
                        self._identities[identity] = (
                            value,
                            value.digest,
                            value.behavior,
                        )
                continue
            if identity in active:
                raise ValueError("semantic identity structure cannot be cyclic")
            if type(value) is SemanticIdentity:
                if type(value.digest) is not str or type(value.behavior) is not tuple:
                    raise TypeError(
                        "semantic identity requires immutable digest and behavior"
                    )
                previous = self._identities.get(identity)
                if previous is not None:
                    if value.digest != previous[1] or value.behavior is not previous[2]:
                        raise ValueError("semantic identity changed during audit")
                    continue
                active.add(identity)
                pending.append((value, True))
                pending.append((value.behavior, False))
            elif type(value) is tuple:
                if identity in self._tuples:
                    continue
                active.add(identity)
                pending.append((value, True))
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
        # Caller labels do not authorize identity. Constructors derive the root
        # digest; retained roots must already match it. Encoding has one owner.
        return self._digests[id(root.behavior)].hex()


def _tuple_digest(value: tuple[object, ...], children: dict[int, bytes]) -> bytes:
    """Versioned structural digest; sharing does not change semantic identity.

    Scalars have bounded integer width and have already been type-checked.
    Flat tables use C-level repr without recursing into any container. Parent
    tuples encode fixed-width child hashes; exact equality still checks the
    complete behavior, including when a digest collision occurs.
    """
    digest = sha256(b"semantic-tuple-v2\0")
    if not any(type(item) in (tuple, SemanticIdentity) for item in value):
        digest.update(b"flat\0")
        digest.update(repr(value).encode("utf-8"))
    else:
        digest.update(b"parent\0")
        for item in value:
            if type(item) is tuple:
                digest.update(b"t" + children[id(item)])
            elif type(item) is SemanticIdentity:
                digest.update(b"i" + sha256(item.digest.encode("utf-8")).digest())
            else:
                encoded = repr(item).encode("utf-8")
                digest.update(b"s" + str(len(encoded)).encode("ascii") + b":" + encoded)
    return digest.digest()


__all__ = ["SemanticIdentity", "SemanticIdentityDomain", "SemanticIdentityValidator"]
