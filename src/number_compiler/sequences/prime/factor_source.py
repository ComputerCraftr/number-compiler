"""Owner-bound prime factor identities and cache capabilities."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class PrimeFactorSourceIdentity:
    """Read-only identity for one append-only prime-factor source."""

    _owner_token: object
    mutation_stamp: tuple[object, int]
    factor_count: int

    def belongs_to(self, owner_token: object) -> bool:
        """Check the opaque issuer identity without exposing it to callers."""
        return self._owner_token is owner_token


@dataclass(frozen=True, slots=True)
class CachedPrimePrefixCapability:
    """Owner-bound permission to import the next factor of one issued prefix."""

    _owner_token: object
    _issuer: object
    _factors: tuple[object, ...]

    def next_factor(
        self,
        *,
        owner_token: object,
        issuer: object,
        prefix: tuple[int, ...],
    ) -> int:
        """Return exactly the next item after validating the issued prefix."""
        if (
            self._owner_token is not owner_token
            or self._issuer is not issuer
            or type(prefix) is not tuple
            or len(prefix) >= len(self._factors)
            or self._factors[: len(prefix)] != prefix
        ):
            raise ValueError("cached prime prefix is not bound to this source")
        value = self._factors[len(prefix)]
        if type(value) is not int:
            raise ValueError("cached prime prefix contains a noninteger factor")
        return value
