"""Owner-private issuance checks shared by immutable result records."""

from __future__ import annotations


class PublishedResult:
    __slots__ = ()
    _publication_owner: object | None
    _publication_snapshot: tuple[object, ...] | None

    def issued_by(self, authority: object) -> bool:
        return self._publication_owner is authority

    def publication_matches(self, expected: tuple[object, ...]) -> bool:
        return self._publication_snapshot == expected
