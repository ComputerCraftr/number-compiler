from __future__ import annotations

from number_compiler.resources.approved_effect_keys import (
    effect_key_fingerprint,
    effect_key_snapshot,
)


def test_effect_key_fingerprint_preserves_distinct_equal_large_integer_keys() -> None:
    first = int("9" * 180)
    second = int("9" * 180)
    assert first == second and first is not second

    approved = ("effect", first)
    observed = ("effect", second)
    snapshot = effect_key_snapshot(approved)
    assert snapshot is not None
    approved_fingerprint, authorized_ids = snapshot

    assert approved_fingerprint == effect_key_fingerprint(
        observed, authorized_identity_ids=authorized_ids
    )


def test_effect_key_fingerprint_bounds_pending_tuple_work() -> None:
    oversized = ("effect", *range(65_535))

    assert effect_key_fingerprint(oversized, authorized_identity_ids=set()) is None
