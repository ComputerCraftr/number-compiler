"""Semantic identities derive cache identity from bounded behavior."""

import pytest

from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityValidator,
)


def test_equal_behavior_ignores_caller_digest_label() -> None:
    first = SemanticIdentity("first-label", ("kernel", "same-behavior"))
    second = SemanticIdentity("second-label", ("kernel", "same-behavior"))
    assert first == second
    assert hash(first) == hash(second)
    assert first.digest == second.digest


def test_distinct_behavior_cannot_alias_through_claimed_digest() -> None:
    first = SemanticIdentity("claimed", ("kernel", "first"))
    second = SemanticIdentity("claimed", ("kernel", "second"))
    assert first != second
    assert first.digest != second.digest


def test_nested_identity_rejects_unbounded_integer_payload() -> None:
    with pytest.raises(ValueError, match="unbounded integer"):
        SemanticIdentity("claimed", ("kernel", 1 << 128))


def test_shared_squaring_identity_hashes_each_tuple_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts import semantic_identity

    original = semantic_identity.tuple_digest
    visits = 0

    def counted(value: tuple[object, ...], children: dict[int, bytes]) -> bytes:
        nonlocal visits
        visits += 1
        return original(value, children)

    monkeypatch.setattr(semantic_identity, "tuple_digest", counted)
    behavior: tuple[object, ...] = ("primitive", 1)
    for _ in range(128):
        behavior = (behavior, behavior)
    result = SemanticIdentity("caller-label", behavior)
    assert visits == 129
    assert len(result.digest) == 64


def test_deep_semantic_identity_does_not_use_recursive_repr() -> None:
    behavior: tuple[object, ...] = ("leaf",)
    for _ in range(2048):
        behavior = (behavior,)
    result = SemanticIdentity("deep", behavior)
    assert result == SemanticIdentity("same", behavior)


def test_semantic_digest_is_independent_of_tuple_sharing() -> None:
    shared: tuple[object, ...] = ("leaf", 3)
    first = SemanticIdentity("shared", (shared, shared))
    copies = (tuple(iter(shared)), tuple(iter(shared)))
    assert copies[0] is not copies[1]
    second = SemanticIdentity("copied", copies)
    assert first.digest == second.digest
    assert first == second


def test_digest_collision_does_not_authorize_different_behavior() -> None:
    first = SemanticIdentity("first", ((1, 2),))
    second = SemanticIdentity("second", ((1, 3),))
    object.__setattr__(second, "digest", first.digest)
    assert hash(first) == hash(second)
    assert first != second


def test_validation_rejects_forged_digest_without_repairing_it() -> None:
    identity = SemanticIdentity("label", ("valid",))
    identity.validate()
    object.__setattr__(identity, "digest", "forged")
    with pytest.raises(ValueError, match="digest"):
        identity.validate()
    assert identity.digest == "forged"
    with pytest.raises(ValueError, match="nested"):
        SemanticIdentity("parent", (identity,))
    assert identity.digest == "forged"


def test_audit_validator_hashes_one_shared_union_dag_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts import semantic_identity

    behavior: tuple[object, ...] = ("leaf", 3)
    for _ in range(64):
        behavior = (behavior, behavior)
    identities = tuple(SemanticIdentity("label", behavior) for _ in range(8))
    original = semantic_identity.tuple_digest
    visits = 0

    def counted(value: tuple[object, ...], children: dict[int, bytes]) -> bytes:
        nonlocal visits
        visits += 1
        return original(value, children)

    monkeypatch.setattr(semantic_identity, "tuple_digest", counted)
    validator = SemanticIdentityValidator()
    for identity in identities:
        validator.validate(identity)
    validator.finish()
    assert visits == 65


def test_audit_validator_rejects_forgery_without_repair() -> None:
    identity = SemanticIdentity("label", ("valid",))
    object.__setattr__(identity, "digest", "forged")
    validator = SemanticIdentityValidator()
    with pytest.raises(ValueError, match="digest"):
        validator.validate(identity)
    assert identity.digest == "forged"


def test_audit_validator_rejects_change_before_finish() -> None:
    identity = SemanticIdentity("label", ("valid",))
    validator = SemanticIdentityValidator()
    validator.validate(identity)
    object.__setattr__(identity, "behavior", ("changed",))
    with pytest.raises(ValueError, match="changed"):
        validator.finish()


def test_invalid_middle_candidate_preserves_prior_audit_snapshots() -> None:
    first = SemanticIdentity("first", ("valid", 1))
    forged = SemanticIdentity("forged", ("invalid", 2))
    last = SemanticIdentity("last", ("valid", 3))
    object.__setattr__(forged, "digest", "forged")
    validator = SemanticIdentityValidator()
    validator.validate(first)
    with pytest.raises(ValueError, match="digest"):
        validator.validate(forged)
    validator.validate(last)
    object.__setattr__(first, "behavior", ("changed",))
    with pytest.raises(ValueError, match="changed"):
        validator.finish()
