"""Semantic identities derive cache identity from bounded behavior."""

import pytest

from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity


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
