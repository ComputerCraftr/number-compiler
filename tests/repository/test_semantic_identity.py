"""Regression checks for canonical semantic identity construction."""

from __future__ import annotations

import hashlib
import json
from array import array

import pytest

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityDomain,
)


def test_finite_block_identity_skips_redundant_json_digest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("finite block construction repeated identity hashing")

    with monkeypatch.context() as poison:
        poison.setattr(hashlib, "sha256", forbidden)
        poison.setattr(json, "dumps", forbidden)
        effect = FiniteBlockEffect(
            base=2,
            exponent=1,
            left_count=1,
            right_count=1,
            alphabet_size=4,
            initial_left=0,
            initial_right=0,
            left_transitions=array("I", [0] * 4),
            right_transitions=array("I", [0] * 4),
            outputs=bytes(range(4)),
            kernel_name="identity",
            storage_bytes=36,
            uncompressed_bytes=36,
            blank_left_tail=0,
            blank_right_tail=0,
            stable_blank_output=True,
        )
        identity = effect.canonical_key[1]
        assert type(identity) is SemanticIdentity
        identity.validate()

    assert type(identity) is SemanticIdentity


def test_semantic_identity_normalizes_named_domain_to_plain_string() -> None:
    identity = SemanticIdentity(SemanticIdentityDomain.ACTION_PROGRAM, ("x",))

    assert type(identity.digest) is str
    identity.validate()
