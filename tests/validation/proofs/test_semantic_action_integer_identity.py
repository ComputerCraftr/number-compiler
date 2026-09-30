"""Semantic Collatz action identities reject Python numeric aliases."""

from typing import Never, cast

import pytest

from devtools.verification.collatz_semantic_action import (
    CollatzBlockAction,
    CollatzBlockActionArena,
)
from number_compiler.arithmetic.fields.directed_field import DirectedTileTransducerArena
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan


@pytest.mark.parametrize("field", ("action_id", "local_shift"))
@pytest.mark.parametrize("value", (True, False, 0.0, 1.0))
def test_collatz_action_rejects_boolean_and_float_identity_aliases(
    field: str, value: bool | float
) -> None:
    values = {"action_id": 0, "local_shift": 0}
    values[field] = cast(int, value)
    with pytest.raises(TypeError, match="exact integer"):
        CollatzBlockAction(**values)


def test_action_arena_rejects_duck_span_before_work() -> None:
    class Mul3:
        def action_ref(self, _tile: object) -> Never:
            raise AssertionError("invalid span reached spatial action compilation")

    class Span:
        start = 0
        length = 1
        chunks = ()

    arena = CollatzBlockActionArena(cast(DirectedTileTransducerArena, Mul3()))
    before = arena.metrics()
    with pytest.raises(TypeError, match="exact dyadic span"):
        arena.intern(cast(DyadicSpan, Span()), 0)
    assert arena.metrics() == before
