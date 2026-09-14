"""Weak source-word interning rejects integer aliases before cache probes."""

from typing import cast

import pytest

from number_compiler.arithmetic.automata.program_word import (
    CanonicalWord,
    concat,
    from_runs,
    leaf,
    reverse,
    run,
    slice_runs,
)


@pytest.mark.parametrize("alias", [True, 1.0, "1"])
def test_word_constructors_reject_integer_aliases(alias: object) -> None:
    with pytest.raises(TypeError):
        leaf(cast(int, alias))
    with pytest.raises(TypeError):
        run(1, cast(int, alias))
    with pytest.raises(TypeError):
        from_runs(((1, cast(int, alias)),))


def test_counterfeit_word_cannot_claim_a_warm_node_identity() -> None:
    left, right = leaf(8), leaf(9)
    expected = concat(left, right)
    counterfeit = CanonicalWord(
        expected.node_id,
        expected.length,
        expected.run_count,
        left=left,
        right=right,
    )
    with pytest.raises(ValueError, match="foreign or stale"):
        reverse(counterfeit)
    with pytest.raises(ValueError, match="foreign or stale"):
        concat(counterfeit, leaf(7))


def test_mutated_live_word_cannot_use_its_old_warm_identity() -> None:
    word = concat(leaf(4), leaf(5))
    reverse(word)
    object.__setattr__(word, "length", word.length + 1)
    with pytest.raises(ValueError):
        reverse(word)


@pytest.mark.parametrize("start,length", [(True, 1), (0, True), (0.0, 1), (0, 1.0)])
def test_slice_rejects_coordinate_aliases(start: object, length: object) -> None:
    with pytest.raises(TypeError):
        slice_runs(from_runs(((1, 2), (0, 1))), cast(int, start), cast(int, length))
