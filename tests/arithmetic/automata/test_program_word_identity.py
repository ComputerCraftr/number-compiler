"""Weak source-word interning rejects integer aliases before cache probes."""

from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.automata.program_word import (
    EMPTY,
    CanonicalWord,
    concat,
    from_runs,
    from_values,
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


def test_bulk_word_constructor_preserves_exact_concat_normal_form() -> None:
    for length in range(9):
        for values in product((0, 1), repeat=length):
            expected = EMPTY
            for value in values:
                expected = concat(expected, leaf(value))
            assert from_values(iter(values)) is expected
            assert from_runs((value, 3) for value in values) is from_values(
                value for value in values for _ in range(3)
            )


def test_bulk_word_constructor_never_rebalances_prefixes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.automata import program_word

    def forbidden(*_args: object) -> None:
        raise AssertionError("bulk construction replayed prefix concatenation")

    monkeypatch.setattr(program_word, "concat", forbidden)
    word = from_runs(((7, 0), (1, 2), (1, 3), (0, 4), (1, 1)))
    assert tuple(program_word.iter_runs(word)) == ((1, 5), (0, 4), (1, 1))


def test_word_authority_releases_definition_with_last_reference() -> None:
    import gc
    import weakref

    from number_compiler.arithmetic.automata import program_word

    word = from_values((724019, 724021, 724023))
    identifier = word.node_id
    reference = weakref.ref(word)
    assert program_word._WORD_WATCHES[identifier]() is word
    assert identifier in program_word._WORD_DEFINITIONS
    del word
    gc.collect()
    assert reference() is None
    assert identifier not in program_word._WORD_WATCHES
    assert identifier not in program_word._WORD_DEFINITIONS
    assert identifier not in program_word._WORD_SYMBOL_BOUNDS
