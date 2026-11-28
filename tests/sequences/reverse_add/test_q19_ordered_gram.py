"""Independent literal checks for ordered Q19 carry correlation actions."""

from itertools import product
from math import comb

import pytest

from number_compiler.sequences.reverse_add.q19_ordered_gram import Q19OrderedGramAction


def literal(
    word: tuple[int, ...], a: int, b: int, z: int, m: int, degree: int
) -> tuple[tuple[int, int], tuple[tuple[int, ...], ...]]:
    forward: list[int] = []
    backward: list[int] = []
    for symbol in word:
        forward.append(1 - 2 * a)
        a = (symbol + a) // 10
    for symbol in reversed(word):
        backward.append(1 - 2 * b)
        b = (symbol + b) // 10
    backward.reverse()
    channels = (
        forward,
        backward,
        [x * y for x, y in zip(forward, backward, strict=True)],
        [x * y for x, y in zip(forward[:-1], backward[1:], strict=True)],
        [x * y for x, y in zip(forward[1:], backward[:-1], strict=True)],
    )

    def evaluate(values: list[int]) -> tuple[int, ...]:
        return tuple(
            sum(
                v * comb(i, k) * pow(z, i - k, m)
                for i, v in enumerate(values)
                if i >= k
            )
            % m
            for k in range(degree)
        )

    return (a, b), tuple(map(evaluate, channels))


@pytest.mark.parametrize("z,m", [(1, 2), (1, 8), (2, 8), (0, 9), (5, 17)])
def test_ordered_words_all_inlets_and_split_points(z: int, m: int) -> None:
    degree = 4
    for word in product((0, 4, 9, 10, 14, 18), repeat=3):
        actions = [Q19OrderedGramAction.atom(s, z, m, degree) for s in word]
        for split in (1, 2):
            left = Q19OrderedGramAction.identity(z, m, degree)
            right = Q19OrderedGramAction.identity(z, m, degree)
            for item in actions[:split]:
                left = left.then(item)
            for item in actions[split:]:
                right = right.then(item)
            result = left.then(right)
            for a, b in product((0, 1), repeat=2):
                row = result.rows[2 * a + b]
                exits, channels = literal(word, a, b, z, m, degree)
                assert (row.left_exit, row.right_exit) == exits
                assert (row.a, row.b, row.ab, row.a_next_b, row.next_a_b) == channels


def test_repeat_is_ordered_and_uses_binary_power() -> None:
    z, m, degree = 2, 8, 5
    motif = (0, 9, 18)
    action = Q19OrderedGramAction.identity(z, m, degree)
    for symbol in motif:
        action = action.then(Q19OrderedGramAction.atom(symbol, z, m, degree))
    joins = 0

    def count() -> None:
        nonlocal joins
        joins += 1

    repeated = action.repeat(31, on_compose=count)
    assert joins <= 10
    for a, b in product((0, 1), repeat=2):
        row = repeated.rows[2 * a + b]
        exits, channels = literal(motif * 31, a, b, z, m, degree)
        assert (row.left_exit, row.right_exit) == exits
        assert (row.a, row.b, row.ab, row.a_next_b, row.next_a_b) == channels
    assert action.repeat(0) == Q19OrderedGramAction.identity(z, m, degree)


def test_order_and_ring_guards() -> None:
    left = Q19OrderedGramAction.atom(9, 1, 16, 2)
    right = Q19OrderedGramAction.atom(4, 1, 16, 2)
    assert left.then(right) != right.then(left)
    with pytest.raises(ValueError):
        left.then(Q19OrderedGramAction.atom(4, 2, 16, 2))
    with pytest.raises(ValueError):
        left.repeat(-1)
    with pytest.raises(ValueError):
        Q19OrderedGramAction.atom(19, 1, 16, 2)


def test_ordered_34_column_tiles_and_physical_101_seams() -> None:
    a = (1, 9, 5, 9, 1, 3, 7, 3)
    b = (1, 9, 5, 9, 5, 9, 1, 3, 7, 3)
    u, v = a + a + b + a, a + b + a + a
    assert len(u) == len(v) == 34
    assert u != v

    def compile_word(word: tuple[int, ...]) -> Q19OrderedGramAction:
        result = Q19OrderedGramAction.identity(1, 1_000_000_007, 3)
        for symbol in word:
            result = result.then(Q19OrderedGramAction.atom(symbol, 1, 1_000_000_007, 3))
        return result

    u_action, v_action = compile_word(u), compile_word(v)
    assert u_action == v_action
    for left, right in product((u, v), repeat=2):
        word = left + right
        result = compile_word(left).then(compile_word(right))
        for low, high in product((0, 1), repeat=2):
            row = result.rows[2 * low + high]
            exits, channels = literal(word, low, high, 1, 1_000_000_007, 3)
            assert (row.left_exit, row.right_exit) == exits
            assert (row.a, row.b, row.ab, row.a_next_b, row.next_a_b) == channels

        # A physical source with the exact pair word and both end digits nonzero.
        pair_field = (17,) + word + (11,)
        low_digits = [max(0, symbol - 9) for symbol in pair_field]
        high_digits = [
            symbol - low for symbol, low in zip(pair_field, low_digits, strict=True)
        ]
        low_digits[0], high_digits[0] = 8, 9
        source = int("".join(map(str, low_digits + high_digits[::-1])))
        widths: list[int] = []
        for _ in range(3):
            digits = str(source)
            following = source + int(digits[::-1])
            widths.append(len(str(following)) - len(digits))
            source = following
        assert widths == [1, 0, 1]
        digits = str(source)
        field = [int(x) + int(y) for x, y in zip(digits, reversed(digits), strict=True)]
        assert field[2] == 11
        assert field[3:69] == [2] * 66
        assert field[69] == 3

    # Empty tile grammar is a distinct physical case, with two central 11s.
    empty_field = (17, 11, 11, 17)
    empty = compile_word(empty_field).rows[0]
    exits, channels = literal(empty_field, 0, 0, 1, 1_000_000_007, 3)
    assert (empty.left_exit, empty.right_exit) == exits
    assert (empty.a, empty.b, empty.ab, empty.a_next_b, empty.next_a_b) == channels
    source = 8299
    for _ in range(3):
        source += int(str(source)[::-1])
    digits = str(source)
    assert tuple(
        int(x) + int(y) for x, y in zip(digits, reversed(digits), strict=True)
    ) == (8, 8, 1, 1, 8, 8)

    # Equal low residue or a matching histogram cannot authorize the action.
    lifted_u = u[:12] + (u[12] + 9,) + u[13:]
    lifted_v = v[:12] + (v[12] + 9,) + v[13:]
    assert compile_word(lifted_u).rows[0].a[0] != compile_word(lifted_v).rows[0].a[0]
