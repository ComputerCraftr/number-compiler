"""Independent finite-language check for the guarded 101 inverse relation."""

from __future__ import annotations

from collections import deque
from itertools import product
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    UniformConeNotAuthorized,
)
from tests.support.q19_tiles import physical_seed
from tests.support.reference_arithmetic import literal_reverse_add_digits


def _direct(word: tuple[int, ...]) -> int | None:
    a, b, c, d = (x + y for x, y in zip(word, word[1:], strict=False))
    if 9 in (a, b, c, d):
        return None
    first = 2 * (b % 10) + int(a > 9) + int(c > 9)
    second = 2 * (c % 10) + int(b > 9) + int(d > 9)
    if first == 9 or second == 9:
        return None
    return first - 9 * int(first > 9) + second - 9 * int(second > 9)


def _inverse_graph(
    target: int,
) -> tuple[
    list[tuple[int, int, int, int]],
    dict[tuple[int, int], list[int]],
    list[list[tuple[int, int]]],
]:
    output_digits = [x for x in range(10) if 0 <= target - x <= 9]
    states = list(product(range(1, 10), range(2), range(2), output_digits))
    index = {state: i for i, state in enumerate(states)}
    starts: dict[tuple[int, int], list[int]] = {}
    edges: list[list[tuple[int, int]]] = []
    for i, (previous_digit, c0, c1, output_digit) in enumerate(states):
        starts.setdefault((previous_digit, c0), []).append(i)
        row: list[tuple[int, int]] = []
        for c2 in (0, 1):
            carry_sum = c0 + c2
            raw = (
                output_digit if output_digit % 2 == carry_sum % 2 else output_digit + 9
            )
            if raw == 9 or raw > 18:
                continue
            previous_sum = 10 * c1 + (raw - carry_sum) // 2
            if not 2 <= previous_sum <= 18 or previous_sum == 9:
                continue
            if (previous_sum > 9) != bool(c1):
                continue
            next_digit = previous_sum - previous_digit
            if 1 <= next_digit <= 9:
                row.append(
                    (next_digit, index[next_digit, c1, c2, target - output_digit])
                )
        edges.append(row)
    return states, starts, edges


def _language_size(target: int) -> int:
    states, starts, edges = _inverse_graph(target)
    initial: tuple[tuple[int, ...], frozenset[int]] = ((), frozenset())
    pending: deque[tuple[tuple[int, ...], frozenset[int]]] = deque((initial,))
    seen: set[tuple[tuple[int, ...], frozenset[int]]] = {initial}
    while pending:
        word, response = pending.popleft()
        for digit in range(1, 10):
            n = len(word)
            expected = n < 4 or _direct(word + (digit,)) == target
            if n == 0:
                next_response: frozenset[int] = frozenset()
                accepted = True
            elif n == 1:
                pair_sum = word[0] + digit
                next_response = frozenset(
                    starts.get((digit, int(pair_sum > 9)), ()) if pair_sum != 9 else ()
                )
                accepted = True
            else:
                pair_sum = word[-1] + digit
                accepted = (
                    n < 4
                    or pair_sum != 9
                    and any(states[state][2] == int(pair_sum > 9) for state in response)
                )
                next_response = frozenset(
                    successor
                    for state in response
                    for label, successor in edges[state]
                    if label == digit
                )
            assert accepted == expected, (target, word, digit)
            if not expected:
                assert not next_response
                continue
            item = ((word + (digit,))[-4:], next_response)
            if item not in seen:
                seen.add(item)
                pending.append(item)
    return len(seen)


def test_every_guarded_inverse_output_has_the_same_finite_language() -> None:
    for target in range(19):
        assert _language_size(target) == 7381


def test_same_inverse_output_does_not_authenticate_the_center_fringe() -> None:
    words = ((1, 1, 1, 1, 1), (1, 1, 1, 1, 2))
    assert tuple(map(_direct, words)) == (8, 8)
    fields: list[tuple[int, ...]] = []
    for word in words:
        seed = int(physical_seed(word))
        rows = [literal_reverse_add_digits(seed, tick) for tick in range(4)]
        assert [len(b) - len(a) for a, b in zip(rows, rows[1:], strict=False)] == [
            1,
            0,
            1,
        ]
        digits = rows[-1]
        fields.append(
            tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
        )
    assert fields[0] != fields[1]


def test_uniform_inverse_endpoint_has_nonperiodic_intermediate_frames() -> None:
    choices = ((1, 3, 7, 3, 1, 9), (5, 9, 1, 3, 7, 3, 1, 9))
    random = Random(415)
    word: tuple[int, ...] = (7, 3, 1, 9)
    for _ in range(90):
        word += random.choice(choices)
    assert all(_direct(word[i : i + 5]) == 2 for i in range(len(word) - 4))
    seed = int(physical_seed(tuple(18 if digit == 9 else digit for digit in word)))
    rows = [literal_reverse_add_digits(seed, tick) for tick in range(4)]
    assert [len(b) - len(a) for a, b in zip(rows, rows[1:], strict=False)] == [1, 0, 1]
    for tick, row in enumerate(rows):
        pairs = tuple(a + b for a, b in zip(row, reversed(row), strict=True))
        segment = pairs[200:264]
        if tick == 3:
            assert set(segment) == {2}
        else:
            assert all(
                any(segment[i] != segment[i - period] for i in range(period, 64))
                for period in range(1, 33)
            )
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=3, window_digits=1
        )
        assert certificate.growth_word == (1, 0, 1)
        for period in range(1, 33):
            with pytest.raises(
                UniformConeNotAuthorized, match="spatial bank guard mismatch"
            ):
                owner.authorize_spatial_bank_morphism(
                    owner.initial,
                    steps=3,
                    start=200,
                    count=64,
                    period_size=period,
                    growth_control=certificate,
                    max_states=128,
                )
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0
