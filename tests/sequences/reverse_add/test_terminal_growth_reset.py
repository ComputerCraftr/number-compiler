"""Terminal growth uses the first decisive domain of an admitted pair field."""

from __future__ import annotations

from collections.abc import Iterator

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)


@pytest.mark.parametrize("base", (2, 3, 7, 10, 16))
@pytest.mark.parametrize(
    "seed", (0, 1, 9, 18, 90, 108, 198, 196, 909, 1041, 1051, 1593)
)
def test_growth_matches_full_fold_and_stops_at_first_decisive_domain(
    seed: int, base: int
) -> None:
    digits = digits_lsd(seed, base)
    pair = tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
    carry = 0
    for coefficient in pair:
        carry = int(coefficient + carry >= base)
    reads = next(
        (i + 1 for i, coefficient in enumerate(pair) if coefficient != base - 1),
        len(pair),
    )
    ledger = ResourceLedger()
    cutover = ReverseRecursiveTemporalCutover(
        ledger, digits, base=base, maximum_steps=1
    )
    occurrence = cutover.pair_image(1)
    assert cutover.width(occurrence) == len(pair) + carry
    assert ledger.counters["reverse_recursive_terminal_reset_prefix_symbols"] == reads
    assert ledger.counters.get("reverse_recursive_direct_carry_steps", 0) == 0
    expected = seed + sum(digit * base**i for i, digit in enumerate(reversed(digits)))
    emitted = tuple(cutover.iter_digits(occurrence))
    assert sum(digit * base**i for i, digit in enumerate(emitted)) == expected


def test_growth_does_not_consume_after_reset_and_closes_stream(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), (8, 9, 1), base=10, maximum_steps=1
    )
    occurrence = cutover.pair_image(1)  # Pair field is (9,18,9).
    closed: list[bool] = []

    def prefix(*_args: object) -> Iterator[int]:
        try:
            yield 9
            yield 18
            raise AssertionError("terminal carry continued beyond decisive domain")
        finally:
            closed.append(True)

    monkeypatch.setattr(cutover, "_pair_stream", prefix)
    assert cutover.width(occurrence) == 4
    assert closed == [True]
    assert cutover.ledger.counters["reverse_recursive_terminal_reset_hits"] == 1
