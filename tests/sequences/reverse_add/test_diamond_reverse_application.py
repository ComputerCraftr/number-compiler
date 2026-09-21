"""Certified reverse/add uses the shared field-transfer executor."""

from typing import Never, cast

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def oracle(seed: int, base: int, steps: int) -> tuple[int, ...]:
    for _ in range(steps):
        reversed_value = 0
        for digit in digits_lsd(seed, base):
            reversed_value = reversed_value * base + digit
        seed += reversed_value
    return tuple(digits_lsd(seed, base))


@pytest.mark.parametrize("base", [2, 3, 4, 5, 10])
@pytest.mark.parametrize("steps", [0, 1, 2, 3])
@pytest.mark.parametrize("seed_kind", ["zero", "palindrome", "asymmetric", "carry"])
@pytest.mark.validation  # Eighty public base/step/source-kind differentials.
def test_certified_route_matches_exact_reverse_oracle(
    base: int,
    steps: int,
    seed_kind: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = {
        "zero": 0,
        "palindrome": base + 1,
        "asymmetric": 2 * base + 1,
        "carry": base * base - 1,
    }[seed_kind]
    term = ReverseAddPoweredTerm(seed, steps, base=base)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("certified route entered the generic diamond scheduler")

    monkeypatch.setattr(DiamondRuntime, "_transfer", forbidden)
    monkeypatch.setattr(DiamondRuntime, "_output", forbidden)
    expected = oracle(seed, base, steps)
    assert tuple(term.digit(index) for index in range(len(expected))) == expected
    assert term.width() == len(expected)
    with pytest.raises(IndexError):
        term.digit(term.maximum_width)
    assert term.digits() == expected
    assert all(row.accounting_delta == 0 for row in term._ledger.inventory())
    assert not term._ledger.counters.get("sequential_generation_advances", 0)


@pytest.mark.parametrize(
    ("seed", "steps", "base"),
    [(True, 0, 2), (1, False, 2), (1, 1, True)],
)
def test_certified_route_rejects_noninteger_metadata(
    seed: object,
    steps: object,
    base: object,
) -> None:
    with pytest.raises(TypeError):
        ReverseAddPoweredTerm(cast(int, seed), cast(int, steps), base=cast(int, base))
