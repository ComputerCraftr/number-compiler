"""Scalar power-of-two radix points preserve blank versus zero padding."""

from typing import Never

import pytest

from number_compiler.api.number_api import PoweredCollatzTermPayload
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize(
    "seed,steps",
    ((1, 0), (2, 0), (63, 0), (64, 0), (82, 0), (1, 1), (2, 1), (27, 3), (16, 4)),
)
@pytest.mark.parametrize("radix", (4, 64, 1 << 63))
def test_partial_limb_and_exterior_without_width_or_materialization(
    seed: int, steps: int, radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    expected = seed
    for _ in range(steps):
        expected = 3 * expected + 1 if expected & 1 else expected // 2

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("scalar limb observed the complete endpoint")

    for name in ("width", "digits", "iter_digits", "materialize"):
        monkeypatch.setattr(PoweredCollatzTerm, name, forbidden)
    term = PoweredCollatzTerm(seed, steps)
    payload = PoweredCollatzTermPayload(term, radix)
    remaining, index = expected, 0
    while remaining:
        remaining, digit = divmod(remaining, radix)
        assert payload.digit(index) == digit
        index += 1
    with pytest.raises(IndexError) as exterior:
        payload.digit(index)
    assert exterior.value.args == (index,)
    with pytest.raises(IndexError):
        term.digit(expected.bit_length())
    assert term.digit(expected.bit_length() - 1) == 1


def test_limb_does_not_swallow_an_internal_point_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = HashLifeBlockIndex.direct_powered_point

    def broken(index: HashLifeBlockIndex, position: int) -> int:
        if position == 1:
            raise IndexError("internal point failure")
        return original(index, position)

    monkeypatch.setattr(HashLifeBlockIndex, "direct_powered_point", broken)
    with pytest.raises(IndexError, match="internal point failure"):
        PoweredCollatzTermPayload(PoweredCollatzTerm(1, 1), 64).digit(0)


def test_limb_rejects_an_invalid_kernel_symbol(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        HashLifeBlockIndex, "direct_powered_point", lambda _self, _position: 3
    )
    with pytest.raises(AssertionError):
        PoweredCollatzTermPayload(PoweredCollatzTerm(1, 1), 64).digit(0)
