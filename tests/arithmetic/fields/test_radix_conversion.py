"""Endpoint conversions preserve positional semantics with bounded digit work."""

import builtins

import pytest

from number_compiler.arithmetic.fields import radix


@pytest.mark.parametrize("base", (2, 3, 4, 7, 10, 16, 32, 36, 257))
@pytest.mark.parametrize("width", (0, 1, 31, 32, 33, 63, 64, 65, 129, 1025))
def test_balanced_conversion_matches_positional_reference(
    base: int, width: int
) -> None:
    word = tuple((i * 17 + 1) % base for i in range(width))
    expected = 0
    for digit in reversed(word):
        expected = expected * base + digit
    assert radix.value_from_lsd_digits(iter(word), base) == expected
    canonical = list(word)
    while canonical and canonical[-1] == 0:
        canonical.pop()
    assert radix.digits_lsd(expected, base) == tuple(canonical or [0])
    if width:
        assert radix.digits_lsd(expected, base, width) == word


@pytest.mark.parametrize("base", (3, 7, 10, 36))
def test_single_digit_divisions_only_visit_bounded_leaves(
    base: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    value = base**4097 + base**2048 + 1
    digit_bound = base**32

    def bounded_divmod(numerator: int, denominator: int) -> tuple[int, int]:
        if denominator == base:
            assert numerator < digit_bound
        return builtins.divmod(numerator, denominator)

    monkeypatch.setattr(radix, "divmod", bounded_divmod, raising=False)
    digits = radix.digits_lsd(value, base)
    assert len(digits) == 4098
    assert {i for i, digit in enumerate(digits) if digit} == {0, 2048, 4097}


def test_width_and_invalid_digits_preserve_contract() -> None:
    assert radix.value_from_lsd_digits([], 10) == 0
    assert radix.digits_lsd(0, 10, 3) == (0, 0, 0)
    assert radix.reverse_radix_integer(1200, 10) == 21
    with pytest.raises(ValueError):
        radix.digits_lsd(10, 10, 1)
    with pytest.raises(ValueError):
        radix.value_from_lsd_digits([0] * 64 + [10], 10)


@pytest.mark.parametrize("value", (0, 1, 123))
def test_single_digit_large_base_does_not_build_power_tree(
    value: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden_division(*_args: object) -> tuple[int, int]:
        raise AssertionError("single digit entered radix splitting")

    monkeypatch.setattr(radix, "divmod", forbidden_division, raising=False)
    assert radix.digits_lsd(value, (1 << 100_000) + 1, 2) == (value, 0)


def test_balanced_stream_is_lazy_charged_and_releases_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    value = 10**4097 + 10**2048 + 1
    operations: list[int] = []
    bit_work: list[int] = []
    workspace: list[tuple[int, int]] = []
    leaves = 0

    def bounded_divmod(numerator: int, denominator: int) -> tuple[int, int]:
        nonlocal leaves
        if denominator == 10:
            assert numerator < 10**32
            leaves += 1
        return builtins.divmod(numerator, denominator)

    monkeypatch.setattr(radix, "divmod", bounded_divmod, raising=False)
    stream = radix.iter_digits_lsd(
        value,
        10,
        charge=operations.append,
        charge_bits=bit_work.append,
        observe_workspace=lambda slots, bits: workspace.append((slots, bits)),
    )
    assert not operations and not workspace
    assert next(stream) == 1
    assert leaves == 1
    assert 0 < sum(operations) < 32
    assert sum(bit_work) > value.bit_length()
    assert workspace[-1][0] > 0
    stream.close()
    assert workspace[-1] == (0, 0)


def test_stream_budget_failure_cleans_up_before_any_digit() -> None:
    workspace: list[tuple[int, int]] = []

    def refuse(_: int) -> None:
        raise ValueError("stream work budget")

    stream = radix.iter_digits_lsd(
        10**100,
        10,
        charge=refuse,
        observe_workspace=lambda slots, bits: workspace.append((slots, bits)),
    )
    with pytest.raises(ValueError, match="stream work budget"):
        next(stream)
    assert workspace == [(0, 0)]
