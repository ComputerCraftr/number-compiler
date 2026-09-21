"""Focused checks for lazy source-derived spatial carry ports."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


def _digits(value: int, base: int) -> tuple[int, ...]:
    result: list[int] = []
    while True:
        result.append(value % base)
        value //= base
        if not value:
            return tuple(result)


def _source(value: int, base: int) -> ExactSource:
    return ExactSource(_digits(value, base), base, orbit="reverse-add")


def _pairs(digits: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def _carries(pairs: tuple[int, ...], base: int) -> tuple[int, ...]:
    carry = 0
    result = [0]
    for pair in pairs:
        carry = int(pair + carry >= base)
        result.append(carry)
    return tuple(result)


def _step_digits(digits: tuple[int, ...], base: int) -> tuple[int, ...]:
    pairs = _pairs(digits)
    carries = _carries(pairs, base)
    result = tuple((pair + carries[i]) % base for i, pair in enumerate(pairs))
    return result + ((1,) if carries[-1] else ())


def test_neutral_source_ports_do_not_make_the_successor_a_temporal_identity() -> None:
    ports = SourceCarryPorts(_source(18, 10), ResourceLedger())
    assert ports.range_transfer(1, 0, 2) is CarryFn.ID
    # 18 -> 99: the original neutral pair coefficients (9,9) become (18,18).
    assert ports.range_transfer(2, 0, 2) is CarryFn.CONST1
    assert ports.range_transfer(1, 0, 2) is CarryFn.ID
    ports.dispose()


@pytest.mark.parametrize(
    ("value", "base"),
    ((0, 2), (1, 2), (11, 2), (5, 3), (41, 3), (99, 10), (196, 10)),
)
def test_first_and_second_ports_match_literal_carry_scans(
    value: int, base: int
) -> None:
    source = _source(value, base)
    first_pairs = _pairs(source.digits)
    first_carries = _carries(first_pairs, base)
    first_output = _step_digits(source.digits, base)
    second_pairs = _pairs(first_output)
    second_carries = _carries(second_pairs, base)
    ports = SourceCarryPorts(source, ResourceLedger())
    assert tuple(ports.pair(i) for i in range(ports.width)) == first_pairs
    assert tuple(ports.carry(i) for i in range(ports.width + 1)) == first_carries
    assert ports.terminal == first_carries[-1]
    assert tuple(ports.second_pair(i) for i in range(len(second_pairs))) == second_pairs
    assert (
        tuple(ports.second_carry(i) for i in range(len(second_pairs) + 1))
        == second_carries
    )
    assert ports.second_width() == len(_step_digits(first_output, base))


def test_interval_cache_is_lazy_and_retains_only_carry_actions() -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_source(196, 10), ledger)
    account = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_interval"
    )
    assert account.entries == account.nodes == 0
    assert ports.carry(2) == 1
    account = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_interval"
    )
    assert account.entries == account.nodes > 0
    assert all(type(value).__name__ == "CarryFn" for value in ports._cache.values())


@pytest.mark.parametrize(
    ("low", "high", "terminal"),
    ((8, 0, 0), (9, 9, 1)),
)
def test_cold_terminal_stops_at_decisive_outer_pair(
    low: int, high: int, terminal: int
) -> None:
    digits = (low,) + (4,) * 63 + (5,) * 63 + (high,)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(ExactSource(digits, 10, orbit="reverse-add"), ledger)
    assert ports.terminal == terminal
    assert ledger.counters["reverse_source_pullback_pair_reads"] <= 5


def test_ports_never_normalize_or_emit_output_digits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.formula.skew_residue_laws as skew
    import number_compiler.sequences.reverse_add.source_images as images

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("carry ports entered output normalization")

    monkeypatch.setattr(skew, "skew_normalized_digit", forbidden)
    monkeypatch.setattr(images._ReverseSourceImageAdapter, "_normalized", forbidden)
    monkeypatch.setattr(
        images._ReverseSourceImageAdapter, "iter_primitive_digits", forbidden
    )
    ports = SourceCarryPorts(_source(196, 10), ResourceLedger())
    assert ports.terminal == 0
    assert ports.second_width() == 4


def test_all_point_prefix_queries_have_bounded_spatial_cache() -> None:
    source = _source(int("4" * 128 + "5" * 128), 10)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    for boundary in range(ports.width + 1):
        ports.carry(boundary)
    first_width = ports.width + ports.terminal
    for boundary in range(first_width + 1):
        ports.second_carry(boundary)
    account = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_interval"
    )
    assert account.entries < 8 * ports.width
    assert ledger.counters["reverse_source_ports_prefix_blocks"] < (
        4 * ports.width * ports.width.bit_length()
    )
    assert ledger.counters["reverse_source_pullback_predecessor_search"] == 0


def test_source_binding_is_exact_and_disposal_releases_cache() -> None:
    source = _source(196, 10)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    ports.check_source(source)
    with pytest.raises(ValueError, match="foreign"):
        ports.check_source(_source(196, 10))
    ports.second_width()
    ports.dispose()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        ports.carry(0)


def test_same_ledger_cache_substitution_is_rejected() -> None:
    source = _source(196, 10)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    original = ports._cache
    owner = ledger.register("foreign-source-port-cache", "test_foreign_cache")
    foreign: OwnedMemo[tuple[int, int, int], object] = OwnedMemo(ledger, owner)
    object.__setattr__(ports, "_cache", foreign)
    with pytest.raises(ValueError, match="altered"):
        ports.check_source(source)
    object.__setattr__(ports, "_cache", original)
    foreign.dispose()
    ports.dispose()


def test_failed_interval_publication_rolls_back_query_entries() -> None:
    ledger = ResourceLedger(max_nodes=2)
    ports = SourceCarryPorts(_source(12345678, 10), ledger)
    with pytest.raises(BlockContextBudgetExceeded):
        _ = ports.terminal
    assert ledger.entries == ledger.nodes == 0
