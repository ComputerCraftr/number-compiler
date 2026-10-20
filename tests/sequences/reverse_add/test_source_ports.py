"""Focused checks for lazy source-derived spatial carry ports."""

from __future__ import annotations

from collections.abc import Callable
from itertools import pairwise
from typing import cast

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.private_attributes import private_test_attribute
from tests.support.reverse_source_ports import (
    carry_scan,
    pair_sums,
    source_from_value,
    successor_digits,
)


def test_neutral_source_ports_do_not_make_the_successor_a_temporal_identity() -> None:
    ports = SourceCarryPorts(source_from_value(18, 10), ResourceLedger())
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
    source = source_from_value(value, base)
    first_pairs = pair_sums(source.digits)
    first_carries = carry_scan(first_pairs, base)
    first_output = successor_digits(source.digits, base)
    second_pairs = pair_sums(first_output)
    second_carries = carry_scan(second_pairs, base)
    ports = SourceCarryPorts(source, ResourceLedger())
    assert tuple(ports.pair(i) for i in range(ports.width)) == first_pairs
    assert tuple(ports.carry(i) for i in range(ports.width + 1)) == first_carries
    assert ports.terminal == first_carries[-1]
    assert tuple(ports.second_pair(i) for i in range(len(second_pairs))) == second_pairs
    assert (
        tuple(ports.second_carry(i) for i in range(len(second_pairs) + 1))
        == second_carries
    )
    assert ports.second_width() == len(successor_digits(first_output, base))


def test_interval_cache_is_lazy_and_retains_only_carry_actions() -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source_from_value(196, 10), ledger)
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
    assert all(
        type(value).__name__ == "CarryFn"
        for value in ports.audit_snapshot().cache.payload_view.values()
    )


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
    monkeypatch.setattr(images.ReverseSourceImageAdapter, "_normalized", forbidden)
    monkeypatch.setattr(
        images.ReverseSourceImageAdapter, "iter_primitive_digits", forbidden
    )
    ports = SourceCarryPorts(source_from_value(196, 10), ResourceLedger())
    assert ports.terminal == 0
    assert ports.second_width() == 4


def test_all_point_prefix_queries_have_bounded_spatial_cache() -> None:
    source = source_from_value(int("4" * 128 + "5" * 128), 10)
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
    source = source_from_value(196, 10)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    ports.check_source(source)
    with pytest.raises(ValueError, match="foreign"):
        ports.check_source(source_from_value(196, 10))
    ports.second_width()
    ports.dispose()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        ports.carry(0)


def test_same_ledger_cache_substitution_is_rejected() -> None:
    source = source_from_value(196, 10)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    original = ports.audit_snapshot().cache_identity
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
    ports = SourceCarryPorts(source_from_value(12345678, 10), ledger)
    with pytest.raises(BlockContextBudgetExceeded):
        _ = ports.terminal
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("seed", [0, 1, 18, 99, 196, 909, 1041, 1051, 1593])
def test_decimal_thresholds_use_output_crt_without_next_pair_reconstruction(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("threshold consumer reconstructed the next pair")

    source = source_from_value(seed, 10)
    first = successor_digits(source.digits, 10)
    expected = carry_scan(pair_sums(first), 10)
    ports = SourceCarryPorts(source, ResourceLedger())
    monkeypatch.setattr(SourceCarryPorts, "_raw_second_pair", forbidden)
    assert tuple(ports.second_carry(i) for i in range(len(first) + 1)) == expected
    assert ports.second_width() == len(first) + expected[-1]
    # A second demand reuses the same admitted interval summaries.
    assert tuple(ports.second_carry(i) for i in range(len(first) + 1)) == expected
    ports.dispose()


@pytest.mark.parametrize(
    "value,base", [(0, 2), (27, 2), (41, 3), (18, 10), (196, 10), (1593, 10)]
)
def test_regional_carry_stream_matches_forward_scan_in_both_coordinate_orders(
    value: int,
    base: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = source_from_value(value, base)
    expected = carry_scan(pair_sums(source.digits), base)
    ports = SourceCarryPorts(source, ResourceLedger())

    def forbidden(*_args: object) -> int:
        raise AssertionError("stream reopened a point prefix")

    monkeypatch.setattr(SourceCarryPorts, "_first_prefix", forbidden)
    pairs = tuple(pairwise(expected))
    assert tuple(ports.iter_first_ports()) == pairs
    assert tuple(ports.iter_first_ports(reflected=True)) == pairs[::-1]
    ports.dispose()


def test_regional_carry_stream_releases_partial_traversal_stack() -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source_from_value(int("45" * 64), 10), ledger)
    stream = ports.iter_first_ports(reflected=True)
    next(stream)
    stream.close()
    account = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_workspace"
    )
    assert account.nodes == 0
    ports.dispose()
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("value", [18, 196, 909, 1041, 1051, 1593])
def test_second_pair_stream_uses_one_growth_prefix_only(
    value: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = source_from_value(value, 10)
    ports = SourceCarryPorts(source, ResourceLedger())
    original = cast(
        Callable[[SourceCarryPorts, int], int],
        private_test_attribute(SourceCarryPorts, "_first_prefix"),
    )
    calls = 0

    def single_growth(self: SourceCarryPorts, boundary: int) -> int:
        nonlocal calls
        calls += 1
        assert calls == 1 and boundary == ports.width
        return original(self, boundary)

    monkeypatch.setattr(SourceCarryPorts, "_first_prefix", single_growth)
    assert tuple(ports.iter_second_pairs()) == pair_sums(
        successor_digits(source.digits, 10)
    )
    assert calls == 1
    ports.dispose()


def test_neutral_region_stream_propagates_identity_without_ancestor_search() -> None:
    width = 1024
    ledger = ResourceLedger()
    ports = SourceCarryPorts(ExactSource((4,) * 512 + (5,) * 512, 10), ledger)
    assert ports.terminal == 0
    before = dict(ledger.counters)
    assert tuple(ports.iter_first_ports()) == ((0, 0),) * width
    assert tuple(ports.iter_first_ports(reflected=True)) == ((0, 0),) * width
    for counter in (
        "reverse_source_ports_identity_ancestor_probes",
        "reverse_source_pullback_pair_reads",
        "reverse_source_ports_prefix_blocks",
        "reverse_source_ports_layer_1_carry_queries",
    ):
        assert ledger.counters.get(counter, 0) == before.get(counter, 0)
    assert ledger.counters["reverse_source_ports_stream_region_visits"] == 4 * width - 2
    ports.dispose()


def test_regional_stream_budget_failure_releases_stack() -> None:
    ledger = ResourceLedger(max_nodes=1)
    ports = SourceCarryPorts(source_from_value(1593, 10), ledger)
    stream = ports.iter_first_ports()
    with pytest.raises(BlockContextBudgetExceeded):
        next(stream)
    account = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_workspace"
    )
    assert account.nodes == 0
    ports.dispose()
    assert ledger.nodes == ledger.entries == 0
