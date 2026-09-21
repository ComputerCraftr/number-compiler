"""Bounded spatial normalization of neutral source carry intervals."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import (
    SourceCarryPorts,
    _QueryWorkspace,
)


def _neutral_source(width: int) -> ExactSource:
    if width < 2 or width % 2:
        raise ValueError("neutral test source requires a positive even width")
    return ExactSource(
        (4,) * (width // 2) + (5,) * (width // 2),
        10,
        orbit="reverse-add",
    )


def test_neutral_ranges_match_literal_carry_oracle_after_normalization() -> None:
    width = 64
    ports = SourceCarryPorts(_neutral_source(width), ResourceLedger())
    assert ports.range_transfer(1, 0, width) is CarryFn.ID
    for start, stop in ((0, 0), (0, 1), (3, 19), (16, 48), (63, 64)):
        effect = ports.range_transfer(1, start, stop)
        for incoming in (0, 1):
            expected = incoming
            for _position in range(start, stop):
                expected = int(9 + expected >= 10)
            assert apply_carry_fn(effect, incoming) == expected


def test_warm_identity_ancestor_answers_points_without_source_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    width = 128
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_neutral_source(width), ledger)
    assert ports.range_transfer(1, 0, width) is CarryFn.ID
    probes = ledger.counters.get("reverse_source_ports_identity_ancestor_probes", 0)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("identity restriction descended to a source pair")

    monkeypatch.setattr(SourceCarryPorts, "_raw_first_pair", forbidden)
    assert ports.range_transfer(1, 37, 38) is CarryFn.ID
    assert ledger.counters["reverse_source_ports_identity_ancestor_probes"] > probes
    assert ledger.counters["reverse_source_ports_identity_ancestor_hits"] >= 1


def test_reset_ancestor_is_never_inherited_by_a_subinterval(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = ExactSource((9,) * 16, 10, orbit="reverse-add")
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    assert ports.range_transfer(1, 0, 16) is CarryFn.CONST1

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("proper reset subinterval required source discovery")

    monkeypatch.setattr(SourceCarryPorts, "_raw_first_pair", forbidden)
    with pytest.raises(AssertionError, match="required source discovery"):
        ports.range_transfer(1, 0, 1)
    assert ledger.counters["reverse_source_ports_reset_ancestor_rejections"] >= 1


def test_identity_cache_is_layer_scoped(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ports = SourceCarryPorts(_neutral_source(32), ResourceLedger())
    assert ports.range_transfer(1, 0, 32) is CarryFn.ID

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("layer two inherited a layer-one identity")

    monkeypatch.setattr(SourceCarryPorts, "_raw_second_pair", forbidden)
    with pytest.raises(AssertionError, match="layer two inherited"):
        ports.range_transfer(2, 0, 1)


def test_whole_neutral_interval_retains_only_its_normalized_root() -> None:
    width = 256
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_neutral_source(width), ledger)
    assert ports.range_transfer(1, 0, width) is CarryFn.ID
    assert dict(ports._cache) == {(1, 0, width): CarryFn.ID}
    account = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_interval"
    )
    assert account.entries == account.nodes == 1
    assert ledger.counters["reverse_source_ports_identity_children_pruned"] > 0
    # Inner cold construction uses exact child probes; ancestor probes occur
    # only at the requested dyadic boundary.
    assert ledger.counters.get("reverse_source_ports_identity_ancestor_probes", 0) == 0


def test_failed_parent_normalization_preserves_preexisting_identity_child(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_neutral_source(8), ledger)
    assert ports.range_transfer(1, 0, 2) is CarryFn.ID
    before = ledger.snapshot()
    original = SourceCarryPorts._publish

    def fail_after_pruning_is_staged(
        self: SourceCarryPorts,
        workspace: _QueryWorkspace,
        key: tuple[int, int, int],
        result: CarryFn,
    ) -> None:
        original(self, workspace, key, result)
        if key == (1, 0, 4):
            raise BlockContextBudgetExceeded("forced normalization refusal")

    monkeypatch.setattr(SourceCarryPorts, "_publish", fail_after_pruning_is_staged)
    with pytest.raises(BlockContextBudgetExceeded, match="forced normalization"):
        ports.range_transfer(1, 0, 8)
    assert dict(ports._cache) == {(1, 0, 2): CarryFn.ID}
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
    workspace = next(
        item
        for item in ledger.inventory()
        if item.role == "reverse_source_carry_workspace"
    )
    assert workspace.entries == workspace.nodes == 0
