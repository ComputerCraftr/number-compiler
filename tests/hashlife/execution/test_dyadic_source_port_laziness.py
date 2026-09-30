"""Cycle admission and cylinder splitting do not assemble unused exact sources."""

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.physical_images import (
    COLLATZ_PHYSICAL_LAW,
    CollatzPhysicalImageWorkspace,
)


def _forbid_source_assembly(*_args: object) -> int:
    raise AssertionError("unused full source was assembled")


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
def test_balanced_large_source_does_not_assemble_tracking_value(
    law: object, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw

    assert isinstance(law, DyadicReturnLaw)
    seed, steps = (1 << 4096) + 27, 129
    monkeypatch.setattr(
        DyadicReturnImageWorkspace, "_source_value", _forbid_source_assembly
    )
    workspace = (
        CollatzPhysicalImageWorkspace(ResourceLedger(), seed, steps)
        if law == COLLATZ_PHYSICAL_LAW
        else DyadicReturnImageWorkspace(ResourceLedger(), seed, steps, law)
    )
    summary = workspace.summary()
    expected = seed
    for _ in range(steps):
        branch = expected & 1
        expected = (law.gains[branch] * expected + law.offsets[branch]) // 2
    numerator = summary.transfer.upper * seed + summary.transfer.offset
    assert numerator % summary.transfer.lower == 0
    assert numerator // summary.transfer.lower == expected


def test_cycle_membership_uses_source_ports(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        DyadicReturnImageWorkspace, "_source_value", _forbid_source_assembly
    )
    workspace = DyadicReturnImageWorkspace(
        ResourceLedger(), 1, 10**12, COLLATZ_PHYSICAL_LAW
    )
    summary = workspace.summary()
    assert summary.transfer.upper == 0
    assert summary.transfer.offset == 4
    assert summary.cycle is not None
    assert workspace.ledger.counters["collatz_physical_cycle_source_comparisons"] > 0


def test_cycleless_first_child_never_constructs_parent_integer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        DyadicReturnImageWorkspace, "_source_value", _forbid_source_assembly
    )
    workspace = DyadicReturnImageWorkspace(
        ResourceLedger(), (1 << 4096) + 27, 129, ANTIHYDRA_ARITHMETIC_LAW
    )
    children = workspace.action_node(workspace.root_action).children
    assert children is not None
    core = workspace.scheduler._source_image_core()
    parent = core.view(core._origin(workspace, workspace.root_source))
    child = workspace.first_child_source(workspace.root_action, parent, *children)
    node = workspace.source_node(child)
    assert not node.exact
    assert node.lift == 0
    assert node.residue == 27


def test_public_mixed_collatz_skips_unused_exact_source_assembly(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    seed = (1 << 4096) + 27
    expected = seed
    for _ in range(129):
        expected = 3 * expected + 1 if expected & 1 else expected // 2
    monkeypatch.setattr(
        DyadicReturnImageWorkspace, "_source_value", _forbid_source_assembly
    )
    term = PoweredCollatzTerm(seed, 129)
    assert term.materialize(max_bits=8192) == expected
    assert term._ledger.counters["collatz_physical_temporal_balanced_routes"] == 1
