"""First-failure demands refine admitted cylinders without branch support replay."""

from collections.abc import Hashable

import pytest

from number_compiler.hashlife.execution import dyadic_return_observers as observers
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnActionID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
)
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnCycle
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
    AntihydraArithmeticImageWorkspace,
)


class SaturatedWorkspace(DyadicReturnImageWorkspace):
    def retain_chronological_support(self) -> bool:
        return False

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        if (
            demand in (None, SourceImageDemand("physical-summary"))
            and type(action) is DyadicReturnActionID
            and self.action_node(action).children is not None
            and source.binding.action == self.identity
        ):
            return self.complete_composite_candidate(action, source)
        return super().apply_composite(action, source, demand)


def assert_root_saturated(workspace: DyadicReturnImageWorkspace) -> None:
    support = workspace.summary().support
    assert support is not None
    node = workspace.support_node(support)
    assert node.saturated and node.children is None and node.branch_word is None


def reference_failure(law: DyadicReturnLaw, seed: int, width: int) -> int | None:
    balance, current = 0, seed
    for index in range(width):
        bit = current & 1
        balance += law.weights[bit]
        if balance < 0:
            return index
        current = (law.gains[bit] * current + law.offsets[bit]) // 2
    return None


def forbid_replay(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("first failure replayed source runs or expanded support")

    monkeypatch.setattr(observers, "_expanded_saturated_support", forbidden)
    monkeypatch.setattr(observers, "balanced_residue_macro", forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "_source_value", forbidden)
    monkeypatch.setattr(AntihydraArithmeticImageWorkspace, "_runs", forbidden)


@pytest.mark.parametrize("seed,width", [(1, 129), (1 << 70, 160), (1 << 80, 129)])
def test_saturated_failure_matches_retained_support_without_expansion(
    monkeypatch: pytest.MonkeyPatch, seed: int, width: int
) -> None:
    law = DyadicReturnLaw("failure-descent", "v1", (1, 1), (0, 1), (1, -1))
    retained = DyadicReturnImageWorkspace(ResourceLedger(), seed, width, law)
    ledger = ResourceLedger()
    saturated = SaturatedWorkspace(ledger, seed, width, law)
    assert_root_saturated(saturated)
    expected = reference_failure(law, seed, width)
    assert retained.first_failure_index() == expected
    before = (
        len(saturated.support),
        len(saturated.images),
        ledger.nodes,
        ledger.entries,
    )
    forbid_replay(monkeypatch)
    assert saturated.first_failure_index() == expected
    assert (
        len(saturated.support),
        len(saturated.images),
        ledger.nodes,
        ledger.entries,
    ) == before
    assert not saturated.demanded_support
    assert not saturated.macros
    assert not saturated.macro_stack and not saturated.balanced_stack
    if expected is not None:
        prefix = saturated.counter_prefix
        if expected == 0:
            assert ledger.counters.get(f"{prefix}_first_failure_refinements", 0) == 0
        else:
            assert ledger.counters[f"{prefix}_first_failure_refinements"] > 0
        assert 0 < ledger.counters[f"{prefix}_first_failure_leaf_steps"] <= 64


def test_first_symbol_failure_never_constructs_half_horizon(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = SaturatedWorkspace(ResourceLedger(), 7, 1024, ANTIHYDRA_ARITHMETIC_LAW)
    assert_root_saturated(workspace)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("first-symbol failure constructed a future effect")

    monkeypatch.setattr(observers, "balanced_residue_effect", forbidden)
    forbid_replay(monkeypatch)
    assert workspace.first_failure_index() == 0


@pytest.mark.parametrize("seed", [7, 8])
def test_antihydra_fixed_sources_use_shared_failure_demand(
    monkeypatch: pytest.MonkeyPatch, seed: int
) -> None:
    width = 129
    workspace = (
        AntihydraArithmeticImageWorkspace(ResourceLedger(), width)
        if seed == 8
        else SaturatedWorkspace(ResourceLedger(), seed, width, ANTIHYDRA_ARITHMETIC_LAW)
    )
    assert_root_saturated(workspace)
    expected = reference_failure(ANTIHYDRA_ARITHMETIC_LAW, seed, width)
    forbid_replay(monkeypatch)
    assert workspace.first_failure_index() == expected
    assert not workspace.demanded_support


def test_saturated_cycle_failure_skips_safe_prefix_without_support_expansion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    law = DyadicReturnLaw(
        "failure-cycle", "v1", (1, 1), (0, 1), (1, -1), DyadicReturnCycle((1,))
    )
    seed, width = 1 << 70, 1024
    workspace = SaturatedWorkspace(ResourceLedger(), seed, width, law)
    assert_root_saturated(workspace)
    assert workspace.summary().cycle is not None
    forbid_replay(monkeypatch)
    assert workspace.first_failure_index() == reference_failure(law, seed, width) == 140
    assert not workspace.demanded_support


@pytest.mark.parametrize("width", [274, 275, 276])
def test_cycle_failure_preserves_phase_and_partial_copy(
    monkeypatch: pytest.MonkeyPatch, width: int
) -> None:
    law = DyadicReturnLaw(
        "failure-rotated-cycle",
        "v1",
        (1, 6),
        (0, 2),
        (1, -3),
        DyadicReturnCycle((1, 4, 2)),
    )
    seed = 1 << 70
    workspace = SaturatedWorkspace(ResourceLedger(), seed, width, law)
    assert_root_saturated(workspace)
    cycle = workspace.summary().cycle
    assert cycle is not None and cycle.cycle_phase == 1
    assert cycle.remainder == (width - cycle.entry_steps) % 3
    expected = reference_failure(law, seed, width)
    assert expected == (274 if width >= 275 else None)
    forbid_replay(monkeypatch)
    assert workspace.first_failure_index() == expected
    assert not workspace.demanded_support


def test_saturated_descent_releases_work_after_transport_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    law = DyadicReturnLaw("failure-cleanup", "v1", (1, 1), (0, 1), (1, -1))
    ledger = ResourceLedger()
    workspace = SaturatedWorkspace(ledger, 1 << 70, 160, law)
    assert_root_saturated(workspace)
    before = ledger.nodes, ledger.entries

    def fail(*args: object, **kwargs: object) -> None:
        raise ArithmeticError("injected demanded transport failure")

    monkeypatch.setattr(observers, "transport_low", fail)
    with pytest.raises(ArithmeticError, match="injected demanded transport"):
        workspace.first_failure_index()
    assert (ledger.nodes, ledger.entries) == before
    assert not workspace.macros
    assert not workspace.macro_stack and not workspace.balanced_stack
