"""Bounded differential checks for the modeled dyadic postorder constructor.

These tests compare the published effect with an independent literal branch
reference. They are evidence for a refinement mapping, not a Python proof.
"""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnLaw,
    DyadicReturnSupportID,
    _SupportNode,
)
from number_compiler.hashlife.execution.dyadic_return_transport import (
    balanced_residue_effect,
    balanced_residue_macro,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.physical_images import COLLATZ_PHYSICAL_LAW


def _literal(
    law: DyadicReturnLaw, source: int, width: int
) -> tuple[int, int, int, int, int]:
    """Use only the two integer branch formulas, without production actions."""
    value, branch_word, odd_steps, delta, minimum = source, 0, 0, 0, 0
    for index in range(width):
        bit = value % 2
        branch_word |= bit << index
        odd_steps += bit
        delta += law.weights[bit]
        minimum = min(minimum, delta)
        numerator = law.gains[bit] * value + law.offsets[bit]
        assert numerator % 2 == 0
        value = numerator // 2
    return value, branch_word, odd_steps, delta, minimum


def _assert_physical_effect(effect: _SupportNode, residue: int, width: int) -> None:
    endpoint, _word, odd_steps, delta, minimum = _literal(
        COLLATZ_PHYSICAL_LAW, residue, width
    )
    transfer = effect.transfer
    assert (transfer.upper * residue + transfer.offset) // transfer.lower == endpoint
    assert (effect.odd_steps, effect.delta, effect.minimum) == (
        odd_steps,
        delta,
        minimum,
    )


def _retained_word(
    workspace: DyadicReturnImageWorkspace, root: DyadicReturnSupportID
) -> int:
    """Flatten bounded leaves solely to check a retained support DAG."""
    pending = [root]
    offset = word = 0
    while pending:
        node = workspace.support_node(pending.pop())
        if node.children is not None:
            left, right = node.children
            pending.extend((right, left))
            continue
        assert node.branch_word is not None
        word |= node.branch_word << offset
        offset += node.width
    assert offset == workspace.support_node(root).width
    return word


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
@pytest.mark.parametrize("width", (1, 3, 64, 65, 97, 128, 129, 257))
@pytest.mark.parametrize("retain", (False, True))
def test_balanced_effect_matches_literal_fibers_and_safety(
    law: DyadicReturnLaw, width: int, retain: bool
) -> None:
    """Exercise unequal splits, the leaf boundary, and discarded high fibers."""
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 0, 0, law)
    residue = (1 << width) // 3 + 1
    if retain:
        support = balanced_residue_macro(workspace, width, residue)
        effect = workspace.support_node(support)
        retained_word = _retained_word(workspace, support)
    else:
        effect = balanced_residue_effect(workspace, width, residue)
        assert effect.children is None
        assert effect.saturated == (width > workspace.MAX_LEAF_STEPS)
        retained_word = None
    assert (effect.width, effect.residue) == (width, residue)
    for high in (0, 1, (1 << 73) + 5):
        source = residue + (high << width)
        endpoint, word, odd_steps, delta, minimum = _literal(law, source, width)
        transfer = effect.transfer
        numerator = transfer.upper * source + transfer.offset
        assert numerator % transfer.lower == 0
        assert numerator // transfer.lower == endpoint
        assert (effect.odd_steps, effect.delta, effect.minimum) == (
            odd_steps,
            delta,
            minimum,
        )
        if retained_word is not None:
            assert retained_word == word
        elif width <= workspace.MAX_LEAF_STEPS:
            assert effect.branch_word == word
    assert not workspace.balanced_stack
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_balanced_memo_reuses_exact_subcylinders_without_retaining_entries() -> None:
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 0, 0, COLLATZ_PHYSICAL_LAW)
    effect = balanced_residue_effect(workspace, 1024, 0)
    assert effect.transfer.offset == 0
    counters = ledger.counters
    prefix = workspace.counter_prefix + "_"
    assert counters[prefix + "balanced_effect_memo_hits"] > 0
    assert counters[prefix + "transient_leaf_steps"] <= 64
    assert counters[prefix + "reused_temporal_extent"] >= 960
    assert not workspace.balanced_stack
    assert ledger.inventory()[workspace.balanced_stack_owner].entries == 0
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_balanced_memo_eviction_preserves_high_entropy_effect() -> None:
    width = 2049  # More than 64 distinct postorder nodes, including the root.
    residue = Random(0xC011A72).getrandbits(width) | (1 << (width - 1))
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 0, 0, COLLATZ_PHYSICAL_LAW)
    effect = balanced_residue_effect(workspace, width, residue)
    _assert_physical_effect(effect, residue, width)
    assert (
        ledger.counters[workspace.counter_prefix + "_balanced_effect_memo_evictions"]
        > 0
    )
    assert ledger.inventory()[workspace.balanced_stack_owner].entries == 0
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_optional_balanced_memo_refusal_keeps_exact_result() -> None:
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 0, 0, ANTIHYDRA_ARITHMETIC_LAW)
    baseline = ledger.nodes, ledger.entries
    ledger.max_nodes = ledger.nodes + 1
    effect = balanced_residue_effect(workspace, 65, 5)
    endpoint, _word, odd_steps, delta, minimum = _literal(
        ANTIHYDRA_ARITHMETIC_LAW, 5, 65
    )
    transfer = effect.transfer
    assert (transfer.upper * 5 + transfer.offset) // transfer.lower == endpoint
    assert (effect.odd_steps, effect.delta, effect.minimum) == (
        odd_steps,
        delta,
        minimum,
    )
    assert (ledger.nodes, ledger.entries) == baseline
    assert not workspace.balanced_stack
    ledger.max_nodes = None
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_full_balanced_memo_evicts_before_optional_reserve_refusal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A refused cache insertion after FIFO eviction cannot change the effect."""
    width = 2049
    residue = Random(0xF1F0).getrandbits(width) | (1 << (width - 1))
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 0, 0, COLLATZ_PHYSICAL_LAW)
    prefix = workspace.counter_prefix + "_"
    original_reserve = ledger.reserve
    refused = False

    def refuse_after_first_eviction(
        owner: int, entries: int = 0, nodes: int = 0
    ) -> None:
        nonlocal refused
        if (
            owner == workspace.balanced_stack_owner
            and ledger.counters.get(prefix + "balanced_effect_memo_evictions", 0)
            and not refused
        ):
            refused = True
            raise BlockContextBudgetExceeded("injected optional memo refusal")
        original_reserve(owner, entries=entries, nodes=nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "reserve", refuse_after_first_eviction)
        effect = balanced_residue_effect(workspace, width, residue)
    assert refused
    assert ledger.counters[prefix + "balanced_effect_memo_evictions"] > 0
    _assert_physical_effect(effect, residue, width)
    assert ledger.inventory()[workspace.balanced_stack_owner].entries == 0
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0
