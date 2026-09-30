"""Finite-cylinder arithmetic is shared, exact on high fibers, and ephemeral."""

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw
from number_compiler.hashlife.execution.dyadic_return_transport import (
    _residue_effect,
    balanced_residue_effect,
    residue_macro,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.physical_images import COLLATZ_PHYSICAL_LAW
from tests.support.reference_arithmetic import literal_dyadic_orbit


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
def test_all_finite_residues_match_every_branch_and_high_fiber(
    law: DyadicReturnLaw, monkeypatch: pytest.MonkeyPatch
) -> None:
    law = replace(law, cycle=None)
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, law)

    def forbidden(*args: object) -> int:
        raise AssertionError("finite arithmetic read a source endpoint")

    monkeypatch.setattr(workspace, "_source_value", forbidden)
    for width in range(1, 9):
        for residue in range(1 << width):
            transient = _residue_effect(workspace, width, residue)
            retained = workspace.support_node(residue_macro(workspace, width, residue))
            assert transient == retained
            for lift in (0, 1, (1 << 97) + 5):
                source = residue + (lift << width)
                value, word, odd, delta, minimum = literal_dyadic_orbit(
                    source, width, law
                )
                transfer = transient.transfer
                numerator = transfer.upper * source + transfer.offset
                assert numerator % transfer.lower == 0
                assert numerator // transfer.lower == value
                assert (
                    transient.branch_word,
                    transient.odd_steps,
                    transient.delta,
                    transient.minimum,
                ) == (word, odd, delta, minimum)
            assert not workspace.macros
    workspace.dispose()
    assert workspace.ledger.nodes == workspace.ledger.entries == 0


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
def test_large_effect_reuses_finite_atoms_without_retained_cache(
    law: DyadicReturnLaw, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, law)
    initial = workspace.ledger.nodes, workspace.ledger.entries
    original = workspace._bump
    observed: set[int] = set()

    def inspect(suffix: str, amount: int = 1) -> None:
        if suffix == "finite_block_publications":
            assert len(workspace.macros) <= 256
            for owner, descriptor, width, residue in workspace.macros:
                assert owner is workspace.owner
                assert descriptor == law.descriptor
                assert type(width) is int and type(residue) is int
                assert 0 < width <= 8 and 0 <= residue < 1 << width
                observed.add(width)
        original(suffix, amount)

    monkeypatch.setattr(workspace, "_bump", inspect)
    width = 1024
    source = (1 << width) // 3
    effect = balanced_residue_effect(workspace, width, source)
    value = source
    for _ in range(width):
        bit = value & 1
        value = (law.gains[bit] * value + law.offsets[bit]) // 2
    assert (
        effect.transfer.upper * source + effect.transfer.offset
    ) // effect.transfer.lower == value
    prefix = workspace.counter_prefix + "_"
    assert workspace.ledger.counters[prefix + "finite_block_hits"] > 0
    assert workspace.ledger.counters[prefix + "finite_block_cold_steps"] < width
    assert 4 in observed and 8 in observed
    assert (
        not workspace.macros
        and not workspace.macro_stack
        and not workspace.balanced_stack
    )
    assert (workspace.ledger.nodes, workspace.ledger.entries) == initial
    workspace.dispose()


def test_finite_cache_failure_cleanup_and_foreign_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, COLLATZ_PHYSICAL_LAW)
    other = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, ANTIHYDRA_ARITHMETIC_LAW)
    original = workspace._bump
    initial = workspace.ledger.nodes, workspace.ledger.entries

    def reject(suffix: str, amount: int = 1) -> None:
        if suffix == "finite_block_publications":
            raise MemoryError("finite publication failure")
        original(suffix, amount)

    with monkeypatch.context() as patch:
        patch.setattr(workspace, "_bump", reject)
        with pytest.raises(MemoryError, match="finite publication"):
            balanced_residue_effect(workspace, 129, 19)
    assert (
        not workspace.macros
        and not workspace.macro_stack
        and not workspace.balanced_stack
    )
    assert (workspace.ledger.nodes, workspace.ledger.entries) == initial
    support = residue_macro(workspace, 8, 19)
    with pytest.raises(ValueError):
        other.support_node(support)
    with monkeypatch.context() as patch:
        patch.setattr(workspace, "law", ANTIHYDRA_ARITHMETIC_LAW)
        with pytest.raises(ValueError):
            _residue_effect(workspace, 8, 19)
    workspace.dispose()
    with pytest.raises(ValueError):
        _residue_effect(workspace, 8, 19)
    other.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_finite_memo_eviction_and_scope_cleanup() -> None:
    from number_compiler.hashlife.execution.dyadic_return_transport import (
        _clear_finite_memo,
    )

    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, COLLATZ_PHYSICAL_LAW)
    initial = workspace.ledger.nodes, workspace.ledger.entries
    try:
        for residue in range(256):
            effect = _residue_effect(workspace, 8, residue, keep_memo=True)
            value = residue
            for _ in range(8):
                value = 3 * value + 1 if value & 1 else value // 2
            transfer = effect.transfer
            assert (
                transfer.upper * residue + transfer.offset
            ) // transfer.lower == value
            assert len(workspace.macros) <= 256
            inventory = workspace.ledger.inventory()[workspace.macro_owner]
            assert inventory.entries == inventory.nodes == len(workspace.macros)
        assert len(workspace.macros) == 256
        assert (
            workspace.ledger.counters[
                workspace.counter_prefix + "_finite_block_evictions"
            ]
            > 0
        )
        # Entries are acceleration state, never a new independently reusable
        # public source. A second unscoped call rejects the unfinished scope.
        with pytest.raises(RuntimeError, match="unfinished"):
            _residue_effect(workspace, 8, 0)
    finally:
        _clear_finite_memo(workspace)
    assert (workspace.ledger.nodes, workspace.ledger.entries) == initial
    assert not workspace.macros
    workspace.dispose()
    assert workspace.ledger.nodes == workspace.ledger.entries == 0
