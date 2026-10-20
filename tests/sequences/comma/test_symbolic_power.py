"""Exact skew squaring consumes completed columns, never point trajectories."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Protocol, cast

import pytest

from devtools.verification.comma_b1_source_continuation import production_semantic_owner
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.comma import return_scope_observer, semantic_power
from number_compiler.sequences.comma.domain import canonical_offset_orbit
from number_compiler.sequences.comma.semantic_continuation import SemanticContinuation
from number_compiler.sequences.comma.semantic_power import SymbolicDecadePowers


class _PowerBinding(Protocol):
    labels: tuple[int, ...]


def _memo(powers: SymbolicDecadePowers, attribute: str) -> OwnedMemo[object, object]:
    return cast(OwnedMemo[object, object], object.__getattribute__(powers, attribute))


def _power_labels(
    powers: SymbolicDecadePowers, level: int, root: int
) -> tuple[int, ...]:
    view: Mapping[object, object] = _memo(powers, "_powers").audit_payload_view()
    return cast(_PowerBinding, view[level, root]).labels


def _workspace_owner(powers: SymbolicDecadePowers) -> int:
    owner = object.__getattribute__(powers, "_composition_workspace_owner")
    if type(owner) is not int:
        raise AssertionError("composition workspace owner is not an integer")
    return owner


def _lifecycle_flag(powers: SymbolicDecadePowers, name: str) -> bool:
    value = object.__getattribute__(powers, name)
    if type(value) is not bool:
        raise AssertionError("symbolic power lifecycle flag is not Boolean")
    return value


def _reference(
    view: SemanticContinuation, root: int, phase: int, span: int
) -> tuple[str, int]:
    for elapsed in range(span):
        identifier, _ = view.source_address(view.roots[root])
        action = view.evaluate_id(identifier, (phase + elapsed) % 924)
        if action.kind == "stop":
            assert action.stop_j is not None
            return "stop", 9 * elapsed + action.stop_j
        assert action.live_root is not None
        root = canonical_offset_orbit(action.live_root)
    return "live", root


@pytest.mark.validation
def test_completed_columns_square_without_point_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    view = production_semantic_owner()
    samples = tuple(
        (level, root, phase)
        for level in range(6)
        for root in (0, 7, 24, 45)
        for phase in (0, 1, 42, 460, 923)
    )
    expected = {
        sample: _reference(view, sample[1], sample[2], 1 << sample[0])
        for sample in samples
    }

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("symbolic square reopened point continuation")

    monkeypatch.setattr(SemanticContinuation, "evaluate_id", forbidden)
    monkeypatch.setattr(SemanticContinuation, "evaluate", forbidden)
    monkeypatch.setattr(SemanticFunctionArena, "__init__", forbidden)
    monkeypatch.setattr(return_scope_observer, "_legacy_rebase_result", forbidden)
    baseline_entries = view.ledger.entries
    baseline_nodes = view.ledger.nodes
    with SymbolicDecadePowers(view) as powers:
        powers.construct(0)
        monkeypatch.setattr(semantic_power, "canonical_return_template", forbidden)
        powers.construct(1)
        # B1 occurrence rebases are now settled. Higher powers must select
        # shifted right cofactors directly, without materializing translations.
        monkeypatch.setattr(semantic_power, "translate_return_columns", forbidden)
        for sample in samples:
            assert powers.evaluate(*sample) == expected[sample]
        # The sharp B32 stop: fiber 24, phase 42, Fork 5 at height 26.
        assert powers.evaluate(5, 24, 42) == ("stop", 9 * 26 + 3)
        powers.construct(5)
        b32_offsets = tuple(
            label - 46 for root in range(46) for label in _power_labels(powers, 5, root)
        )
        assert b32_offsets
        assert all(
            label >= 46
            for root in range(46)
            for label in _power_labels(powers, 5, root)
        )
        assert max(offset // 9 for offset in b32_offsets) == 26
        publications = view.ledger.counters["comma_power_publications"]
        substitution_states = view.ledger.counters["comma_power_substitution_states"]
        assert substitution_states > 0
        assert view.ledger.counters["comma_power_substitution_cofactors"] > 0
        assert "comma_power_column_joins" not in view.ledger.counters
        assert publications == 46 * 6
        column_id_hits = view.ledger.counters["comma_power_column_id_hits"]
        terminal_copies = view.ledger.counters["comma_power_absorbing_terminal_copies"]
        assert column_id_hits > 0
        assert terminal_copies > 0
        assert powers.evaluate(5, 24, 42) == ("stop", 237)
        assert view.ledger.counters["comma_power_publications"] == publications
        assert (
            view.ledger.counters["comma_power_substitution_states"]
            == substitution_states
        )
        assert view.ledger.counters["comma_power_column_id_hits"] == column_id_hits
        assert (
            view.ledger.counters["comma_power_absorbing_terminal_copies"]
            == terminal_copies
        )
    assert view.ledger.entries == baseline_entries
    assert view.ledger.nodes == baseline_nodes
    with pytest.raises(RuntimeError, match="closed"):
        powers.evaluate(0, 0, 0)


def test_symbolic_power_requires_complete_ordered_root_authority() -> None:
    view = production_semantic_owner(())
    before = view.ledger.owner_count
    with pytest.raises(ValueError, match="46 ordered canonical roots"):
        SymbolicDecadePowers(view)
    assert view.ledger.owner_count == before


def test_symbolic_power_owner_name_collision_preflights_without_inventory(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    view = production_semantic_owner()
    ledger = view.ledger
    next_prefix = ledger.owner_count + 1
    owner = ledger.register(
        f"comma-symbolic-powers-{next_prefix}-columns", "semantic_return_column"
    )
    ledger.make_dict(owner)
    before = ledger.owner_count

    def forbidden_inventory(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("owner-name preflight must not inventory ledger stores")

    monkeypatch.setattr(ledger, "inventory", forbidden_inventory)
    with pytest.raises(ValueError, match="owner name is already registered"):
        SymbolicDecadePowers(view)
    assert ledger.owner_count == before


def test_failed_symbolic_power_close_is_fail_closed_and_retryable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    view = production_semantic_owner()
    baseline_entries = view.ledger.entries
    baseline_nodes = view.ledger.nodes
    powers = SymbolicDecadePowers(view)
    owners = (
        _memo(powers, "_input_templates").owner,
        _memo(powers, "_powers").owner,
        _memo(powers, "_columns").owner,
        _memo(powers, "_base").owner,
        _workspace_owner(powers),
    )
    power_memo = _memo(powers, "_powers")
    dispose_powers = power_memo.dispose
    attempts = 0

    def fail_once() -> None:
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            raise RuntimeError("power memo cleanup failed")
        dispose_powers()

    monkeypatch.setattr(power_memo, "dispose", fail_once)
    with pytest.raises(RuntimeError, match="power memo cleanup failed"):
        powers.close()

    assert attempts == 1
    assert _lifecycle_flag(powers, "_closing")
    assert not _lifecycle_flag(powers, "_closed")
    assert view.ledger.inventory_owner(owners[0]).disposed
    assert not view.ledger.inventory_owner(owners[1]).disposed
    assert all(view.ledger.inventory_owner(owner).disposed for owner in owners[2:])
    with pytest.raises(RuntimeError, match="closing or closed"):
        powers.construct(0)
    with pytest.raises(RuntimeError, match="closing or closed"):
        powers.__enter__()

    monkeypatch.undo()
    powers.close()
    assert _lifecycle_flag(powers, "_closed")
    assert not _lifecycle_flag(powers, "_closing")
    assert all(view.ledger.inventory_owner(owner).disposed for owner in owners)
    assert view.ledger.entries == baseline_entries
    assert view.ledger.nodes == baseline_nodes


def test_symbolic_power_context_disposes_its_workspace_on_failure() -> None:
    view = production_semantic_owner()
    owner: int | None = None
    with (
        pytest.raises(ValueError, match="synthetic consumer failure"),
        SymbolicDecadePowers(view) as powers,
    ):
        owner = _workspace_owner(powers)
        raise ValueError("synthetic consumer failure")
    assert owner is not None
    with pytest.raises(RuntimeError, match="disposed"):
        view.ledger.registered_container(owner)
    powers.close()
