from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.field_action import ProgramRole
from number_compiler.sequences.collatz.runtime_action import (
    build_collatz_runtime_action,
)
from number_compiler.sequences.collatz.runtime_programs import (
    CollatzRuntimeProgram,
    CollatzRuntimeProgramArena,
)


@pytest.mark.parametrize("steps", (True, 1.0))
def test_collatz_runtime_action_rejects_numeric_step_aliases(steps: object) -> None:
    ledger = ResourceLedger()
    before = ledger.snapshot()
    with pytest.raises(TypeError):
        build_collatz_runtime_action(cast(int, steps), ledger)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_collatz_runtime_action_is_logarithmic_and_has_no_proof_states() -> None:
    for steps in (1, 2, 4, 8, 16, 32, 64, 256):
        ledger = ResourceLedger()
        bundle = build_collatz_runtime_action(steps, ledger)
        output = bundle.actions.resolve(bundle.powered).output_morphism
        assert bundle.programs.resolve(output).exponent == steps
        assert bundle.actions.metrics.composition_evaluations <= steps.bit_length() + 1
        assert bundle.actions.metrics.composition_early_hits == 0
        assert (
            ledger.counters.get("collatz_field_action_late_duplicate_reductions", 0)
            == 0
        )
        assert len(bundle.programs.nodes) <= 6 * (steps.bit_length() + 2)
        assert bundle.defects.class_count == 1
        assert all("proof" not in item.role for item in ledger.inventory())
        assert ledger.counters.get("proof_machine_applications", 0) == 0
        assert ledger.counters.get("sequential_generation_advances", 0) == 0


def test_collatz_field_action_semantics_do_not_use_local_integer_ordinals() -> None:
    first = build_collatz_runtime_action(19, ResourceLedger())
    second = build_collatz_runtime_action(19, ResourceLedger())

    assert first.powered.owner != second.powered.owner
    assert first.actions.semantic_identity(first.powered) == (
        second.actions.semantic_identity(second.powered)
    )
    with pytest.raises(TypeError):
        first.actions.semantic_identity(cast(FieldCellActionID, first.powered.local_id))
    with pytest.raises(TypeError):
        first.actions.semantic_identity(cast(FieldCellActionID, True))
    with pytest.raises(TypeError):
        first.actions.semantic_identity(cast(FieldCellActionID, 1.0))
    with pytest.raises(ValueError):
        first.actions.semantic_identity(second.powered)


def test_collatz_runtime_programs_validate_scope_sort_and_role_before_hits() -> None:
    with pytest.raises(ValueError, match="unknown Collatz"):
        CollatzRuntimeProgram(cast(ProgramRole, "bogus"), 0)
    arena = CollatzRuntimeProgramArena(ResourceLedger())
    root = arena.primitive("root")
    output = arena.primitive("output")
    assert arena.compose("output", output, output) is arena.compose(
        "output",
        output,
        output,
    )
    with pytest.raises(ValueError):
        arena.compose("output", root, output)
    with pytest.raises(ValueError):
        arena.validate("root", output)
    with pytest.raises(ValueError):
        arena.resolve(ActionProgramID(ArenaToken("foreign"), root.kind, root.local_id))
    with pytest.raises(TypeError):
        arena.resolve(cast(ActionProgramID, True))


def test_runtime_programs_canonicalize_equal_powers_before_publication() -> None:
    arena = CollatzRuntimeProgramArena(ResourceLedger())
    atom = arena.primitive("output")
    second = arena.compose("output", atom, atom)
    third_left = arena.compose("output", second, atom)
    third_right = arena.compose("output", atom, second)

    assert third_left == third_right
    assert arena.resolve(third_left).exponent == 3
    assert arena.semantic_identity("output", third_left) == arena.semantic_identity(
        "output",
        third_right,
    )


def test_runtime_program_semantics_are_source_free_and_owner_independent() -> None:
    first = CollatzRuntimeProgramArena(ResourceLedger())
    second = CollatzRuntimeProgramArena(ResourceLedger())
    first_power = first.compose(
        "root", first.primitive("root"), first.primitive("root")
    )
    second_power = second.compose(
        "root",
        second.primitive("root"),
        second.primitive("root"),
    )

    assert first_power.owner != second_power.owner
    assert first.semantic_identity("root", first_power) == second.semantic_identity(
        "root",
        second_power,
    )
    for alias in (first_power.local_id, True, 1.0):
        with pytest.raises(TypeError):
            first.semantic_identity("root", cast(ActionProgramID, alias))


def test_collatz_runtime_program_budget_failure_is_atomic() -> None:
    ledger = ResourceLedger(max_nodes=1, max_cache_entries=2)
    arena = CollatzRuntimeProgramArena(ledger)
    arena.identity("output")
    before = ledger.snapshot()
    with pytest.raises(RuntimeError):
        arena.primitive("output")
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert arena.nodes == (arena.resolve(arena.identity("output")),)


def test_collatz_runtime_program_stores_are_independently_inventoried() -> None:
    ledger = ResourceLedger()
    arena = CollatzRuntimeProgramArena(ledger)
    primitive = arena.primitive("output")
    arena.compose("output", primitive, primitive)
    rows = {
        row.role: row
        for row in ledger.inventory()
        if row.role
        in {
            "action_program",
            "action_program_interner",
            "action_construction_metadata",
        }
    }
    assert rows.keys() == {
        "action_program",
        "action_program_interner",
        "action_construction_metadata",
    }
    assert rows["action_program"].observed_nodes == len(arena.nodes)
    assert rows["action_construction_metadata"].composition_entries == 1
    assert all(
        row.entries == row.observed_entries
        and row.payloads_registered
        and not row.evictable
        for row in rows.values()
    )
