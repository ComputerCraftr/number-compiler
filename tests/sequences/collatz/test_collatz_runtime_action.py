from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
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


@pytest.mark.parametrize(("power", "steps"), ((2, 0), (5, 2), (8, 3), (12, 7)))
def test_collatz_public_queries_keep_distinct_exact_durations(
    power: int,
    steps: int,
) -> None:
    source = 1 << power

    before_one = PoweredCollatzTerm(source, steps).materialize(max_bits=power + 1)
    at_one = PoweredCollatzTerm(source, power).materialize(max_bits=power + 1)

    assert before_one == 1 << (power - steps)
    assert at_one == 1
    assert before_one != at_one


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
    assert arena.semantic_identity("output", second) != arena.semantic_identity(
        "output", third_left
    )
    assert arena.composed_semantic_identity(
        "output", second, atom
    ) == arena.semantic_identity("output", third_left)


def test_runtime_program_identity_encodes_and_memoizes_huge_exact_exponents() -> None:
    arena = CollatzRuntimeProgramArena(ResourceLedger())
    exponent = 10**5000

    first = arena._semantic_identity_for("output", exponent)
    hits_before = arena.ledger.counters.get("collatz_runtime_identity_cache_hits", 0)
    second = arena._semantic_identity_for("output", exponent)
    next_power = arena._semantic_identity_for("output", exponent + 1)

    assert first is second
    assert first != next_power
    descriptor = first.behavior[2]
    assert type(descriptor) is tuple
    assert descriptor[0] == "exact-exponent-u64-v1"
    assert descriptor[1] == exponent.bit_length()
    limbs = descriptor[2]
    assert type(limbs) is tuple
    assert all(type(limb) is int and limb.bit_length() <= 64 for limb in limbs)
    assert sum(limb << (64 * offset) for offset, limb in enumerate(limbs)) == exponent
    assert (
        arena.ledger.counters["collatz_runtime_identity_cache_hits"] == hits_before + 1
    )
    assert arena.ledger.counters["collatz_runtime_identity_retained_limb_bytes"] == (
        8 * len(limbs) * 2
    )
    rows = {
        row.role: row
        for row in arena.ledger.inventory()
        if row.role == "semantic_identity_cache"
    }
    assert len(rows) == 1
    row = next(iter(rows.values()))
    assert row.entries == 2
    next_limb_count = ((exponent + 1).bit_length() + 63) // 64
    assert row.observed_nodes == 2 + len(limbs) + next_limb_count


def test_runtime_program_identity_cache_hit_checks_seal_without_redigest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = CollatzRuntimeProgramArena(ResourceLedger())
    identity = arena._semantic_identity_for("output", 13)

    def forbidden(*_args: object, **_kwargs: object) -> str:
        pytest.fail("trusted semantic identity cache hit rehashed its behavior")

    monkeypatch.setattr(SemanticIdentity, "_canonical_digest", forbidden)
    assert arena._semantic_identity_for("output", 13) is identity

    object.__setattr__(identity, "digest", "0" * 64)
    with pytest.raises(ValueError, match="lost its seal"):
        arena._semantic_identity_for("output", 13)


def test_runtime_program_identity_cache_rejects_cross_exponent_record_reuse() -> None:
    arena = CollatzRuntimeProgramArena(ResourceLedger())
    arena._semantic_identity_for("output", 13)
    arena._semantic_identity_for("output", 14)
    records = arena._semantic_identities
    records._data["output", 14] = records["output", 13]

    with pytest.raises(ValueError, match="malformed cached Collatz semantic identity"):
        arena._semantic_identity_for("output", 14)


def test_collatz_identity_cache_rejects_coherent_forged_same_width_limbs() -> None:
    arena = CollatzRuntimeProgramArena(ResourceLedger())
    one = arena.primitive("output")
    two = arena.compose("output", one, one)
    four = arena.compose("output", two, two)
    eight = arena.compose("output", four, four)
    twelve = arena.compose("output", eight, four)
    reference = arena.compose("output", twelve, one)
    arena.semantic_identity("output", reference)
    forged_behavior = (
        "collatz-runtime-program-v2-binary-exponent",
        "output",
        ("exact-exponent-u64-v1", 4, (14,)),
    )
    forged = SemanticIdentity("", forged_behavior)
    arena._semantic_identities._data["output", 13] = (
        forged,
        forged.digest,
        forged.behavior,
        13,
    )

    with pytest.raises(ValueError, match="malformed cached Collatz semantic identity"):
        arena.semantic_identity("output", reference)


@pytest.mark.parametrize("after_insert", (False, True))
def test_collatz_identity_publication_rolls_back_both_stores(
    monkeypatch: pytest.MonkeyPatch,
    after_insert: bool,
) -> None:
    from tests.support.ledger_failures import inject_write_once_failure

    ledger = ResourceLedger()
    arena = CollatzRuntimeProgramArena(ledger)
    before = ledger.snapshot()
    inject_write_once_failure(
        monkeypatch,
        arena._semantic_identity_authority,
        after_insert=after_insert,
    )

    with pytest.raises(RuntimeError, match="issued-store publication failure"):
        arena._semantic_identity_for("output", 13)

    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert not arena._semantic_identities
    assert not arena._semantic_identity_authority
    assert arena._identity_storage_nodes == 0


def test_runtime_program_identity_budget_refusal_precedes_limb_allocation() -> None:
    ledger = ResourceLedger(max_nodes=1, max_cache_entries=1)
    arena = CollatzRuntimeProgramArena(ledger)
    before = ledger.snapshot()

    with pytest.raises(BlockContextBudgetExceeded):
        arena._semantic_identity_for("output", 1 << 128)

    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert len(arena._semantic_identities) == 0
    assert "collatz_runtime_identity_transient_byte_work" not in after.counters


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
