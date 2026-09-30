from __future__ import annotations

from dataclasses import fields
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.character import CollatzRadialCharacter
from number_compiler.sequences.collatz.field_action import (
    CollatzActionGeometry,
    CollatzCharacterAction,
    CollatzCocyclePrograms,
    CollatzDefectArena,
    CollatzDefectClassID,
    CollatzFieldAction,
    CollatzFieldActionArena,
    CollatzFieldActionID,
    ProgramRole,
    bounded_3adic_innovation,
)
from tests.support.assertions import assert_associative


class _FinitePrograms:
    """Small noncommuting symbolic algebra used only by carrier tests."""

    def __init__(self) -> None:
        self.owner = ArenaToken("test-collatz-symbolic-programs")
        self._values: list[tuple[ProgramRole, tuple[int, int, int, int]]] = []
        self._ids: dict[tuple[ProgramRole, tuple[int, int, int, int]], int] = {}
        self._identities = {
            role: self.atom(role, (1, 0, 0, 1))
            for role in (
                "root",
                "affine",
                "output",
                "physical-tick",
                "valuation",
                "frame",
            )
        }

    @staticmethod
    def _multiply(
        first: tuple[int, int, int, int],
        second: tuple[int, int, int, int],
    ) -> tuple[int, int, int, int]:
        a, b, c, d = first
        e, f, g, h = second
        return (e * a + f * c, e * b + f * d, g * a + h * c, g * b + h * d)

    def atom(
        self, role: ProgramRole, value: tuple[int, int, int, int]
    ) -> ActionProgramID:
        key = (role, value)
        found = self._ids.get(key)
        if found is None:
            found = len(self._values)
            self._ids[key] = found
            self._values.append(key)
        return ActionProgramID(self.owner, "test-symbolic-" + role, found)

    def identity(self, role: ProgramRole) -> ActionProgramID:
        return self._identities[role]

    def validate(self, role: ProgramRole, reference: ActionProgramID) -> int:
        if type(reference) is not ActionProgramID:
            raise TypeError(reference)
        reference.validate(self.owner, "test-symbolic-" + role, size=len(self._values))
        stored_role, _value = self._values[reference.local_id]
        if stored_role != role:
            raise ValueError(reference)
        return reference.local_id

    def semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity:
        index = self.validate(role, reference)
        behavior = ("test-collatz-matrix-program-v1", role, self._values[index][1])
        return SemanticIdentity("", behavior)

    def composed_semantic_identity(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> SemanticIdentity:
        first, second = self.validate(role, before), self.validate(role, after)
        behavior = (
            "test-collatz-matrix-program-v1",
            role,
            self._multiply(self._values[first][1], self._values[second][1]),
        )
        return SemanticIdentity("", behavior)

    def compose(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> ActionProgramID:
        first, second = self.validate(role, before), self.validate(role, after)
        return self.atom(
            role, self._multiply(self._values[first][1], self._values[second][1])
        )


def _fixture() -> tuple[CollatzFieldActionArena, _FinitePrograms, CollatzDefectArena]:
    ledger = ResourceLedger(max_nodes=10_000, max_cache_entries=10_000)
    defects = CollatzDefectArena(((0, 1), (1, 0)), identity=0, ledger=ledger)
    programs = _FinitePrograms()
    arena = CollatzFieldActionArena(
        programs,
        defects,
        radial_orders=(2, 5),
        padic_precision=4,
        ledger=ledger,
    )
    return arena, programs, defects


def test_collatz_precision_rejects_before_large_integer_materialization() -> None:
    ledger = ResourceLedger()
    defects = CollatzDefectArena(((0,),), identity=0, ledger=ledger)
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="64-bit limb"):
        CollatzFieldActionArena(
            _FinitePrograms(),
            defects,
            padic_precision=10**9,
            ledger=ledger,
        )
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    with pytest.raises(ValueError, match="64-bit limb"):
        bounded_3adic_innovation(10**9, 1, 0)


def _action(
    arena: CollatzFieldActionArena,
    programs: _FinitePrograms,
    defects: CollatzDefectArena,
    *,
    matrix: tuple[int, int, int, int],
    multiplier: int,
    innovation: int,
    phase: int,
) -> CollatzFieldActionID:
    program = {
        role: programs.atom(role, matrix)
        for role in (
            "root",
            "affine",
            "output",
            "physical-tick",
            "valuation",
            "frame",
        )
    }
    return arena.intern(
        CollatzFieldAction(
            CollatzCharacterAction(
                phase,
                (
                    CollatzRadialCharacter(2, phase),
                    CollatzRadialCharacter(5, phase + 1),
                ),
            ),
            program["root"],
            program["affine"],
            bounded_3adic_innovation(4, multiplier, innovation, steps=1),
            defects.class_id(phase),
            CollatzCocyclePrograms(
                program["physical-tick"],
                program["valuation"],
                program["frame"],
            ),
            program["output"],
            CollatzActionGeometry(),
        )
    )


@pytest.mark.algebra
def test_composition_is_canonical_associative_and_ordered() -> None:
    arena, programs, defects, a, b = _noncommuting_actions()
    c = _action(
        arena,
        programs,
        defects,
        matrix=(2, 1, 1, 1),
        multiplier=4,
        innovation=1,
        phase=1,
    )

    assert_associative(arena.compose, a, b, c)
    assert arena.compose(a, b) != arena.compose(b, a)
    assert arena.compose(arena.identity, a) == a
    assert arena.compose(a, arena.identity) == a
    assert arena.metrics.action_nodes == arena.action_count
    assert arena.metrics.early_hits > 0
    assert arena.production_residual_state_classes == 2
    assert (
        arena.ledger.counters.get(
            "collatz_field_action_late_duplicate_reductions",
            0,
        )
        == 0
    )
    assert arena.ledger.counters.get("collatz_field_action_semantic_pre_hits", 0) > 0


@pytest.mark.accounting
def test_composition_cache_hits_before_symbolic_or_affine_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, programs, _unused_defects_binding, a, b = _noncommuting_actions()
    expected = arena.compose(a, b)
    before = arena.metrics
    counters = arena.ledger.snapshot().counters

    def poisoned(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm composition replayed symbolic program algebra")

    monkeypatch.setattr(programs, "compose", poisoned)
    assert arena.compose(a, b) == expected
    after = arena.metrics
    observed = arena.ledger.snapshot().counters
    assert after.composition_evaluations == before.composition_evaluations
    assert after.composition_requests == before.composition_requests + 1
    assert after.composition_early_hits == before.composition_early_hits + 1
    assert after.composition_cache_entries == before.composition_cache_entries
    assert (
        observed["temporal_parent_requests"] == counters["temporal_parent_requests"] + 1
    )
    assert (
        observed["temporal_parent_early_hits"]
        == counters.get(
            "temporal_parent_early_hits",
            0,
        )
        + 1
    )
    assert (
        observed["temporal_parent_compositions"]
        == counters["temporal_parent_compositions"]
    )


@pytest.mark.accounting
def test_failed_composition_reservation_publishes_no_partial_state() -> None:
    arena, _unused_programs_binding, _unused_defects_binding, a, b = (
        _noncommuting_actions()
    )
    ledger = arena.ledger
    ledger.tighten_limits(ledger.nodes, ledger.entries)
    before = (
        arena.action_count,
        len(arena._compositions),
        len(arena._witnesses),
        ledger.snapshot(),
    )
    with pytest.raises(BlockContextBudgetExceeded):
        arena.compose(a, b)
    after = (
        arena.action_count,
        len(arena._compositions),
        len(arena._witnesses),
        ledger.snapshot(),
    )
    assert after[:3] == before[:3]
    assert after[3].entries == before[3].entries
    assert after[3].nodes == before[3].nodes
    assert after[3].counters["temporal_parent_requests"] == (
        before[3].counters.get("temporal_parent_requests", 0) + 1
    )
    assert after[3].counters.get("temporal_parent_compositions", 0) == (
        before[3].counters.get("temporal_parent_compositions", 0)
    )


@pytest.mark.algebra
def test_bounded_innovation_annihilates_old_source_and_stays_dead() -> None:
    arena, programs, defects = _fixture()
    atom = _action(
        arena,
        programs,
        defects,
        matrix=(1, 1, 0, 1),
        multiplier=3,
        innovation=1,
        phase=1,
    )
    fourth = arena.power(atom, 4)
    dead = arena.resolve(fourth).innovation
    assert dead.source_annihilated
    assert dead.source_unit is None
    assert dead.multiplier() == 0
    assert arena.resolve(arena.compose(fourth, atom)).innovation.source_annihilated
    assert arena.metrics.source_annihilation_derivations > 0
    assert (
        arena.ledger.counters.get(
            "collatz_field_action_source_annihilation_derivations",
            0,
        )
        > 0
    )
    assert arena.ledger.counters.get("source_annihilations", 0) == 0


@pytest.mark.representation
def test_records_hold_only_scoped_symbolic_refs_and_bounded_innovation() -> None:
    arena, programs, defects = _fixture()
    action_id = _action(
        arena,
        programs,
        defects,
        matrix=(1, 1, 0, 1),
        multiplier=3,
        innovation=80,
        phase=1,
    )
    action = arena.resolve(action_id)
    names = {field.name for field in fields(action)}
    assert names == {
        "character",
        "root_action",
        "affine_action",
        "innovation",
        "defect",
        "cocycles",
        "output_morphism",
        "geometry",
    }
    assert type(action.root_action) is ActionProgramID
    assert type(action.affine_action) is ActionProgramID
    assert type(action.output_morphism) is ActionProgramID
    assert action.innovation.modulus <= 1 << 64
    assert not any(
        name in names
        for name in ("tail", "suffix", "digits", "complete_b", "proof_state")
    )


@pytest.mark.representation
def test_foreign_wrong_sort_and_integer_aliases_reject_before_mutation() -> None:
    arena, programs, defects = _fixture()
    good = _action(
        arena,
        programs,
        defects,
        matrix=(1, 1, 0, 1),
        multiplier=3,
        innovation=1,
        phase=1,
    )
    before = (arena.action_count, arena.retained_entries, arena.ledger.snapshot())

    with pytest.raises(TypeError):
        arena.resolve(cast(CollatzFieldActionID, good.local_id))
    with pytest.raises(TypeError):
        arena.resolve(cast(CollatzFieldActionID, True))
    with pytest.raises(ValueError):
        arena.resolve(
            CollatzFieldActionID(ArenaToken("foreign"), good.kind, good.local_id)
        )
    with pytest.raises(ValueError):
        arena.resolve(CollatzFieldActionID(good.owner, "proof-c4-state", good.local_id))
    with pytest.raises(TypeError):
        arena.intern(
            CollatzFieldAction(
                arena.resolve(good).character,
                cast(
                    ActionProgramID,
                    CollatzDefectClassID(defects.owner, "proof-c4-state", 0),
                ),
                arena.resolve(good).affine_action,
                arena.resolve(good).innovation,
                defects.identity,
                arena.resolve(good).cocycles,
                arena.resolve(good).output_morphism,
                arena.resolve(good).geometry,
            )
        )

    after = (arena.action_count, arena.retained_entries, arena.ledger.snapshot())
    assert after[0:2] == before[0:2]
    assert after[2].entries == before[2].entries
    assert after[2].nodes == before[2].nodes


@pytest.mark.accounting
def test_zero_budget_rejects_before_publication() -> None:
    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    defects = CollatzDefectArena(((0,),), identity=0, ledger=ledger)
    arena = CollatzFieldActionArena(_FinitePrograms(), defects, ledger=ledger)
    with pytest.raises(BlockContextBudgetExceeded):
        _ = arena.identity
    assert arena.action_count == 0
    assert arena.retained_entries == 0
    assert ledger.nodes == 0
    assert ledger.entries == 0


def test_invalid_residual_certificate_and_large_payload_reject() -> None:
    with pytest.raises(ValueError):
        CollatzDefectArena(((0, 1), (0, 1)), identity=0)
    with pytest.raises(ValueError):
        bounded_3adic_innovation(41, 3, 1)
    with pytest.raises(TypeError):
        bounded_3adic_innovation(4, True, 1)


def _noncommuting_actions() -> tuple[
    CollatzFieldActionArena,
    _FinitePrograms,
    CollatzDefectArena,
    CollatzFieldActionID,
    CollatzFieldActionID,
]:
    arena, programs, defects = _fixture()
    a = _action(
        arena,
        programs,
        defects,
        matrix=(1, 1, 0, 1),
        multiplier=3,
        innovation=1,
        phase=1,
    )
    b = _action(
        arena,
        programs,
        defects,
        matrix=(1, 0, 1, 1),
        multiplier=2,
        innovation=2,
        phase=0,
    )
    return arena, programs, defects, a, b
