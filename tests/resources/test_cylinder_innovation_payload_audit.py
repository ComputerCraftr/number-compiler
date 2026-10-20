"""Independent audit of primitive source-bound cylinder authority."""

from collections.abc import Callable
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.radial_innovation import (
    SymbolicRadialInnovation,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add.cylinder_innovation import (
    PrimitiveSuccessorClause,
    primitive_successor_clause,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.arithmetic_fixtures import forge_growth


def _clause() -> tuple[ResourceLedger, SourceCarryPorts, PrimitiveSuccessorClause]:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(ExactSource((6, 9, 1), 10, orbit="reverse-add"), ledger)
    arena = SymbolicInnovationArena(ledger)
    return ledger, ports, primitive_successor_clause(arena, ports)


def _reforge(clause: PrimitiveSuccessorClause) -> None:
    record = clause.audit_snapshot().record
    authority_for_test = cast(
        Callable[[], object],
        object.__getattribute__(clause, "_record_authority"),
    )
    object.__setattr__(record, "authority", authority_for_test())


def test_live_clause_is_audited_without_executing_runtime_callbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _ports, clause = _clause()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("payload audit executed cylinder runtime code")

    monkeypatch.setattr(type(clause), "validate", forbidden)
    monkeypatch.setattr(SourceCarryPorts, "check_source", forbidden)
    monkeypatch.setattr(SymbolicInnovationArena, "resolve", forbidden)
    report = audit_registered_payloads(ledger)

    assert report.forbidden_future_payloads == 0
    assert report.unbounded_future_integers == 0
    assert report.unknown_payloads == 0


@pytest.mark.parametrize("tamper", ("growth", "expressions", "foreign-source"))
def test_coordinated_reforged_authority_is_still_forbidden(tamper: str) -> None:
    ledger, _ports, clause = _clause()
    record = clause.audit_snapshot().record
    if tamper == "growth":
        growth = 1 - clause.growth
        forge_growth(clause, growth)
        object.__setattr__(record, "growth", growth)
        object.__setattr__(record, "output_extent", clause.output_extent)
        object.__setattr__(record, "action", clause.action)
    elif tamper == "expressions":
        snapshot = clause.audit_snapshot()
        object.__setattr__(clause, "_correction", clause.arena.zero)
        object.__setattr__(clause, "_beta", clause.arena.zero)
        object.__setattr__(
            clause,
            "action",
            SymbolicRadialInnovation(clause.action.multiplier, clause.arena.zero),
        )
        object.__setattr__(record, "correction", snapshot.arena.zero)
        object.__setattr__(record, "beta", snapshot.arena.zero)
        object.__setattr__(record, "action", clause.action)
    else:
        foreign = SourceCarryPorts(
            ExactSource((9, 7, 8), 10, orbit="reverse-add"), ledger
        )
        object.__setattr__(clause.carry_atom, "_ports", foreign)
        object.__setattr__(
            clause.carry_atom, "_source", foreign.audit_snapshot().source
        )
    _reforge(clause)

    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_closed_clause_releases_its_audited_authority() -> None:
    ledger, _ports, clause = _clause()
    clause.close()

    report = audit_registered_payloads(ledger)
    assert report.forbidden_future_payloads == 0
    assert report.unknown_payloads == 0


@pytest.mark.parametrize("tamper", ("arena", "missing-record"))
def test_malformed_clause_is_reported_without_running_it(tamper: str) -> None:
    ledger, _ports, clause = _clause()
    if tamper == "arena":
        object.__setattr__(clause, "arena", object())
    else:
        object.__delattr__(clause, "_record")
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
