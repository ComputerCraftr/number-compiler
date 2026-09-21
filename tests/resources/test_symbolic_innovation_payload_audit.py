"""Scoped payload audit for the source-free symbolic innovation algebra."""

import subprocess
import sys
from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
    _Add,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads


def test_unrelated_resource_audit_does_not_load_innovation_machinery() -> None:
    subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import sys\n"
                "from number_compiler.resources.ledger import ResourceLedger\n"
                "from number_compiler.resources.payload_audit import audit_registered_payloads\n"
                "name = 'number_compiler.arithmetic.fields.symbolic_innovation'\n"
                "assert name not in sys.modules\n"
                "audit_registered_payloads(ResourceLedger())\n"
                "assert name not in sys.modules\n"
            ),
        ],
        check=True,
        capture_output=True,
        text=True,
    )


def _mixed_arena() -> tuple[ResourceLedger, SymbolicInnovationArena]:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    left = arena.atom(SemanticIdentity("", ("audit", "left")))
    right = arena.atom(SemanticIdentity("", ("audit", "right")))
    charted = arena.chart(left, CylinderChart(-1, 7))
    radial = arena.radial(charted, RadialMultiplier(2, 3))
    interval = arena.interval((1 << 130) + 3)
    summed = arena.linear_combination(
        ((3, radial), (-2, right), (1, left), (1, interval))
    )
    arena.power(arena.action(RadialMultiplier(1, 1), summed), 16)
    return ledger, arena


def test_live_mixed_dag_is_fully_audited_without_runtime_callbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, arena = _mixed_arena()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("payload audit executed symbolic arithmetic")

    monkeypatch.setattr(type(arena), "resolve", forbidden)
    monkeypatch.setattr(type(arena), "project_cyclotomic", forbidden)
    before = dict(ledger.counters)
    report = audit_registered_payloads(ledger)

    assert report.forbidden_future_payloads == 0
    assert report.unbounded_future_integers == 0
    assert report.unknown_payloads == 0
    assert dict(ledger.counters) == before


def test_wide_operator_integer_metadata_is_accepted_with_exact_accounting() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    one = arena.interval(1)
    arena.linear_combination((((1 << 130) + 1, one),))
    arena.radial(one, RadialMultiplier(1 << 130, 1 << 129))
    arena.chart(one, CylinderChart(-1, -(1 << 130)))

    report = audit_registered_payloads(ledger)

    assert report.forbidden_future_payloads == 0
    assert report.unbounded_future_integers == 0
    assert report.unknown_payloads == 0


@pytest.mark.parametrize(
    "tamper", ["foreign-child", "foreign-store", "interner", "accounting"]
)
def test_tampered_symbolic_dag_is_forbidden(tamper: str) -> None:
    ledger, arena = _mixed_arena()
    if tamper == "foreign-child":
        other = SymbolicInnovationArena(ResourceLedger())
        node = arena._nodes[-1]
        assert type(node) is _Add
        arena._nodes._data[-1] = replace(node, left=other.zero)
    elif tamper == "foreign-store":
        other = SymbolicInnovationArena(ResourceLedger())
        arena._keys = other._keys
    elif tamper == "interner":
        reference = next(iter(arena._keys.values()))
        object.__setattr__(reference, "seal", "forged")
    else:
        arena._nodes._data.append(arena._nodes[0])

    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_closed_and_refused_arenas_release_all_authority() -> None:
    ledger, arena = _mixed_arena()
    arena.close()
    report = audit_registered_payloads(ledger)
    assert ledger.entries == ledger.nodes == 0
    assert report.forbidden_future_payloads == report.unknown_payloads == 0

    refused = ResourceLedger(max_cache_entries=1)
    with pytest.raises(BlockContextBudgetExceeded):
        SymbolicInnovationArena(refused)
    assert refused.entries == refused.nodes == 0
    assert all(row.disposed for row in refused.inventory())
