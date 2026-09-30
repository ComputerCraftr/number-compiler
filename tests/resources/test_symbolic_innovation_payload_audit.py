"""Scoped payload audit for the source-free symbolic innovation algebra."""

import subprocess
import sys
from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.f5_innovation import compose_f5_forcing
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
    _Add,
)
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.support.arithmetic_fixtures import wide_innovation_operators


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


def test_live_f5_memo_is_audited_without_evaluating_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    before = F5AffineTransport(F5SpatialTransport(), arena.interval(1))
    after = F5AffineTransport(F5SpatialTransport(3, 5**64 - 1), arena.interval(2))
    compose_f5_forcing(arena, before, after)
    memo = arena._f5_composition_cache()
    assert memo.nodes_per_entry == 3

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("F5 payload audit evaluated arithmetic")

    monkeypatch.setattr(type(arena), "resolve", forbidden)
    counters = dict(ledger.counters)
    report = audit_registered_payloads(ledger)
    assert report.forbidden_future_payloads == report.unknown_payloads == 0
    assert report.unbounded_future_integers == 0
    assert ledger.counters == counters
    ledger.evict_query_memos()
    assert len(memo) == 0
    arena.close()
    report = audit_registered_payloads(ledger)
    assert ledger.entries == ledger.nodes == 0
    assert report.forbidden_future_payloads == report.unknown_payloads == 0


def test_f5_memo_capacity_grows_by_eviction_with_exact_metadata_accounting() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    before = F5AffineTransport(F5SpatialTransport(), arena.interval(1))
    compose_f5_forcing(arena, before, before)
    old = arena._f5_composition_cache()
    after = F5AffineTransport(F5SpatialTransport(0, 5**64), before.forcing)
    compose_f5_forcing(arena, before, after)
    current = arena._f5_composition_cache()
    assert old._disposed and len(old._data) == 0
    assert current is not old and current.nodes_per_entry == 3
    assert all(row.accounting_delta in (None, 0) for row in ledger.inventory())
    report = audit_registered_payloads(ledger)
    assert report.forbidden_future_payloads == report.unknown_payloads == 0


@pytest.mark.parametrize(
    "tamper", ("foreign-result", "foreign-empty-memo", "uncharged-key", "missing-field")
)
def test_f5_memo_audit_rejects_foreign_or_uncharged_payloads(tamper: str) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    action = F5AffineTransport(F5SpatialTransport(), arena.interval(1))
    compose_f5_forcing(arena, action, action)
    memo = arena._f5_composition_cache()
    key = next(iter(memo))
    if tamper == "foreign-result":
        foreign = SymbolicInnovationArena(ResourceLedger())
        memo[key] = foreign.zero
    elif tamper == "foreign-empty-memo":
        sibling = SymbolicInnovationArena(ledger)
        arena._f5_compositions = sibling._f5_composition_cache()
    elif tamper == "uncharged-key":
        value = memo[key]
        del memo[key]
        memo[(key[0], key[1], 1 << 130, key[3])] = value
    else:
        del arena._f5_compositions
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


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
    ledger, arena = wide_innovation_operators()

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
