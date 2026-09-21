"""Execution inventory recognizes semantic functions without observing them."""

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemanticsAdapter,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_registry import NODE_ROLE_GROUPS
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("inventory attempted a semantic observation or reduction")


def test_semantic_inventory_counts_real_nodes_and_work_without_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    bits = BitFunctionArena(ledger, functions)
    carry = FinitePort(PortVariable(0, 0, "carry", 0), (1 << 63) - 1)
    symbol = FinitePort(PortVariable(0, 0, "symbol", 0), 2)
    division = bits.divide_binary(carry.cardinality, carry, symbol)
    assert (
        bits.evaluate(division.quotient, {carry.variable: 17, symbol.variable: 1}) == 0
    )
    before = ledger.snapshot()
    monkeypatch.setattr(functions, "evaluate", forbidden)
    monkeypatch.setattr(functions, "ite", forbidden)
    monkeypatch.setattr(functions, "substitute", forbidden)
    report = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    assert report.metrics_schema_version == 7
    assert report.semantic_function_nodes == len(functions.nodes) + len(bits.nodes)
    assert report.semantic_binary_division_compilations == 1
    assert report.semantic_function_evaluations > 0
    assert report.semantic_function_published_nodes == len(functions.nodes)
    assert (
        report.resource_observed_nodes
        == sum(getattr(report, name) for name, _ in NODE_ROLE_GROUPS)
        + report.other_retained_nodes
    )
    assert report.resource_observed_entries == ledger.entries
    assert (
        report.forbidden_future_payloads == report.resource_audit_unknown_payloads == 0
    )
    assert report.exact_microblock_nodes == report.exact_microblock_entries == 0
    assert not audit_execution_ownership(ledger).violations


def test_primitive_records_are_admitted_through_the_actual_kernel(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    functions = SemanticFunctionArena(ledger)
    adapter = PrimitiveSemanticsAdapter(kernels, functions)
    adapter.compile(CollatzPhysicalBlockEffect())
    before = ledger.snapshot()
    monkeypatch.setattr(functions, "evaluate", forbidden)
    monkeypatch.setattr(adapter, "compile", forbidden)
    audit = audit_registered_payloads(ledger)
    assert (
        audit.forbidden_future_payloads
        == audit.unknown_payloads
        == audit.unbounded_future_integers
        == 0
    )
    assert ledger.snapshot() == before


def test_orphan_and_malformed_semantic_records_do_not_gain_class_name_authority() -> (
    None
):
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    zero = functions.atom(FunctionSignature((), BOOL), 0)
    node = functions.resolve(zero)
    owner = ledger.register("untrusted-semantic-records", "semantic_function")
    records: LedgerList[object]
    records = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(replace(node))
    audit = audit_registered_payloads(ledger)
    assert audit.forbidden_future_payloads > 0


def test_forged_finite_effect_identity_is_rejected_without_repair() -> None:
    from tests.support.diamond_observation_adversarial import neighbor_xor

    ledger = ResourceLedger()
    effect = neighbor_xor()
    identity = effect._semantic_identity
    object.__setattr__(identity, "digest", "forged")
    owner = ledger.register("forged-finite-effect", "compiled_action_program")
    records: LedgerList[object] = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(effect)
    before = ledger.snapshot()
    audit = audit_registered_payloads(ledger)
    assert audit.forbidden_future_payloads > 0
    assert identity.digest == "forged"
    assert ledger.snapshot() == before


def test_factored_higher_outputs_are_accounted_without_observing_outer_ports(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    structures = StructureArena(bits)
    x = FinitePort(PortVariable(0, 0, "x", 0), 1 << 64)
    y = FinitePort(PortVariable(0, 0, "y", 0), 2)
    word = AtomSort("word", 1 << 64)
    left = bits.variable((x, y), x, word)
    right = bits.variable((x, y), y, BOOL)
    function = structures.curry(structures.atom(bits.add(left, right, word)), (y,))
    outer = structures.atom(bits.variable((x,), x, word))
    structures.product((outer, function))
    monkeypatch.setattr(bits.functions, "evaluate", forbidden)
    before = ledger.snapshot()
    report = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    assert report.semantic_function_nodes == len(bits.functions.nodes) + len(
        bits.nodes
    ) + len(structures.nodes)
    assert (
        report.forbidden_future_payloads == report.resource_audit_unknown_payloads == 0
    )
