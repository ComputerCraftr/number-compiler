"""Symbolic cell pullback is local closure, not a temporal powering claim."""

import pytest

from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.tile_reverse_functions import (
    reverse_leaf_components,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add.primitive_output_morphism import (
    CHANNEL_SYMBOL,
    LEFT_STATE,
    PORTS,
    RIGHT_STATE,
    SYMBOL,
    ReversePrimitiveOutputMorphism,
)


def test_correlated_symbol_and_ports_are_substituted_simultaneously() -> None:
    bits = BitFunctionArena(ResourceLedger())
    arena = ReversePrimitiveOutputMorphism(bits)
    # Reuse the template symbol name deliberately: replacements must read the
    # old environment, rather than recursively rewriting each other.
    source = bits.variable((SYMBOL,), SYMBOL, CHANNEL_SYMBOL)
    symbol = bits.map_atoms(
        source, CHANNEL_SYMBOL, tuple((i + 7) % 20 for i in range(20))
    )
    left = bits.map_atoms(source, LEFT_STATE, tuple((3 * i) % 43 for i in range(20)))
    right = bits.map_atoms(source, RIGHT_STATE, tuple(i % 5 for i in range(20)))
    first = arena.pullback_channels(symbol, left, right)
    second = arena.pullback_channels(first[2], left, right)
    expected_by_symbol: dict[int, tuple[ReversePortFunction, ...]] = {}

    def expected_leaf(symbol_value: int) -> tuple[ReversePortFunction, ...]:
        cached = expected_by_symbol.get(symbol_value)
        if cached is None:
            raw = reverse_leaf_components(
                PORTS, 10, symbol_value, bits.ledger
            ).functions()
            cached = tuple(
                function for function in raw if type(function) is ReversePortFunction
            )
            expected_by_symbol[symbol_value] = cached
        return cached

    for i in range(20):
        binding = {SYMBOL.variable: i}
        previous = (i + 7) % 20
        for channels in (first, second):
            expected = expected_leaf(previous)
            values = tuple(
                f.evaluate(((3 * i) % 43, i % 5), bits.ledger) for f in expected
            )
            assert tuple(bits.evaluate(f, binding) for f in channels) == values
            previous = values[2]


def test_partial_argument_invalidates_every_channel_and_warm_reuse_is_shared() -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    arena = ReversePrimitiveOutputMorphism(bits)
    port = FinitePort(PortVariable(0, 0, "source-admission", 0), 2)
    guard = bits.variable((port,), port, BOOL)
    symbol = bits.restrict(
        bits.constant(FunctionSignature((), CHANNEL_SYMBOL), 19), guard
    )
    left = bits.constant(FunctionSignature((), LEFT_STATE), 31)
    right = bits.constant(FunctionSignature((), RIGHT_STATE), 0)
    channels = arena.pullback_channels(symbol, left, right)
    assert all(bits.evaluate(f, {port.variable: 0}) is None for f in channels)
    assert all(bits.evaluate(f, {port.variable: 1}) is not None for f in channels)
    before = ledger.snapshot()
    assert arena.pullback_channels(symbol, left, right) == channels
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
    assert ledger.counters["reverse_symbolic_channel_alphabet_branches"] == 20
    assert ledger.counters["semantic_bit_batch_composition_hits"] >= 1
    assert not arena._leaves
    payload = audit_registered_payloads(ledger)
    assert (
        payload.unknown_payloads,
        payload.forbidden_future_payloads,
        payload.unbounded_future_integers,
    ) == (0, 0, 0)
    assert not audit_execution_ownership(ledger).violations


def test_foreign_or_wrong_sort_arguments_are_rejected_before_template_construction() -> (
    None
):
    bits = BitFunctionArena(ResourceLedger())
    arena = ReversePrimitiveOutputMorphism(bits)
    left = bits.constant(FunctionSignature((), LEFT_STATE), 0)
    right = bits.constant(FunctionSignature((), RIGHT_STATE), 0)
    foreign = BitFunctionArena(ResourceLedger()).constant(
        FunctionSignature((), CHANNEL_SYMBOL), 7
    )
    for bad in (foreign, left):
        with pytest.raises(ValueError):
            arena.pullback_channels(bad, left, right)
    assert not arena._channel_templates


def test_budget_refusal_publishes_no_partial_channel_template() -> None:
    ledger, _unused_bits_binding, arena, symbol, left, right = (
        _constant_channel_fixture()
    )
    for allowance in (0, 50):
        ledger.max_nodes = ledger.nodes + allowance
        with pytest.raises(BlockContextBudgetExceeded):
            arena.pullback_channels(symbol, left, right)
        assert not arena._channel_templates
        assert not arena._channel_seals
        assert all(item.accounting_delta == 0 for item in ledger.inventory())
    ledger.max_nodes = None
    assert len(arena.pullback_channels(symbol, left, right)) == 13


def test_modified_template_is_rejected_and_eviction_rebuilds_it() -> None:
    ledger, bits, arena, symbol, left, right = _constant_channel_fixture()
    expected = arena.pullback_channels(symbol, left, right)
    template = arena._channel_templates[0]
    forged = bits.constant(bits.resolve(template[0]).signature, 0)
    assert forged != template[0]
    arena._channel_templates[0] = (forged, *template[1:])
    with pytest.raises(ValueError, match="changed after publication"):
        arena.pullback_channels(symbol, left, right)
    arena._channel_templates[0] = template
    handle = template[0]
    original_id = handle.local_id
    try:
        object.__setattr__(handle, "local_id", forged.local_id)
        with pytest.raises(ValueError, match="changed after publication"):
            arena.pullback_channels(symbol, left, right)
    finally:
        object.__setattr__(handle, "local_id", original_id)
    del arena._channel_templates[0]
    with pytest.raises(ValueError, match="incomplete publication"):
        arena.pullback_channels(symbol, left, right)
    ledger.evict_query_memos()
    assert arena.pullback_channels(symbol, left, right) == expected


def _constant_channel_fixture() -> tuple[
    ResourceLedger,
    BitFunctionArena,
    ReversePrimitiveOutputMorphism,
    FactoredFunctionID,
    FactoredFunctionID,
    FactoredFunctionID,
]:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    arena = ReversePrimitiveOutputMorphism(bits)
    symbol = bits.constant(FunctionSignature((), CHANNEL_SYMBOL), 7)
    left = bits.constant(FunctionSignature((), LEFT_STATE), 0)
    right = bits.constant(FunctionSignature((), RIGHT_STATE), 0)
    return ledger, bits, arena, symbol, left, right
