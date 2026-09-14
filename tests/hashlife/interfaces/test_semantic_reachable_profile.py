"""Certified ordinal profiles never alter the arbitrary-function interface."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
    FunctionSort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    ReachableCodec,
    SemanticProfileArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from tests.support.diamond_query import build

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
        SemanticProfileID,
    )


def setup() -> tuple[
    DiamondRuntime,
    SemanticProfileArena,
    SemanticProfileID,
    StructureArena,
    ReachableCodec,
]:
    app = build(PhysicalCollatzFourBlockEffect(), (0, 1), 16, 1)
    runtime, primitive = app.runtime, app.root
    runtime.kernel(primitive)
    pair = runtime.actions.compose(primitive, primitive)
    arena = SemanticProfileArena(runtime)
    profile = arena.c4_pair_left(pair)
    structures = StructureArena(
        BitFunctionArena(runtime.ledger, runtime.semantic_functions)
    )
    codec = arena.binding(profile, pair, 0, PortVariable(0, 0, "test", 0), structures)
    assert isinstance(codec, ReachableCodec)
    return runtime, arena, profile, structures, codec


def test_binding_is_lazy_and_anchor_never_builds_continuation() -> None:
    runtime, arena, profile, structures, codec = setup()
    assert codec.encoded_bits == 11 and codec.structure is None
    assert len(arena.decodes) == 0 and len(structures.nodes) == 0
    anchor = arena.component(codec, 0, structures)
    definition = arena.resolve(profile).definition
    for index in range(1234):
        assert (
            structures.evaluate_atom(anchor, {codec.ports[0].variable: index})
            == definition.states[index].anchor
        )
    for index in (1234, 2047):
        assert (
            structures.evaluate_atom(anchor, {codec.ports[0].variable: index}) is None
        )
    assert {key.component for key in arena.decodes} == {0}
    assert runtime.ledger.counters["semantic_reachable_decoder_table_cells"] == 1234


def test_continuation_fixed_table_and_invalid_codes() -> None:
    _, arena, profile, structures, codec = setup()
    function = arena.component(codec, 1, structures)
    output_sort = structures.resolve(function).signature.output
    assert isinstance(output_sort, FunctionSort)
    declaration = output_sort.inputs[0]
    definition = arena.resolve(profile).definition
    for argument in (0, 1, 17, 66, 89):
        value = structures.bits.constant(
            FunctionSignature((), AtomSort("primitive-right-state", 90)), argument
        )
        column = structures.apply(function, {declaration.variable: value})
        for ordinal in range(1234):
            state = definition.states[ordinal]
            assert (
                structures.evaluate_atom(column, {codec.ports[0].variable: ordinal})
                == definition.functions[state.continuation][argument]
            )
        assert structures.evaluate_atom(column, {codec.ports[0].variable: 1234}) is None


def test_foreign_profiles_codecs_and_wrong_domain_reject_before_warm_mutation() -> None:
    runtime, arena, profile, structures, codec = setup()
    arena.component(codec, 0, structures)
    other = SemanticProfileArena(runtime)
    other_profile = other.c4_pair_left(codec.request.action)
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.resolve(other_profile)
    with pytest.raises(ValueError):
        arena.component(replace(codec), 0, structures)
    with pytest.raises(UnsupportedInterfaceError):
        arena.ports(profile, codec.request.action, 1, codec.request.namespace)
    with pytest.raises(ValueError):
        arena.ports(profile, codec.request.action, True, codec.request.namespace)
    assert runtime.ledger.snapshot() == before


@pytest.mark.validation  # Full profiled C⁴ fourth-summary compiler validation.
def test_source_initial_profile_compiles_actual_c4_fourth_right_summary() -> None:
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        LowerFinite,
    )
    from tests.support.c4_summary_artifact import fresh_c4_fourth_right_summary
    from tests.support.runtime_limits import deadline

    with deadline(35, "profiled C4 fourth RIGHT16 compilation"):
        artifact = fresh_c4_fourth_right_summary()
        runtime, pair = artifact.runtime, artifact.pair
        profile = runtime.semantic_compiler.source_initial_profile(pair)
        arena = runtime.higher.expressions
        closure = arena.closures.resolve(artifact.closure)
        assert closure.support == ()
        result = runtime.semantic_compiler.compile_structured(
            closure.body, profile=profile
        )
        structures = runtime.semantic_compiler.structures
        assert structures is not None
        assert structures.resolve(result.structure).kind == "product"
        assert structures is not None
        first = structures.component(structures.component(result.structure, 0), 0)
        expected = runtime.execute(
            LowerFinite(arena.anchor(arena.anchor(closure.body)))
        )
        assert structures is not None
        assert structures.evaluate_atom(first, {}) == expected


def test_exhausted_decode_cache_preflight_and_warm_hit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.interfaces.semantic_reachable_profile as module
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    runtime, arena, _, structures, codec = setup()
    runtime.ledger.max_cache_entries = runtime.ledger.entries
    before = runtime.ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.component(codec, 0, structures)
    assert runtime.ledger.snapshot() == before
    runtime.ledger.max_cache_entries = None
    anchor = arena.component(codec, 0, structures)
    runtime.ledger.max_cache_entries = runtime.ledger.entries
    runtime.ledger.max_nodes = runtime.ledger.nodes

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm decoder rebuilt a finite table")

    monkeypatch.setattr(module, "_Builder", forbidden)
    assert arena.component(codec, 0, structures) == anchor


def test_decoder_late_node_budget_failure_is_atomic() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    runtime, arena, _, structures, codec = setup()
    runtime.ledger.max_nodes = runtime.ledger.nodes
    before = runtime.ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.component(codec, 0, structures)
    after = runtime.ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert (
        len(structures.nodes) == len(structures.bits.nodes) == len(arena.decodes) == 0
    )


def test_profile_loader_failure_releases_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.contracts.physical_collatz_pair_certificate as domain

    app = build(PhysicalCollatzFourBlockEffect(), (0,), 8, 1)
    pair = app.runtime.actions.compose(app.root, app.root)
    arena = SemanticProfileArena(app.runtime)

    def broken() -> Never:
        raise ValueError("bad artifact")

    # The proof loader is deliberately imported at the admission boundary so
    # production modules do not retain the proof certificate. Patch the
    # forwarding proof facade that the boundary resolves.
    monkeypatch.setattr(domain, "load_verified_c4_pair_left", broken)
    before = app.runtime.ledger.snapshot()
    with pytest.raises(ValueError, match="bad artifact"):
        arena.c4_pair_left(pair)
    after = app.runtime.ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert not arena.nodes and not arena.keys


def test_fixed_subtable_is_reused_before_boolean_decisions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.functions.finite_function_types import FinitePort
    from number_compiler.arithmetic.functions.semantic_function_transactions import (
        _Transaction,
    )
    from number_compiler.hashlife.interfaces.semantic_bits import _Circuit
    from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
        _FixedTableLookup,
    )

    runtime, arena, _, structures, _ = setup()
    port = FinitePort(PortVariable(0, 0, "fixed-test-column", 0), 16)
    circuit = _Circuit(structures.functions, (port,))
    lookup = _FixedTableLookup(arena, circuit, port, 2)
    values = (0, 1, 2, 3) * 4
    roots = lookup.compile(values)
    signature = FunctionSignature((port,), AtomSort("column", 4))
    result = structures.bits._publish(
        circuit, (circuit.normalized(signature, roots, circuit.admitted()),)
    )[0]
    for value in range(16):
        assert structures.bits.evaluate(result, {port.variable: value}) == value % 4
    before = runtime.ledger.counters[
        "semantic_reachable_decoder_subtable_bit_decisions"
    ]

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("equal fixed subtable reached Boolean construction")

    monkeypatch.setattr(_Transaction, "decision", forbidden)
    assert lookup.compile(tuple(values)) == roots
    assert (
        runtime.ledger.counters["semantic_reachable_decoder_subtable_bit_decisions"]
        == before
    )
    assert runtime.ledger.counters["semantic_reachable_decoder_subtable_early_hits"] > 0


def test_every_original_continuation_argument_is_preserved() -> None:
    _, arena, profile, structures, codec = setup()
    function = arena.component(codec, 1, structures)
    node = structures.resolve(function)
    assert node.body is not None
    body = structures.resolve(node.body)
    assert body.atom is not None
    definition = arena.resolve(profile).definition
    for argument in range(90):
        for ordinal in (0, 1, 31, 617, 1233):
            inputs = {
                codec.ports[0].variable: ordinal,
                node.bound[0].variable: argument,
            }
            state = definition.states[ordinal]
            assert (
                structures.bits.evaluate(body.atom, inputs)
                == definition.functions[state.continuation][argument]
            )
    for argument in (90, 127):
        assert (
            structures.bits.evaluate(
                body.atom,
                {codec.ports[0].variable: 0, node.bound[0].variable: argument},
            )
            is None
        )
