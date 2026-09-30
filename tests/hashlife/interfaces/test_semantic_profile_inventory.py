"""Reachable certificates and decoders need actual ownership and fixed semantics."""

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
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_boundary_expr import StateSort
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
    ExpressionAdmissionKey,
    ExpressionDomainProof,
)
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    ReachableCodec,
    ReachableCodecKey,
    ReachableDecodeKey,
    SemanticProfileArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.assertions import assert_forbidden_payloads_read_only
from tests.support.diamond_query import build

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
        SemanticProfileID,
    )
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication


def setup() -> tuple[
    DiamondApplication,
    SemanticProfileArena,
    SemanticProfileID,
    StructureArena,
    ReachableCodec,
]:
    app = build(PhysicalCollatzFourBlockEffect(), (0, 1), 16, 1)
    runtime = app.runtime
    runtime.kernel(app.root)
    pair = runtime.actions.compose(app.root, app.root)
    profile = runtime.semantic_compiler.source_initial_profile(pair)
    arena = runtime.semantic_compiler.profiles
    structures = StructureArena(
        BitFunctionArena(runtime.ledger, runtime.semantic_functions)
    )
    assert arena is not None
    codec = arena.binding(profile, pair, 0, PortVariable(0, 0, "audit", 0), structures)
    assert type(codec) is ReachableCodec
    return app, arena, profile, structures, codec


@pytest.mark.parametrize("component", (None, 0, 1, 2))
def test_actual_profile_tables_and_lazy_decoders_have_read_only_inventory(
    monkeypatch: pytest.MonkeyPatch, component: None | int
) -> None:
    app, arena, _, structures, codec = setup()
    runtime = app.runtime
    if component is not None:
        assert arena is not None
        arena.decode(codec, structures) if component == 2 else arena.component(
            codec, component, structures
        )

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("independent inventory executed a producer")

    for name in ("resolve", "ports", "validate_codec", "component", "decode"):
        monkeypatch.setattr(arena, name, forbidden)
    monkeypatch.setattr(runtime, "execute", forbidden)
    monkeypatch.setattr(structures, "evaluate_atom", forbidden)
    monkeypatch.setattr(structures.functions, "evaluate", forbidden)
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert runtime.ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    assert report.forbidden_future_payloads == 0
    expected = sum(
        row.observed_nodes or 0
        for row in report.resource_inventory
        if row.role
        in (
            "semantic_port_signature",
            "semantic_state_codec",
            "semantic_reachable_profile",
            "semantic_reachable_codec",
        )
    )
    assert report.semantic_signature_nodes == expected >= 2
    assert report.reachable_profile_definition_records == 1
    assert report.reachable_profile_definition_integer_slots == 2 + 921 * 90 + 1234 * 7
    assert report.reachable_profile_codec_records == 1
    assert report.reachable_profile_decoder_cache_entries == (
        0 if component is None else 3 if component == 2 else 1
    )


@pytest.mark.parametrize(
    "fault",
    (
        "digest-copy",
        "bool-state",
        "foreign-profile",
        "wrong-side",
        "extra-structure",
        "wrong-port",
    ),
)
def test_profile_or_codec_forgery_is_not_a_kernel_definition_exemption(
    fault: str,
) -> None:
    app, arena, profile, structures, codec = setup()
    runtime = app.runtime
    assert arena is not None
    key = next(iter(arena.records))
    if fault in ("digest-copy", "bool-state"):
        assert arena is not None
        record = arena.nodes[profile.local_id]
        states = record.definition.states
        state = replace(
            states[0],
            anchor=True if fault == "bool-state" else (states[0].anchor + 1) % 50,
        )
        object.__setattr__(
            record,
            "definition",
            replace(record.definition, states=(state, *states[1:])),
        )
    elif fault == "foreign-profile":
        other = SemanticProfileArena(runtime)
        foreign = other.c4_pair_left(codec.request.action)
        assert arena is not None
        arena.records._data[key] = replace(codec, profile=foreign)
    elif fault == "wrong-side":
        assert arena is not None
        arena.records._data[key] = replace(
            codec, request=replace(codec.request, side=1)
        )
    elif fault == "extra-structure":
        assert arena is not None
        arena.records._data[key] = replace(
            codec, structure=arena.component(codec, 0, structures)
        )
    else:
        assert arena is not None
        arena.records._data[key] = replace(
            codec, ports=(replace(codec.ports[0], cardinality=2048),)
        )
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0
    assert runtime.ledger.snapshot() == before


def test_same_signature_wrong_decoder_is_rejected_without_observation() -> None:
    app, arena, _, structures, codec = setup()
    runtime = app.runtime
    assert arena is not None
    arena.component(codec, 0, structures)
    function = structures.bits.constant(
        FunctionSignature(codec.ports, AtomSort("primitive-left-state", 50)), 0
    )
    wrong = structures.atom(function)
    key = ReachableDecodeKey(ReachableCodecKey(codec.profile, codec.request), 0)
    assert arena is not None
    arena.decodes._data[key] = wrong
    before = runtime.ledger.snapshot()
    assert collect_ledger_metrics(runtime.ledger).forbidden_future_payloads > 0
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize("fault", (None, "foreign", "scalar", "wrong-side"))
def test_admission_proof_profile_is_bound_to_exact_compiler_and_domain(
    fault: None | str,
) -> None:
    app, _arena, profile, _, codec = setup()
    runtime = app.runtime
    expressions = runtime.higher.expressions
    side = 1 if fault == "wrong-side" else 0
    variable = expressions.variable(
        StateSort(codec.request.action, side), "profile-domain"
    )
    expression = expressions.lambda_(variable, variable)
    key = ExpressionAdmissionKey(expression, True, profile)
    if fault == "foreign":
        other = SemanticProfileArena(runtime)
        key = replace(key, profile=other.c4_pair_left(codec.request.action))
    elif fault == "scalar":
        object.__setattr__(key, "structured", False)
    runtime.semantic_compiler.admissions[key] = ExpressionDomainProof(key)
    before = runtime.ledger.snapshot()
    report = collect_ledger_metrics(runtime.ledger)
    assert runtime.ledger.snapshot() == before
    assert (report.forbidden_future_payloads == 0) is (fault is None)


def test_function_decoder_parent_validity_is_not_inferred_from_body() -> None:
    app, arena, _, structures, codec = setup()
    assert arena is not None
    function = arena.component(codec, 1, structures)
    from number_compiler.arithmetic.functions.finite_function_types import BOOL

    all_valid = structures.functions.atom(FunctionSignature(codec.ports, BOOL), 1)
    malformed = replace(structures.nodes[function.local_id], valid=all_valid)
    app.runtime.ledger.reserve_many(
        ((structures.node_owner, 1, 1), (structures.key_owner, 1, 0))
    )
    forged = structures._handle(len(structures.nodes))
    structures.nodes.append(malformed)
    structures.keys[malformed] = forged.local_id
    key = ReachableDecodeKey(ReachableCodecKey(codec.profile, codec.request), 1)
    assert arena is not None
    arena.decodes._data[key] = forged
    assert_forbidden_payloads_read_only(app.runtime.ledger)


def test_profile_interner_cannot_borrow_an_equal_profile_from_another_arena() -> None:
    app, arena, _, _, codec = setup()
    other = SemanticProfileArena(app.runtime)
    foreign = other.c4_pair_left(codec.request.action)
    assert arena is not None
    arena.keys[codec.request.action] = foreign
    assert_forbidden_payloads_read_only(app.runtime.ledger)


def test_bypassed_frozen_key_mutation_is_reported_instead_of_crashing() -> None:
    app, arena, _, structures, codec = setup()
    assert arena is not None
    function = arena.component(codec, 1, structures)
    from number_compiler.arithmetic.functions.finite_function_types import BOOL

    all_valid = structures.functions.atom(FunctionSignature(codec.ports, BOOL), 1)
    # This bypasses the public immutable-record boundary and invalidates the
    # existing interner key hash; an adversarial audit must still finish.
    object.__setattr__(structures.nodes[function.local_id], "valid", all_valid)
    assert_forbidden_payloads_read_only(app.runtime.ledger)
