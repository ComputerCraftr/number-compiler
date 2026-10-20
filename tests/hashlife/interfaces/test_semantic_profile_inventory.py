"""Reachable certificates and decoders need actual ownership and fixed semantics."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
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
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.sequences.collatz.physical_pair_certificate import (
    C4PairLeftCertificate,
)
from tests.support.assertions import assert_forbidden_payloads_read_only
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_application

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
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
    app = build_collatz_diamond_application(
        PhysicalCollatzFourBlockEffect(), (0, 1), 16, 1
    )
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


def _assert_read_only_profile_inventory(
    monkeypatch: pytest.MonkeyPatch,
    runtime: DiamondRuntime,
    arena: SemanticProfileArena,
    structures: StructureArena,
    expected_decoder_entries: int,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("independent inventory executed a producer")

    with monkeypatch.context() as observers_blocked:
        for name in ("resolve", "ports", "validate_codec", "component", "decode"):
            observers_blocked.setattr(arena, name, forbidden)
        observers_blocked.setattr(runtime, "execute", forbidden)
        observers_blocked.setattr(structures, "evaluate_atom", forbidden)
        observers_blocked.setattr(structures.functions, "evaluate", forbidden)
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
        assert (
            report.reachable_profile_definition_integer_slots == 2 + 921 * 90 + 1234 * 7
        )
        assert report.reachable_profile_codec_records == 1
        assert (
            report.reachable_profile_decoder_cache_entries == expected_decoder_entries
        )


@pytest.mark.parametrize(
    "full_inventory",
    (False, pytest.param(True, marks=pytest.mark.validation)),
)
def test_actual_profile_tables_and_lazy_decoders_have_read_only_inventory(
    monkeypatch: pytest.MonkeyPatch,
    full_inventory: bool,
) -> None:
    app, arena, _, structures, codec = setup()
    runtime = app.runtime
    assert arena is not None

    if full_inventory:
        # The validation tier checks every lazy cache level on the full C4 table.
        _assert_read_only_profile_inventory(monkeypatch, runtime, arena, structures, 0)
        arena.component(codec, 0, structures)
        _assert_read_only_profile_inventory(monkeypatch, runtime, arena, structures, 1)
        arena.component(codec, 1, structures)
        _assert_read_only_profile_inventory(monkeypatch, runtime, arena, structures, 2)
    else:
        # Unit coverage audits a real C4 profile after its first lazy decoder.
        arena.component(codec, 0, structures)
        _assert_read_only_profile_inventory(monkeypatch, runtime, arena, structures, 1)


@pytest.mark.parametrize(
    "full_inventory",
    (False, pytest.param(True, marks=pytest.mark.validation)),
)
def test_cold_full_profile_decode_builds_the_expected_product(
    monkeypatch: pytest.MonkeyPatch,
    full_inventory: bool,
) -> None:
    app, arena, _, structures, codec = setup()
    runtime = app.runtime
    assert arena is not None

    # Keep this cold: decode must construct both components itself. The unit
    # assertion checks its product and all three cache entries; validation also
    # inventories the full fixed-size profile after construction.
    decoded = arena.decode(codec, structures)
    assert structures.resolve(decoded).kind == "product"
    assert len(arena.decodes) == 3
    if full_inventory:
        _assert_read_only_profile_inventory(monkeypatch, runtime, arena, structures, 3)


def test_profile_audit_checks_action_once_and_rejects_stale_action_before_load() -> (
    None
):
    app, arena, profile, _, codec = setup()
    runtime = app.runtime
    hooks = runtime.family_hooks
    assert hooks is not None
    assert hooks.validate_source_profile_action is not None
    assert hooks.make_source_profile is not None
    validator = cast(Callable[..., bool], hooks.validate_source_profile_action)
    loader = cast(Callable[..., object], hooks.make_source_profile)
    calls = {"validator": 0, "loader": 0}

    def count_validator(runtime_arg: DiamondRuntime, action: ActionProgramID) -> bool:
        calls["validator"] += 1
        return validator(runtime_arg, action)

    def count_loader(runtime_arg: DiamondRuntime, action: ActionProgramID) -> object:
        calls["loader"] += 1
        return loader(runtime_arg, action)

    def forbidden_loader(*args: object, **kwargs: object) -> Never:
        raise AssertionError("stale source action reached the profile loader")

    object.__setattr__(hooks, "validate_source_profile_action", count_validator)
    object.__setattr__(hooks, "make_source_profile", count_loader)
    try:
        report = collect_ledger_metrics(runtime.ledger)
        assert report.forbidden_future_payloads == 0
        assert calls == {"validator": 1, "loader": 1}

        calls.update(validator=0, loader=0)
        action = runtime.actions.resolve(codec.request.action)
        assert action.kind == "compose"
        stale_action = runtime.actions.reference(action.first)
        assert runtime.actions.resolve(stale_action).kind == "atom"
        object.__setattr__(arena.nodes[profile.local_id], "action", stale_action)
        object.__setattr__(hooks, "make_source_profile", forbidden_loader)
        before = runtime.ledger.snapshot()
        stale_report = collect_ledger_metrics(runtime.ledger)
        assert stale_report.forbidden_future_payloads > 0
        assert runtime.ledger.snapshot() == before
        assert calls == {"validator": 1, "loader": 0}
    finally:
        object.__setattr__(hooks, "validate_source_profile_action", validator)
        object.__setattr__(hooks, "make_source_profile", loader)


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
        definition = cast(C4PairLeftCertificate, record.definition)
        states = definition.states
        state = replace(
            states[0],
            anchor=True if fault == "bool-state" else (states[0].anchor + 1) % 50,
        )
        object.__setattr__(
            record,
            "definition",
            replace(definition, states=(state, *states[1:])),
        )
    elif fault == "foreign-profile":
        other = SemanticProfileArena(runtime)
        foreign = other.source_initial_profile(codec.request.action)
        assert arena is not None
        arena.records[key] = replace(codec, profile=foreign)
    elif fault == "wrong-side":
        assert arena is not None
        arena.records[key] = replace(codec, request=replace(codec.request, side=1))
    elif fault == "extra-structure":
        assert arena is not None
        arena.records[key] = replace(
            codec, structure=arena.component(codec, 0, structures)
        )
    else:
        assert arena is not None
        arena.records[key] = replace(
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
    arena.decodes[key] = wrong
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
        key = replace(key, profile=other.source_initial_profile(codec.request.action))
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
    forged = StructureID(structures.token, "semantic-structure", len(structures.nodes))
    structures.nodes.append(malformed)
    structures.keys[malformed] = forged.local_id
    key = ReachableDecodeKey(ReachableCodecKey(codec.profile, codec.request), 1)
    assert arena is not None
    arena.decodes[key] = forged
    assert_forbidden_payloads_read_only(app.runtime.ledger)


def test_profile_interner_cannot_borrow_an_equal_profile_from_another_arena() -> None:
    app, arena, _, _, codec = setup()
    other = SemanticProfileArena(app.runtime)
    foreign = other.source_initial_profile(codec.request.action)
    assert arena is not None
    arena.keys[codec.request.action] = foreign
    assert_forbidden_payloads_read_only(app.runtime.ledger)


@pytest.mark.parametrize(
    "component_index",
    (0, pytest.param(1, marks=pytest.mark.validation)),
)
def test_profile_table_audit_rechecks_frozen_mutations_on_next_query(
    component_index: int,
) -> None:
    app, arena, _, structures, codec = setup()
    assert arena is not None
    # Unit coverage for the exact interner-key mutation uses the compact first
    # component. The full function-decoder component remains in validation.
    function = arena.component(codec, component_index, structures)
    from number_compiler.arithmetic.functions.finite_function_types import BOOL

    all_valid = structures.functions.atom(FunctionSignature(codec.ports, BOOL), 1)
    node = structures.nodes[function.local_id]
    assert node.valid != all_valid
    assert (
        audit_registered_payloads(
            app.runtime.ledger, fresh=True
        ).forbidden_future_payloads
        == 0
    )

    # A new inventory pass must inspect the current frozen record, not reuse
    # the previous query's successful table-audit result. The record is also
    # part of the interner key, so this bypassed hash mutation must be rejected
    # without crashing the audit.
    object.__setattr__(node, "valid", all_valid)
    before = app.runtime.ledger.snapshot()
    assert (
        audit_registered_payloads(
            app.runtime.ledger, fresh=True
        ).forbidden_future_payloads
        > 0
    )
    assert app.runtime.ledger.snapshot() == before
