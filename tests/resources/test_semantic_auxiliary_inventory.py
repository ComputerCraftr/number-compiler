"""Issued metadata does not excuse malformed finite interfaces or foreign IDs."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_state_codec import StateCodecArena
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.projection.lazy_radix import collatz_radix_digit
from number_compiler.projection.radix_fused_action import (
    FusedRadixArena,
    FusedRadixBindingKey,
)
from number_compiler.projection.radix_original_source import OriginalRadixArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.semantic_payload import SemanticPayloadRegistry
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.assertions import (
    assert_mutation_rejected,
    assert_rejected_atomically,
)
from tests.support.diamond_continuation_reduction import machine

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_state_codec import (
        StateCodec,
    )


def registry(
    ledger: ResourceLedger,
) -> SemanticPayloadRegistry:
    diamond = DiamondPayloadRegistry(ledger)
    return SemanticPayloadRegistry(ledger, lambda value: False, diamond._handle)


def codec() -> tuple[StateCodecArena, StateCodec]:
    runtime, action = machine()
    arena = StateCodecArena(runtime, StructureArena(BitFunctionArena(runtime.ledger)))
    record = arena.compile(runtime.actions.compose(action, action), 0)
    return arena, record


@pytest.mark.parametrize("composed", (False, True))
def test_codec_inventory_is_complete_read_only_and_requires_issued_record(
    composed: bool,
) -> None:
    runtime, action = machine()
    arena = StateCodecArena(runtime, StructureArena(BitFunctionArena(runtime.ledger)))
    record = arena.compile(
        runtime.actions.compose(action, action) if composed else action, 0
    )
    before = runtime.ledger.snapshot()
    audit = registry(runtime.ledger)
    assert audit.valid(record) and audit.valid(record.request)
    assert not audit.valid(replace(record))
    metrics = collect_ledger_metrics(runtime.ledger)
    assert metrics.resource_audit_complete == 1
    assert metrics.forbidden_future_payloads == 0
    assert runtime.ledger.snapshot() == before


@pytest.mark.parametrize(
    "field,value",
    (
        ("owner", ArenaToken("unissued")),
        ("anchor_cardinality", True),
        ("anchor_cardinality", 1 << 1000),
        ("continuation_cardinality", True),
        ("component_ports", []),
        ("ports", []),
        ("argument_port", None),
    ),
)
def test_codec_rechecks_mutated_record_domains_and_all_immutable_fields(
    field: str, value: object
) -> None:
    arena, record = codec()
    assert_mutation_rejected(
        record, field, value, lambda candidate: registry(arena.ledger).valid(candidate)
    )


def test_codec_rejects_same_ledger_wrong_structure_owner_and_wrong_namespace() -> None:
    arena, record = codec()
    other = StateCodecArena(
        arena.runtime, StructureArena(BitFunctionArena(arena.ledger))
    )
    foreign = other.compile(record.request.action, 0)
    original = record.structure
    object.__setattr__(record, "structure", foreign.structure)
    try:
        assert not registry(arena.ledger).valid(record)
    finally:
        object.__setattr__(record, "structure", original)
    old = record.request.namespace
    object.__setattr__(record.request, "namespace", PortVariable(5, 0, "wrong", 0))
    try:
        assert not registry(arena.ledger).valid(record)
    finally:
        object.__setattr__(record.request, "namespace", old)


@pytest.mark.parametrize("physical", (False, True))
def test_fused_complete_interface_inventory_is_read_only(physical: bool) -> None:
    arena = FusedRadixArena(ResourceLedger())
    record = arena.compile((1, 0, 1), radix=3, stages=2, physical=physical)
    before = arena.ledger.snapshot()
    assert registry(arena.ledger).valid(record)
    assert not registry(arena.ledger).valid(replace(record))
    metrics = collect_ledger_metrics(arena.ledger)
    assert metrics.resource_audit_complete == 1
    assert metrics.forbidden_future_payloads == 0
    assert arena.ledger.snapshot() == before


@pytest.mark.parametrize(
    "field,value",
    (
        ("radix", True),
        ("radix", 13),
        ("stages", 0),
        ("stages", 5),
        ("level", 1 << 1000),
        ("physical", 1),
        ("ports", []),
        ("physical_exit", ()),
        ("division_exit", ((0, 1),)),
    ),
)
def test_fused_record_rejects_unbounded_or_untyped_channel_metadata(
    field: str, value: object
) -> None:
    arena = FusedRadixArena(ResourceLedger())
    record = arena.compile((1,), radix=3, stages=1, physical=False)
    assert_mutation_rejected(
        record, field, value, lambda candidate: registry(arena.ledger).valid(candidate)
    )


@pytest.mark.parametrize("foreign", (False, True))
def test_fused_channels_require_actual_function_owner_and_full_joint_signature(
    foreign: bool,
) -> None:
    arena = FusedRadixArena(ResourceLedger())
    record = arena.compile((1,), radix=3, stages=1, physical=False)
    functions = SemanticFunctionArena(arena.ledger) if foreign else arena.functions
    signature = FunctionSignature(record.ports if foreign else (), BOOL)
    wrong = functions.atom(signature, 0)
    original = record.output
    object.__setattr__(record, "output", wrong)
    try:
        assert not registry(arena.ledger).valid(record)
    finally:
        object.__setattr__(record, "output", original)


@pytest.mark.parametrize(
    "field,kind", (("valid", "false"), ("valid", "true"), ("output", "invalid"))
)
def test_fused_interface_must_cover_every_legal_input_and_normalize_unused_codes(
    field: str, kind: str
) -> None:
    arena = FusedRadixArena(ResourceLedger())
    record = arena.compile((1,), radix=3, stages=1, physical=False)
    signature = FunctionSignature(record.ports, BOOL)
    wrong = (
        arena.functions.invalid(signature)
        if kind == "invalid"
        else arena.functions.atom(signature, int(kind == "true"))
    )
    original = getattr(record, field)
    object.__setattr__(record, field, wrong)
    try:
        assert not registry(arena.ledger).valid(record)
    finally:
        object.__setattr__(record, field, original)


@pytest.mark.parametrize("steps", (0, 1))
@pytest.mark.parametrize("radix", (3, 6))
def test_public_radix_inventory_matches_actual_native_or_complete_action_route(
    steps: int, radix: int
) -> None:
    term = PoweredCollatzTerm(27, steps)
    expected = 27 if not steps else 82
    assert collatz_radix_digit(term, radix, 1) == expected // radix % radix
    before = term._ledger.snapshot()
    report = collect_ledger_metrics(term._ledger)
    assert report.resource_audit_complete == 1
    assert report.forbidden_future_payloads == 0
    assert report.cache_slots == term._ledger.entries
    assert term._ledger.snapshot() == before


def test_actual_fused_binding_must_match_stage_and_source_mode() -> None:
    term = PoweredCollatzTerm(27, 1)
    collatz_radix_digit(term, 10, 0)
    projection = term._radix_projections[10]
    key = FusedRadixBindingKey(1)
    value = next(iter(projection._fused_actions.values()))
    term._ledger.reserve(projection._fused_actions.owner, entries=1)
    projection._fused_actions._data[key] = value
    report = collect_ledger_metrics(term._ledger)
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0


def test_original_reencoding_is_valid_under_point_scope_without_exact_tree_calls(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(27, 0)
    arena = OriginalRadixArena(term._ledger)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("original reencoding attempted an exact tree constructor")

    from number_compiler.arithmetic.fields import dyadic_tile

    monkeypatch.setattr(dyadic_tile, "leaf", forbidden)
    monkeypatch.setattr(dyadic_tile, "join", forbidden)
    record = source_reads_only(arena.encode)(term._source_construction, 3)
    assert record.digits == (0, 0, 0, 1)
    before = term._ledger.snapshot()
    assert registry(term._ledger).valid(record)
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    assert term._ledger.snapshot() == before


def test_exact_source_role_cannot_launder_a_future_radix_encoding() -> None:
    term = PoweredCollatzTerm(27, 1)
    arena = OriginalRadixArena(term._ledger)
    record = arena.encode(term._source_construction, 3)
    original = record.digits
    object.__setattr__(record, "digits", (1, 0, 0, 1))  # 28, not the original 27.
    try:
        assert not registry(term._ledger).valid(record)
        report = collect_ledger_metrics(term._ledger)
        assert report.forbidden_future_payloads > 0
        assert report.representation_boundary_complete == 0
    finally:
        object.__setattr__(record, "digits", original)


def test_same_ledger_distinct_original_cannot_reuse_warm_radix_action() -> None:
    ledger = ResourceLedger()
    first = PoweredCollatzTerm(27, 1)
    second = PoweredCollatzTerm(29, 1)
    ledger = first._ledger
    second._ledger = ledger
    collatz_radix_digit(first, 6, 0)
    projection = first._radix_projections[6]
    assert_rejected_atomically(
        ledger,
        lambda: projection.digit(second, 0),
        ValueError,
        match="another binary source",
    )
