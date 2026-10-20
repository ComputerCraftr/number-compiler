"""Validation checks for the optional public finite-function return builder."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import replace
from types import MappingProxyType
from typing import cast

import pytest

from devtools.verification.comma_b1_quotient import offset_orbit, offset_representatives
from devtools.verification.comma_b1_source_continuation import (
    production_semantic_owner,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import return_scope_observer, symbolic_return
from number_compiler.sequences.comma.boundary_chart import PERIOD, BoundaryChart
from number_compiler.sequences.comma.return_mdd import (
    _mdd_cardinality,
    canonical_return_template,
    evaluate_return_column,
    intersect_return_columns,
    substitute_return_column,
    translate_return_column,
    translate_return_columns,
    union_return_columns,
    validate_return_mdd_partition,
)
from number_compiler.sequences.comma.return_scope_observer import (
    canonical_partition_rebase,
)
from number_compiler.sequences.comma.return_scopes import (
    B1ReturnPartitionRecord,
    ReturnColumnKey,
    ReturnMDDPartition,
    continuation_return_partition,
    scope_column_key,
)
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticAction,
    SemanticContinuation,
)
from number_compiler.sequences.comma.symbolic_return import (
    SymbolicReturnView,
    build_symbolic_returns,
)


def _scope_column(
    symbolic: SymbolicReturnView, scopes: tuple[tuple[int, int], ...]
) -> SemanticFunctionID:
    build = cast(
        Callable[[tuple[tuple[int, int], ...]], SemanticFunctionID],
        object.__getattribute__(symbolic, "_scope_column"),
    )
    return build(scopes)


def _clock_values(
    symbolic: SymbolicReturnView, function: SemanticFunctionID, phase: int
) -> dict[PortVariable, int]:
    values = cast(
        Callable[[SemanticFunctionID, int], dict[PortVariable, int]],
        object.__getattribute__(symbolic, "_clock_values"),
    )
    return values(function, phase)


@pytest.fixture(scope="module")
def source_view() -> SemanticContinuation:
    """Share its immutable published view, not any symbolic return runtime."""
    view = production_semantic_owner()
    assert type(view.transitions) is MappingProxyType
    assert type(view.source_ids) is MappingProxyType
    assert type(view.actions_by_id) is MappingProxyType
    return view


@pytest.mark.validation
def test_symbolic_returns_match_sampled_complete_controls(
    source_view: SemanticContinuation,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    assert len(symbolic.functions) == len(source_view.actions_by_id)
    assert len(set(symbolic.functions.values())) <= len(symbolic.functions)
    counters = symbolic.arena.ledger.counters
    assert len(symbolic.valid_mask_cache) <= 6
    assert counters["comma_symbolic_valid_mask_cache_misses"] == len(
        symbolic.valid_mask_cache
    )
    assert counters["comma_symbolic_valid_mask_cache_hits"] > 0
    for identifier in tuple(symbolic.functions)[:8]:
        for phase in (0, 1, 17, 460, 923):
            action = source_view.evaluate_id(identifier, phase)
            if action.kind == "stop":
                assert action.stop_j is not None
                expected = ("stop", action.stop_j)
            else:
                assert action.live_root is not None
                expected = ("live", offset_orbit(action.live_root))
            assert symbolic.evaluate(identifier, phase) == expected


@pytest.mark.validation
def test_symbolic_shift_keeps_occurrence_rebase_separate(
    source_view: SemanticContinuation,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    source = BoundaryChart("entry", 1, 0, offset_representatives()[0])
    function, occurrence_shift = symbolic.source_address(source, delta=1849)
    unshifted, no_occurrence_shift = symbolic.source_address(source)
    assert function == unshifted
    assert occurrence_shift == 1849
    assert no_occurrence_shift == 0

    identifier = source_view.source_ids[source]
    assert symbolic.shifted(identifier, 0) == symbolic.function_for(identifier)
    shifted = symbolic.shifted(identifier, 2)
    assert symbolic.shift_function(shifted, 3) == symbolic.shifted(identifier, 5)
    for phase in (0, 1, 17, 923):
        assert symbolic.evaluate_function(shifted, phase) == symbolic.evaluate(
            identifier, (phase + 2) % 924
        )

    canonical = symbolic.canonical_shift(identifier, shifts=(1, 2))
    assert not canonical.complete
    assert canonical.scanned_shifts == 2
    for phase in (0, 1, 17, 923):
        assert symbolic.evaluate_function(
            canonical.function, (phase + canonical.return_shift) % 924
        ) == symbolic.evaluate(identifier, phase)

    binding = symbolic.canonical_source_address(source, delta=1849, shifts=(1, 2))
    assert binding.input_shift == (1849 + binding.return_shift) % 924
    for phase in (0, 1, 17, 923):
        action = source_view.evaluate(source, phase, delta=1849).action
        if action.kind == "stop":
            assert action.stop_j is not None
            expected = ("stop", action.stop_j)
        else:
            assert action.live_root is not None
            expected = ("live", offset_orbit(action.live_root))
        assert symbolic.evaluate_binding(binding, phase) == expected
    for invalid_phase in (-1, True, 924):
        with pytest.raises(ValueError, match="phase"):
            symbolic.evaluate_binding(binding, invalid_phase)
    for invalid_shift in (-1, True, 924):
        with pytest.raises(ValueError, match="return shift"):
            replace(binding, return_shift=invalid_shift)
    for invalid_occurrence in (-1, True):
        with pytest.raises(ValueError, match="occurrence shift"):
            replace(binding, occurrence_shift=invalid_occurrence)


@pytest.mark.validation
def test_symbolic_shift_preserves_invalid_clock_padding_and_composes(
    source_view: SemanticContinuation,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    even_clock = _scope_column(symbolic, ((2, 0),))
    odd_clock = _scope_column(symbolic, ((2, 1),))
    for phase in range(4):
        even = symbolic.arena.evaluate(
            even_clock, _clock_values(symbolic, even_clock, phase)
        )
        odd = symbolic.arena.evaluate(
            odd_clock, _clock_values(symbolic, odd_clock, phase)
        )
        assert (even.kind, even.value) == ("atom", int(phase % 2 == 0))
        assert (odd.kind, odd.value) == ("atom", int(phase % 2 == 1))
    for component, invalid_value in (("r3", 3), ("r7", 7), ("r11", 15)):
        identifier = next(
            identifier
            for identifier, function in symbolic.functions.items()
            if any(
                port.variable.role.startswith(f"comma-clock-{component}")
                for port in symbolic.arena.signature(function).inputs
            )
        )
        function = symbolic.shifted(identifier, 2)
        values = {
            port.variable: 0 for port in symbolic.arena.signature(function).inputs
        }
        for variable in tuple(values):
            if variable.role.startswith(f"comma-clock-{component}"):
                bit = int(variable.role.rsplit("-b", 1)[1])
                values[variable] = (invalid_value >> bit) & 1
        assert symbolic.arena.evaluate(function, values).kind == "invalid"

    twice = symbolic.shift_function(symbolic.shifted(identifier, 2), 3)
    once = symbolic.shifted(identifier, 5)
    for phase in (0, 1, 17, 923):
        assert symbolic.evaluate_function(twice, phase) == symbolic.evaluate_function(
            once, phase
        )


@pytest.mark.validation
def test_symbolic_shift_reuses_clock_primitives_and_masks(
    source_view: SemanticContinuation, monkeypatch: pytest.MonkeyPatch
) -> None:
    symbolic = build_symbolic_returns(source_view)
    identifier = next(iter(symbolic.functions))
    first = symbolic.shifted(identifier, 1)
    assert len(symbolic.clock_shift_cache) > 0
    assert len(symbolic.valid_mask_cache) > 0
    symbolic.shift_cache.clear()

    def cold_primitive(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("rebuilt a cached clock primitive")

    monkeypatch.setattr(symbolic_return, "shifted_component_bit", cold_primitive)
    monkeypatch.setattr(symbolic_return, "_valid_clock_mask", cold_primitive)
    assert symbolic.shifted(identifier, 1) == first


@pytest.mark.validation
def test_complete_shift_orbit_has_one_owner_local_representative(
    source_view: SemanticContinuation,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    identifier = next(iter(symbolic.functions))
    support_period = symbolic.translation_period(symbolic.function_for(identifier))
    canonical = symbolic.canonical_shift(identifier)
    explicit = symbolic.canonical_shift(identifier, shifts=tuple(range(support_period)))
    rotations = {
        shift: tuple(
            symbolic.evaluate(identifier, (shift + phase) % support_period)
            for phase in range(support_period)
        )
        for shift in range(support_period)
    }
    expected_shift, expected_row = min(rotations.items(), key=lambda item: item[1])
    assert canonical.complete
    assert support_period < 924
    assert canonical.scanned_shifts == 1
    assert canonical.phase_reads > 0
    assert canonical.comparisons > 0
    assert explicit.complete
    assert explicit.function == canonical.function
    assert explicit.return_shift == canonical.return_shift
    assert explicit.phase_reads > 0
    assert explicit.comparisons > 0
    assert (-canonical.return_shift) % 924 == expected_shift
    assert (
        tuple(
            symbolic.evaluate_function(canonical.function, phase)
            for phase in range(support_period)
        )
        == expected_row
    )
    assert canonical.return_shift in range(924)
    assert symbolic.shifted(identifier, support_period) == symbolic.function_for(
        identifier
    )
    shifted_once = symbolic.shifted(identifier, 1)
    cache_size = len(symbolic.shift_cache)
    assert symbolic.shifted(identifier, 1 + support_period) == shifted_once
    assert len(symbolic.shift_cache) == cache_size


@pytest.mark.validation
def test_known_shift_equivalent_sources_share_canonical_function(
    source_view: SemanticContinuation,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    by_local_id = {
        identifier.local_id: source
        for source, identifier in source_view.source_ids.items()
    }
    first = symbolic.canonical_source_address(by_local_id[0])
    second = symbolic.canonical_source_address(by_local_id[29])
    assert first.complete and second.complete
    assert first.function == second.function
    for phase in (0, 1, 17, 923):
        for binding, source in (
            (first, by_local_id[0]),
            (second, by_local_id[29]),
        ):
            action = source_view.evaluate(source, phase).action
            if action.kind == "stop":
                assert action.stop_j is not None
                expected = ("stop", action.stop_j)
            else:
                assert action.live_root is not None
                expected = ("live", offset_orbit(action.live_root))
            assert symbolic.evaluate_binding(binding, phase) == expected


@pytest.mark.validation
def test_output_template_forgets_labels_but_reconstructs_them_exactly(
    source_view: SemanticContinuation,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    arena = symbolic.arena
    first_partition = (
        (0, ((4, 0),)),
        (1, ((4, 2),)),
    )
    relabeled_partition = (
        (1, ((4, 0),)),
        (0, ((4, 2),)),
    )
    first_key = canonical_partition_rebase(first_partition)[4]
    second_key = canonical_partition_rebase(relabeled_partition)[4]
    assert first_key == second_key

    source = BoundaryChart("entry", 1, 0, offset_representatives()[0])
    first = symbolic.canonical_source_template(source)
    shifted = symbolic.canonical_source_template(source, delta=37)
    assert first.complete and shifted.complete
    assert first.function == shifted.function
    assert first.output_binding
    assert arena.ledger.counters["comma_output_template_anchor_candidates"] > 0
    assert "comma_output_template_shift_candidates" not in arena.ledger.counters
    for phase in (0, 1, 17, 460, 923):
        action = source_view.evaluate(source, phase).action
        if action.kind == "stop":
            assert action.stop_j is not None
            expected = ("stop", action.stop_j)
        else:
            assert action.live_root is not None
            expected = ("live", offset_orbit(action.live_root))
        assert symbolic.evaluate_template_binding(first, phase) == expected
        rebased_action = source_view.evaluate(source, phase, delta=37).action
        if rebased_action.kind == "stop":
            assert rebased_action.stop_j is not None
            rebased_expected = ("stop", rebased_action.stop_j)
        else:
            assert rebased_action.live_root is not None
            rebased_expected = ("live", offset_orbit(rebased_action.live_root))
        assert symbolic.evaluate_template_binding(shifted, phase) == rebased_expected
    forged_labels = tuple(reversed(first.output_binding))
    if forged_labels == first.output_binding:
        forged_labels = ((first.output_binding[0] + 1) % 55,)
    forged = replace(first, output_binding=forged_labels)
    with pytest.raises(ValueError, match="stale or forged"):
        symbolic.evaluate_template_binding(forged, 0)
    foreign_arena = SemanticFunctionArena(ResourceLedger())
    foreign_function = foreign_arena.atom(
        FunctionSignature((), AtomSort("foreign-template", 1)), 0
    )
    foreign = replace(first, function=foreign_function)
    with pytest.raises(ValueError, match="different arena"):
        symbolic.evaluate_template_binding(foreign, 0)
    assert symbolic.arena.ledger.counters["comma_output_template_cache_hits"] >= 1


@pytest.mark.validation
def test_scope_canonicalization_merges_equivalent_crt_cylinders() -> None:
    compact = (
        (0, ((2, 0),)),
        (1, ((2, 1),)),
    )
    split = (
        (0, ((4, 0), (4, 2))),
        (1, ((4, 1), (4, 3))),
    )
    compact_result = canonical_partition_rebase(compact)
    split_result = canonical_partition_rebase(split)
    assert compact_result[4] == split_result[4]
    assert compact_result[0] == split_result[0]


@pytest.mark.validation
def test_mixed_period_partition_uses_extensional_rebase_anchors() -> None:
    first = (
        (0, ((2, 0), (6, 3))),
        (1, ((6, 1), (6, 5))),
    )
    second = (
        (0, ((3, 0), (6, 2), (6, 4))),
        (1, ((6, 1), (6, 5))),
    )
    assert scope_column_key(first[0][1]) == scope_column_key(second[0][1])
    canonical = canonical_partition_rebase(first)
    assert canonical[4] == canonical_partition_rebase(second)[4]
    assert canonical[0] == canonical_partition_rebase(second)[0]
    for shift in range(6):
        for partition in (first, second):
            translated = tuple(
                (
                    label,
                    tuple(
                        (period, (residue + shift) % period)
                        for period, residue in scopes
                    ),
                )
                for label, scopes in partition
            )
            result = canonical_partition_rebase(translated)
            assert result[4] == canonical[4]
            assert result[0] == canonical[0]


@pytest.mark.validation
@pytest.mark.parametrize("scope", (((5, 0),), ((2, 2),), ((True, 0),), ((2, True),)))
def test_scope_canonicalization_rejects_noncanonical_scopes(
    scope: tuple[tuple[int, int], ...],
) -> None:
    with pytest.raises((TypeError, ValueError)):
        canonical_partition_rebase(((0, scope),))


@pytest.mark.validation
def test_continuation_rejects_foreign_cached_goto_before_cache_lookup() -> None:
    owner = ArenaToken("return-scope-test")
    foreign_owner = ArenaToken("foreign-return-scope-test")
    root = ContinuationID(owner, "comma-continuation", 0)
    foreign_target = ContinuationID(foreign_owner, "comma-continuation", 0)
    source_view = SemanticContinuation(
        ResourceLedger(),
        owner,
        (),
        {},
        {},
        {},
        {root: (SemanticAction("goto", target=foreign_target),)},
    )
    cache: dict[ContinuationID, B1ReturnPartitionRecord] = {
        foreign_target: cast(
            B1ReturnPartitionRecord,
            ReturnMDDPartition(
                1,
                ((0, scope_column_key(((1, 0),))),),
            ),
        )
    }

    with pytest.raises(ValueError, match="different arena"):
        continuation_return_partition(source_view, root, cache)


def _single_stop_view(label: str) -> tuple[SemanticContinuation, ContinuationID]:
    owner = ArenaToken(label)
    identifier = ContinuationID(owner, "comma-continuation", 0)
    view = SemanticContinuation(
        ResourceLedger(),
        owner,
        (),
        {},
        {},
        {},
        {identifier: (SemanticAction("stop", stop_j=0),)},
    )
    return view, identifier


def _assert_untrusted_partition_is_not_published(
    symbolic: symbolic_return.SymbolicReturnView,
    identifier: ContinuationID,
) -> None:
    with pytest.raises(ValueError, match="foreign authority"):
        symbolic.canonical_output_template(symbolic.function_for(identifier))

    assert len(symbolic.output_template_cache) == 0
    assert len(symbolic.output_template_intern) == 0


@pytest.mark.validation
@pytest.mark.parametrize(
    "partition",
    (
        ReturnMDDPartition(
            1,
            (
                (0, scope_column_key(((2, 0),))),
                (1, scope_column_key(((2, 1),))),
            ),
        ),
        ReturnMDDPartition(
            2,
            (
                (0, scope_column_key(((1, 0),))),
                (1, scope_column_key(((1, 0),))),
            ),
        ),
    ),
    ids=("underperiod", "overlap"),
)
def test_unsealed_malformed_partition_cannot_publish_template(
    partition: ReturnMDDPartition,
) -> None:
    view, identifier = _single_stop_view("return-partition-shape")
    symbolic = build_symbolic_returns(view)
    cast(
        MutableMapping[ContinuationID, B1ReturnPartitionRecord],
        symbolic.return_partition_cache,
    )[identifier] = cast(B1ReturnPartitionRecord, partition)

    _assert_untrusted_partition_is_not_published(symbolic, identifier)
    symbolic.return_partition_cache.clear()


@pytest.mark.validation
def test_partition_period_must_be_conservative_and_columns_disjoint() -> None:
    even = scope_column_key(((2, 0),))
    odd = scope_column_key(((2, 1),))
    with pytest.raises(ValueError, match="period is not conservative"):
        validate_return_mdd_partition(ReturnMDDPartition(1, ((0, even), (1, odd))))
    with pytest.raises(ValueError, match="columns overlap"):
        validate_return_mdd_partition(ReturnMDDPartition(2, ((0, even), (1, even))))


class _ColumnWorkspace:
    def __init__(self, ledger: ResourceLedger, label: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(label, "semantic_return_column_workspace")
        self.held = 0
        self.peak = 0

    def reserve(self, nodes: int) -> None:
        self.ledger.reserve(self.owner, nodes=nodes)
        self.held += nodes
        self.peak = max(self.peak, self.held)

    def release(self, nodes: int) -> None:
        self.ledger.release(self.owner, nodes=nodes)
        self.held -= nodes


@pytest.mark.validation
def test_column_transport_reuses_shared_geometry() -> None:
    column = scope_column_key(((4, 1),))
    ledger = ResourceLedger()
    workspace = _ColumnWorkspace(ledger, "column-shift")
    charges: list[tuple[str, int]] = []

    translated = translate_return_columns(
        (column, column),
        1,
        charge=lambda name, amount: charges.append((name, amount)),
        reserve_workspace=workspace.reserve,
        release_workspace=workspace.release,
    )
    output_bindings = tuple(zip((11, 47), translated, strict=True))
    assert tuple(label for label, _ in output_bindings) == (11, 47)
    assert translated[0] == translated[1]
    assert any(
        name == "comma_output_template_mdd_shift_cache_hits" for name, _ in charges
    )
    workspace.release(workspace.held)
    assert ledger.nodes == 0


@pytest.mark.validation
def test_substitution_reserves_child_states_before_allocating_them() -> None:
    mask = scope_column_key(((4, 1),))
    continuation = ((0, scope_column_key(((1, 0),))),)
    ledger = ResourceLedger(max_nodes=4)
    workspace = _ColumnWorkspace(ledger, "substitution-work")
    charges: list[tuple[str, int]] = []

    with pytest.raises(BlockContextBudgetExceeded):
        substitute_return_column(
            mask,
            continuation,
            charge=lambda name, amount: charges.append((name, amount)),
            reserve_workspace=workspace.reserve,
            release_workspace=workspace.release,
        )
    assert workspace.held == 0
    assert ledger.nodes == 0
    assert not any(name == "comma_power_substitution_cofactors" for name, _ in charges)


@pytest.mark.validation
def test_substitution_releases_dead_call_scratch_between_compositions() -> None:
    mask = scope_column_key(((4, 1),))
    continuation = ((0, scope_column_key(((1, 0),))),)
    ledger = ResourceLedger(max_nodes=64)
    workspace = _ColumnWorkspace(ledger, "substitution-lifetime")

    first = substitute_return_column(
        mask,
        continuation,
        charge=lambda _name, _amount: None,
        reserve_workspace=workspace.reserve,
        release_workspace=workspace.release,
    )
    first_retained = workspace.held
    assert 0 < first_retained < workspace.peak

    second = substitute_return_column(
        mask,
        continuation,
        charge=lambda _name, _amount: None,
        reserve_workspace=workspace.reserve,
        release_workspace=workspace.release,
    )
    assert second == first
    assert workspace.held > first_retained
    workspace.release(workspace.held)
    assert ledger.nodes == 0


@pytest.mark.parametrize("shift", [0, 1, 13, 924, -1])
@pytest.mark.parametrize(("period", "extent"), [(28, 84), (22, 132)])
def test_shifted_substitution_matches_exact_clock_coordinates(
    shift: int, period: int, extent: int
) -> None:
    mask = scope_column_key(((3, 1), (4, 2)))
    continuation = tuple(
        (label, scope_column_key(((period, label),))) for label in range(period)
    )
    ledger = ResourceLedger()
    workspace = _ColumnWorkspace(ledger, "shifted-substitution")
    result = substitute_return_column(
        mask,
        continuation,
        shift=shift,
        charge=ledger.bump,
        reserve_workspace=workspace.reserve,
        release_workspace=workspace.release,
    )
    for phase in range(extent):
        outputs = tuple(
            label for label, column in result if evaluate_return_column(column, phase)
        )
        expected = (
            ((phase + shift) % period,) if phase % 3 == 1 or phase % 4 == 2 else ()
        )
        assert outputs == expected
    workspace.release(workspace.held)
    assert ledger.nodes == 0


def test_shifted_substitution_false_mask_never_visits_right_children() -> None:
    ledger = ResourceLedger()
    workspace = _ColumnWorkspace(ledger, "absorbing-shifted-substitution")
    continuation = ((0, scope_column_key(((28, 7),))),)
    result = substitute_return_column(
        scope_column_key(()),
        continuation,
        shift=13,
        charge=ledger.bump,
        reserve_workspace=workspace.reserve,
        release_workspace=workspace.release,
    )
    assert result == ()
    assert ledger.counters.get("comma_power_substitution_cofactors", 0) == 0
    assert ledger.counters["comma_power_substitution_states"] == 1
    workspace.release(workspace.held)
    assert ledger.nodes == 0


@pytest.mark.validation
def test_column_transport_failure_releases_reserved_workspace() -> None:
    column = scope_column_key(((4, 1),))
    ledger = ResourceLedger()
    workspace = _ColumnWorkspace(ledger, "failed-column-shift")
    shift_nodes = 0

    def fail_during_translation(name: str, amount: int) -> None:
        nonlocal shift_nodes
        if name == "comma_output_template_mdd_shift_nodes":
            shift_nodes += amount
            if shift_nodes == 2:
                raise RuntimeError("injected column translation failure")

    with pytest.raises(RuntimeError, match="injected column translation failure"):
        translate_return_columns(
            (column,),
            1,
            charge=fail_during_translation,
            reserve_workspace=workspace.reserve,
            release_workspace=workspace.release,
        )
    assert workspace.held == 0
    assert ledger.nodes == 0

    malformed = cast(ReturnColumnKey, object())
    with pytest.raises(TypeError, match="exact MDD key"):
        translate_return_columns(
            (malformed,),
            0,
            charge=lambda _name, _amount: None,
            reserve_workspace=workspace.reserve,
            release_workspace=workspace.release,
        )


@pytest.mark.validation
def test_direct_template_does_not_enter_legacy_scope_observer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    full_clock = scope_column_key(((1, 0),))
    partition = ReturnMDDPartition(1, ((17, full_clock),))

    def reject_legacy_conversion(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("direct canonical template invoked legacy observer")

    monkeypatch.setattr(
        return_scope_observer, "_legacy_rebase_result", reject_legacy_conversion
    )
    template = canonical_return_template(partition)
    assert template.period == 1
    assert template.columns == (full_clock,)
    assert template.labels == (17,)


@pytest.mark.validation
def test_mdd_keys_hash_equal_structural_dags_and_remain_collision_safe(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    first = scope_column_key(((2, 0),))
    equal = scope_column_key(((4, 0), (4, 2)))
    assert first == equal
    assert hash(first) == hash(equal)
    assert {first: "same"}[equal] == "same"

    distinct = scope_column_key(((2, 1),))

    def constant_hash(_key: ReturnColumnKey) -> int:
        return 0

    monkeypatch.setattr(ReturnColumnKey, "__hash__", constant_hash)
    collision_map = {first: "even", distinct: "odd"}
    assert first != distinct
    assert collision_map[first] == "even"
    assert collision_map[distinct] == "odd"


@pytest.mark.validation
def test_partition_cardinality_memo_reuses_equal_column_subgraphs() -> None:
    first = scope_column_key(((2, 0),))
    equal = scope_column_key(((4, 0), (4, 2)))
    memo: dict[tuple[int, ReturnColumnKey], int] = {}
    charged: list[tuple[str, int]] = []
    count_first = _mdd_cardinality(
        first, lambda name, amount: charged.append((name, amount)), memo
    )
    nodes_after_first = len(memo)
    charge_count_after_first = len(charged)
    count_equal = _mdd_cardinality(
        equal, lambda name, amount: charged.append((name, amount)), memo
    )
    assert count_first == count_equal == 462
    assert len(memo) == nodes_after_first
    assert len(charged) == charge_count_after_first


@pytest.mark.validation
def test_true_radix_columns_cover_and_transport_the_full_crt_clock() -> None:
    full_clock = scope_column_key(((1, 0),))
    even_phase = scope_column_key(((2, 0),))
    phase_mod_three = scope_column_key(((3, 1),))
    phase_mod_eleven = scope_column_key(((11, 4),))
    shifted_even = translate_return_column(even_phase, 137)
    intersection = intersect_return_columns(phase_mod_three, phase_mod_eleven)
    union = union_return_columns(phase_mod_three, phase_mod_eleven)

    assert full_clock.kind == 1
    assert validate_return_mdd_partition(ReturnMDDPartition(1, ((17, full_clock),)))
    for phase in range(PERIOD):
        assert evaluate_return_column(full_clock, phase)
        assert evaluate_return_column(even_phase, phase) == (phase % 2 == 0)
        assert evaluate_return_column(shifted_even, phase) == ((phase + 137) % 2 == 0)
        first = phase % 3 == 1
        second = phase % 11 == 4
        assert evaluate_return_column(intersection, phase) == (first and second)
        assert evaluate_return_column(union, phase) == (first or second)


@pytest.mark.validation
def test_foreign_partition_record_cannot_be_used_as_a_warm_cache_hit() -> None:
    source, source_id = _single_stop_view("partition-source-owner")
    receiver, receiver_id = _single_stop_view("partition-receiver-owner")
    source_symbolic = build_symbolic_returns(source)
    receiver_symbolic = build_symbolic_returns(receiver)
    source_partition = continuation_return_partition(
        source,
        source_id,
        source_symbolic.return_partition_cache,
    )
    assert source_partition.period == 1
    receiver_symbolic.return_partition_cache[receiver_id] = (
        source_symbolic.return_partition_cache[source_id]
    )

    _assert_untrusted_partition_is_not_published(receiver_symbolic, receiver_id)


@pytest.mark.validation
def test_b1_partition_record_constructor_requires_producer_authority() -> None:
    view, identifier = _single_stop_view("partition-record-authority")
    math_partition = ReturnMDDPartition(
        1,
        ((0, scope_column_key(((1, 0),))),),
    )
    with pytest.raises(ValueError, match="producer-owned"):
        B1ReturnPartitionRecord(
            math_partition,
            view.owner,
            identifier,
            _authority=object(),
        )


@pytest.mark.validation
def test_source_output_template_keeps_chart_shift_as_occurrence_data(
    source_view: SemanticContinuation,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    symbolic = build_symbolic_returns(source_view)
    source = BoundaryChart("entry", 1, 0, offset_representatives()[0])
    delta = 1849
    binding = symbolic.canonical_source_template(source, delta=delta)
    assert binding.complete
    assert binding.occurrence_shift == delta
    assert binding.input_shift == (delta + binding.return_shift) % PERIOD

    def poisoned(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm output-template lookup rebuilt its constructor")

    monkeypatch.setattr(type(symbolic), "_construct_output_template", poisoned)
    additional_shift = 91
    first_composition = symbolic.canonical_output_template(
        binding.source_function,
        occurrence_shift=binding.occurrence_shift + 37,
    )
    rebased = symbolic.canonical_output_template(
        binding.source_function,
        occurrence_shift=binding.occurrence_shift + 37 + additional_shift,
    )
    assert rebased.function == first_composition.function == binding.function
    assert (
        rebased.return_shift == first_composition.return_shift == binding.return_shift
    )
    for phase in (0, 1, 17, 460, 923):
        action = source_view.evaluate(source, phase, delta=delta).action
        if action.kind == "stop":
            assert action.stop_j is not None
            expected = ("stop", action.stop_j)
        else:
            assert action.live_root is not None
            expected = ("live", offset_orbit(action.live_root))
        assert symbolic.evaluate_template_binding(binding, phase) == expected
        assert symbolic.evaluate_template_binding(rebased, phase) == (
            symbolic.evaluate_template_binding(
                first_composition,
                (phase + additional_shift) % PERIOD,
            )
        )
