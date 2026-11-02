"""Exact guarded boundary actions stay source-bound and demand-aware."""

from collections.abc import Callable
from copy import copy
from dataclasses import fields, replace
from typing import TypeAlias

import pytest

from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz import border_identity as border_identity_module
from number_compiler.sequences.collatz import boundary_templates
from number_compiler.sequences.collatz.border_identity import (
    BOUNDARY_SELECTOR_IDENTITIES,
    CYCLE_89,
    CYCLE_26847,
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    PATH_305,
    PATH_630,
    BoundaryOccurrenceProducerStamp,
    BoundaryPathKind,
    BoundarySelectorGuard,
    ClosedBorderCycle,
    CycleEntryPhase,
    GuardedBorderPath,
    MixedParityMotif,
    border_return_path,
)
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    admit_boundary_macro_plan,
    boundary_metric_key,
    boundary_metric_suffix,
    select_boundary_macro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
    BoundaryTemplateIdentity,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)

BoundaryTemplateKey: TypeAlias = tuple[BoundaryTemplateIdentity, int]
BoundaryTemplateValue: TypeAlias = tuple[
    BoundaryTemplateIdentity,
    int,
    tuple[DyadicTerminalFieldAction, int, int, int],
]
BoundaryTemplateMemo: TypeAlias = OwnedMemo[BoundaryTemplateKey, BoundaryTemplateValue]


def _physical(source: int, ticks: int) -> int:
    for _ in range(ticks):
        source = 3 * source + 1 if source & 1 else source // 2
    return source


def test_guarded_macro_is_exact_and_issued_only_by_the_selector() -> None:
    macro = select_boundary_macro(2174, 13)
    assert macro is not None
    validate_boundary_macro(macro)
    assert not hasattr(CollatzBoundaryMacro, "from_structural_payload")
    assert (macro.identity, macro.repetitions, macro.physical_ticks) == (
        ENTRY_4721,
        3,
        13,
    )
    assert macro.endpoint == _physical(2174, 13)
    with pytest.raises(TypeError):
        CollatzBoundaryMacro()
    uninitialized = object.__new__(CollatzBoundaryMacro)
    with pytest.raises(ValueError, match="no producer authority"):
        validate_boundary_macro(uninitialized)

    forged = object.__new__(CollatzBoundaryMacro)
    for item in fields(macro):
        object.__setattr__(forged, item.name, getattr(macro, item.name))
    object.__setattr__(forged, "endpoint", macro.endpoint + 1)
    with pytest.raises(ValueError, match="changed after issuance"):
        validate_boundary_macro(forged)


def test_boundary_macro_rejects_rebound_same_endpoint_field_action() -> None:
    macro = select_boundary_macro(327679, 300, minimum_repetitions=2)
    assert macro is not None and macro.identity == ENTRY_89_AT_NINE
    assert macro.fields.endpoint(macro.source) == macro.endpoint
    coefficients = list(macro.fields.coefficient_snapshot()[1:])
    coefficients[2] += 1  # preserve endpoint, alter the emitted sum action
    altered = DyadicTerminalFieldAction.restore_untrusted_cache_payload(
        macro.fields.steps, tuple(coefficients)
    )
    assert not altered.producer_issued
    assert (altered.gain * macro.source + altered.offset) // (
        1 << altered.steps
    ) == macro.endpoint
    assert altered.coefficient_snapshot() != macro.fields.coefficient_snapshot()

    object.__setattr__(macro, "fields", altered)
    assert not macro.issuance_matches()
    with pytest.raises(ValueError, match="fields are malformed"):
        validate_boundary_macro(macro)


def test_cycle_display_phase_does_not_create_an_unguarded_entry_action() -> None:
    eight_entry = CycleEntryPhase(CYCLE_89, 0)
    assert eight_entry.display_label == "898"
    assert eight_entry not in BOUNDARY_SELECTOR_IDENTITIES
    assert ENTRY_89_AT_NINE.display_label == "989"
    assert boundary_metric_suffix(ENTRY_89_AT_NINE) == "989"
    assert admit_boundary_macro_plan(18, 100, minimum_repetitions=1) is None
    with (
        BoundaryActionTemplateMemo(ResourceLedger()) as templates,
        pytest.raises(ValueError, match="unknown Collatz boundary action"),
    ):
        templates.get(eight_entry, 2)


def test_mixed_motif_keeps_order_and_rejects_changed_cache_identity() -> None:
    motif = MixedParityMotif((0, 1))
    rotated = MixedParityMotif((1, 0))
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        action = templates.get(motif, 8)[0]
        assert templates.get(motif, 8)[0] is action
        assert templates.get(rotated, 8)[0].offset != action.offset
        object.__setattr__(motif, "bits", rotated.bits)
        with pytest.raises(ValueError, match="changed after admission"):
            templates.get(motif, 8)


def test_nine_entry_boundary_metrics_keep_schema_eight_spellings() -> None:
    assert tuple(
        boundary_metric_key(ENTRY_89_AT_NINE, metric)
        for metric in _collatz_keys.BoundaryMacroMetric
    ) == (
        "collatz_physical_boundary_989_macro_actions",
        "collatz_physical_boundary_989_macro_repetitions",
        "collatz_physical_boundary_989_macro_physical_ticks",
    )
    assert tuple(map(boundary_metric_suffix, ENTRY_26847_PHASES)) == (
        "26847",
        "26847P1",
        "26847P2",
        "26847P3",
        "26847P4",
    )


def test_repeated_cycle_labels_keep_explicit_phase_and_guarded_ports() -> None:
    cycle, rotated_entry = ClosedBorderCycle.from_rotation(
        (2, 1, 2, 1), entry_position=0
    )
    assert cycle.ports is cycle.ports
    first = CycleEntryPhase(cycle, rotated_entry)
    second = CycleEntryPhase(cycle, 1)
    assert first.entry_digit == second.entry_digit == 2
    assert first.phase == 3
    assert first.phase != second.phase
    assert first.structural_key() != second.structural_key()
    with pytest.raises(ValueError, match="exactly one phase"):
        cycle.phase_for_entry(1)

    eight_entry = CycleEntryPhase(CYCLE_89, 0)
    assert eight_entry.selector_guard is None
    assert ENTRY_89_AT_NINE.selector_guard == BoundarySelectorGuard(9, 10, 1)
    assert ENTRY_89_AT_NINE.display_label == "989"


def test_cycle_rotation_moves_complete_guarded_ports_without_reflection() -> None:
    nine_guard = BoundarySelectorGuard(9, 10, 1)
    canonical, canonical_entry = ClosedBorderCycle.from_rotation(
        (8, 9), (None, nine_guard), entry_position=1
    )
    rotated, rotated_entry = ClosedBorderCycle.from_rotation((9, 8), (nine_guard, None))
    misplaced, _ = ClosedBorderCycle.from_rotation((8, 9), (nine_guard, None))
    assert rotated == canonical
    assert CycleEntryPhase(rotated, rotated_entry) == CycleEntryPhase(
        canonical, canonical_entry
    )
    assert CycleEntryPhase(rotated, rotated_entry).display_label == "989"
    assert misplaced != canonical
    assert ENTRY_89_AT_NINE.cycle == canonical

    assert PATH_630.display_label == "6→3→0"
    assert PATH_305.display_label == "3→0*→5"
    assert PATH_630.selector_guard == BoundarySelectorGuard(6, 20, 1)
    assert PATH_305.selector_guard == BoundarySelectorGuard(3, 10, 1)
    assert border_return_path(3, 8).display_label == "3→0*→5→6→8"
    assert border_return_path(6, 8).display_label == "6→3→0*→5→6→8"
    assert border_return_path(5, 3).display_label == "5→6→3→0*→5→6→3"
    assert border_return_path(0, 4).display_label == "0*→(3|5→6→3)→0*→5→6→8→4"

    with pytest.raises(ValueError, match="exact entry and exit"):
        GuardedBorderPath(BoundaryPathKind.SIX_THREE_ZERO, 6, 3)


def test_guarded_cycle_key_fits_a_bounded_source_image_descriptor() -> None:
    identity = ENTRY_26847_PHASES[0]
    key = identity.structural_key()
    assert key == (
        "collatz-closed-border-cycle-v3",
        CYCLE_26847.digits,
        tuple(
            None if guard is None else guard.wire_value()
            for guard in CYCLE_26847.selector_guards
        ),
        0,
    )
    phases: list[int] = []
    for entry in ENTRY_26847_PHASES:
        entry_key = entry.structural_key()
        assert type(entry_key) is tuple and len(entry_key) == 4
        phase = entry_key[3]
        assert type(phase) is int
        phases.append(phase)
    assert tuple(phases) == tuple(range(len(ENTRY_26847_PHASES)))
    unguarded_cycle, _ = ClosedBorderCycle.from_rotation(CYCLE_26847.digits)
    assert unguarded_cycle.structural_key(0) != CYCLE_26847.structural_key(0)

    macro = select_boundary_macro(112, 6, minimum_repetitions=1)
    assert macro is not None and macro.identity == identity
    SourceImageCandidate(
        payload=0,
        extent=macro.physical_ticks,
        boundary_ports=(
            ("collatz-first-boundary-macro-v1", (0, macro.structural_payload())),
        ),
    )


def test_cycle_and_phase_reject_forged_mutation_before_key_consumption() -> None:
    nine_guard = BoundarySelectorGuard(9, 10, 1)
    cycle, _ = ClosedBorderCycle.from_rotation((8, 9), (None, nine_guard))
    entry = CycleEntryPhase(cycle, 1)
    cycle_hash = hash(cycle)
    entry_hash = hash(entry)
    cycle_keys = {cycle: "canonical"}
    entry_keys = {entry: "phase-nine"}
    assert hash(cycle) == cycle_hash
    assert hash(entry) == entry_hash
    assert cycle_keys[cycle] == "canonical"
    assert entry_keys[entry] == "phase-nine"

    object.__setattr__(cycle, "digits", (9, 8))
    with pytest.raises(ValueError, match="changed after admission"):
        cycle_keys[cycle]
    with pytest.raises(ValueError, match="changed after admission"):
        entry_keys[entry]

    guarded_cycle, _ = ClosedBorderCycle.from_rotation((8, 9), (None, nine_guard))
    guarded_entry = CycleEntryPhase(guarded_cycle, 1)
    object.__setattr__(nine_guard, "residue", 8)
    with pytest.raises(ValueError, match="changed after admission"):
        _ = guarded_entry.selector_guard
    with pytest.raises(ValueError, match="changed after admission"):
        guarded_entry.structural_key()

    phase_cycle, _ = ClosedBorderCycle.from_rotation((1, 2, 1, 2))
    fresh_entry = CycleEntryPhase(phase_cycle, 1)
    object.__setattr__(fresh_entry, "phase", 0)
    with pytest.raises(ValueError, match="changed after admission"):
        _ = fresh_entry.display_label
    with pytest.raises(ValueError, match="changed after admission"):
        hash(fresh_entry)


@pytest.mark.parametrize(
    ("field", "value"),
    (("modulus", 0), ("residue", 10), ("minimum_source", 0)),
)
def test_border_admission_rejects_previously_corrupted_guard(
    field: str, value: int
) -> None:
    guard = BoundarySelectorGuard(9, 10, 1)
    object.__setattr__(guard, field, value)
    with pytest.raises(ValueError, match="invalid finite boundary selector guard"):
        ClosedBorderCycle.from_rotation((8, 9), (None, guard))
    with pytest.raises(ValueError, match="invalid finite boundary selector guard"):
        GuardedBorderPath(BoundaryPathKind.THREE_ZERO_FIVE, 3, 5, guard)


def test_cycle_cache_key_validation_does_not_recanonicalize(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cycle, _ = ClosedBorderCycle.from_rotation((8, 9))

    def forbidden(*args: object, **kwargs: object) -> object:
        raise AssertionError("cycle reuse must not rediscover canonical rotation")

    monkeypatch.setattr(border_identity_module, "canonical_cycle_rotation", forbidden)
    first_hash = hash(cycle)
    assert hash(cycle) == first_hash
    assert cycle == cycle
    assert len(cycle.ports) == 2


@pytest.mark.parametrize(
    ("source", "ticks", "identity"),
    (
        (164, 7, ENTRY_421),
        (94, 9, ENTRY_4721),
        (26, 5, PATH_630),
        (19, 4, ENTRY_89_AT_NINE),
    ),
)
def test_each_guarded_family_matches_endpoint_f5_joint_and_width(
    source: int, ticks: int, identity: object
) -> None:
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ResourceLedger(),
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
        include_innovation_tape=True,
    )
    endpoint = _physical(source, ticks)
    assert result.endpoint == endpoint
    assert result.run_actions == 1
    assert result.first_boundary is not None
    assert result.first_boundary[0] == 0
    assert result.first_boundary_macro is not None
    assert result.first_boundary_macro.identity == identity
    assert result.first_boundary_macro.endpoint == endpoint
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == endpoint % 5
    assert result.joint_action is not None
    assert result.joint_action.endpoint == endpoint
    assert result.tape_width_summary is not None
    assert result.tape_width_summary.target_width == endpoint.bit_length()


@pytest.mark.parametrize("source,ticks", ((164, 7), (94, 9), (26, 5), (19, 4)))
def test_partial_boundary_ranges_still_match_literal_physical_steps(
    source: int, ticks: int
) -> None:
    result = compile_collatz_temporal_run_quotient(
        source, ticks - 1, ledger=ResourceLedger(), include_innovation_tape=True
    )
    assert result.endpoint == _physical(source, ticks - 1)
    if result.first_boundary_macro is not None:
        assert result.first_boundary is not None
        assert (
            result.first_boundary[0] + result.first_boundary_macro.physical_ticks
            <= ticks - 1
        )


@pytest.mark.parametrize(
    ("source", "ticks", "identity", "repetitions"),
    (
        (164, 7, ENTRY_421, 2),
        (2174, 13, ENTRY_4721, 3),
        (30, 9, ENTRY_0563, 2),
        (112, 6, ENTRY_26847_PHASES[0], 1),
        (296, 10, ENTRY_26847_PHASES[1], 2),
        (148, 9, ENTRY_26847_PHASES[2], 2),
        (74, 8, ENTRY_26847_PHASES[3], 2),
        (37, 7, ENTRY_26847_PHASES[4], 2),
        (26, 5, PATH_630, 2),
        (13, 4, PATH_305, 2),
        (19, 4, ENTRY_89_AT_NINE, 2),
    ),
)
def test_admitted_plan_binds_a_repetition_limit_for_each_identity(
    source: int, ticks: int, identity: object, repetitions: int
) -> None:
    plan = admit_boundary_macro_plan(source, ticks, minimum_repetitions=1)

    assert plan is not None
    assert plan.identity == identity
    assert plan.repetitions == repetitions
    assert plan.maximum_repetitions >= plan.repetitions
    assert plan.physical_ticks == ticks


def test_midrun_boundary_occurrence_cannot_be_rebound() -> None:
    result = compile_collatz_temporal_run_quotient(
        109,
        9,
        ledger=ResourceLedger(),
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
        include_innovation_tape=True,
    )
    assert result.first_boundary is not None
    assert result.first_boundary[0] == 2
    assert result.first_boundary_macro is not None
    assert result.first_boundary[1] == 164
    assert result.first_boundary_stamp is not None
    with pytest.raises(ValueError, match="lost producer authority"):
        replace(result, first_boundary_stamp=copy(result.first_boundary_stamp))
    with pytest.raises(ValueError, match="lost producer authority"):
        replace(
            result,
            first_boundary=(
                0,
                result.first_boundary[1],
                result.first_boundary[2],
                result.first_boundary[3],
            ),
        )
    assert not result.first_boundary_stamp.certifies(
        True,
        result.physical_ticks,
        result.first_boundary,
        result.first_boundary_macro,
    )
    replacement_macro = select_boundary_macro(164, 7)
    assert replacement_macro is not None
    assert replacement_macro is not result.first_boundary_macro
    object.__setattr__(result.first_boundary_stamp, "macro", replacement_macro)
    with pytest.raises(ValueError, match="lost producer authority"):
        result.validate_boundary_producer_stamp()


def test_long_quiet_boundary_is_one_pumped_action_without_d8_discovery() -> None:
    source = 4 + 40 * (1 << 256)
    ticks = 388
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
    )
    endpoint = _physical(source, ticks)
    assert result.endpoint == endpoint
    assert result.run_actions == 1
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == endpoint % 5
    assert result.joint_action is not None
    assert result.joint_action.endpoint == endpoint
    assert result.tape_width_summary is not None
    assert result.tape_width_summary.target_width == endpoint.bit_length()
    assert ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) == 0
    assert ledger.counters["collatz_physical_boundary_421_macro_actions"] == 1


def test_template_memo_warm_hit_bypasses_exact_cold_constructor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    with BoundaryActionTemplateMemo(ledger) as memo:
        cold = memo.get(ENTRY_4721, 2)

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("warm boundary template lookup rebuilt its action")

        monkeypatch.setattr(
            boundary_templates, "build_boundary_action_template", forbidden
        )
        assert memo.get(ENTRY_4721, 2) is cold
    assert ledger.counters["collatz_boundary_template_publications"] == 1
    assert ledger.counters["collatz_boundary_template_hits"] == 1


def test_template_memo_cleanup_failure_blocks_use_and_can_be_retried(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    memo = BoundaryActionTemplateMemo(ledger)
    memo.get(ENTRY_4721, 2)
    owner = next(
        account.owner
        for account in ledger.inventory()
        if account.name.startswith("collatz-boundary-action-templates-")
    )
    original_dispose: Callable[[BoundaryTemplateMemo], None] = OwnedMemo[
        BoundaryTemplateKey, BoundaryTemplateValue
    ].dispose
    failed = False

    def fail_once(instance: BoundaryTemplateMemo) -> None:
        nonlocal failed
        if not failed:
            failed = True
            raise RuntimeError("injected template cleanup failure")
        original_dispose(instance)

    monkeypatch.setattr(OwnedMemo, "dispose", fail_once)
    with pytest.raises(RuntimeError, match="injected template cleanup failure"):
        memo.dispose()

    assert failed
    assert ledger.inventory_owner(owner).entries > 0
    with pytest.raises(RuntimeError, match="closed"):
        memo.get(ENTRY_4721, 2)

    memo.dispose()
    disposed = ledger.inventory_owner(owner)
    assert disposed.disposed and disposed.entries == disposed.nodes == 0


def test_foreign_macro_cannot_publish_at_another_root_origin() -> None:
    source_macro = select_boundary_macro(164, 7)
    assert source_macro is not None
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), 165, 7, include_innovation_tape=True
    )
    candidate = SourceImageCandidate(workspace.root_payload, workspace.steps)
    occurrence = (0, 164, source_macro.physical_ticks, source_macro.identity)
    stamp = BoundaryOccurrenceProducerStamp.from_selected_macro(165, 7, 7, source_macro)
    with pytest.raises(ValueError, match="outside its demanded root"):
        workspace.attach_boundary_macro(candidate, occurrence, stamp, source_macro)


def test_macro_occurrence_retention_is_ledger_owned_and_disposed() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(
        ledger,
        2174,
        13,
        retain_chronology=False,
        include_innovation_tape=True,
    )
    assert workspace.first_boundary_macro is not None
    owner = next(
        account.owner
        for account in ledger.inventory()
        if account.name.startswith("collatz-boundary-macro-occurrences-")
    )
    before = ledger.inventory_owner(owner)
    assert before.entries == 1 and before.nodes > 0

    workspace.dispose()

    after = ledger.inventory_owner(owner)
    assert after.disposed
    assert after.entries == 0 and after.nodes == 0


def test_run_constructor_publishes_only_a_demanded_executed_macro() -> None:
    ordinary_ledger = ResourceLedger()
    ordinary = compile_collatz_temporal_run_quotient(2174, 13, ledger=ordinary_ledger)
    assert ordinary.endpoint == _physical(2174, 13)
    assert ordinary.first_boundary is None
    assert ordinary.first_boundary_macro is None
    assert ordinary_ledger.counters["collatz_physical_boundary_4721_macro_actions"] == 1
    assert ordinary_ledger.counters.get("collatz_boundary_template_publications") == 1

    observed_ledger = ResourceLedger()
    observed = compile_collatz_temporal_run_quotient(
        2174, 13, ledger=observed_ledger, include_innovation_tape=True
    )
    assert observed.endpoint == ordinary.endpoint
    assert observed.first_boundary is not None
    assert observed.first_boundary[0] == 0
    assert observed.first_boundary_macro is not None
    assert observed.first_boundary_macro.source == 2174


def test_reentered_chain_keeps_the_first_boundary_source_authoritative() -> None:
    # The root reaches a later reentry point before applying a joined action.
    # The final result need not retain that non-root chain, so assert its actual
    # application through the production counter and its published boundary.
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        4348,
        300,
        ledger=ledger,
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
        include_innovation_tape=True,
        innovation_modulus=49,
    )

    assert (
        ledger.counters[_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_APPLIED_ACTIONS] > 0
    )
    assert result.first_boundary is not None
    assert result.first_boundary[0] > 0
    assert result.first_boundary[1] != result.source
    assert result.first_boundary_macro is not None
    assert result.first_boundary[1] == result.first_boundary_macro.source
    assert result.first_boundary_stamp is not None
    assert result.first_boundary_stamp.certifies(
        result.source,
        result.physical_ticks,
        result.first_boundary,
        result.first_boundary_macro,
    )


def test_selected_macro_stamp_uses_witness_source_after_outer_rebase() -> None:
    macro = select_boundary_macro(164, 7)
    assert macro is not None
    stamp = BoundaryOccurrenceProducerStamp.from_selected_macro(
        4348, 128, 111, macro, boundary_offset=17
    )

    assert stamp.occurrence == (17, 164, 7, ENTRY_421)
    assert stamp.certifies(4348, 128, stamp.occurrence, macro)


def test_ordinary_odd_run_does_not_build_observer_specific_989_macro() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(19, 4, ledger=ledger)
    assert result.endpoint == _physical(19, 4)
    assert result.first_boundary_macro is None
    assert ledger.counters.get("collatz_physical_boundary_989_macro_actions", 0) == 0
    assert ledger.counters.get("collatz_boundary_template_lookups") is None


@pytest.mark.usefixtures("isolated_process_cache")
def test_warm_guarded_parent_is_used_before_cold_macro_or_d8(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import clear_process_cache

    clear_process_cache()
    source = 4 + 40 * (1 << 256)
    compile_collatz_temporal_run_quotient(
        source, 388, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        cell = macros.lookup(source, 256)
        assert cell is not None and cell.width == 256
        physical_ticks = cell.width + cell.odd_symbols

    def forbidden_template(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm parent reconstructed the guarded action")

    def forbidden_d8(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm parent fell back to D8 discovery")

    monkeypatch.setattr(
        boundary_templates, "build_boundary_action_template", forbidden_template
    )
    monkeypatch.setattr(D8TemporalTable, "select", forbidden_d8)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source, physical_ticks, ledger=ledger, shared_cache=True
    )
    assert result.endpoint == cell.apply(source)
    assert result.normalized_symbols == 256
    assert ledger.counters["collatz_hashlife_occurrence_applied_hits"] == 1
    assert ledger.counters.get("collatz_physical_boundary_plan_checks", 0) == 0
    assert ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) == 0
    assert ledger.counters.get("collatz_physical_boundary_421_macro_actions", 0) == 0
    clear_process_cache()


def test_eight_bit_parity_prefix_does_not_authorize_a_longer_action() -> None:
    from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder
    from number_compiler.sequences.collatz.parity import normalized_collatz

    cylinder = HenselCylinder(8, 1)
    assert cylinder.contains(1) and cylinder.contains(257)
    assert not HenselCylinder(9, 1).contains(257)

    endpoints: list[int] = []
    for source in (1, 257):
        value = source
        odd_symbols = 0
        for _ in range(8):
            odd_symbols += value & 1
            value = normalized_collatz(value)
        result = compile_collatz_temporal_run_quotient(
            source,
            8 + odd_symbols,
            ledger=ResourceLedger(),
        )
        assert result.normalized_symbols == 8
        assert result.endpoint == value
        endpoints.append(value)
    assert endpoints == [1, 82]


def test_demanded_989_macro_keeps_the_exact_completed_endpoint() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        19, 4, ledger=ledger, include_innovation_tape=True
    )
    assert result.endpoint == _physical(19, 4)
    assert result.first_boundary_macro is not None
    assert result.first_boundary_macro.identity == ENTRY_89_AT_NINE
