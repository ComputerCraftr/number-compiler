from __future__ import annotations

from collections.abc import Callable
from typing import cast

import pytest

from devtools.verification import comma_borrow_vieta_audit as audit
from devtools.verification.comma_semantic_quotients import CommaFutureGraph
from number_compiler.sequences.comma import (
    boundary_occurrence_chart as chart_occurrence_module,
)
from number_compiler.sequences.comma.boundary_carry_clock import (
    GuardedC1ChartPower,
    powered_chart_carry,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD, BoundaryChart
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
    MacroTemplate,
    construct_macro,
)
from number_compiler.sequences.comma.carry_generator import BitsCharge, WorkCharge
from number_compiler.sequences.comma.occurrence import OccurrencePrefixReturn

_state_id = cast(
    Callable[[BoundaryState], int],
    object.__getattribute__(audit, "_state_id"),
)
_macro_child_returns = cast(
    Callable[
        [
            int,
            int,
            tuple[BoundaryState, ...],
            tuple[MacroTemplate, ...],
            dict[tuple[int, int], OccurrencePrefixReturn],
        ],
        tuple[OccurrencePrefixReturn | None, OccurrencePrefixReturn | None],
    ],
    object.__getattribute__(audit, "_macro_child_returns"),
)
_pointed_only_payload = cast(
    Callable[[CommaFutureGraph], dict[str, object]],
    object.__getattribute__(audit, "_pointed_only_payload"),
)


def test_macro_cycle_fragments_use_the_shared_powered_c1_return(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = BoundaryState("Z", 2, 10)
    macro = construct_macro(state, grouped_near=True)
    assert any(fragment.period for fragment in macro.sector_fragments)
    calls: list[tuple[BoundaryChart, int]] = []
    shared_powered_chart_carry = powered_chart_carry

    def tracked_power(
        exponent_phase: int,
        chart: BoundaryChart,
        exponent: int,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> GuardedC1ChartPower:
        calls.append((chart, steps))
        return shared_powered_chart_carry(
            exponent_phase,
            chart,
            exponent,
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )

    monkeypatch.setattr(chart_occurrence_module, "powered_chart_carry", tracked_power)
    result = audit.macro_c1_return_constructive(macro, 10)
    assert calls
    assert any(steps > 1 for _, steps in calls)
    # Only Near -> Near segments still need the shared recurrence power.
    # Entry -> Near counts are consumed from their sealed chart endpoint, and
    # Near -> Entry seams are one literal edge.
    assert len(calls) == sum(
        segment.source.kind == "near" and segment.target.kind == "near"
        for segment in macro.chart_segments
    )
    assert tuple(chart for chart, _ in calls) == tuple(
        segment.source
        for segment in macro.chart_segments
        if segment.source.kind == "near" and segment.target.kind == "near"
    )
    assert 0 <= result.terminal_low_suffix < 100
    assert result.c1_count >= 0


def test_entry_macro_uses_closed_c1_count_without_repowering_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = BoundaryState("Z", 2, 10)
    exponent = 10
    macro = construct_macro(state, grouped_near=True)
    scale = 10**exponent
    expected_entry_count = 0
    expected_near_counts: list[int] = []
    expected_seam_count = 0

    for segment in macro.chart_segments:
        steps = chart_occurrence_module.weighted_chart_value(
            segment.duration,
            scale,
            segment.source.delta,
            charge_work=None,
            charge_bits=None,
        )
        displacement = chart_occurrence_module.weighted_chart_value(
            segment.displacement,
            scale,
            segment.source.delta,
            charge_work=None,
            charge_bits=None,
        )
        source_value = chart_occurrence_module.chart_value(
            segment.source, scale, charge_work=None, charge_bits=None
        )
        target_delta = segment.target.delta - segment.source.delta
        assert target_delta in (0, 1)
        target_scale = scale * (10 if target_delta else 1)
        target_value = chart_occurrence_module.chart_value(
            segment.target, target_scale, charge_work=None, charge_bits=None
        )
        assert target_value - source_value == displacement

        if segment.target.kind == "entry":
            assert segment.source.kind == "near"
            assert steps == 1
            expected_seam_count += target_value // 100 - source_value // 100
        else:
            reference = powered_chart_carry(
                state.exponent_residue, segment.source, exponent, steps
            )
            assert reference.displacement == displacement
            if segment.source.kind == "entry":
                expected_entry_count += reference.carry_count
            else:
                expected_near_counts.append(reference.carry_count)

        scale = target_scale

    assert expected_entry_count > 0
    shared_powered_chart_carry = powered_chart_carry
    observed_near_counts: list[int] = []

    def reject_entry_repower(
        exponent_phase: int,
        chart: BoundaryChart,
        receiving_exponent: int,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> GuardedC1ChartPower:
        if chart.kind == "entry":
            pytest.fail("Entry action was rebuilt instead of using its closed C1 count")
        powered = shared_powered_chart_carry(
            exponent_phase,
            chart,
            receiving_exponent,
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        observed_near_counts.append(powered.carry_count)
        return powered

    monkeypatch.setattr(
        chart_occurrence_module, "powered_chart_carry", reject_entry_repower
    )
    result = audit.macro_c1_return_constructive(macro, exponent)
    assert observed_near_counts == expected_near_counts
    assert result.c1_count == (
        expected_entry_count + expected_seam_count + sum(expected_near_counts)
    )


def test_child_returns_use_actual_transported_exponent() -> None:
    parent = BoundaryState("N", 5, 921)
    parent_macro = construct_macro(parent, grouped_near=True)
    assert parent_macro.exponent_delta == 8
    assert parent_macro.ordered_children == (
        BoundaryState("N", 6, 5),
        BoundaryState("Z", 6, 5),
    )
    actual_exponent = audit.canonical_exponent(parent.exponent_residue)
    actual_exponent += parent_macro.exponent_delta
    assert actual_exponent == 929

    states = tuple(
        BoundaryState(kind, a, residue)
        for kind in ("N", "Z")
        for a in range(2, 10)
        for residue in range(PERIOD)
    )
    parent_id = _state_id(parent)
    macro_slots = [parent_macro] * len(states)
    cache: dict[tuple[int, int], OccurrencePrefixReturn] = {}
    canonical: list[OccurrencePrefixReturn] = []
    for child in parent_macro.ordered_children:
        child_id = _state_id(child)
        child_macro = construct_macro(child, grouped_near=True)
        macro_slots[child_id] = child_macro
        canonical_exponent = audit.canonical_exponent(child.exponent_residue)
        canonical_return = audit.macro_c1_return_constructive(
            child_macro, canonical_exponent
        )
        cache[(child_id, canonical_exponent)] = canonical_return
        canonical.append(canonical_return)

    actual = _macro_child_returns(
        parent_id,
        audit.canonical_exponent(parent.exponent_residue),
        states,
        tuple(macro_slots),
        cache,
    )
    assert all(result is not None for result in actual)
    actual_returns = tuple(result for result in actual if result is not None)

    assert tuple(result.c1_count for result in canonical) == (4_000, 93_999)
    assert tuple(result.c1_count for result in actual_returns) == (
        4_000 * 10**PERIOD,
        94_000 * 10**PERIOD - 1,
    )
    assert actual_returns[0] is not canonical[0]
    assert actual_returns[1] is not canonical[1]
    assert tuple(result.source.exponent for result in actual_returns) == (929, 929)
    assert tuple(result.width_delta for result in actual_returns) == tuple(
        macro_slots[_state_id(child)].exponent_delta
        for child in parent_macro.ordered_children
    )
    assert (_state_id(parent_macro.ordered_children[0]), actual_exponent) in cache
    assert (_state_id(parent_macro.ordered_children[1]), actual_exponent) in cache
    actual_zeta = actual_returns[1].c1_count - actual_returns[0].c1_count + 1
    canonical_zeta = canonical[1].c1_count - canonical[0].c1_count + 1
    assert canonical_zeta == 90_000
    assert actual_zeta == canonical_zeta * 10**PERIOD


def test_fragment_accumulation_can_run_without_endpoint_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = BoundaryState("N", 2, 10)
    macro = construct_macro(state, grouped_near=True)
    endpoint = macro.endpoint
    evaluate_at_scale = AffineWeight.evaluate_at_scale

    def reject_endpoint_evaluation(
        self: AffineWeight,
        scale: int,
        *,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        if self is endpoint:
            pytest.fail("fragment producer read the completed macro endpoint")
        return evaluate_at_scale(self, scale, charge_bits=charge_bits)

    monkeypatch.setattr(AffineWeight, "evaluate_at_scale", reject_endpoint_evaluation)
    result = audit.macro_c1_return_constructive(macro, 10, check_endpoint=False)
    assert 0 <= result.terminal_low_suffix < 100
    assert result.c1_count >= 0


def test_greatest_live_pruning_uses_reverse_edges_and_preserves_cycles() -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(8))
    graph = CommaFutureGraph(
        states,
        (
            (1, None),
            (2, None),
            (1, None),
            (0, None),
            (5, None),
            (None, None),
            (5, None),
            (7, None),
        ),
        (0,) * len(states),
    )

    assert audit.greatest_live_fixed_point(graph) == frozenset((0, 1, 2, 3, 7))


def test_pointed_only_payload_does_not_construct_c1_returns(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(4))
    graph = CommaFutureGraph(
        states,
        ((1, None), (None, 0), (3, None), (None, None)),
        (462, 462, 0, 0),
    )

    def forbidden(*_args: object, **_kwargs: object) -> OccurrencePrefixReturn:
        pytest.fail("pointed-only path constructed carry returns")

    monkeypatch.setattr(audit, "macro_c1_return_constructive", forbidden)
    payload = _pointed_only_payload(graph)
    assert payload["rank_labelled"] is False
    assert payload["endpoint_derived_counts"] is False
    scope = payload["scope"]
    assert isinstance(scope, dict)
    assert scope["macro_c1_runtime_used"] is False
    assert payload["endpoint_role"] == "not evaluated in pointed-only mode"
