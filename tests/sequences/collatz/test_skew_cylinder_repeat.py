"""Source and publication checks for repeated admitted parity words."""

from __future__ import annotations

from collections.abc import Callable
from copy import copy
from dataclasses import fields, replace
from typing import Protocol, cast
from unittest.mock import patch

import pytest

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as collatz_keys
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_89_AT_NINE,
    ENTRY_421,
    CollatzSegmentIdentity,
)
from number_compiler.sequences.collatz.boundary_macros import (
    admit_boundary_macro_plan,
    select_admitted_boundary_macro,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_skew_power import (
    GuardedSkewCylinderPower,
)
from number_compiler.sequences.collatz.innovation_input_tape import (
    ParityProgramBuilder,
)
from number_compiler.sequences.collatz.radial_boundary_coupling import (
    CollatzRadialBoundarySeam,
)
from number_compiler.sequences.collatz.skew_cylinder_repeat import (
    RepeatedWordMooreCylinder,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    BoundaryWitness,
    FactorSpecs,
    UnifiedSkewChain,
    select_unified_skew_chain,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock
from tests.support.collatz_finite_trace import physical_values


class _IssuedPowerFactory(Protocol):
    def __call__(
        self,
        *,
        source: int,
        expected_endpoint: int,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
        physical_ticks: int,
        clock: SkewQuadraticClock | None,
        repetitions: int,
        evaluator: GrowthArithmeticEvaluator | None,
        preflight: Callable[[int], None] | None,
        cylinder: RepeatedWordMooreCylinder | None = None,
    ) -> GuardedSkewCylinderPower: ...


class _UnifiedChainFactory(Protocol):
    def __call__(
        self,
        source: int,
        endpoint: int,
        fields: DyadicTerminalFieldAction,
        width_blank: BlankLedger,
        clock: SkewQuadraticClock | None,
        odd_symbols: int,
        factors: FactorSpecs,
        segment_identities: tuple[CollatzSegmentIdentity, ...],
        first_boundary: tuple[int, BoundaryWitness] | None,
        seams: tuple[CollatzRadialBoundarySeam, ...],
        repeat_cylinder: RepeatedWordMooreCylinder | None = None,
    ) -> UnifiedSkewChain: ...


def _from_issued_action(
    *,
    source: int,
    expected_endpoint: int,
    action: DyadicTerminalFieldAction,
    odd_symbols: int,
    physical_ticks: int,
    clock: SkewQuadraticClock | None,
    repetitions: int,
    evaluator: GrowthArithmeticEvaluator | None,
    preflight: Callable[[int], None] | None,
    cylinder: RepeatedWordMooreCylinder | None = None,
) -> GuardedSkewCylinderPower:
    factory = cast(
        _IssuedPowerFactory,
        type.__getattribute__(GuardedSkewCylinderPower, "_from_issued_action"),
    )
    return factory(
        source=source,
        expected_endpoint=expected_endpoint,
        action=action,
        odd_symbols=odd_symbols,
        physical_ticks=physical_ticks,
        clock=clock,
        repetitions=repetitions,
        evaluator=evaluator,
        preflight=preflight,
        cylinder=cylinder,
    )


def _issue_unified_chain(
    source: int,
    endpoint: int,
    fields: DyadicTerminalFieldAction,
    width_blank: BlankLedger,
    clock: SkewQuadraticClock | None,
    odd_symbols: int,
    factors: FactorSpecs,
    segment_identities: tuple[CollatzSegmentIdentity, ...],
    first_boundary: tuple[int, BoundaryWitness] | None,
    seams: tuple[CollatzRadialBoundarySeam, ...],
    repeat_cylinder: RepeatedWordMooreCylinder | None = None,
) -> UnifiedSkewChain:
    factory = cast(
        _UnifiedChainFactory,
        type.__getattribute__(UnifiedSkewChain, "_issue"),
    )
    return factory(
        source,
        endpoint,
        fields,
        width_blank,
        clock,
        odd_symbols,
        factors,
        segment_identities,
        first_boundary,
        seams,
        repeat_cylinder,
    )


def _issued_989_power() -> GuardedSkewCylinderPower:
    ledger = ResourceLedger()
    plan = admit_boundary_macro_plan(19, 2, minimum_repetitions=1)
    assert plan is not None and plan.identity == ENTRY_89_AT_NINE
    with BoundaryActionTemplateMemo(ledger) as templates:
        macro = select_admitted_boundary_macro(plan, templates=templates)
    with GrowthArithmeticEvaluator(ledger) as evaluator:
        return GuardedSkewCylinderPower.from_boundary_macro(
            macro, 2, evaluator=evaluator
        )


def _materialize(
    power: GuardedSkewCylinderPower,
) -> tuple[DyadicTerminalFieldAction, int]:
    with GrowthArithmeticEvaluator(ResourceLedger()) as evaluator:
        return power.materialize(max_materialization_bits=512, evaluator=evaluator)


def test_source_certified_power_matches_literal_physical_endpoint() -> None:
    power = _issued_989_power()
    action, endpoint = _materialize(power)
    assert endpoint == physical_values(19, 4)[-1] == 44
    assert action.steps == 2
    assert power.physical_ticks == 4
    assert power.skew_clock is not None
    assert power.skew_clock.physical_ticks == 4


def test_power_publication_rejects_forgery_and_dataclass_replacement() -> None:
    power = _issued_989_power()
    forged = object.__new__(GuardedSkewCylinderPower)
    for item in fields(power):
        object.__setattr__(forged, item.name, getattr(power, item.name))
    with pytest.raises(ValueError):
        _materialize(forged)
    with pytest.raises((TypeError, ValueError)):
        replace(power, repetitions=3)
    with pytest.raises(TypeError, match="one work owner"):
        power.materialize(max_materialization_bits=512)


def test_power_rechecks_action_fields_before_materializing() -> None:
    power = _issued_989_power()
    action = power.action
    object.__setattr__(action, "offset", action.offset + 1)
    # Even a caller that edits the action's own internal tuple cannot rewrite
    # the outer publisher's independent coefficient snapshot.
    object.__setattr__(action, "_issued_coefficients", action.coefficient_snapshot())
    with (
        patch.object(
            DyadicTerminalFieldAction,
            "power",
            side_effect=AssertionError("forged fields reached materialization"),
        ),
        pytest.raises(ValueError),
    ):
        _materialize(power)


def test_power_detects_mutated_nested_cylinder_and_quadratic_clock() -> None:
    changed_cylinder = _issued_989_power()
    object.__setattr__(
        changed_cylinder.cylinder,
        "defect",
        changed_cylinder.cylinder.defect + 1,
    )
    with pytest.raises(ValueError):
        _materialize(changed_cylinder)

    changed_clock = _issued_989_power()
    clock = changed_clock.skew_clock
    assert clock is not None
    object.__setattr__(clock, "value", clock.value ^ 1)
    with pytest.raises(ValueError):
        _materialize(changed_clock)


def test_repeat_cylinder_requires_its_issuer_at_power_admission() -> None:
    power = _issued_989_power()
    cylinder = power.cylinder
    with pytest.raises(TypeError):
        RepeatedWordMooreCylinder()
    with pytest.raises(TypeError):
        replace(cylinder, remaining_repetitions=None)

    copied = copy(cylinder)
    with pytest.raises(ValueError, match="cylinder seal"):
        copied.verify_for(power.action, power.source)
    with pytest.raises(ValueError, match="cylinder seal"):
        _from_issued_action(
            source=power.source,
            expected_endpoint=power.action.endpoint(power.source),
            action=power.action,
            odd_symbols=power.odd_symbols,
            physical_ticks=power.action.steps + power.odd_symbols,
            clock=None,
            repetitions=2,
            evaluator=None,
            preflight=None,
            cylinder=copied,
        )
    object.__setattr__(cylinder, "remaining_repetitions", None)
    with pytest.raises(ValueError, match="cylinder seal"):
        _from_issued_action(
            source=power.source,
            expected_endpoint=power.action.endpoint(power.source),
            action=power.action,
            odd_symbols=power.odd_symbols,
            physical_ticks=power.action.steps + power.odd_symbols,
            clock=None,
            repetitions=2,
            evaluator=None,
            preflight=None,
            cylinder=cylinder,
        )


def _multifactor_chain(ledger: ResourceLedger) -> UnifiedSkewChain:
    with BoundaryActionTemplateMemo(ledger) as templates:
        chain = select_unified_skew_chain(
            77,
            8,
            templates=templates,
            ledger=ledger,
            preflight=lambda _required: None,
            include_quadratic_clock=False,
        )
    assert chain is not None and chain.repeat_cylinder is not None
    return chain


def test_unified_chain_rejects_copied_or_mutated_repeat_cylinder() -> None:
    ledger = ResourceLedger()
    chain = _multifactor_chain(ledger)
    cylinder = chain.repeat_cylinder
    assert cylinder is not None
    copied = copy(cylinder)
    with pytest.raises(ValueError, match="cylinder seal"):
        _issue_unified_chain(
            chain.source,
            chain.endpoint,
            chain.fields,
            chain.width_blank,
            chain.clock,
            chain.odd_symbols,
            chain.factors,
            chain.segment_identities,
            chain.first_boundary,
            chain.seams,
            copied,
        )

    object.__setattr__(cylinder, "remaining_repetitions", None)
    with pytest.raises(ValueError, match="cylinder seal"):
        chain.verify()


def test_repeated_unified_grammar_preserves_multifactor_chronology_and_guards() -> None:
    ledger = ResourceLedger()
    chain = _multifactor_chain(ledger)
    assert len(chain.factors) > 1
    power = GuardedSkewCylinderPower.from_chain(
        chain,
        2,
        preflight=lambda _bits: None,
    )
    motif = tuple(
        bit
        for bits, repetitions in chain.factors
        for _ in range(repetitions)
        for bit in bits
    )
    expected_word = motif * power.repetitions

    def literal_endpoint(source: int, word: tuple[int, ...]) -> int:
        value = source
        for bit in word:
            assert value & 1 == bit
            value = (3 * value + 1) // 2 if bit else value // 2
        return value

    expected_endpoint = literal_endpoint(chain.source, expected_word)
    powered_action = power.action.power(power.repetitions)
    assert expected_endpoint == powered_action.endpoint(chain.source)
    composition_operand_bits: list[int] = []
    endpoint_calls = 0
    power_calls = 0
    original_endpoint = DyadicTerminalFieldAction.endpoint
    original_power = DyadicTerminalFieldAction.power
    source_operand_bits_before = ledger.counters.get(
        collatz_keys.COLLATZ_INNOVATION_SOURCE_OPERAND_BITS, 0
    )
    compositions_before = ledger.counters.get(
        collatz_keys.COLLATZ_FIELD_ACTION_COMPOSITIONS, 0
    )

    def counted_endpoint(action: DyadicTerminalFieldAction, source: int) -> int:
        nonlocal endpoint_calls
        endpoint_calls += 1
        return original_endpoint(action, source)

    def counted_power(
        action: DyadicTerminalFieldAction,
        repetitions: int,
        *,
        on_compose: Callable[
            [DyadicTerminalFieldAction, DyadicTerminalFieldAction], None
        ]
        | None = None,
    ) -> DyadicTerminalFieldAction:
        nonlocal power_calls
        power_calls += 1
        if on_compose is None:
            return original_power(action, repetitions)

        def observe_composition(
            first: DyadicTerminalFieldAction,
            second: DyadicTerminalFieldAction,
        ) -> None:
            composition_operand_bits.append(
                sum(
                    value.bit_length()
                    for value in (
                        *first.coefficient_snapshot(),
                        *second.coefficient_snapshot(),
                    )
                )
            )
            on_compose(first, second)

        return original_power(
            action,
            repetitions,
            on_compose=observe_composition,
        )

    with ParityProgramBuilder(chain.source, ledger) as refused_builder:
        before_refused = refused_builder.issuance_snapshot()

        def refuse_preflight(_bits: int) -> None:
            raise MemoryError("repeated grammar preflight refused")

        with (
            patch.object(
                DyadicTerminalFieldAction,
                "power",
                side_effect=AssertionError("preflight refusal reached power"),
            ),
            pytest.raises(MemoryError, match="preflight refused"),
        ):
            refused_builder.append_guarded_skew_repetitions(
                chain,
                power,
                expected_endpoint,
                preflight=refuse_preflight,
            )
        assert refused_builder.issuance_snapshot() == before_refused

    with ParityProgramBuilder(chain.source, ledger) as builder:
        with (
            patch.object(DyadicTerminalFieldAction, "endpoint", counted_endpoint),
            patch.object(DyadicTerminalFieldAction, "power", counted_power),
        ):
            builder.append_guarded_skew_repetitions(
                chain,
                power,
                expected_endpoint,
                preflight=lambda _bits: None,
            )
        snapshot = builder.issuance_snapshot()
        emitted_word = tuple(
            bit
            for factor in snapshot.factors
            for _ in range(factor.repetitions)
            for bit in factor.motif
        )
        assert emitted_word == expected_word
        assert snapshot.source == expected_endpoint
        assert power_calls == 1
        assert endpoint_calls == 1
    expected_endpoint_operand_bits = 2 * (
        chain.source.bit_length()
        + powered_action.gain.bit_length()
        + abs(powered_action.offset).bit_length()
        + powered_action.steps
        + 1
    )
    assert ledger.counters[collatz_keys.COLLATZ_INNOVATION_SOURCE_OPERAND_BITS] - (
        source_operand_bits_before
    ) == (
        sum(composition_operand_bits)
        + expected_endpoint_operand_bits
        + chain.fields.steps
    )
    assert ledger.counters[collatz_keys.COLLATZ_FIELD_ACTION_COMPOSITIONS] - (
        compositions_before
    ) == len(composition_operand_bits)
    assert ledger.entries == ledger.nodes == 0

    with ParityProgramBuilder(chain.source, ledger) as wrong_endpoint_builder:
        before_wrong_endpoint = wrong_endpoint_builder.issuance_snapshot()
        with pytest.raises(ValueError, match="endpoint differs"):
            wrong_endpoint_builder.append_guarded_skew_repetitions(
                chain,
                power,
                expected_endpoint + 1,
                preflight=lambda _bits: None,
            )
        assert wrong_endpoint_builder.issuance_snapshot() == before_wrong_endpoint
    assert ledger.entries == ledger.nodes == 0

    object.__setattr__(power, "source", power.source + 1)
    try:
        with ParityProgramBuilder(chain.source, ledger) as forged_builder:
            with (
                patch.object(
                    DyadicTerminalFieldAction,
                    "power",
                    side_effect=AssertionError("forged guard reached action power"),
                ),
                pytest.raises(ValueError, match="seal is invalid"),
            ):
                forged_builder.append_guarded_skew_repetitions(
                    chain,
                    power,
                    expected_endpoint,
                    preflight=lambda _bits: None,
                )
    finally:
        object.__setattr__(power, "source", chain.source)
    assert ledger.entries == ledger.nodes == 0


def test_repeated_parity_word_does_not_extend_named_family_guard() -> None:
    plan = admit_boundary_macro_plan(244, 4, minimum_repetitions=1)
    assert plan is not None and plan.identity == ENTRY_421
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        macro = select_admitted_boundary_macro(plan, templates=templates)
    assert macro.endpoint == 92
    with GrowthArithmeticEvaluator(ResourceLedger()) as evaluator:
        power = GuardedSkewCylinderPower.from_boundary_macro(
            macro, 2, evaluator=evaluator
        )
    assert _materialize(power)[1] == 35
    assert power.physical_ticks == 8
    assert macro.endpoint % 40 != 4


def test_production_executor_powers_only_when_width_spine_is_not_demanded() -> None:
    ordinary = PoweredCollatzTerm(77, 8, max_context_nodes=10_000)
    assert ordinary.materialize(max_bits=32) == physical_values(77, 8)[-1] == 11
    assert (
        ordinary.resource_ledger.counters[
            "collatz_physical_unified_skew_powered_actions"
        ]
        == 1
    )
    assert (
        ordinary.resource_ledger.counters[
            "collatz_physical_unified_skew_additional_repetitions"
        ]
        == 1
    )

    width_demand = PoweredCollatzTerm(77, 8, max_context_nodes=10_000)
    width_demand.prepare_width_spine()
    assert width_demand.materialize(max_bits=32) == 11
    assert width_demand.width() == 4
    first_endpoint = physical_values(77, 4)[-1]
    assert first_endpoint == 29
    assert first_endpoint.bit_length() - (77).bit_length() == -2
    assert (11).bit_length() - first_endpoint.bit_length() == -1
    summary = width_demand.source_image().tape_width_summary
    assert summary is not None
    # Repeating the first segment's -2 displacement would predict width 3.
    # The exact second segment loses only one bit, so the endpoint is width 4.
    assert summary.blank.delta == -3
    assert (
        width_demand.resource_ledger.counters.get(
            "collatz_physical_unified_skew_powered_actions", 0
        )
        == 0
    )
    assert (
        width_demand.resource_ledger.counters.get(
            "collatz_physical_unified_skew_additional_repetitions", 0
        )
        == 0
    )
