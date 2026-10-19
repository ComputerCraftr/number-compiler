"""Radial ports are derived from the same admitted Collatz macro clocks."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.api.cylinder_observation import (
    observe_collatz,
    observe_physical_clock,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import BoundaryActionTemplateMemo
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers
from number_compiler.sequences.collatz.observation_kind import (
    CollatzObservationKind,
)
from number_compiler.sequences.collatz.power import CollatzEventArena
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    select_unified_skew_chain,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock


def _string_object_mapping(value: object) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise AssertionError("expected an object-valued radial packet")
    result: dict[str, object] = {}
    for key, item in value.items():
        if type(key) is not str:
            raise AssertionError("radial packet keys must be strings")
        result[key] = item
    return result


def test_guarded_collatz_macro_and_event_observers_share_radial_factor() -> None:
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        chain = select_unified_skew_chain(
            13, 9, templates=templates, include_quadratic_clock=True
        )
    assert chain is not None
    chain.verify()
    assert chain.endpoint == 1
    assert chain.clock is not None
    with GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=10_000_000) as e:
        packet = chain.radial_leading_binary(e, 8)
        assert packet == chain.clock.radial_leading_binary(e, 8)
        observation = chain.observation(radial_evaluator=e)
        radial = _string_object_mapping(observation["radial_sturmian"])
        prefix_value = radial["prefix_value"]
        assert type(prefix_value) is int
        assert prefix_value == packet.prefix_value
        assert chain.clock.radial_sturmian_clock.scale == HomogeneousGrowthScale(
            chain.odd_symbols, chain.normalized_symbols
        )
        assert "radial_sturmian" not in chain.observation()


def test_pumped_grammar_exponents_are_observed_without_expanding_motifs() -> None:
    motif = (1, 0, 1, 0, 0)
    count = 1 << 35
    pumped = SkewQuadraticClock.factors(((motif, count),), precision=32)
    assert pumped.steps == len(motif) * count
    assert pumped.odds == sum(motif) * count
    assert pumped.radial_sturmian_clock.scale == HomogeneousGrowthScale(
        2 * count, 5 * count
    )
    with GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=20_000_000) as e:
        packet = pumped.radial_leading_binary(e, 8)
        assert len(packet.prefix_binary) == 8
        assert packet.binary_order < 0


def test_powered_event_node_has_a_demanded_radial_port_not_a_new_source() -> None:
    arena = CollatzEventArena()
    count = 10**20 + 19
    root = arena.power(arena.event(2), count)
    views = CollatzClockObservers(arena)
    with GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=20_000_000) as e:
        observed = views.radial_leading_binary(root, e)
        assert observed.growths == count
        assert observed.halvings == 2 * count
        assert views.clock(root).radial_sturmian_clock.scale == HomogeneousGrowthScale(
            count, 2 * count
        )
    assert arena.cocycle_materializations == 0


def test_existing_collatz_clock_api_publishes_typed_rotation() -> None:
    physical = observe_physical_clock(
        13, 9, max_ticks=40, max_digits=32, _include_metrics=False
    )["value"]
    accelerated = observe_collatz(
        13, 2, kind=CollatzObservationKind.CLOCK, _include_metrics=False
    )["value"]
    physical_value = _string_object_mapping(physical)
    accelerated_value = _string_object_mapping(accelerated)
    physical_radial = _string_object_mapping(physical_value["radial_sturmian"])
    accelerated_radial = _string_object_mapping(accelerated_value["radial_sturmian"])
    assert physical_radial == accelerated_radial
    prefix_value = physical_radial["prefix_value"]
    scope = physical_radial["scope"]
    assert type(prefix_value) is int
    assert prefix_value == 144
    assert isinstance(scope, str)
    assert scope.startswith("homogeneous multiplier")


def test_full_source_bound_temporal_quotient_keeps_its_own_radial_clock() -> None:
    for ticks in (9, 12, 21):
        result = compile_collatz_temporal_run_quotient(
            13, ticks, ledger=ResourceLedger(), include_joint_cocycle=True
        )
        with GrowthArithmeticEvaluator(
            ResourceLedger(), max_work_units=5_000_000
        ) as evaluator:
            radial = result.radial_leading_binary(evaluator)
            assert radial.growths == result.odd_ticks
            assert radial.halvings == result.division_ticks
            assert radial.binary_order == (
                (3**result.odd_ticks).bit_length() - 1 - result.division_ticks
            )
        if result.unified_skew_chain is not None:
            assert result.unified_skew_chain.physical_ticks <= result.physical_ticks
