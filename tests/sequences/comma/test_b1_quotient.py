"""Source-key collisions and an independent literal check of the B1 teacher."""

from collections import Counter
from typing import cast

import pytest

from devtools.verification.comma_b1_quotient import (
    B1Observation,
    B1State,
    audit_b1_quotient,
    observe_b1,
    offset_orbit,
    offset_representatives,
)
from number_compiler.sequences.comma import decisive_endpoint
from number_compiler.sequences.comma.arithmetic import (
    cycle_power_residue,
    cycle_residue_period,
    cycle_transfer,
    is_sector9_landmine_headroom,
)
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    near_chart_target,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.decisive_endpoint import (
    DecisiveEndpoint,
    EndpointOccurrence,
    EndpointOutcome,
    EndpointRun,
    endpoint_step,
    evaluate_b1_source,
    source_endpoint,
)
from tests.support.comma_oracles import literal_children


@pytest.mark.validation
def test_key_audit_does_not_rediscover_expanded_moore_graph(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("unrequested expanded Moore baseline")

    monkeypatch.setattr(
        "devtools.verification.comma_b1_quotient.minimize_finite_observer", forbidden
    )
    result = audit_b1_quotient()
    assert result["states"] == 42_504
    assert result["complete_domain"] is True
    assert result["posthoc_moore_classes"] is None
    assert result["posthoc_moore_refinement_rounds"] is None


def test_canonical_representatives_match_checked_orbit_numbering() -> None:
    reps = offset_representatives()
    assert len(reps) == 46
    assert reps[24] == 68
    assert tuple(offset_orbit(x) for x in reps) == tuple(range(46))
    assert {offset_orbit(x) for x in range(91)} == set(range(46))


def test_source_core_equality_does_not_imply_decade_observation_equality() -> None:
    assert cycle_power_residue(460, 1) == cycle_power_residue(460, 23)
    left = observe_b1(B1State(0, 1))
    right = observe_b1(B1State(0, 23))
    assert left.observation == B1Observation("live", 12)
    assert right.observation == B1Observation("live", 39)
    assert left.successor == B1State(12, 2)
    assert right.successor == B1State(39, 24)


@pytest.mark.parametrize(
    ("phase", "live_fibers", "terminal"),
    [
        (0, (14, 11, 2), B1Observation("fork", 6)),
        (28, (34, 19, 25, 13, 23, 19), B1Observation("landmine", 0)),
    ],
)
def test_local_clock_period_does_not_determine_complete_decade_height(
    phase: int, live_fibers: tuple[int, ...], terminal: B1Observation
) -> None:
    """Equal mod-28 clocks can have distinct complete futures and heights.

    This bounded witness checks both the chart reference and the source-selected
    endpoint consumer. It does not assert a global rank certificate.
    """
    assert CyclotomicClock.from_phase(phase).phase(28) == 0
    state = B1State(0, phase)
    representatives = offset_representatives()
    for expected in (
        *(B1Observation("live", fiber) for fiber in live_fibers),
        terminal,
    ):
        reference = observe_b1(state)
        assert reference.observation == expected
        result = evaluate_b1_source(
            CyclotomicClock.from_phase(state.phase), representatives[state.fiber]
        ).outcome
        assert result.kind == expected.kind
        if expected.kind == "live":
            assert result.entry_coordinate is not None
            assert offset_orbit(result.entry_coordinate) == expected.value
            assert result.exponent_advance == 1
            assert reference.successor == B1State(
                expected.value, (state.phase + 1) % 924
            )
            assert reference.successor is not None
            state = reference.successor
        else:
            assert reference.successor is None
            assert result.fork_a == (
                expected.value if expected.kind == "fork" else None
            )


def test_class_self_loop_requires_phase_in_a_strictly_decreasing_rank() -> None:
    # A class-only potential would require rank(26) < rank(26). The phase
    # change is occurrence data, but it cannot be discarded from this proof.
    source = B1State(26, 0)
    assert offset_representatives()[source.fiber] == 17
    reference = observe_b1(source)
    assert reference.observation == B1Observation("live", 26)
    assert reference.successor == B1State(26, 1)
    result = evaluate_b1_source(CyclotomicClock.from_phase(0), 17).outcome
    assert result.kind == "live"
    assert result.entry_coordinate is not None
    assert offset_orbit(result.entry_coordinate) == source.fiber
    assert result.exponent_advance == 1


def test_equal_terminal_summaries_do_not_select_the_first_b1_successor() -> None:
    """The terminal residual alone does not determine the first live action.

    This is a bounded witness about that projection only. An occurrence-aware
    quotient may retain the missing source information separately.
    """
    cases = (
        (
            B1State(0, 1),
            B1State(12, 2),
            (
                B1Observation("live", 12),
                B1Observation("live", 29),
                B1Observation("landmine", 0),
            ),
        ),
        (
            B1State(0, 13),
            B1State(23, 14),
            (
                B1Observation("live", 23),
                B1Observation("live", 27),
                B1Observation("landmine", 0),
            ),
        ),
    )
    summaries: list[tuple[int, B1Observation]] = []
    first_successors: list[B1State | None] = []
    for initial, expected_first, expected_observations in cases:
        state = initial
        observations: list[B1Observation] = []
        first_successor = None
        for _ in range(3):
            reference = observe_b1(state)
            observations.append(reference.observation)
            if reference.successor is None:
                break
            if first_successor is None:
                first_successor = reference.successor
            state = reference.successor

        assert tuple(observations) == expected_observations
        assert first_successor == expected_first
        summaries.append(
            (sum(item.kind == "live" for item in observations), observations[-1])
        )
        first_successors.append(first_successor)

    assert summaries == [(2, B1Observation("landmine", 0))] * 2
    assert first_successors[0] != first_successors[1]


@pytest.mark.parametrize("fiber", [0, 1, 24, 45])
def test_b1_chart_reference_agrees_with_literal_children(fiber: int) -> None:
    value = 100_000 + offset_representatives()[fiber]
    for _ in range(100_000):
        children = literal_children(value)
        if len(children) != 1:
            expected = (
                B1Observation("landmine", 0)
                if not children
                else B1Observation("fork", int(str(children[-1])[0]))
            )
            break
        value = children[0]
        if value >= 1_000_000:
            expected = B1Observation("live", offset_orbit(value - 1_000_000))
            break
    else:
        pytest.fail("bounded literal reference did not reach a decade outcome")
    assert observe_b1(B1State(fiber, 5)).observation == expected


@pytest.mark.parametrize("state", [B1State(-1, 0), B1State(46, 0), B1State(0, 924)])
def test_b1_reference_rejects_states_outside_the_complete_domain(
    state: B1State,
) -> None:
    with pytest.raises(ValueError, match="canonical"):
        observe_b1(state)


def test_source_selected_endpoint_preserves_occurrence_phase_collisions() -> None:
    zero_clock = CyclotomicClock.from_phase(0)
    shifted_clock = CyclotomicClock.from_phase(44)
    zero_source = source_endpoint(zero_clock, 0)
    shifted_source = source_endpoint(shifted_clock, 0)

    # The initial Entry projects both clocks to the same endpoint, but the
    # following source-selected action still consumes the full occurrence
    # clock and therefore distinguishes the future.
    assert zero_source.endpoint == shifted_source.endpoint == DecisiveEndpoint(1, 12)
    zero_run = evaluate_b1_source(zero_clock, 0)
    shifted_run = evaluate_b1_source(shifted_clock, 0)
    assert zero_run.outcome == EndpointOutcome(
        "live", entry_coordinate=49, exponent_advance=1
    )
    assert shifted_run.outcome == EndpointOutcome("landmine")
    assert zero_run.strict_sector_advances == shifted_run.strict_sector_advances == 8
    assert observe_b1(B1State(0, 0)).observation == B1Observation("live", 14)
    assert observe_b1(B1State(0, 44)).observation == B1Observation("landmine", 0)


def test_endpoint_action_uses_full_clock_for_the_successor_entry() -> None:
    first = endpoint_step(
        EndpointOccurrence(DecisiveEndpoint(7, 3), CyclotomicClock.from_phase(0))
    )
    second = endpoint_step(
        EndpointOccurrence(DecisiveEndpoint(7, 3), CyclotomicClock.from_phase(22))
    )
    assert first.next_endpoint == DecisiveEndpoint(8, 33)
    assert second.next_endpoint == DecisiveEndpoint(8, 45)


def test_sector9_c1_landmine_criterion_is_exact() -> None:
    expected = (19, 28, 37, 46, 55, 64, 73, 82)
    assert (
        tuple(
            headroom
            for headroom in range(1, 541)
            if is_sector9_landmine_headroom(headroom)
        )
        == expected
    )


def test_sector9_c1_criterion_differential_matches_admitted_near_targets() -> None:
    clock = CyclotomicClock.from_phase(42)
    for headroom in range(1, 541):
        try:
            endpoint = DecisiveEndpoint(9, headroom)
        except ValueError:
            continue
        move = near_chart_target(BoundaryChart("near", 9, 0, headroom))
        result = endpoint_step(EndpointOccurrence(endpoint, clock))
        assert (move.next_chart is None) == is_sector9_landmine_headroom(headroom)
        if move.next_chart is None:
            assert result == EndpointOutcome(
                "landmine" if move.fork_a is None else "fork",
                fork_a=move.fork_a,
            )
        else:
            assert move.next_chart.kind == "entry"
            assert result == EndpointOutcome(
                "live",
                entry_coordinate=move.next_chart.coordinate,
                exponent_advance=1,
            )


@pytest.mark.parametrize("headroom", [True, 19.0, "19", None])
def test_sector9_c1_criterion_rejects_non_exact_integer_inputs(
    headroom: object,
) -> None:
    assert is_sector9_landmine_headroom(cast(int, headroom)) is False


def test_sector9_landmine_endpoint_short_circuits_chart_selection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("sector-nine landmine rebuilt a generic Near chart")

    monkeypatch.setattr(decisive_endpoint, "BoundaryChart", forbidden)
    monkeypatch.setattr(decisive_endpoint, "near_chart_target", forbidden)
    charges: list[int] = []
    for headroom in (19, 28, 37, 46, 55, 64, 73, 82):
        for phase in (0, 42, 923):
            result = endpoint_step(
                EndpointOccurrence(
                    DecisiveEndpoint(9, headroom),
                    CyclotomicClock.from_phase(phase),
                ),
                charge_work=charges.append,
            )
            assert result == EndpointOutcome("landmine")
    assert charges == [1] * 24


def test_sector9_landmine_budget_is_charged_before_the_fast_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("generic Near work ran before budget admission")

    monkeypatch.setattr(decisive_endpoint, "BoundaryChart", forbidden)
    monkeypatch.setattr(decisive_endpoint, "near_chart_target", forbidden)
    charges: list[int] = []

    def exhausted(amount: int) -> None:
        charges.append(amount)
        raise RuntimeError("budget exhausted")

    with pytest.raises(RuntimeError, match="budget exhausted"):
        endpoint_step(
            EndpointOccurrence(DecisiveEndpoint(9, 19), CyclotomicClock.from_phase(0)),
            charge_work=exhausted,
        )
    assert charges == [1]


@pytest.mark.validation
def test_source_selected_b1_matches_chart_reference() -> None:
    # Several raw offsets share one canonical fiber. Reuse only the immutable
    # chart-reference output for those aliases; every source-selected input is
    # still evaluated independently by the constructor under test.
    clocks = tuple(CyclotomicClock.from_phase(phase) for phase in range(924))
    fibers = tuple(offset_orbit(offset) for offset in range(91))
    reference_outputs: dict[tuple[int, int], B1Observation] = {}
    for offset, fiber in enumerate(fibers):
        for phase, clock in enumerate(clocks):
            result = evaluate_b1_source(clock, offset)
            key = fiber, phase
            reference = reference_outputs.get(key)
            if reference is None:
                reference = observe_b1(B1State(fiber, phase)).observation
                reference_outputs[key] = reference
            value = (
                offset_orbit(result.outcome.entry_coordinate)
                if result.outcome.kind == "live"
                and result.outcome.entry_coordinate is not None
                else result.outcome.fork_a
                if result.outcome.kind == "fork"
                else 0
            )
            assert (result.outcome.kind, value) == (reference.kind, reference.value)
            assert result.strict_sector_advances <= 8


def test_generator_reconstructs_endpoint_oracle_without_retaining_rows() -> None:
    # Bounded discovery belongs only to this oracle. The production owner
    # selects one core action on demand and never builds this carrier/table.
    roots = {
        source_endpoint(CyclotomicClock.from_phase(phase), offset).endpoint
        for offset in offset_representatives()
        for phase in range(22)
    }
    assert len(roots) == 46
    seen = set(roots)
    pending = list(roots)
    periods: Counter[int] = Counter()
    while pending:
        endpoint = pending.pop()
        next_chart = near_chart_target(
            BoundaryChart("near", endpoint.sector, 0, endpoint.headroom)
        ).next_chart
        period = 1
        if next_chart is not None and endpoint.sector < 9:
            period = cycle_residue_period(
                cycle_transfer(
                    next_chart.leading, next_chart.coordinate % 10
                ).displacement
            )
        outputs = tuple(
            endpoint_step(EndpointOccurrence(endpoint, CyclotomicClock.from_phase(r)))
            for r in range(period)
        )
        minimal = next(
            size
            for size in range(1, period + 1)
            if period % size == 0
            and all(output == outputs[r % size] for r, output in enumerate(outputs))
        )
        periods[minimal] += 1
        for output in outputs:
            successor = output.next_endpoint
            if successor is not None and successor not in seen:
                seen.add(successor)
                pending.append(successor)
    assert len(seen) == 446
    assert periods == {1: 166, 2: 21, 3: 75, 6: 134, 22: 22, 28: 28}
    assert sum(period * count for period, count in periods.items()) == 2505


def test_endpoint_path_does_not_construct_weighted_chart_moves(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("endpoint constructor built a weighted chart move")

    monkeypatch.setattr(
        "number_compiler.sequences.comma.boundary_chart.chart_step", forbidden
    )
    assert evaluate_b1_source(CyclotomicClock.from_phase(0), 0).outcome.kind == "live"


def test_entry_budget_is_charged_before_headroom_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    called = False

    def forbidden_headroom(*_args: object, **_kwargs: object) -> object:
        nonlocal called
        called = True
        raise AssertionError("Entry arithmetic ran after budget exhaustion")

    def exhausted(_amount: int) -> None:
        raise RuntimeError("budget exhausted")

    monkeypatch.setattr(decisive_endpoint, "entry_headroom", forbidden_headroom)
    with pytest.raises(RuntimeError, match="budget exhausted"):
        source_endpoint(CyclotomicClock.from_phase(0), 0, charge_work=exhausted)
    assert called is False


def test_clock_subclasses_and_boolean_payloads_are_rejected() -> None:
    class ForgedClock(CyclotomicClock):
        def phase(self, period: int, *, shift: int = 0) -> int:
            return 0

    forged = ForgedClock(0, 0, 0, 0)
    with pytest.raises(ValueError, match="power residue"):
        cycle_power_residue(460, forged)
    with pytest.raises(TypeError, match="cyclotomic occurrence clock"):
        source_endpoint(forged, 0)
    with pytest.raises(TypeError, match="exact integer"):
        EndpointOutcome("live", entry_coordinate=0, exponent_advance=True)
    with pytest.raises(TypeError, match="exact endpoint outcome"):
        EndpointRun(cast(EndpointOutcome, object()), 0)
