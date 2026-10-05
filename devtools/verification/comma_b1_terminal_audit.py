"""Bounded audit of B1 terminal control and Stop(D) occurrence encoding.

This module is deliberately a verification helper, not a source selector.  It
reconstructs the terminal position from the shared Entry/Near arithmetic and
the external cyclotomic clock.  It does not read rank rows, terminal tables,
or a precomputed terminal alphabet.  The complete 46-by-924 population is
available only through the explicit opt-in command.

The audit keeps three quantities separate:

* ``complete_decades`` is the exponent transport at a live seam;
* ``within_decade`` is the strict sector count before the terminal event;
* ``seam_transition_count`` counts only selected Near seam increments; it is
  not a complete literal-prefix timing weight;
* ``literal_transition_weight`` is the one literal crossing edge (zero for a
  fork or landmine).

The terminal position is recorded here only to check the local law.  It is not
added to the production endpoint state or used as a replacement for the exact
height in sparse stop labels.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from typing import Literal

from number_compiler.sequences.comma.arithmetic import (
    classify_near_port,
    entry_headroom,
)
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    NearChartTarget,
    near_chart_target,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.decisive_endpoint import (
    DecisiveEndpoint,
    EndpointRun,
    evaluate_b1_source,
)

from .comma_b1_quotient import offset_representatives

PERIOD = 924
FULL_B1_COUNT = 46 * PERIOD

EXPECTED_FORK_COUNTS: dict[int, int] = {
    2: 924,
    3: 924,
    4: 924,
    5: 616,
    6: 770,
    7: 924,
    8: 672,
    9: 753,
}
EXPECTED_LANDMINE_COUNT = 5_766
EXPECTED_LANDMINE_HEADROOMS = (19, 28, 37, 46, 55, 64, 73, 82)
EXPECTED_REACHABLE_STOP_D = 204
MAX_FUTURE_DECADES = 32


@dataclass(frozen=True, slots=True)
class TerminalControl:
    """One independently reconstructed B1 terminal event."""

    kind: Literal["live", "fork", "landmine"]
    terminal_sector: int
    terminal_headroom: int
    fork_a: int | None
    complete_decades: int
    within_decade: int
    seam_transition_count: int
    literal_transition_weight: int

    def __post_init__(self) -> None:
        if self.kind == "live":
            if (
                self.terminal_sector != 9
                or self.fork_a is not None
                or self.complete_decades != 1
                or self.literal_transition_weight != 1
            ):
                raise AssertionError("invalid live terminal control")
        elif self.kind == "fork":
            if (
                type(self.fork_a) is not int
                or not 2 <= self.fork_a <= 9
                or self.terminal_sector != self.fork_a - 1
                or self.complete_decades != 0
                or self.within_decade != self.fork_a - 2
                or self.literal_transition_weight != 0
            ):
                raise AssertionError("invalid fork terminal control")
        elif self.kind == "landmine":
            if (
                self.terminal_sector != 9
                or self.fork_a is not None
                or self.complete_decades != 0
                or self.within_decade != 8
                or self.literal_transition_weight != 0
            ):
                raise AssertionError("invalid landmine terminal control")
        else:
            raise AssertionError("unknown B1 terminal control")
        if self.terminal_headroom <= 0 or self.seam_transition_count < 0:
            raise AssertionError("invalid B1 terminal arithmetic")


@dataclass(frozen=True, slots=True)
class TerminalPopulation:
    """Aggregate counts from the optional full finite audit."""

    total: int
    live: int
    forks: dict[int, int]
    landmines: int
    landmine_headrooms: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class StopD:
    """One exact occurrence weight; all terminal projections are derived."""

    d: int

    def __post_init__(self) -> None:
        if type(self.d) is not int or not 0 <= self.d <= 9 * MAX_FUTURE_DECADES + 8:
            raise ValueError("Stop(D) is outside the bounded future domain")

    @property
    def complete_decades(self) -> int:
        return self.d // 9

    @property
    def within_decade(self) -> int:
        return self.d % 9

    @property
    def kind(self) -> Literal["fork", "landmine"]:
        return "landmine" if self.within_decade == 8 else "fork"

    @property
    def fork_a(self) -> int | None:
        return None if self.within_decade == 8 else self.within_decade + 2


@dataclass(frozen=True, slots=True)
class SourceStopTrace:
    """A source-run stop paired with its independently observed terminal."""

    stop: StopD
    complete_decades: int
    within_decade: int
    kind: Literal["fork", "landmine"]
    fork_a: int | None


def decode_stop_d(d: int) -> StopD:
    """Decode a bounded weight without consulting a terminal table."""

    return StopD(d)


def _stop_d_from_source_run(complete_decades: int, run: EndpointRun) -> StopD:
    """Build ``D`` from the source run's strict transitions and terminal."""

    if run.outcome.kind not in ("fork", "landmine"):
        raise ValueError("Stop(D) requires a source run ending at a stop")
    within_decade = run.strict_sector_advances
    if run.outcome.kind == "fork":
        if run.outcome.fork_a != within_decade + 2:
            raise AssertionError("Fork sector disagrees with source transitions")
    elif within_decade != 8:
        raise AssertionError("Landmine sector disagrees with source transitions")
    return decode_stop_d(9 * complete_decades + within_decade)


def _stop_trace_from_source_run(
    complete_decades: int, run: EndpointRun
) -> SourceStopTrace:
    """Keep the source terminal beside the independently encoded Stop(D)."""

    if run.outcome.kind not in ("fork", "landmine"):
        raise ValueError("Stop(D) trace requires a source run ending at a stop")
    stop = _stop_d_from_source_run(complete_decades, run)
    return SourceStopTrace(
        stop,
        complete_decades,
        run.strict_sector_advances,
        run.outcome.kind,
        run.outcome.fork_a,
    )


def _root_endpoint(clock: CyclotomicClock, offset: int) -> DecisiveEndpoint:
    """Build the sector-one endpoint without calling the B1 evaluator."""

    _, headroom = entry_headroom(1, offset, clock, exponent_delta=0)
    terminal = classify_near_port(1, headroom)
    return DecisiveEndpoint(1, terminal.terminal_headroom)


def _terminal_from_endpoint(
    endpoint: DecisiveEndpoint,
    move: NearChartTarget,
    *,
    seam_transition_count: int,
) -> TerminalControl:
    """Classify one decisive endpoint using only the Near seam law."""

    if type(move) is not NearChartTarget:
        raise TypeError("terminal endpoint requires its selected Near move")
    if move.next_chart is not None:
        raise AssertionError("decisive endpoint was not at a terminal seam")
    if move.fork_a is None:
        return TerminalControl(
            "landmine",
            endpoint.sector,
            endpoint.headroom,
            None,
            0,
            endpoint.sector - 1,
            seam_transition_count,
            0,
        )
    return TerminalControl(
        "fork",
        endpoint.sector,
        endpoint.headroom,
        move.fork_a,
        0,
        endpoint.sector - 1,
        seam_transition_count,
        0,
    )


def terminal_control(clock: CyclotomicClock, offset: int) -> TerminalControl:
    """Reconstruct one B1 terminal control path independently.

    Entry jumps and Near prefixes use the shared arithmetic owners.  The walk
    retains only a running seam count and the current endpoint; no
    transition rows, rank, or future selector is materialized.
    """

    if type(clock) is not CyclotomicClock:
        raise TypeError("terminal audit requires a cyclotomic clock")
    if type(offset) is not int or not 0 <= offset <= 90:
        raise ValueError("terminal audit offset is outside the canonical domain")

    endpoint = _root_endpoint(clock, offset)
    strict_advances = 0
    seam_transition_count = 0
    while True:
        move = near_chart_target(
            BoundaryChart("near", endpoint.sector, 0, endpoint.headroom)
        )
        seam_transition_count += int(move.literal_increment > 0)
        target = move.next_chart
        if target is None:
            result = _terminal_from_endpoint(
                endpoint,
                move,
                seam_transition_count=seam_transition_count,
            )
            if result.within_decade != strict_advances:
                raise AssertionError("terminal sector and strict count disagree")
            return result

        if target.kind == "near":
            normalized = classify_near_port(target.leading, target.coordinate)
            endpoint = DecisiveEndpoint(target.leading, normalized.terminal_headroom)
            continue

        if target.leading == 1 and target.delta == 1:
            if endpoint.sector != 9:
                raise AssertionError("live seam occurred before sector nine")
            return TerminalControl(
                "live",
                endpoint.sector,
                endpoint.headroom,
                None,
                1,
                strict_advances,
                seam_transition_count,
                1,
            )

        if target.leading != endpoint.sector + 1 or target.delta != 0:
            raise AssertionError("internal B1 transition changed its sector transport")
        _, headroom = entry_headroom(
            target.leading,
            target.coordinate,
            clock,
            exponent_delta=target.delta,
        )
        normalized = classify_near_port(target.leading, headroom)
        endpoint = DecisiveEndpoint(target.leading, normalized.terminal_headroom)
        strict_advances += 1
        if strict_advances > 8:
            raise AssertionError("B1 terminal audit exceeded eight strict advances")


def audit_terminal_population() -> TerminalPopulation:
    """Evaluate all 46 canonical roots at all 924 external phases.

    This is intentionally not called from the default test suite or module
    import path.  It is a finite audit of the arithmetic boundary only.
    """

    forks: Counter[int] = Counter()
    landmine_headrooms: set[int] = set()
    live = landmines = total = 0
    for offset in offset_representatives():
        for phase in range(PERIOD):
            result = terminal_control(CyclotomicClock.from_phase(phase), offset)
            total += 1
            if result.kind == "live":
                live += 1
            elif result.kind == "fork":
                if result.fork_a is None:
                    raise AssertionError("fork audit lost its coefficient")
                forks[result.fork_a] += 1
            else:
                landmines += 1
                landmine_headrooms.add(result.terminal_headroom)
    return TerminalPopulation(
        total,
        live,
        dict(sorted(forks.items())),
        landmines,
        tuple(sorted(landmine_headrooms)),
    )


def assert_claimed_population(population: TerminalPopulation) -> None:
    """Check the claimed finite counts after an explicit audit run."""

    if population.total != FULL_B1_COUNT:
        raise AssertionError(f"unexpected B1 population: {population.total}")
    if population.forks != EXPECTED_FORK_COUNTS:
        raise AssertionError(f"unexpected fork counts: {population.forks}")
    if population.landmines != EXPECTED_LANDMINE_COUNT:
        raise AssertionError(f"unexpected landmine count: {population.landmines}")
    if population.landmine_headrooms != EXPECTED_LANDMINE_HEADROOMS:
        raise AssertionError(
            f"unexpected landmine headrooms: {population.landmine_headrooms}"
        )
    if (
        population.live
        != population.total - sum(population.forks.values()) - population.landmines
    ):
        raise AssertionError("terminal population does not partition into outcomes")


@dataclass(frozen=True, slots=True)
class FuturePopulation:
    """Aggregates from the opt-in recursive Stop(D) audit."""

    total: int
    reachable_d: tuple[int, ...]
    d_multiplicity: dict[int, int]
    ambiguous_d: dict[int, tuple[tuple[str, int | None], ...]]
    eventual_by_root: tuple[tuple[StopD, ...], ...]
    actual_terminal_by_root: tuple[tuple[tuple[str, int | None], ...], ...]
    actual_weight_by_root: tuple[tuple[tuple[int, int], ...], ...]
    maximum_complete_decades: int

    @property
    def terminal_kind_function_count(self) -> int:
        """Distinct Fork/Landmine responses across every external phase."""

        return len(
            {tuple(kind for kind, _ in root) for root in self.actual_terminal_by_root}
        )


def _shift_clock(clock: CyclotomicClock, shift: int) -> CyclotomicClock:
    if type(shift) is not int or shift < 0:
        raise ValueError("future clock shift must be a nonnegative integer")
    return CyclotomicClock(
        (clock.mod4 + shift) % 4,
        (clock.mod3 + shift) % 3,
        (clock.mod7 + shift) % 7,
        (clock.mod11 + shift) % 11,
    )


def eventual_stop(
    clock: CyclotomicClock,
    offset: int,
    *,
    max_complete_decades: int = MAX_FUTURE_DECADES,
) -> StopD:
    """Follow source-selected transitions until Fork/Landmine.

    Each live seam supplies the next source coordinate and increments the
    external clock by one decade.  ``D`` is assembled from that transition
    count and the terminal source run; no evaluated output label is decoded.
    """

    if type(clock) is not CyclotomicClock:
        raise TypeError("future audit requires a cyclotomic clock")
    if type(offset) is not int or not 0 <= offset <= 90:
        raise ValueError("future audit offset is outside the canonical domain")
    if (
        type(max_complete_decades) is not int
        or not 0 <= max_complete_decades <= MAX_FUTURE_DECADES
    ):
        raise ValueError("future audit decade bound is outside the tested domain")

    return _eventual_stop_trace(
        clock,
        offset,
        max_complete_decades=max_complete_decades,
    ).stop


def _eventual_stop_trace(
    clock: CyclotomicClock,
    offset: int,
    *,
    max_complete_decades: int,
) -> SourceStopTrace:
    """Run the future walk once while retaining its source terminal."""

    current_clock = clock
    current_offset = offset
    complete_decades = 0
    while complete_decades <= max_complete_decades:
        run = evaluate_b1_source(current_clock, current_offset)
        if run.outcome.kind in ("fork", "landmine"):
            return _stop_trace_from_source_run(complete_decades, run)
        if run.outcome.kind != "live" or run.outcome.entry_coordinate is None:
            raise AssertionError("source run returned an incomplete live seam")
        if run.outcome.exponent_advance != 1:
            raise AssertionError(
                "live source transition changed by more than one decade"
            )
        complete_decades += run.outcome.exponent_advance
        if complete_decades > max_complete_decades:
            break
        current_offset = run.outcome.entry_coordinate
        current_clock = _shift_clock(current_clock, run.outcome.exponent_advance)
    raise RuntimeError("future Stop(D) audit exceeded its bounded decade horizon")


def audit_future_stop_population() -> FuturePopulation:
    """Audit eventual Stop(D) functions for all 46 roots and 924 phases.

    This is intentionally opt-in: it is a bounded experiment over 42,504
    source occurrences and is not part of the default test suite.
    """

    representatives = offset_representatives()
    by_root: list[tuple[StopD, ...]] = []
    actual_by_root: list[tuple[tuple[str, int | None], ...]] = []
    actual_weights_by_root: list[tuple[tuple[int, int], ...]] = []
    d_multiplicity: Counter[int] = Counter()
    d_outputs: dict[int, set[tuple[str, int | None]]] = {}
    maximum_complete_decades = 0
    for offset in representatives:
        root_results: list[StopD] = []
        root_actual: list[tuple[str, int | None]] = []
        root_actual_weights: list[tuple[int, int]] = []
        for phase in range(PERIOD):
            trace = _eventual_stop_trace(
                CyclotomicClock.from_phase(phase),
                offset,
                max_complete_decades=MAX_FUTURE_DECADES,
            )
            root_results.append(trace.stop)
            root_actual.append((trace.kind, trace.fork_a))
            root_actual_weights.append((trace.complete_decades, trace.within_decade))
            d_multiplicity[trace.stop.d] += 1
            d_outputs.setdefault(trace.stop.d, set()).add((trace.kind, trace.fork_a))
            maximum_complete_decades = max(
                maximum_complete_decades, trace.stop.complete_decades
            )
        by_root.append(tuple(root_results))
        actual_by_root.append(tuple(root_actual))
        actual_weights_by_root.append(tuple(root_actual_weights))
    ambiguous_d = {
        d: tuple(sorted(outputs))
        for d, outputs in d_outputs.items()
        if len(outputs) > 1
    }
    return FuturePopulation(
        len(representatives) * PERIOD,
        tuple(sorted(d_multiplicity)),
        dict(sorted(d_multiplicity.items())),
        dict(sorted(ambiguous_d.items())),
        tuple(by_root),
        tuple(actual_by_root),
        tuple(actual_weights_by_root),
        maximum_complete_decades,
    )


def _assert_stop_matches_source(
    stop: StopD,
    actual_kind: str,
    actual_fork_a: int | None,
    *,
    actual_complete_decades: int,
    actual_within_decade: int,
) -> None:
    if (stop.kind, stop.fork_a) != (actual_kind, actual_fork_a):
        raise AssertionError(
            "Stop(D) projection disagrees with the source terminal: "
            f"{stop} versus {(actual_kind, actual_fork_a)}"
        )
    if (stop.complete_decades, stop.within_decade) != (
        actual_complete_decades,
        actual_within_decade,
    ):
        raise AssertionError(
            "Stop(D) weight disagrees with source transition counts: "
            f"{stop} versus {(actual_complete_decades, actual_within_decade)}"
        )


def assert_claimed_future_population(population: FuturePopulation) -> None:
    """Check the claimed 204 reachable D values and Stop(D) consistency."""

    if population.total != FULL_B1_COUNT:
        raise AssertionError(f"unexpected future population: {population.total}")
    if len(population.reachable_d) != EXPECTED_REACHABLE_STOP_D:
        raise AssertionError(
            f"unexpected reachable Stop(D) count: {len(population.reachable_d)}"
        )
    if population.ambiguous_d:
        raise AssertionError(f"ambiguous Stop(D) outputs: {population.ambiguous_d}")
    if population.terminal_kind_function_count != len(offset_representatives()):
        raise AssertionError(
            "eventual terminal-kind functions do not separate all roots"
        )
    for root_results, actual_results, actual_weights in zip(
        population.eventual_by_root,
        population.actual_terminal_by_root,
        population.actual_weight_by_root,
        strict=True,
    ):
        for result, (actual_kind, actual_fork_a), (actual_height, actual_j) in zip(
            root_results, actual_results, actual_weights, strict=True
        ):
            _assert_stop_matches_source(
                result,
                actual_kind,
                actual_fork_a,
                actual_complete_decades=actual_height,
                actual_within_decade=actual_j,
            )


def full_audit_command() -> str:
    """Return the opt-in command without running the 42,504-cell audit."""

    return (
        "PYTHONPATH=src python3 -m devtools.verification.comma_b1_terminal_audit --full"
    )


def full_future_audit_command() -> str:
    """Return the opt-in recursive Stop(D) command without running it."""

    return (
        "PYTHONPATH=src python3 -m devtools.verification.comma_b1_terminal_audit"
        " --full-future"
    )


def _main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="run all 42,504 cells")
    parser.add_argument(
        "--full-future",
        action="store_true",
        help="run the bounded recursive Stop(D) audit",
    )
    args = parser.parse_args()
    if not args.full and not args.full_future:
        parser.error("audits are opt-in; pass --full or --full-future")
    if args.full:
        population = audit_terminal_population()
        assert_claimed_population(population)
        print(population)
    if args.full_future:
        future_population = audit_future_stop_population()
        assert_claimed_future_population(future_population)
        repeated_d = tuple(
            d for d, count in future_population.d_multiplicity.items() if count > 1
        )
        print(
            "future_stop_total="
            f"{future_population.total} "
            f"reachable_d={len(future_population.reachable_d)} "
            f"repeated_d_values={len(repeated_d)} "
            f"ambiguous_d={len(future_population.ambiguous_d)} "
            f"max_complete_decades={future_population.maximum_complete_decades} "
            f"terminal_kind_functions={future_population.terminal_kind_function_count}"
        )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(_main))
