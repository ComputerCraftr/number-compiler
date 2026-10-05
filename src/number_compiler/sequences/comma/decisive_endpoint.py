"""Source-selected, on-demand B1 endpoint actions.

The endpoint is a spatial state ``(sector, headroom)``.  The cyclotomic clock
belongs to the occurrence using that endpoint and is never interned into its
semantic state.  This module stores no per-phase transition rows: a caller
selects one exact action with the shared Entry/Near arithmetic.

This is an arithmetic constructor only.  It does not decide infinite-path
safety or authorize a CLI cutover.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Literal

from number_compiler.sequences.comma.arithmetic import (
    classify_near_port,
    entry_headroom,
    is_sector9_landmine_headroom,
)
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    near_chart_target,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.domain import decade_root_coordinate


@dataclass(frozen=True, slots=True, order=True)
class DecisiveEndpoint:
    """A canonical Near endpoint at the end of a strict sector run."""

    sector: int
    headroom: int

    def __post_init__(self) -> None:
        if type(self.sector) is not int or not 1 <= self.sector <= 9:
            raise ValueError("decisive endpoint sector must be in 1..9")
        if type(self.headroom) is not int:
            raise ValueError("decisive endpoint headroom must be an integer")
        extra = int(self.sector < 9)
        active_digit = (-self.headroom) % 10
        if not (
            self.headroom > extra
            and self.headroom <= 10 * active_digit + self.sector + extra
        ):
            raise ValueError("headroom is outside the decisive Near boundary")


@dataclass(frozen=True, slots=True)
class EndpointOccurrence:
    """Occurrence-local clock paired with a reusable spatial endpoint."""

    endpoint: DecisiveEndpoint
    clock: CyclotomicClock

    def __post_init__(self) -> None:
        if type(self.endpoint) is not DecisiveEndpoint:
            raise TypeError("endpoint occurrence requires a decisive endpoint")
        if type(self.clock) is not CyclotomicClock:
            raise TypeError("endpoint occurrence requires an external cyclotomic clock")


@dataclass(frozen=True, slots=True)
class EndpointOutcome:
    """One exact endpoint action, with successor occurrence data separate."""

    kind: Literal["advance", "live", "fork", "landmine"]
    next_endpoint: DecisiveEndpoint | None = None
    entry_coordinate: int | None = None
    fork_a: int | None = None
    exponent_advance: int = 0

    def __post_init__(self) -> None:
        if type(self.kind) is not str:
            raise TypeError("endpoint outcome kind must be an exact string")
        if type(self.exponent_advance) is not int:
            raise TypeError("endpoint exponent advance must be an exact integer")
        if self.kind == "advance":
            if (
                type(self.next_endpoint) is not DecisiveEndpoint
                or self.entry_coordinate is not None
                or self.fork_a is not None
                or self.exponent_advance != 0
            ):
                raise ValueError("invalid endpoint advance payload")
        elif self.kind == "live":
            if (
                self.next_endpoint is not None
                or type(self.entry_coordinate) is not int
                or not decade_root_coordinate(1, self.entry_coordinate)
                or self.fork_a is not None
                or self.exponent_advance != 1
            ):
                raise ValueError("invalid live endpoint payload")
        elif self.kind == "fork":
            if (
                self.next_endpoint is not None
                or self.entry_coordinate is not None
                or type(self.fork_a) is not int
                or not 2 <= self.fork_a <= 9
                or self.exponent_advance != 0
            ):
                raise ValueError("invalid fork endpoint payload")
        elif self.kind == "landmine":
            if (
                self.next_endpoint is not None
                or self.entry_coordinate is not None
                or self.fork_a is not None
                or self.exponent_advance != 0
            ):
                raise ValueError("invalid landmine endpoint payload")
        else:
            raise ValueError("unknown endpoint outcome")


@dataclass(frozen=True, slots=True)
class EndpointRun:
    """Terminal B1 result and the number of strict sector advances used."""

    outcome: EndpointOutcome
    strict_sector_advances: int

    def __post_init__(self) -> None:
        if type(self.outcome) is not EndpointOutcome:
            raise TypeError("endpoint run requires an exact endpoint outcome")
        if self.outcome.kind == "advance":
            raise ValueError("endpoint run must end at a terminal or live action")
        if (
            type(self.strict_sector_advances) is not int
            or not 0 <= self.strict_sector_advances <= 8
        ):
            raise ValueError("B1 run must use at most eight strict sector advances")


def _near_endpoint(
    leading: int,
    headroom: int,
    *,
    charge_work: Callable[[int], None] | None,
    charge_bits: Callable[[int], None] | None,
) -> DecisiveEndpoint:
    returned = classify_near_port(
        leading,
        headroom,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    return DecisiveEndpoint(leading, returned.terminal_headroom)


def _entry_target(
    chart: BoundaryChart,
    clock: CyclotomicClock,
    *,
    charge_bits: Callable[[int], None] | None,
    charge_work: Callable[[int], None] | None,
) -> BoundaryChart:
    """Apply the shared Entry arithmetic without constructing a weighted move."""
    if chart.kind != "entry":
        raise ValueError("endpoint Entry projection requires an Entry chart")
    if charge_work is not None:
        # Charge before doing any transfer or residue arithmetic so an
        # exhausted request cannot perform unaccounted constructor work.
        charge_work(1)
    _, headroom = entry_headroom(
        chart.leading,
        chart.coordinate,
        clock,
        exponent_delta=chart.delta,
        charge_bits=charge_bits,
    )
    return BoundaryChart("near", chart.leading, chart.delta, headroom)


def source_endpoint(
    clock: CyclotomicClock,
    offset: int,
    *,
    charge_bits: Callable[[int], None] | None = None,
    charge_work: Callable[[int], None] | None = None,
) -> EndpointOccurrence:
    """Classify an admitted sector-1 source through its exact Entry action.

    The absolute offset and exact occurrence clock are inputs, not fields of
    ``DecisiveEndpoint``.  The Entry jump and shared Near port selector produce
    the initial endpoint without rank/terminal tables or a decimal trajectory.
    """
    if type(clock) is not CyclotomicClock:
        raise TypeError("source endpoint requires a cyclotomic occurrence clock")
    if not decade_root_coordinate(1, offset):
        raise ValueError("source offset is outside the canonical sector-1 domain")
    entry = BoundaryChart("entry", 1, 0, offset)
    target = _entry_target(
        entry,
        clock,
        charge_bits=charge_bits,
        charge_work=charge_work,
    )
    endpoint = _near_endpoint(
        target.leading,
        target.coordinate,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    return EndpointOccurrence(endpoint, clock)


def endpoint_step(
    occurrence: EndpointOccurrence,
    *,
    charge_bits: Callable[[int], None] | None = None,
    charge_work: Callable[[int], None] | None = None,
) -> EndpointOutcome:
    """Apply the source-selected action at one decisive endpoint on demand."""
    if type(occurrence) is not EndpointOccurrence:
        raise TypeError("endpoint step requires a canonical occurrence")
    endpoint = occurrence.endpoint
    if charge_work is not None:
        charge_work(1)
    if endpoint.sector == 9 and is_sector9_landmine_headroom(endpoint.headroom):
        return EndpointOutcome("landmine")
    near = BoundaryChart("near", endpoint.sector, 0, endpoint.headroom)
    move = near_chart_target(near)
    target = move.next_chart
    if target is None:
        if move.fork_a is not None:
            return EndpointOutcome("fork", fork_a=move.fork_a)
        return EndpointOutcome("landmine")

    if target.kind == "near":
        # This constructor is only defined on decisive Near endpoints. A
        # same-sector Near target would contradict that admission guard.
        if target.leading != endpoint.sector + 1:
            raise ArithmeticError(
                "decisive endpoint produced a non-advancing Near target"
            )
        successor = _near_endpoint(
            target.leading,
            target.coordinate,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        if successor.sector != endpoint.sector + 1:
            raise ArithmeticError("decisive endpoint did not advance its sector")
        return EndpointOutcome("advance", next_endpoint=successor)

    if endpoint.sector == 9:
        if target.leading != 1 or target.delta != 1:
            raise ArithmeticError("sector-9 live seam lost its decade transport")
        return EndpointOutcome(
            "live", entry_coordinate=target.coordinate, exponent_advance=1
        )

    if target.leading != endpoint.sector + 1 or target.delta != 0:
        raise ArithmeticError("interior endpoint changed its sector transport")
    near_target = _entry_target(
        target,
        occurrence.clock,
        charge_bits=charge_bits,
        charge_work=charge_work,
    )
    successor = _near_endpoint(
        near_target.leading,
        near_target.coordinate,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    if successor.sector != endpoint.sector + 1:
        raise ArithmeticError("interior Entry failed strict sector advance")
    return EndpointOutcome("advance", next_endpoint=successor)


def evaluate_b1_source(
    clock: CyclotomicClock,
    offset: int,
    *,
    charge_bits: Callable[[int], None] | None = None,
    charge_work: Callable[[int], None] | None = None,
) -> EndpointRun:
    """Evaluate one source-selected B1 block using at most nine sectors.

    The bound is the finite count of strict decimal sectors 1 through 9, not a
    temporal fuel parameter. It produces an exact live seam, fork or landmine.
    Infinite-path admission remains a separate theorem.
    """
    occurrence = source_endpoint(
        clock, offset, charge_bits=charge_bits, charge_work=charge_work
    )
    advances = 0
    while True:
        outcome = endpoint_step(
            occurrence, charge_bits=charge_bits, charge_work=charge_work
        )
        if outcome.kind != "advance":
            return EndpointRun(outcome, advances)
        target = outcome.next_endpoint
        if target is None or target.sector != occurrence.endpoint.sector + 1:
            raise ArithmeticError("B1 endpoint worklist lost strict sector order")
        if advances >= 8:
            raise ArithmeticError("B1 source exceeded its nine-sector envelope")
        advances += 1
        occurrence = EndpointOccurrence(target, clock)


__all__ = [
    "DecisiveEndpoint",
    "EndpointOccurrence",
    "EndpointOutcome",
    "EndpointRun",
    "endpoint_step",
    "evaluate_b1_source",
    "source_endpoint",
]
