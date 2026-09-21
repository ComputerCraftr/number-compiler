"""Exact exit diagnostics for the restricted fixed-carry pumping rule.

This is not a complete cylinder constructor or a production certificate. It
derives a maximal *fixed-carry, no-growth* interval from the original source.
An exit refutes that particular admission predicate, not temporal closure of
the full cylinder. No future source word or temporal coefficient row is built.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.formula.skew_residue_laws import pair_no_growth
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


@dataclass(frozen=True, slots=True)
class CarryExit:
    """The first source-relative coefficient outside one carry guard.

    ``exponent`` counts completed reverse/add applications. Thus the failed
    carry belongs to application ``exponent + 1``. All coordinates before this
    globally earliest exponent satisfy the original carry pattern.
    """

    exponent: int
    position: int
    original_pair: int
    beta: int
    incoming: int
    outgoing: int
    lower: int
    upper: int
    value: int


@dataclass(frozen=True, slots=True)
class ChamberExitReport:
    """Diagnostic data, deliberately not an admitted semantic-effect handle."""

    width: int
    initial_growth: bool
    safe_applications: int | None
    exit: CarryExit | None


def _first_outside(pair: int, beta: int, lower: int, upper: int) -> int | None:
    if not lower <= pair <= upper:
        raise ValueError("source coefficient does not satisfy its carry guard")
    slope = pair + beta
    if slope == 0:
        return None
    maximum_scale = (
        (upper + beta) // slope if slope > 0 else (-lower - beta) // (-slope)
    )
    # The initial guard ensures maximum_scale >= 1. For a positive integer k,
    # bit_length(k) is the first exponent t for which 2**t > k.
    return maximum_scale.bit_length()


def analyze_chamber_exit(
    source: ExactSource, ledger: ResourceLedger
) -> ChamberExitReport:
    """Find the earliest guard exit using only authenticated source ports.

    Work is spatial: one pass over the original source coordinates, with the
    existing carry-range cache. It is independent of any requested horizon.
    There is no claim that source admission itself is sublinear in its width.
    """
    ports = SourceCarryPorts(source, ledger)
    try:
        if ports.terminal:
            return ChamberExitReport(ports.width, True, 0, None)
        first: CarryExit | None = None
        for position in range(ports.width):
            pair = ports.pair(position)
            incoming, outgoing = ports.carry(position), ports.carry(position + 1)
            reflected_in = ports.carry(ports.width - 1 - position)
            reflected_out = ports.carry(ports.width - position)
            beta = pair_no_growth(
                0, incoming, outgoing, reflected_in, reflected_out, source.base
            )
            lower = source.base - incoming if outgoing else 0
            upper = 2 * source.base - 2 if outgoing else source.base - 1 - incoming
            exponent = _first_outside(pair, beta, lower, upper)
            ledger.bump("reverse_pump_exit_source_coordinates")
            if exponent is not None and (first is None or exponent < first.exponent):
                value = (1 << exponent) * (pair + beta) - beta
                first = CarryExit(
                    exponent,
                    position,
                    pair,
                    beta,
                    incoming,
                    outgoing,
                    lower,
                    upper,
                    value,
                )
        return ChamberExitReport(
            ports.width, False, None if first is None else first.exponent, first
        )
    finally:
        ports.dispose()
