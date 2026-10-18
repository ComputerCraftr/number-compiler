"""Exact seam summaries for finite, source-certified 2rev10 birth layers.

This module summarizes the active one-digit boundaries of an existing
``BirthRingState``.  It does not generate a future word or infer an infinite
period from a finite source horizon.  The only indefinite result is the
separately checked first-pair closed border component.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import double_reverse as metric_keys

from .boundary_cycles import CANDIDATE_COMPONENTS
from .stencil_moore import stencil_cell
from .temporal_hashlife import edge_phase, growth_ports

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger

    from .temporal_birth_ring import BirthRingPorts, BirthRingState


@dataclass(frozen=True, slots=True)
class SeamGate:
    """The only next-bank digits that can depend on the current inlets.

    ``None`` means that the side grows on this tick and therefore shields its
    external inlet.  Active values are the exact retained edge outputs, so
    equality is an observable equivalence rather than a raw-port comparison.
    """

    phase: int
    left_output: int | None
    right_output: int | None


@dataclass(frozen=True, slots=True)
class FiniteInductionWitness:
    """Finite alignment evidence; it never certifies an unbounded source."""

    pairs: int
    lag_fsteps: int
    compared_rows: int
    equal_bank_rows: int
    agreeing_seam_rows: int
    canceled_raw_inlet_rows: int
    gate_break_rows: int
    equal_odd_boundary_rows: int
    unknown_odd_boundary_rows: int
    first_failure_fstep: int | None
    start_fstep: int
    failure_type: str | None
    finite_all_physical_equal: bool
    indefinitely_certified: bool = False


@dataclass(frozen=True, slots=True)
class ClosedBorderPairReturn:
    """Universal four-step return of the outer pair, not the full edge."""

    input_edge: tuple[int, int, int, int]
    phase: int
    outer_pair_return_steps: int
    closed_component_edges: int
    all_binary_carry_words_covered: bool


def seam_gate(state: BirthRingState, inlet: BirthRingPorts) -> SeamGate:
    """Project two raw inlets to their exact effect on the retained K-bank."""
    from .temporal_birth_ring import BirthRingPorts as Ports
    from .temporal_birth_ring import BirthRingState as State

    if type(state) is not State or type(inlet) is not Ports:
        raise TypeError("seam quotient requires issued birth-ring value types")
    left_birth, right_birth = growth_ports(state.phase, 1)
    left_output: int | None = None
    right_output: int | None = None
    if left_birth == 0:
        left_neighbor = state.left[-2] if state.pairs > 1 else 0
        left_output = stencil_cell(left_neighbor, state.left[-1], inlet.left_inner)
    if right_birth == 0:
        right_neighbor = state.right[1] if state.pairs > 1 else 0
        right_output = stencil_cell(inlet.right_inner, state.right[0], right_neighbor)
    return SeamGate(state.phase, left_output, right_output)


def gate_equivalent_next(
    first: BirthRingState,
    second: BirthRingState,
    inlet_a: BirthRingPorts,
    inlet_b: BirthRingPorts,
) -> bool:
    """Check the one-step iff for identical current banks and phase."""
    if first != second:
        raise ValueError("gate equivalence requires identical current K banks")
    equivalent = seam_gate(first, inlet_a) == seam_gate(second, inlet_b)
    actual = first.advance(inlet_a)[0] == second.advance(inlet_b)[0]
    if equivalent != actual:
        raise AssertionError("seam gate disagrees with exact birth stencil")
    return equivalent


def finite_birth_period_induction(
    states: tuple[BirthRingState, ...],
    ports: tuple[BirthRingPorts, ...],
    *,
    lag_fsteps: int,
    start_fstep: int = 0,
    ledger: ResourceLedger | None = None,
) -> FiniteInductionWitness:
    """Compare retained source rows and gates over one finite certified span.

    The caller supplies already authenticated rows from the birth publisher.
    This function only compares those rows; it never asks the temporal engine
    to rediscover a source digit.  The intervening odd physical step remains
    a separate observable and unknown odd rows do not count as equality.
    """
    from .temporal_birth_ring import odd_boundary_pairs

    if (
        type(states) is not tuple
        or type(ports) is not tuple
        or len(states) != len(ports)
        or len(states) < 3
        or type(lag_fsteps) is not int
        or not 1 <= lag_fsteps < len(states) - 1
        or type(start_fstep) is not int
        or not 0 <= start_fstep < len(states) - lag_fsteps - 1
    ):
        raise ValueError("finite induction needs aligned source rows and a valid lag")
    depth = states[0].pairs
    if any(state.pairs != depth for state in states):
        raise ValueError("finite induction changed bank depth")

    end = len(states) - lag_fsteps - 1
    equal_banks = agreeing = cancellations = breaks = odd_equal = odd_unknown = 0
    first_failure: int | None = None
    failure_type: str | None = None
    for time in range(start_fstep, end):
        if ledger is not None:
            ledger.bump(metric_keys.DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS)
        first, later = states[time], states[time + lag_fsteps]
        first_port, later_port = ports[time], ports[time + lag_fsteps]
        if first != later:
            if first_failure is None:
                first_failure, failure_type = time, "existing_bank_difference"
        else:
            equal_banks += 1
            same_gate = seam_gate(first, first_port) == seam_gate(later, later_port)
            if same_gate:
                agreeing += 1
                cancellations += int(first_port != later_port)
            else:
                breaks += 1
                if first_failure is None:
                    first_failure, failure_type = time, "inward_seam_difference"
            next_equal = states[time + 1] == states[time + lag_fsteps + 1]
            if same_gate != next_equal:
                raise AssertionError("retained next rows violate the seam iff")

        odd_first = odd_boundary_pairs(first, first_port)
        odd_later = odd_boundary_pairs(later, later_port)
        if odd_first is None or odd_later is None:
            odd_unknown += 1
            if first_failure is None:
                first_failure, failure_type = time, "odd_boundary_unproved"
        elif odd_first == odd_later:
            odd_equal += 1
        else:
            if first_failure is None:
                first_failure, failure_type = time, "odd_boundary_difference"

    compared = end - start_fstep
    all_equal = (
        equal_banks == compared
        and agreeing == compared
        and odd_equal == compared
        and odd_unknown == 0
    )
    return FiniteInductionWitness(
        depth,
        lag_fsteps,
        compared,
        equal_banks,
        agreeing,
        cancellations,
        breaks,
        odd_equal,
        odd_unknown,
        first_failure,
        start_fstep,
        failure_type,
        all_equal,
    )


def certified_closed_outer_pair_return(
    edge: tuple[int, int, int, int],
) -> ClosedBorderPairReturn:
    """Certify the outer-pair return without claiming a full-edge period.

    Interior edge cells may vary with the carry word. The theorem applies to
    the projected first/last digit pair for all future binary carry inputs.
    """
    if (
        type(edge) is not tuple
        or len(edge) != 4
        or any(type(digit) is not int or not 0 <= digit <= 9 for digit in edge)
    ):
        raise ValueError("source border must be four decimal digits")
    if edge not in CANDIDATE_COMPONENTS[0]:
        raise ValueError("source edge is outside the universally closed border SCC")
    phase = edge_phase(edge[:2], edge[2:])
    if phase is None:
        raise AssertionError("closed border edge has no authenticated phase")
    return ClosedBorderPairReturn(edge, phase, 4, len(CANDIDATE_COMPONENTS[0]), True)


__all__ = [
    "ClosedBorderPairReturn",
    "FiniteInductionWitness",
    "SeamGate",
    "certified_closed_outer_pair_return",
    "finite_birth_period_induction",
    "gate_equivalent_next",
    "seam_gate",
]
