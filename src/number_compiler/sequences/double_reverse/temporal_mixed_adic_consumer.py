"""Source-certified 2rev10 mixed-adic and harmonic return consumer.

This is an autonomous *projected* source consumer, not a physical full-word
period.  A finite admission from the actual seed reaches the forward-closed
nine-edge two-digit cylinder C0.  On that cylinder the phase, width parity,
and X modulo 99 constitute a deterministic successor-closed right congruence.
The lower border fixes X mod 20; CRT therefore lifts to X mod 1980, including
2**2, 5, 9 and 11 simultaneously.  The lossless low/reversed digit-field
mod-18/90 projections are emitted from the SAME state.

A determinized powerset of C0 edges supplies a *sound enclosure* of X mod 100
and, via CRT, X mod 9900. It must not be mistaken for an exact physical carry
selector: some independent edge choices may not form globally feasible paths.

72 and 576 are exact return lengths for the protected harmonic mod-18/90
observer. They are NOT periods of the mixed-adic or complete physical word.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import gcd

from number_compiler.arithmetic.carry.carry_itinerary import crt_coprime
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits

from .boundary_cycles import CANDIDATE_COMPONENTS, boundary_steps
from .temporal_hashlife_borders import (
    PHYSICAL_GROWTH_CYCLES,
    advance_residue_clock,
    edge_phase,
    outer_digits,
)
from .two_rev10_digit_field import TwoReverseDualDigitField18

_MOD99 = 99
_MOD20 = 20
_MOD1980 = 1980
_MOD9900 = 9900
_GROWTH = tuple(cycle[0] for cycle in PHYSICAL_GROWTH_CYCLES)
_LAST_MOD20 = tuple(outer_digits(phase)[1] for phase in range(4))
_C0 = tuple(sorted(CANDIDATE_COMPONENTS[0]))
_EDGE_INDEX = {edge: index for index, edge in enumerate(_C0)}


@lru_cache(maxsize=1)
def certified_edge_action() -> tuple[tuple[int, ...], ...]:
    """Exhaustively prove C0 is successor closed for both inward carry values.

    Each `boundary_steps` edge is the exact two-decimal-cell result for a
    possible incoming interior carry; its arithmetic is independent of the
    rest of the source. Thus checking the nine source edges proves induction
    for EVERY physical future, not just a finite seed orbit sample.
    """
    rows: list[tuple[int, ...]] = []
    if len(_C0) != 9:
        raise AssertionError("protected boundary cylinder changed")
    for edge in _C0:
        phase = edge_phase(edge[:2], edge[2:])
        if phase is None or (
            (edge[0], edge[3]) != outer_digits(phase)
            or (10 * edge[2] + edge[3]) % 20 != _LAST_MOD20[phase]
            or (edge[3] >= 5) != bool(_GROWTH[phase])
        ):
            raise AssertionError("protected source edge has invalid phase/width guard")
        relation = boundary_steps(edge)
        if relation.shrinking_frontier or not relation.steps:
            raise AssertionError("closed C0 unexpectedly has a shrinking frontier")
        destinations: set[int] = set()
        for step in relation.steps:
            if step.target not in _EDGE_INDEX:
                raise AssertionError("protected boundary has a successor outside C0")
            next_phase = edge_phase(step.target[:2], step.target[2:])
            if next_phase != (phase + 1) % 4 or step.width_delta != _GROWTH[phase]:
                raise AssertionError("source edge does not preserve guarded phase")
            destinations.add(_EDGE_INDEX[step.target])
        rows.append(tuple(sorted(destinations)))
    return tuple(rows)


def _edge_mask_successor(mask: int) -> int:
    rows = certified_edge_action()
    next_mask = 0
    for index, destinations in enumerate(rows):
        if mask & (1 << index):
            for destination in destinations:
                next_mask |= 1 << destination
    return next_mask


@lru_cache(maxsize=9)
def _edge_subset_lasso(start_index: int) -> tuple[tuple[int, ...], int, int]:
    """Find the transient and cycle of the reachable subset masks."""
    if type(start_index) is not int or not 0 <= start_index < len(_C0):
        raise ValueError("source entry is not a C0 semantic edge")
    mask = 1 << start_index
    seen: dict[int, int] = {}
    states: list[int] = []
    while mask not in seen:
        if len(states) >= 1 << len(_C0):
            raise AssertionError("finite edge powerset cannot exceed 512 classes")
        seen[mask] = len(states)
        states.append(mask)
        mask = _edge_mask_successor(mask)
    transient = seen[mask]
    return tuple(states), transient, len(states) - transient


def _edge_subset_at(start_index: int, steps: int) -> tuple[int, int, int]:
    if type(steps) is not int or steps < 0:
        raise ValueError("nonnegative successor count required")
    rows, transient, period = _edge_subset_lasso(start_index)
    where = steps if steps < len(rows) else transient + (steps - transient) % period
    return rows[where], transient, period


@dataclass(frozen=True, slots=True)
class SourceEntry:
    generation: int
    edge: tuple[int, int, int, int]
    phase: int
    width_parity: int
    residue99: int

    @property
    def edge_index(self) -> int:
        return _EDGE_INDEX[self.edge]


def source_entry(
    seed: int,
    max_prefix: int = 64,
    *,
    max_state_bits: int = 4096,
) -> SourceEntry | None:
    """Admit a *physical* seed by an exact bounded prefix and a finite proof.

    Does not query the target generation or reconstruct any intermediate
    source beyond the first C0 entry. The finite edge induction then owns all
    future projected steps. A non-admitted seed returns None, never a guess.
    """
    require_integer(seed, "mixed-adic seed", 0)
    require_integer(max_prefix, "mixed-adic admission steps", 0, 64)
    require_integer(max_state_bits, "mixed-adic admission bits", 1, 4096)
    if seed == 0:
        return None
    certified_edge_action()
    x = seed
    for n in range(max_prefix + 1):
        if x.bit_length() > max_state_bits:
            return None
        digits = digits_lsd(x, 10)
        if len(digits) >= 5:
            edge = (digits[-1], digits[-2], digits[1], digits[0])
            if edge in _EDGE_INDEX:
                phase = edge_phase(edge[:2], edge[2:])
                if phase is None:
                    raise AssertionError("source entry missing a protected phase")
                return SourceEntry(n, edge, phase, len(digits) % 2, x % _MOD99)
        if n != max_prefix:
            x = 2 * value_from_lsd_digits(reversed(digits), 10)
    return None


@dataclass(frozen=True, slots=True)
class MixedAdicState:
    """Minimal Moore ID for the mod1980 + protected outer-field program.

    Width parity is erased when r is divisible by 11: the two potential
    2/20 multipliers agree modulo 99, and that property is invariant.
    There are exactly 756 distinguishable future-output classes.
    """

    phase: int
    width_parity: int | None
    residue99: int

    def __post_init__(self) -> None:
        if type(self.phase) is not int or self.phase not in range(4):
            raise ValueError("invalid source-certified phase")
        if type(self.residue99) is not int or not 0 <= self.residue99 < 99:
            raise ValueError("invalid source residue modulo 99")
        if self.residue99 % 11 == 0:
            if self.width_parity is not None and (
                type(self.width_parity) is not int or self.width_parity not in (0, 1)
            ):
                raise ValueError("invalid decimal width parity")
            object.__setattr__(self, "width_parity", None)
        elif type(self.width_parity) is not int or self.width_parity not in (0, 1):
            raise ValueError("nontrivial mod-11 fiber requires width parity")

    @property
    def residue1980(self) -> int:
        return crt_coprime(self.residue99, 99, _LAST_MOD20[self.phase], 20)

    @property
    def field(self) -> TwoReverseDualDigitField18:
        return TwoReverseDualDigitField18(2 * self.residue99 % 18, self.phase)

    def successor(self) -> MixedAdicState:
        return type(self)(
            *advance_residue_clock(self.phase, self.width_parity or 0, self.residue99)
        )

    def power(self, steps: int) -> MixedAdicState:
        """Exact O(log steps) successor, without inspecting physical terms."""
        if type(steps) is not int or steps < 0:
            raise ValueError("mixed-adic power requires a nonnegative integer")
        four_returns, tail = divmod(steps, 4)
        state = type(self)(
            self.phase,
            self.width_parity,
            pow(160, four_returns, 99) * self.residue99 % 99,
        )
        for _ in range(tail):
            state = state.successor()
        return state

    @property
    def primitive_period(self) -> int:
        denominator = 99 // gcd(99, self.residue99)
        if denominator == 1:
            return 4  # zero modulo 99; only the four border phases remain
        for p in (1, 2, 3, 5, 6, 10, 15, 30):
            if pow(160, p, denominator) == 1:
                return 4 * p
        raise AssertionError("proven mod-99 multiplier order exceeded 30")


def _valuation_certificate(
    delta: int, prime: int, known_exponent: int
) -> dict[str, object]:
    modulus = prime**known_exponent
    residue = delta % modulus
    if residue == 0:
        return {"at_least": known_exponent, "exact": None, "precision": known_exponent}
    valuation = 0
    while residue % prime == 0:
        residue //= prime
        valuation += 1
    return {"at_least": valuation, "exact": valuation, "precision": known_exponent}


def _period_certificate(
    state: MixedAdicState,
    length: int,
    source_mod1980: int,
    source_field: TwoReverseDualDigitField18,
) -> dict[str, object]:
    target = state.power(length)
    # The high/low last digits identify the guarded phase; the common mod-9
    # class and even parity recover the temporal mod-18 state.
    field_return = target.field == source_field
    mixed_delta = (target.residue1980 - source_mod1980) % 1980
    return {
        "duration": length,
        "field_mod18_mod90_and_outer_carry_return": field_return,
        "field_return_proof": (
            "phase repeats mod4 and 2**duration == 1 on the source mod9 ideal"
        ),
        "physical_mod99_return": target.residue99 == state.residue99,
        "mixed_mod1980_return": mixed_delta == 0,
        "mixed_delta_mod1980": mixed_delta,
        "return_2_adic": _valuation_certificate(mixed_delta, 2, 2),
        "return_5_adic": _valuation_certificate(mixed_delta, 5, 1),
        "physical_full_carry_vector_period_certified": False,
    }


def certified_mixed_adic_packet(
    seed: int,
    generation: int,
    *,
    max_steps: int = 64,
    max_state_bits: int = 4096,
) -> dict[str, object]:
    """Compile the source-authorized closed quotient and 72/576 tests.

    No term owner, SLP, physical endpoint or post-entry carry occurrence is
    constructed. Source admission is exactly bounded by 64 physical steps.
    """
    require_integer(generation, "mixed-adic generation", 0)
    require_integer(max_steps, "mixed-adic step budget", 0)
    require_integer(max_state_bits, "mixed-adic state budget", 1)
    limit = min(64, generation, max_steps)
    entry = source_entry(seed, limit, max_state_bits=min(4096, max_state_bits))
    if entry is None:
        return {
            "status": "unavailable",
            "reason": "the source has not been admitted into the proved nine-edge cylinder",
            "source_admission_limit": limit,
            "arbitrary_physical_carry_period_certified": False,
        }
    initial = MixedAdicState(entry.phase, entry.width_parity, entry.residue99)
    target = initial.power(generation - entry.generation)
    target_mod1980 = target.residue1980
    mask, transient, subset_period = _edge_subset_at(
        entry.edge_index, generation - entry.generation
    )
    edges = [edge for index, edge in enumerate(_C0) if mask & (1 << index)]
    candidates100 = tuple(sorted({10 * edge[2] + edge[3] for edge in edges}))
    candidates9900 = tuple(
        sorted(
            {
                crt_coprime(target.residue99, 99, last_two, 100)
                for last_two in candidates100
            }
        )
    )
    if not candidates9900 or any(z % 1980 != target_mod1980 for z in candidates9900):
        raise AssertionError("mixed CRT lifted candidates fail their canonical parent")
    field = target.field
    period_returns = tuple(
        _period_certificate(target, length, target_mod1980, field)
        for length in (72, 576)
    )
    return {
        "status": "available",
        "scope": "exact guarded mod1980 quotient and safe mod9900 candidate enclosure; not full physical carry",
        "entry_generation": entry.generation,
        "entry_edge": list(entry.edge),
        "entry_phase": entry.phase,
        "physical_admission_steps": entry.generation,
        "physical_post_entry_steps": 0,
        "full_endpoint_materialized": False,
        "nine_edge_induction_checked": len(certified_edge_action()),
        "raw_product_state_count": 792,
        "moore_minimal_state_count": 756,
        "moore_output_program": "physical mod1980 and four protected mod90 digit-field orientations",
        "semantic_state": {
            "phase": target.phase,
            "width_parity": target.width_parity,
            "residue99": target.residue99,
        },
        "physical_residue1980": target_mod1980,
        "certified_exact_mixed_prime_powers": {"2": 2, "5": 1, "3": 2, "11": 1},
        "mod20_port_from_phase": _LAST_MOD20[target.phase],
        "physical_mod9900_candidates": list(candidates9900),
        "physical_mod100_candidates": list(candidates100),
        "mod9900_candidates_are_a_safe_enclosure_not_a_selected_physical_value": True,
        "edge_powerset_reachable_class_count": len(
            _edge_subset_lasso(entry.edge_index)[0]
        ),
        "edge_powerset_transient": transient,
        "edge_powerset_period": subset_period,
        "field_mod18_mod90": field.packet(),
        "period_72_576_consumer": list(period_returns),
        "primitive_period_mod1980_and_phase": target.primitive_period,
        "source_guards_are_inductively_successor_closed": True,
        "cross_precision_projection_mod9900_to_mod1980": True,
        "full_interior_carry_vector_period_certified": False,
        "arbitrary_physical_carry_period_certified": False,
        "temporal_powered_without_source_scheduler": True,
    }


__all__ = [
    "SourceEntry",
    "MixedAdicState",
    "certified_edge_action",
    "source_entry",
    "certified_mixed_adic_packet",
]
