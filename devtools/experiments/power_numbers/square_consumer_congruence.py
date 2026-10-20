"""Complete bounded square-only consumer congruences for Fermat/Mersenne.

This audit deliberately asks for less than a ring quotient.  Its only
transition is the production recurrence: negacyclic square for Fermat and
cyclic square-minus-two for Mersenne.  Carry/fold and harmonic responses are
derived from :class:`ArithmeticTile`; the final target is observed after the
square so the dead sign of the source is not retained.

The resulting finite Moore machines are research witnesses.  They do not
certify an unbounded carrier or admission to ``TileScheduler``.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from number_compiler.arithmetic.functions.finite_unary import (
    analyze_observer,
    minimize_unary_moore,
    quotient_machine_from_moore,
)
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)


@dataclass(frozen=True, slots=True)
class SquareConsumerCongruenceAudit:
    family: str
    parameter: int
    width: int
    source_states: int
    one_step_image_states: int
    sign_orbit_classes: int
    triangular_product_cells: int
    ordered_product_cells: int
    initial_consumer_classes: int
    initial_successor_conflicts: int
    refinement_rounds: int
    stable_classes: int
    stable_successor_conflicts: int
    quotient_transition_verified: bool
    source_sign_action_conflicts: int
    current_terminal_sign_conflicts: int
    pulled_terminal_sign_conflicts: int
    noninjective: bool
    general_multiplication_required: bool
    general_addition_required: bool
    scheduler_promotion_safe: bool


@dataclass(frozen=True, slots=True)
class TerminalDeckCongruenceAudit:
    """Complete current-terminal observer after the square deck quotient."""

    family: str
    parameter: int
    modulus: int
    source_states: int
    one_step_image_states: int
    deck_classes: int
    expected_half_deck_classes: int
    terminal_observer_classes: int
    terminal_observer_conflicts: int
    square_power_horizons: tuple[int, ...]
    square_power_conflicts: tuple[int, ...]
    terminal_deck_split: bool
    zero_one_merged: bool
    fermat_zero_one_carry_harmonic_equal: bool | None
    zero_one_incoming_interval: tuple[int, int] | None
    full_five_dimensional_germ_descends_claimed: bool
    cyclotomic_lift_marker_sign_invariant_safe: bool
    cyclotomic_lift_marker_owner: str
    scheduler_promotion_safe: bool
    minimal_moore_quotient_claimed: bool


def _parameters() -> tuple[tuple[str, int], ...]:
    return (
        ("fermat", 2),
        ("fermat", 3),
        ("mersenne", 5),
        ("mersenne", 7),
    )


def _deck_parameters() -> tuple[tuple[str, int], ...]:
    return (
        ("fermat", 2),
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 11),
        ("mersenne", 13),
    )


def _target(family: str, value: int, modulus: int) -> bool:
    return value == (modulus - 1 if family == "fermat" else 0)


def class_ids(values: tuple[object, ...]) -> tuple[int, ...]:
    classes: dict[object, int] = {}
    return tuple(classes.setdefault(value, len(classes)) for value in values)


def terminal_deck_key(family: str, value: int, modulus: int) -> tuple[object, ...]:
    """Deck geometry with exactly the current terminal distinction demanded."""
    if family == "fermat":
        if value == modulus - 1:
            return ("fermat-terminal-minus-one",)
        if value in (0, 1):
            return ("fermat-zero-one-tail",)
        return ("fermat-square-deck", min(value, (-value) % modulus))
    return ("mersenne-square-deck", min(value, (-value) % modulus))


def _square_consumer_setup(
    family: str, parameter: int
) -> tuple[ArithmeticTileSpec, int, tuple[int, ...], int]:
    width = (1 << parameter) if family == "fermat" else parameter
    spec = getattr(ArithmeticTileSpec, family)(width)
    modulus = spec.modulus
    transitions = tuple(
        (value * value + spec.addend) % modulus for value in range(modulus)
    )
    return spec, modulus, transitions, width


def _terminal_deck_audit(family: str, parameter: int) -> TerminalDeckCongruenceAudit:
    spec, modulus, transition, _width = _square_consumer_setup(family, parameter)
    keys = tuple(terminal_deck_key(family, value, modulus) for value in range(modulus))
    ids = class_ids(keys)
    terminal = tuple(_target(family, value, modulus) for value in range(modulus))
    analysis = analyze_observer(
        keys,
        tuple(keys[target] for target in transition),
        terminal,
    )
    zero_one_response_equal = None
    zero_one_interval = None
    if family == "fermat":
        pair_intervals = tuple(
            ArithmeticTile.from_value(spec, value).step_with_carry_interval()[1]
            for value in (0, 1)
        )
        incoming_min = min(interval[0] for interval in pair_intervals)
        incoming_max = max(interval[1] for interval in pair_intervals)
        pair_responses: list[tuple[object, ...]] = []
        for value in (0, 1):
            step, harmonic = ArithmeticTile.from_value(
                spec, value
            ).step_with_harmonic_consumer(
                incoming_min=incoming_min,
                incoming_max=incoming_max,
                order=4,
                modulus=2,
            )
            pair_responses.append(
                (
                    step.boundary_action(
                        incoming_min=incoming_min,
                        incoming_max=incoming_max,
                    ).canonical_key,
                    harmonic.canonical_key,
                )
            )
        zero_one_response_equal = pair_responses[0] == pair_responses[1]
        # Record the admitted ports: this local pair check is not a proof
        # for a full-ring port interval or the proposed richer germs.
        zero_one_interval = (incoming_min, incoming_max)
    horizons = (1, 2, 4, 8, 16, 32)
    conflicts: list[int] = []
    powered = tuple(range(modulus))
    elapsed = 0
    for horizon in horizons:
        for _ in range(horizon - elapsed):
            powered = tuple(transition[state] for state in powered)
        elapsed = horizon
        conflicts.append(
            analyze_observer(
                keys, tuple(keys[state] for state in powered)
            ).successor_conflicts
        )
    return TerminalDeckCongruenceAudit(
        family,
        parameter,
        modulus,
        modulus,
        len(set(transition)),
        len(set(ids)),
        (modulus + 1) // 2,
        len(set(terminal)),
        analysis.target_conflicts,
        horizons,
        tuple(conflicts),
        family == "fermat" and ids[1] != ids[modulus - 1],
        ids[0] == ids[1],
        zero_one_response_equal,
        zero_one_interval,
        False,
        family == "mersenne",
        "cyclotomic_binary_lift_marker",
        False,
        False,
    )


def _audit(family: str, parameter: int) -> SquareConsumerCongruenceAudit:
    spec, modulus, transitions, width = _square_consumer_setup(family, parameter)

    # Carry bounds are a demanded observation.  Keep the ordinary production
    # step free of this complete-domain scan.
    intervals = tuple(
        ArithmeticTile.from_value(spec, value).step_with_carry_interval()[1]
        for value in range(modulus)
    )
    incoming_min = min(interval[0] for interval in intervals)
    incoming_max = max(interval[1] for interval in intervals)
    responses: list[object] = []
    for value, successor in enumerate(transitions):
        step, harmonic = ArithmeticTile.from_value(
            spec, value
        ).step_with_harmonic_consumer(
            incoming_min=incoming_min,
            incoming_max=incoming_max,
            order=4,
            modulus=2,
        )
        if step.tile.residue != successor:
            raise AssertionError((family, parameter, value, step.tile.residue))
        carry = step.boundary_action(
            incoming_min=incoming_min, incoming_max=incoming_max
        )
        responses.append(
            (
                carry.canonical_key,
                harmonic.canonical_key,
                _target(family, successor, modulus),
            )
        )

    observations = tuple(responses)
    initial = class_ids(observations)
    initial_analysis = analyze_observer(
        initial, tuple(initial[target] for target in transitions)
    )
    minimized = minimize_unary_moore(transitions, observations)
    stable_analysis = analyze_observer(
        minimized.class_ids,
        tuple(minimized.class_ids[target] for target in transitions),
    )
    machine = quotient_machine_from_moore(
        transitions, observations, minimized.class_ids
    )

    sign_actions = current_terminal = pulled_terminal = 0
    seen_pairs: set[tuple[int, int]] = set()
    for value in range(modulus):
        negative = (-value) % modulus
        pair = (min(value, negative), max(value, negative))
        if pair in seen_pairs:
            continue
        seen_pairs.add(pair)
        sign_actions += int(
            transitions[value] != transitions[negative]
            or observations[value] != observations[negative]
            or minimized.class_ids[value] != minimized.class_ids[negative]
        )
        current_terminal += int(
            _target(family, value, modulus) != _target(family, negative, modulus)
        )
        pulled_terminal += int(
            _target(family, transitions[value], modulus)
            != _target(family, transitions[negative], modulus)
        )

    sign_classes = len({min(value, (-value) % modulus) for value in range(modulus)})
    triangular = width * (width + 1) // 2
    return SquareConsumerCongruenceAudit(
        family,
        parameter,
        width,
        modulus,
        len(set(transitions)),
        sign_classes,
        triangular,
        width * width,
        len(set(initial)),
        initial_analysis.successor_conflicts,
        minimized.rounds,
        minimized.classes,
        stable_analysis.successor_conflicts,
        machine.classes == minimized.classes,
        sign_actions,
        current_terminal,
        pulled_terminal,
        minimized.classes < modulus,
        False,
        False,
        False,
    )


@lru_cache(maxsize=1)
def square_consumer_congruence_audits() -> tuple[SquareConsumerCongruenceAudit, ...]:
    return tuple(_audit(family, parameter) for family, parameter in _parameters())


@lru_cache(maxsize=1)
def terminal_deck_congruence_audits() -> tuple[TerminalDeckCongruenceAudit, ...]:
    return tuple(
        _terminal_deck_audit(family, parameter)
        for family, parameter in _deck_parameters()
    )


__all__ = [
    "SquareConsumerCongruenceAudit",
    "TerminalDeckCongruenceAudit",
    "square_consumer_congruence_audits",
    "terminal_deck_congruence_audits",
]
