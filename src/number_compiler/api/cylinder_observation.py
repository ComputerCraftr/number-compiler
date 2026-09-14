"""Bounded, demanded cylinder observations from canonical arithmetic owners.

Collatz indices count accelerated odd events, stopping at one, except the
physical-clock query which counts ordinary ticks. Accelerated discovery is
explicitly charged; a shared event program is not a claim of sublinear discovery.
Special-number roots are supplied and checked, never advertised as terminal roots.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from typing import Any

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers
from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder
from number_compiler.sequences.power_numbers.etale_factor import factor_from_etale_root
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def observe_physical_clock(
    seed: int,
    ticks: int,
    *,
    max_ticks: int,
    max_digits: int,
    _term: PoweredCollatzTerm | None = None,
) -> dict[str, Any]:
    """Read the existing bound powered result; no accelerated-prefix discovery."""
    seed = require_integer(seed, "seed", 1)
    ticks = require_integer(ticks, "physical ticks", 0)
    require_integer(max_ticks, "physical tick budget", 0)
    require_integer(max_digits, "digit budget", 1)
    if ticks > max_ticks or seed.bit_length() > max_digits:
        raise ValueError("physical clock observation budget exceeded")
    term = _term or PoweredCollatzTerm(
        seed, ticks, max_context_nodes=10000, max_cache_entries=20000
    )
    if (term.seed, term.steps) != (seed, ticks):
        raise ValueError("physical clock term belongs to another source request")
    if ticks and term.maximum_width > max_digits:
        raise ValueError("physical clock target exceeds digit budget")
    clock = term.s_arithmetic_clock()
    return {
        "family": "collatz",
        "kind": "physical-clock",
        "scope": "source-bound physical powered result, including the 1-4-2 cycle",
        "requested_ticks": ticks,
        "value": {
            **asdict(clock),
            "physical_ticks": clock.physical_ticks,
            "real_prime_exponents": clock.real_prime_exponents,
            "two_adic_exponent": clock.two_adic_exponent,
            "three_adic_exponent": clock.three_adic_exponent,
        },
        "work_counters": dict(term._ledger.counters),
        "peak_nodes": term._ledger.peak_nodes,
        "retained_nodes": term._ledger.nodes,
    }


class CollatzObservationContext:
    """One admitted accelerated prefix and one reusable observer for a query."""

    def __init__(
        self, seed: int, events: int, *, max_events: int, max_digits: int
    ) -> None:
        from number_compiler.sequences.collatz.source_publisher import (
            CollatzSourcePublisher,
        )

        require_integer(seed, "seed", 1)
        require_integer(events, "events", 0)
        require_integer(max_events, "event budget", 0)
        require_integer(max_digits, "digit budget", 1)
        if not seed & 1:
            raise ValueError("accelerated event observations require an odd seed")
        if events > max_events or seed.bit_length() > 2 * max_digits:
            raise ValueError("source observation budget exceeded")
        publisher = CollatzSourcePublisher(
            seed, events, max_events=max_events, max_digits=max_digits
        )
        published = publisher.publish()
        arena, root = publisher.events, published.event_root
        observer = CollatzClockObservers(arena)
        self.binding = (seed, events, max_events, max_digits)
        self.publisher, self.published = publisher, published
        self.physical_support = published.physical_support
        self.arena, self.root, self.observer = arena, root, observer
        self.discovered = published.discovered_events
        self.digit_work = published.discovery_digit_work
        self.reached_one = published.reached_one


def observe_collatz(
    seed: int,
    events: int,
    *,
    kind: str,
    modulus: int = 257,
    width: int = 2,
    sign: int = -1,
    precision: int = 8,
    target: int = 0,
    s_weight: int = 1,
    z_weight: int = 1,
    max_events: int = 4096,
    max_digits: int = 4096,
    _context: CollatzObservationContext | None = None,
) -> dict[str, Any]:
    if kind not in {
        "clock",
        "modular",
        "twisted",
        "hasse",
        "hensel",
        "tropical",
        "factor",
    }:
        raise ValueError("unknown Collatz observation")
    seed = require_integer(seed, "seed", 1)
    events = require_integer(events, "events", 0)
    require_integer(max_events, "event budget", 0)
    require_integer(max_digits, "digit budget", 1)
    if not seed & 1:
        raise ValueError("accelerated event observations require an odd seed")
    if events > max_events or seed.bit_length() > 2 * max_digits:
        raise ValueError("source observation budget exceeded")
    if modulus < 2 or modulus.bit_length() > 4096 or not 1 <= width <= 256:
        raise ValueError("observer coefficient/width budget exceeded")
    if not 0 <= precision <= 4096:
        raise ValueError("observer precision budget exceeded")
    context = _context or CollatzObservationContext(
        seed, events, max_events=max_events, max_digits=max_digits
    )
    if context.binding != (seed, events, max_events, max_digits):
        raise ValueError(
            "accelerated observer context belongs to another source request"
        )
    context.published.validate()
    if (
        context.arena is not context.publisher.events
        or context.root is not context.published.event_root
        or context.physical_support is not context.published.physical_support
        or context.observer.arena is not context.arena
        or context.publisher.binding[1:] != context.binding
    ):
        raise ValueError("accelerated observer lost its published source binding")
    arena, root, observer = context.arena, context.root, context.observer
    discovered, digit_work = context.discovered, context.digit_work
    value: Any
    if kind == "clock":
        clock = observer.clock(root)
        value = {
            **asdict(clock),
            "physical_ticks": clock.physical_ticks,
            "real_prime_exponents": clock.real_prime_exponents,
            "two_adic_exponent": clock.two_adic_exponent,
            "three_adic_exponent": clock.three_adic_exponent,
        }
    elif kind == "modular":
        value = asdict(observer.modular(root, modulus))
    elif kind == "twisted":
        value = observer.twisted(root, width=width, sign=sign, modulus=modulus)
    elif kind == "hasse":
        value = observer.hasse(root, degree=width, modulus=modulus)
    elif kind == "hensel":
        value = asdict(
            observer.hensel_pullback(root, HenselCylinder(precision, target))
        )
    elif kind == "tropical":
        value = observer.tropical(root, s_weight=s_weight, z_weight=z_weight)
    elif kind == "factor":
        support = observer.factor_observation(root, modulus)
        value = {"support": support.divisor, "factor": support.proper_factor}
    else:
        raise ValueError("unknown Collatz observation")
    return {
        "family": "collatz",
        "kind": kind,
        "value": value,
        "scope": "source-derived accelerated prefix, stopping at one if reached",
        "reached_one": context.reached_one,
        "requested_events": events,
        "discovered_events": discovered,
        "discovery_digit_work": digit_work,
        "admission_digit_comparisons": context.published.admission_digit_comparisons,
        "source_support_ticks": context.physical_support.ticks,
        "source_work_counters": dict(context.publisher.ledger.counters),
        "source_support_retained_nodes": context.publisher.ledger.nodes,
        "separately_retained": context.publisher.separately_retained,
        "arena_nodes": arena.node_count,
        "normalization_compositions": arena.composition_operations,
        "observer_nodes": observer.node_evaluations,
        "observer_compositions": observer.compositions,
        "ring_power_compositions": observer.ring_power_compositions,
    }


def observe_mirror(
    seed: int,
    generation: int,
    *,
    first_width: int,
    max_digits: int,
    base: int = 10,
    _term: ReverseAddPoweredTerm | None = None,
) -> dict[str, Any]:
    require_integer(max_digits, "digit budget", 1)
    first_width = require_integer(first_width, "first sheet width", 1)
    if first_width > max_digits:
        raise ValueError("mirror sheet exceeds digit budget")
    term = _term or ReverseAddPoweredTerm(
        seed, generation, base=base, max_context_nodes=10000, max_cache_entries=20000
    )
    if (term.seed, term.generation, term.base) != (seed, generation, base):
        raise ValueError("mirror term belongs to another source request")
    if term.maximum_width > require_integer(max_digits, "digit budget", 1):
        raise ValueError("mirror target exceeds digit budget")
    projection = term.mirror_obstruction(first_width=first_width)
    return {
        "family": "196",
        "kind": "mirror",
        "generation": generation,
        "scope": "current target only",
        "palindrome": projection is None,
        "value": None if projection is None else asdict(projection),
        "work_counters": dict(term._ledger.counters),
        "peak_nodes": term._ledger.peak_nodes,
        "retained_nodes": term._ledger.nodes,
    }


def observe_etale_root(
    family: str, parameter: int, defect: int, *, max_digits: int
) -> dict[str, Any]:
    parameter = require_integer(parameter, "parameter", 0)
    require_integer(max_digits, "digit budget", 2)
    if (
        family == "fermat"
        and parameter >= max_digits.bit_length()
        or family == "mersenne"
        and parameter > max_digits
    ):
        raise ValueError("root observation width budget exceeded")
    width = (1 << parameter) if family == "fermat" else parameter
    if width > max_digits:
        raise ValueError("root observation width budget exceeded")
    spec = ArithmeticTileSpec(family, width)
    factor = factor_from_etale_root(spec.modulus, defect)
    tile = ArithmeticTile.from_value(spec, defect)
    _, key = tile.step_with_primary_carry_jet()
    _, projection = tile.step_with_twisted_projection(
        width=width, sign=spec.boundary_sign
    )
    return {
        "family": family,
        "kind": "root",
        "scope": "supplied checked root; no terminal construction",
        "key": asdict(key),
        "field": projection.coefficients,
        "factor": factor,
        "factor_proof": "nontrivial-etale-root" if factor is not None else None,
    }


def execute_observation(args: argparse.Namespace) -> dict[str, Any]:
    if args.family == "antihydra":
        from number_compiler.api.antihydra_observation import observe

        return observe(args)
    if args.family == "collatz":
        if args.seed is None:
            raise ValueError("Collatz observation requires --seed")
        if args.kind == "physical-clock":
            return observe_physical_clock(
                args.seed,
                args.index,
                max_ticks=args.max_events,
                max_digits=args.max_digits,
            )
        return observe_collatz(
            args.seed,
            args.index,
            kind=args.kind or "clock",
            modulus=args.modulus,
            width=args.width,
            sign=args.sign,
            precision=args.precision,
            target=args.target,
            s_weight=args.s_weight,
            z_weight=args.z_weight,
            max_events=args.max_events,
            max_digits=args.max_digits,
        )
    if args.family == "196":
        if args.kind not in (None, "mirror"):
            raise ValueError("196 supports the mirror observation")
        return observe_mirror(
            196 if args.seed is None else args.seed,
            args.index,
            first_width=args.width,
            max_digits=args.max_digits,
        )
    if args.kind not in (None, "root") or args.defect is None:
        raise ValueError("special root observation requires --defect")
    return observe_etale_root(
        args.family, args.index, args.defect, max_digits=args.max_digits
    )
