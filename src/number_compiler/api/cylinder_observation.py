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
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder
from number_compiler.sequences.collatz.power import CollatzEventArena
from number_compiler.sequences.collatz.raw_field import (
    accelerated_collatz_sentinel_step_digits,
)
from number_compiler.sequences.power_numbers.etale_factor import factor_from_etale_root
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def observe_physical_clock(
    seed: int, ticks: int, *, max_ticks: int, max_digits: int
) -> dict[str, Any]:
    """Read the existing bound powered result; no accelerated-prefix discovery."""
    seed = require_integer(seed, "seed", 1)
    ticks = require_integer(ticks, "physical ticks", 0)
    require_integer(max_ticks, "physical tick budget", 0)
    require_integer(max_digits, "digit budget", 1)
    if ticks > max_ticks or seed.bit_length() > max_digits:
        raise ValueError("physical clock observation budget exceeded")
    term = PoweredCollatzTerm(
        seed, ticks, max_context_nodes=10000, max_cache_entries=20000
    )
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
    arena = CollatzEventArena()
    root = arena.identity
    digits = tuple(digits_lsd(seed, 4))
    digit_work = 0
    discovered = 0
    for _ in range(events):
        if digits == (1,):
            break
        if len(digits) > max_digits:
            raise ValueError("source observation digit budget exceeded")
        step = accelerated_collatz_sentinel_step_digits(digits, base=4)
        digit_work += step.source_width
        discovered += 1
        root = arena.concat(root, arena.event(step.valuation))
        digits = step.target_digits
    observer = CollatzClockObservers(arena)
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
        "reached_one": digits == (1,),
        "requested_events": events,
        "discovered_events": discovered,
        "discovery_digit_work": digit_work,
        "arena_nodes": arena.node_count,
        "normalization_compositions": arena.composition_operations,
        "observer_nodes": observer.node_evaluations,
        "observer_compositions": observer.compositions,
        "ring_power_compositions": observer.ring_power_compositions,
    }


def observe_mirror(
    seed: int, generation: int, *, first_width: int, max_digits: int
) -> dict[str, Any]:
    require_integer(max_digits, "digit budget", 1)
    first_width = require_integer(first_width, "first sheet width", 1)
    if first_width > max_digits:
        raise ValueError("mirror sheet exceeds digit budget")
    term = ReverseAddPoweredTerm(
        seed, generation, max_context_nodes=10000, max_cache_entries=20000
    )
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
