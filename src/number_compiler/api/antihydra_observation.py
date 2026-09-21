"""Public finite Antihydra observations; all indices count macro returns."""

from __future__ import annotations

import argparse
from dataclasses import asdict
from typing import Any

from number_compiler.api.json_output import json_integers
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.antihydra.machine import MACHINE, MACHINE_SHA256
from number_compiler.sequences.antihydra.mahler import tangent
from number_compiler.sequences.antihydra.observers import (
    SpaceTimeProjection,
    tape_projection,
)
from number_compiler.sequences.antihydra.runtime import ArithmeticResult, Run, run
from number_compiler.sequences.antihydra.support import (
    directional_hasse,
    tape_hasse,
    tape_intervals,
)


def observe(args: argparse.Namespace) -> dict[str, Any]:
    """Compatibility Python adapter; the family-first CLI uses a shared query owner."""
    if args.seed is not None or args.defect is not None:
        raise ValueError(
            "Antihydra uses the pinned blank-tape source; no --seed or --defect"
        )
    kind = args.kind or "clock"
    if kind not in {
        "clock",
        "physical-clock",
        "tape",
        "twisted",
        "hasse",
        "tropical",
        "factor",
        "spacetime",
        "mahler",
        "hensel",
        "modular",
    }:
        raise ValueError("unsupported Antihydra observation")
    require_integer(args.modulus, "coefficient modulus", 2)
    if args.modulus.bit_length() > 4096:
        raise ValueError("coefficient modulus exceeds bit budget")
    require_integer(args.width, "spatial width", 1, 256)
    require_integer(args.precision, "precision", 1, 4096)
    if kind == "hasse":
        require_integer(args.width, "Hasse order", 1, 8)
    if (
        kind == "factor"
        and pow(2, args.width, args.modulus) != args.sign % args.modulus
    ):
        raise ValueError("factor target is incompatible with the tape cylinder")
    result = run(args.index, max_returns=args.max_events, max_bits=args.max_digits)
    return observe_run(
        result,
        kind=kind,
        modulus=args.modulus,
        width=args.width,
        sign=args.sign,
        precision=args.precision,
        time_width=args.time_width,
        time_sign=args.time_sign,
        max_observer_terms=args.max_observer_terms,
    )


def observe_arithmetic(
    result: ArithmeticResult, *, kind: str, precision: int = 8
) -> dict[str, Any]:
    """Demand a total arithmetic observation without requesting physical execution."""
    if kind not in {"mahler", "hensel"}:
        raise ValueError("unsupported arithmetic Antihydra observation")
    result.require_source()
    value = tangent(result, precision)
    if kind == "mahler":
        from number_compiler.sequences.antihydra.mahler_action import associated_action

        value["associated_action"] = associated_action(result)
    return json_integers(
        {
            "family": "antihydra",
            "machine": MACHINE,
            "machine_sha256": MACHINE_SHA256,
            "source_binding": result.source_binding,
            "kind": kind,
            "index_unit": "macro_returns_after_11_step_startup",
            "requested_returns": result.returns,
            "completed_returns": result.returns,
            "guarded_physical_status": "not_requested",
            "ledger_first_failure_index": result.first_failure_index,
            "nonhalting_certified": False,
            "scope": "total arithmetic iteration; all-time barrier unresolved",
            "value": value,
            "work_counters": dict(result.ledger.counters),
            "peak_nodes": result.ledger.peak_nodes,
            "retained_nodes": result.ledger.nodes,
        }
    )


def observe_run(
    result: Run,
    *,
    kind: str,
    modulus: int = 257,
    width: int = 2,
    sign: int = -1,
    precision: int = 8,
    time_width: int = 2,
    time_sign: int = 1,
    max_observer_terms: int = 1_000_000,
) -> dict[str, Any]:
    """Demand one projection from an existing authenticated physical owner."""
    if kind not in {
        "clock",
        "physical-clock",
        "tape",
        "twisted",
        "hasse",
        "tropical",
        "factor",
        "spacetime",
        "mahler",
        "hensel",
        "modular",
    }:
        raise ValueError("unsupported Antihydra observation")
    result.require_source()
    if result.halted:
        return json_integers(
            {
                "family": "antihydra",
                "kind": kind,
                "status": "unavailable",
                "reason": "requested returning section reaches or passes the halting boundary",
                "requested_returns": result.requested,
                "halt_boundary": result.returns,
                "halted": True,
                "physical_ticks_at_halt": result.physical_ticks,
                "nonhalting_certified": False,
            }
        )
    value: Any
    if kind in {"clock", "physical-clock"}:
        value = {
            "left": result.left,
            "right": result.right,
            "physical_ticks": result.physical_ticks,
            "head": result.head,
            "ledger": result.balance,
            "minimum_ledger": result.minimum,
            "h": result.h,
            "centered_odd_events": result.odd_events,
            "odd_a_steps": result.returns - result.odd_events,
        }
    elif kind in {"mahler", "hensel"}:
        value = tangent(result, precision)
        if kind == "mahler":
            from number_compiler.sequences.antihydra.mahler_action import (
                associated_action,
            )

            value["associated_action"] = associated_action(result)
    elif kind == "modular":
        value = {
            "modulus": modulus,
            "h": result.h % modulus,
            "left": result.left % modulus,
            "right": result.right % modulus,
            "physical_ticks": result.physical_ticks % modulus,
        }
    elif kind == "spacetime":
        value = SpaceTimeProjection(
            result, width, time_width, sign, time_sign, modulus, max_observer_terms
        ).evaluate()
    elif kind == "hasse":
        value = {
            "center": 1,
            "modulus": modulus,
            "coefficients": tape_hasse(result, width, modulus),
            "directional_events": directional_hasse(result, width, modulus),
        }
        result.ledger.counters["tape_hasse_terms"] = (width + 1) * len(
            tape_intervals(result)
        )
    elif kind == "tropical":
        intervals = tape_intervals(result)
        # This is the full positive prime tape; no modular cancellation is discarded.
        value = {
            "newton_hull": [intervals[0][0], intervals[-1][1] - 1],
            "visited_min": intervals[0][0],
            "visited_max": intervals[-1][1] - 1,
            "coefficient_domain": "positive integer prime tape",
        }
    else:
        projection = tape_projection(result, width, sign, modulus)
        value = asdict(projection)
        value["modulus"] = modulus
        if kind == "factor":
            support = projection.support(radix=2, modulus=modulus)
            value.update(
                factor_target=modulus,
                divisor=support.divisor,
                factor=support.proper_factor,
            )
            result.ledger.counters["factor_gcd_queries"] = 1
    return json_integers(
        {
            "family": "antihydra",
            "machine": MACHINE,
            "machine_sha256": MACHINE_SHA256,
            "source_binding": result.source_binding,
            "kind": kind,
            "index_unit": "macro_returns_after_11_step_startup",
            "requested_returns": result.requested,
            "completed_returns": result.returns,
            "halted": result.halted,
            "nonhalting_certified": False,
            "scope": "exact finite source execution; all-time barrier unresolved",
            "value": value,
            "work_counters": dict(result.ledger.counters),
            "peak_nodes": result.ledger.peak_nodes,
            "retained_nodes": result.ledger.nodes,
        }
    )


__all__ = ["json_integers", "observe", "observe_arithmetic", "observe_run"]
