"""Public finite Antihydra observations; all indices count macro returns."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict
from typing import Any

from number_compiler.api.json_output import json_integers
from number_compiler.resources.metric_keys import api as _api_metrics
from number_compiler.sequences.antihydra.machine import MACHINE, MACHINE_SHA256
from number_compiler.sequences.antihydra.mahler import tangent
from number_compiler.sequences.antihydra.observers import (
    SpaceTimeProjection,
    tape_projection,
)
from number_compiler.sequences.antihydra.runtime import ArithmeticResult, Run
from number_compiler.sequences.antihydra.support import (
    directional_hasse,
    tape_hasse,
    tape_intervals,
)


def observe_arithmetic(
    result: ArithmeticResult,
    *,
    kind: str,
    precision: int = 8,
    _include_metrics: bool = True,
) -> dict[str, Any]:
    """Demand a total arithmetic observation without requesting physical execution."""
    return observe_arithmetic_many(
        result,
        kinds=(kind,),
        precision=precision,
        _include_metrics=_include_metrics,
    )[kind]


def observe_arithmetic_many(
    result: ArithmeticResult,
    *,
    kinds: tuple[str, ...],
    precision: int = 8,
    _include_metrics: bool = True,
) -> dict[str, dict[str, Any]]:
    """Evaluate the shared tangent once for the explicitly demanded observers."""
    if (
        type(kinds) is not tuple
        or not 1 <= len(kinds) <= 2
        or any(type(kind) is not str for kind in kinds)
    ):
        raise ValueError("unsupported arithmetic Antihydra observation")
    requested = kinds if len(kinds) == 1 or kinds[0] != kinds[1] else kinds[:1]
    if any(kind not in {"mahler", "hensel"} for kind in requested):
        raise ValueError("unsupported arithmetic Antihydra observation")
    # ``tangent`` authenticates the source at its public demand boundary.
    # Deep copies below are required because ``json_integers`` lowers in place.
    shared = tangent(result, precision)
    action: dict[str, object] | None = None
    if "mahler" in requested:
        from number_compiler.sequences.antihydra.mahler_action import associated_action

        action = associated_action(result, include_radix_ports=True)
    packets: dict[str, dict[str, Any]] = {}
    for index, kind in enumerate(requested):
        value = deepcopy(shared) if index + 1 < len(requested) else shared
        if kind == "mahler":
            if action is None:
                raise ArithmeticError("Mahler action demand was not evaluated")
            value["associated_action"] = action
        packets[kind] = json_integers(
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
                **(
                    {
                        "work_counters": dict(result.ledger.counters),
                        "peak_nodes": result.ledger.peak_nodes,
                        "retained_nodes": result.ledger.nodes,
                    }
                    if _include_metrics
                    else {}
                ),
            }
        )
    return packets


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
    _include_metrics: bool = True,
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

            value["associated_action"] = associated_action(
                result, include_radix_ports=True
            )
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
        result.ledger.counters[_api_metrics.TAPE_HASSE_TERMS] = (width + 1) * len(
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
            result.ledger.counters[_api_metrics.FACTOR_GCD_QUERIES] = 1
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
            **(
                {
                    "work_counters": dict(result.ledger.counters),
                    "peak_nodes": result.ledger.peak_nodes,
                    "retained_nodes": result.ledger.nodes,
                }
                if _include_metrics
                else {}
            ),
        }
    )


__all__ = ["observe_arithmetic", "observe_run"]
