"""Public finite Antihydra observations; all indices count macro returns."""

from __future__ import annotations

from collections.abc import Mapping
from copy import deepcopy
from dataclasses import asdict
from enum import StrEnum
from typing import TYPE_CHECKING, Literal, overload

from number_compiler.api.json_output import (
    is_string_object_mapping,
    json_integers,
    json_value,
)
from number_compiler.api.output_schema import (
    AntihydraArithmeticPacket,
    AntihydraMahlerTangentPacket,
    AntihydraRunAvailablePacket,
    AntihydraRunMahlerPacket,
    AntihydraRunUnavailablePacket,
    AntihydraSourceFields,
    AntihydraTangentPacket,
    JsonInteger,
    JsonValue,
    MahlerActionPacket,
    RationalValuePacket,
)
from number_compiler.resources.metric_keys import api as _api_metrics
from number_compiler.sequences.antihydra.machine import MACHINE, MACHINE_SHA256

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.runtime import ArithmeticResult, Run


def tangent(result: Run | ArithmeticResult, precision: int) -> dict[str, object]:
    """Load the arithmetic observer only for an explicit tangent demand."""
    from number_compiler.sequences.antihydra.mahler import tangent as observe_tangent

    return observe_tangent(result, precision)


class AntihydraArithmeticKind(StrEnum):
    MAHLER = "mahler"
    HENSEL = "hensel"


class AntihydraRunKind(StrEnum):
    CLOCK = "clock"
    PHYSICAL_CLOCK = "physical-clock"
    TAPE = "tape"
    TWISTED = "twisted"
    HASSE = "hasse"
    TROPICAL = "tropical"
    FACTOR = "factor"
    SPACETIME = "spacetime"
    MAHLER = "mahler"
    HENSEL = "hensel"
    MODULAR = "modular"


def observe_arithmetic(
    result: ArithmeticResult,
    *,
    kind: AntihydraArithmeticKind,
    precision: int = 8,
    _include_metrics: bool = True,
) -> AntihydraArithmeticPacket:
    """Demand a total arithmetic observation without requesting physical execution."""
    return observe_arithmetic_many(
        result,
        kinds=(kind,),
        precision=precision,
        _include_metrics=_include_metrics,
    )[kind.value]


def observe_arithmetic_many(
    result: ArithmeticResult,
    *,
    kinds: tuple[AntihydraArithmeticKind, ...],
    precision: int = 8,
    _include_metrics: bool = True,
) -> dict[str, AntihydraArithmeticPacket]:
    """Evaluate the shared tangent once for the explicitly demanded observers."""
    if (
        type(kinds) is not tuple
        or not 1 <= len(kinds) <= 2
        or any(type(kind) is not AntihydraArithmeticKind for kind in kinds)
    ):
        raise ValueError("unsupported arithmetic Antihydra observation")
    requested = kinds if len(kinds) == 1 or kinds[0] != kinds[1] else kinds[:1]
    # ``tangent`` authenticates the source at its public demand boundary.
    # Deep copies below let the two demanded observers own independent packets.
    shared = tangent(result, precision)
    action: dict[str, object] | None = None
    if AntihydraArithmeticKind.MAHLER in requested:
        from number_compiler.sequences.antihydra.mahler_action import associated_action

        action = associated_action(result, include_radix_ports=True)
    packets: dict[str, AntihydraArithmeticPacket] = {}
    for index, kind in enumerate(requested):
        value = deepcopy(shared) if index + 1 < len(requested) else shared
        if kind is AntihydraArithmeticKind.MAHLER:
            if action is None:
                raise ArithmeticError("Mahler action demand was not evaluated")
            value["associated_action"] = action
        packets[kind.value] = _arithmetic_packet(
            {
                "family": "antihydra",
                "machine": MACHINE,
                "machine_sha256": MACHINE_SHA256,
                "source_binding": result.source_binding,
                "kind": kind.value,
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


@overload
def observe_run(
    result: Run,
    *,
    kind: Literal[AntihydraRunKind.MAHLER],
    modulus: int = 257,
    width: int = 2,
    sign: int = -1,
    precision: int = 8,
    time_width: int = 2,
    time_sign: int = 1,
    max_observer_terms: int = 1_000_000,
    _include_metrics: bool = True,
) -> AntihydraRunMahlerPacket: ...


@overload
def observe_run(
    result: Run,
    *,
    kind: AntihydraRunKind,
    modulus: int = 257,
    width: int = 2,
    sign: int = -1,
    precision: int = 8,
    time_width: int = 2,
    time_sign: int = 1,
    max_observer_terms: int = 1_000_000,
    _include_metrics: bool = True,
) -> Mapping[str, object]: ...


def observe_run(
    result: Run,
    *,
    kind: AntihydraRunKind,
    modulus: int = 257,
    width: int = 2,
    sign: int = -1,
    precision: int = 8,
    time_width: int = 2,
    time_sign: int = 1,
    max_observer_terms: int = 1_000_000,
    _include_metrics: bool = True,
) -> Mapping[str, object]:
    """Demand one projection from an existing authenticated physical owner."""
    if type(kind) is not AntihydraRunKind:
        raise ValueError("unsupported Antihydra observation")
    result.require_source()
    if result.halted:
        unavailable: dict[str, object] = {
            "family": "antihydra",
            "kind": kind.value,
            "status": "unavailable",
            "reason": "requested returning section reaches or passes the halting boundary",
            "requested_returns": result.requested,
            "halt_boundary": result.returns,
            "halted": True,
            "physical_ticks_at_halt": result.physical_ticks,
            "nonhalting_certified": False,
        }
        if kind is AntihydraRunKind.MAHLER:
            return _unavailable_mahler_packet(unavailable)
        return json_integers(unavailable)
    value: object
    if kind in {AntihydraRunKind.CLOCK, AntihydraRunKind.PHYSICAL_CLOCK}:
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
    elif kind in {AntihydraRunKind.MAHLER, AntihydraRunKind.HENSEL}:
        tangent_value = tangent(result, precision)
        if kind is AntihydraRunKind.MAHLER:
            from number_compiler.sequences.antihydra.mahler_action import (
                associated_action,
            )

            tangent_value["associated_action"] = associated_action(
                result, include_radix_ports=True
            )
        value = tangent_value
    elif kind is AntihydraRunKind.MODULAR:
        value = {
            "modulus": modulus,
            "h": result.h % modulus,
            "left": result.left % modulus,
            "right": result.right % modulus,
            "physical_ticks": result.physical_ticks % modulus,
        }
    elif kind is AntihydraRunKind.SPACETIME:
        from number_compiler.sequences.antihydra.observers import SpaceTimeProjection

        value = SpaceTimeProjection(
            result, width, time_width, sign, time_sign, modulus, max_observer_terms
        ).evaluate()
    elif kind is AntihydraRunKind.HASSE:
        from number_compiler.sequences.antihydra.support import (
            directional_hasse,
            tape_hasse,
            tape_intervals,
        )

        value = {
            "center": 1,
            "modulus": modulus,
            "coefficients": tape_hasse(result, width, modulus),
            "directional_events": directional_hasse(result, width, modulus),
        }
        result.ledger.counters[_api_metrics.TAPE_HASSE_TERMS] = (width + 1) * len(
            tape_intervals(result)
        )
    elif kind is AntihydraRunKind.TROPICAL:
        from number_compiler.sequences.antihydra.support import tape_intervals

        intervals = tape_intervals(result)
        # This is the full positive prime tape; no modular cancellation is discarded.
        value = {
            "newton_hull": [intervals[0][0], intervals[-1][1] - 1],
            "visited_min": intervals[0][0],
            "visited_max": intervals[-1][1] - 1,
            "coefficient_domain": "positive integer prime tape",
        }
    else:
        from number_compiler.sequences.antihydra.observers import tape_projection

        projection = tape_projection(result, width, sign, modulus)
        projection_value = asdict(projection)
        projection_value["modulus"] = modulus
        if kind is AntihydraRunKind.FACTOR:
            support = projection.support(radix=2, modulus=modulus)
            projection_value.update(
                factor_target=modulus,
                divisor=support.divisor,
                factor=support.proper_factor,
            )
            result.ledger.counters[_api_metrics.FACTOR_GCD_QUERIES] = 1
        value = projection_value
    packet: dict[str, object] = {
        "family": "antihydra",
        "machine": MACHINE,
        "machine_sha256": MACHINE_SHA256,
        "source_binding": result.source_binding,
        "kind": kind.value,
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
    if kind is AntihydraRunKind.MAHLER:
        return _available_mahler_packet(packet)
    return json_integers(packet)


def _required(mapping: Mapping[str, object], key: str) -> object:
    if key not in mapping:
        raise ValueError(f"observation packet is missing {key!r}")
    return mapping[key]


def _json_integer(value: object) -> JsonInteger:
    if type(value) is not int:
        raise TypeError("observation integer fields require exact integers")
    if value.bit_length() > 12000:
        return {"encoding": "hex", "value": hex(value), "bits": value.bit_length()}
    return value


def _source_fields(value: Mapping[str, object]) -> AntihydraSourceFields:
    """Validate shared source and reporting fields once per packet boundary."""
    if _required_string(value, "family") != "antihydra":
        raise ValueError("observation packet has a foreign family")
    fields: AntihydraSourceFields = {
        "family": "antihydra",
        "machine": _required_string(value, "machine"),
        "machine_sha256": _required_string(value, "machine_sha256"),
        "source_binding": _required_string(value, "source_binding"),
        "kind": _required_string(value, "kind"),
        "index_unit": _required_string(value, "index_unit"),
        "requested_returns": _json_integer(_required(value, "requested_returns")),
        "completed_returns": _json_integer(_required(value, "completed_returns")),
        "scope": _required_string(value, "scope"),
    }
    if "work_counters" in value:
        fields["work_counters"] = _json_object(value["work_counters"])
    if "peak_nodes" in value:
        fields["peak_nodes"] = _json_integer(value["peak_nodes"])
    if "retained_nodes" in value:
        fields["retained_nodes"] = _json_integer(value["retained_nodes"])
    return fields


def _rational_packet(value: object) -> RationalValuePacket:
    if not is_string_object_mapping(value):
        raise TypeError("Mahler rational packet must be an object")
    return {
        "numerator": _json_integer(_required(value, "numerator")),
        "denominator": _json_integer(_required(value, "denominator")),
    }


def _mahler_action_packet(value: object) -> MahlerActionPacket:
    if not is_string_object_mapping(value):
        raise TypeError("Mahler action packet must be an object")
    packet: MahlerActionPacket = {
        "source_binding": _required_string(value, "source_binding"),
        "extent": _json_integer(_required(value, "extent")),
        "homogeneous_growth": json_value(_required(value, "homogeneous_growth")),
        "radial_sturmian": json_value(_required(value, "radial_sturmian")),
        "bit_convention": _required_string(value, "bit_convention"),
        "scale": _rational_packet(_required(value, "scale")),
        "offset": _rational_packet(_required(value, "offset")),
        "cap": _optional_rational_packet(_required(value, "cap")),
        "initial_margin": _required_string(value, "initial_margin"),
        "pulled_threshold": json_value(_required(value, "pulled_threshold")),
        "first_failure": _optional_json_integer(_required(value, "first_failure")),
        "first_failure_index_unit": _required_string(value, "first_failure_index_unit"),
        "predicate": _required_string(value, "predicate"),
        "temporal_run_residual": json_value(_required(value, "temporal_run_residual")),
        "root_shell": json_value(_required(value, "root_shell")),
        "all_time_claim": _required_bool(value, "all_time_claim"),
    }
    # Keep the TypedDict boundary statically named so each packet field keeps
    # its precise wire type.
    if "source_bound_radix6_difference" in value:
        packet["source_bound_radix6_difference"] = json_value(
            value["source_bound_radix6_difference"]
        )
    if "source_bound_joint_successor" in value:
        packet["source_bound_joint_successor"] = json_value(
            value["source_bound_joint_successor"]
        )
    if "source_bound_odd_to_odd" in value:
        packet["source_bound_odd_to_odd"] = json_value(value["source_bound_odd_to_odd"])
    if "source_cylinder" in value:
        packet["source_cylinder"] = json_value(value["source_cylinder"])
    if "radial_affine_arithmetic" in value:
        packet["radial_affine_arithmetic"] = json_value(
            value["radial_affine_arithmetic"]
        )
    return packet


def _tangent_packet(value: object) -> AntihydraTangentPacket:
    if not is_string_object_mapping(value):
        raise TypeError("Antihydra tangent packet must be an object")
    packet: AntihydraTangentPacket = {
        "source": _json_integer(_required(value, "source")),
        "timestamp_macro_returns": _json_integer(
            _required(value, "timestamp_macro_returns")
        ),
        "consumed_centered_odd_events": _json_integer(
            _required(value, "consumed_centered_odd_events")
        ),
        "slack": _json_integer(_required(value, "slack")),
        "at_odd_seam": _required_bool(value, "at_odd_seam"),
        "all_time_barrier_proved": _required_bool(value, "all_time_barrier_proved"),
        "moving_cylinder": json_value(_required(value, "moving_cylinder")),
    }
    if "even_run_depth" in value:
        packet["even_run_depth"] = _json_integer(value["even_run_depth"])
    if "precision" in value:
        packet["precision"] = _json_integer(value["precision"])
    if "normalized_residue" in value:
        packet["normalized_residue"] = _json_integer(value["normalized_residue"])
    if "clock_root" in value:
        packet["clock_root"] = _json_integer(value["clock_root"])
    if "matched_bits" in value:
        packet["matched_bits"] = _json_integer(value["matched_bits"])
    if "matched_radix64_cells" in value:
        packet["matched_radix64_cells"] = _json_integer(value["matched_radix64_cells"])
    if "gap" in value:
        packet["gap"] = _json_integer(value["gap"])
    if "child_precision" in value:
        packet["child_precision"] = _json_integer(value["child_precision"])
    if "child_normalized_residue" in value:
        packet["child_normalized_residue"] = _json_integer(
            value["child_normalized_residue"]
        )
    if "required_next_precision" in value:
        packet["required_next_precision"] = _json_integer(
            value["required_next_precision"]
        )
    if "resolved" in value:
        resolved = value["resolved"]
        if type(resolved) is not bool:
            raise TypeError("tangent resolution flag must be Boolean")
        packet["resolved"] = resolved
    if "associated_action" in value:
        packet["associated_action"] = _mahler_action_packet(value["associated_action"])
    return packet


def _arithmetic_packet(value: Mapping[str, object]) -> AntihydraArithmeticPacket:
    certified = _required(value, "nonhalting_certified")
    if certified is not False:
        raise ValueError("finite arithmetic packet cannot certify nonhalting")
    packet: AntihydraArithmeticPacket = {
        **_source_fields(value),
        "guarded_physical_status": _required_string(value, "guarded_physical_status"),
        "ledger_first_failure_index": _optional_json_integer(
            _required(value, "ledger_first_failure_index")
        ),
        "nonhalting_certified": False,
        "value": _tangent_packet(_required(value, "value")),
    }
    return packet


def _available_mahler_packet(
    value: Mapping[str, object],
) -> AntihydraRunAvailablePacket:
    packet: AntihydraRunAvailablePacket = {
        **_source_fields(value),
        "status": "available",
        "halted": False,
        "nonhalting_certified": False,
        "value": _mahler_tangent_packet(_required(value, "value")),
    }
    return packet


def _mahler_tangent_packet(value: object) -> AntihydraMahlerTangentPacket:
    packet = _tangent_packet(value)
    action = packet.get("associated_action")
    if action is None:
        raise ValueError("Mahler tangent packet is missing its exact action")
    result: AntihydraMahlerTangentPacket = {
        "associated_action": action,
        "source": packet["source"],
        "timestamp_macro_returns": packet["timestamp_macro_returns"],
        "consumed_centered_odd_events": packet["consumed_centered_odd_events"],
        "slack": packet["slack"],
        "at_odd_seam": packet["at_odd_seam"],
        "all_time_barrier_proved": packet["all_time_barrier_proved"],
        "moving_cylinder": packet["moving_cylinder"],
    }
    if "even_run_depth" in packet:
        result["even_run_depth"] = packet["even_run_depth"]
    if "precision" in packet:
        result["precision"] = packet["precision"]
    if "normalized_residue" in packet:
        result["normalized_residue"] = packet["normalized_residue"]
    if "clock_root" in packet:
        result["clock_root"] = packet["clock_root"]
    if "matched_bits" in packet:
        result["matched_bits"] = packet["matched_bits"]
    if "matched_radix64_cells" in packet:
        result["matched_radix64_cells"] = packet["matched_radix64_cells"]
    if "gap" in packet:
        result["gap"] = packet["gap"]
    if "child_precision" in packet:
        result["child_precision"] = packet["child_precision"]
    if "child_normalized_residue" in packet:
        result["child_normalized_residue"] = packet["child_normalized_residue"]
    if "required_next_precision" in packet:
        result["required_next_precision"] = packet["required_next_precision"]
    if "resolved" in packet:
        result["resolved"] = packet["resolved"]
    return result


def _unavailable_mahler_packet(
    value: Mapping[str, object],
) -> AntihydraRunUnavailablePacket:
    if _required_string(value, "family") != "antihydra":
        raise ValueError("unavailable packet has a foreign family")
    if _required(value, "halted") is not True:
        raise ValueError("unavailable packet must name its halt boundary")
    if _required(value, "nonhalting_certified") is not False:
        raise ValueError("halted packet cannot certify nonhalting")
    return {
        "status": "unavailable",
        "family": "antihydra",
        "kind": _required_string(value, "kind"),
        "reason": _required_string(value, "reason"),
        "requested_returns": _json_integer(_required(value, "requested_returns")),
        "halt_boundary": _json_integer(_required(value, "halt_boundary")),
        "halted": True,
        "physical_ticks_at_halt": _json_integer(
            _required(value, "physical_ticks_at_halt")
        ),
        "nonhalting_certified": False,
    }


def _optional_rational_packet(value: object) -> RationalValuePacket | None:
    return None if value is None else _rational_packet(value)


def _optional_json_integer(value: object) -> JsonInteger | None:
    return None if value is None else _json_integer(value)


def _required_string(mapping: Mapping[str, object], key: str) -> str:
    value = _required(mapping, key)
    if type(value) is not str:
        raise TypeError(f"observation field {key!r} must be a string")
    return value


def _required_bool(mapping: Mapping[str, object], key: str) -> bool:
    value = _required(mapping, key)
    if type(value) is not bool:
        raise TypeError(f"observation field {key!r} must be Boolean")
    return value


def _json_object(value: object) -> dict[str, JsonValue]:
    if not is_string_object_mapping(value):
        raise TypeError("observation counters must be an object")
    result: dict[str, JsonValue] = {}
    for key, item in value.items():
        if type(key) is not str:
            raise TypeError("observation counters require string names")
        result[key] = json_value(item)
    return result


__all__ = [
    "AntihydraArithmeticKind",
    "AntihydraRunKind",
    "observe_arithmetic",
    "observe_run",
]
