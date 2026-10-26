"""Compare powered and chronological matrix CLI routes on one endpoint."""

from __future__ import annotations

import argparse
import json
from collections.abc import Callable
from statistics import median
from typing import Literal, TypedDict, TypeGuard, cast

from devtools.benchmarks.public_query_comparison import (
    cli_invocation,
    run_jsonl_report,
)
from number_compiler.api.family_registry import CAPABILITIES, family_spec
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.registry_cli import option_argv
from number_compiler.arithmetic.contracts.family_identity import family_id

Mode = Literal["cold", "warm", "bypass"]


class MatrixSample(TypedDict):
    family: str
    seed: int
    selected_term_index: int
    horizon_ticks: int
    mode: Mode
    clock_unit: str
    trace: bool
    trial: int
    seconds: float
    exit_code: int
    status: object
    unavailable_reason: object
    relation_semantics: object
    source_endpoint: object
    pointed_endpoint: object
    endpoint_facts: object
    shared_cache_policy: str
    future_q19_roots_constructed: object
    chronological_future_roots_constructed: object
    trace_present: bool
    packet: dict[str, object]


def _is_object_dict(value: object) -> TypeGuard[dict[str, object]]:
    if not isinstance(value, dict):
        return False
    candidate = cast(dict[object, object], value)
    return all(isinstance(key, str) for key in candidate)


def _is_object_sequence(value: object) -> TypeGuard[tuple[object, ...] | list[object]]:
    return isinstance(value, (tuple, list))


def _sample(
    arguments: list[str], *, fresh: bool, shared_cache: bool = True
) -> tuple[float, dict[str, object], int]:
    elapsed, code, output, error = cli_invocation(
        arguments, fresh=fresh, shared_cache=shared_cache
    )
    try:
        packet: object = json.loads(output)
    except json.JSONDecodeError as error_json:
        raise ValueError(
            f"CLI returned no JSON (exit {code}): {error or output}"
        ) from error_json
    if code not in (0, 3) or not _is_object_dict(packet):
        raise ValueError(f"CLI failed (exit {code}): {error or output}")
    return elapsed, packet, code


def _endpoint_facts(
    family: str, matrix: dict[str, object], trace: bool
) -> tuple[object, object, object]:
    """Select stable public endpoint facts, excluding arena-local root IDs."""
    source_pair = matrix.get("source_pair")
    if family not in {"reverse-add", "2rev10"}:
        # Compare actual semantic fields; retain the complete packet separately
        # so work measurements and refusal evidence are never discarded.
        keys = (
            "endpoint",
            "physical_ticks",
            "normalized_steps",
            "odd_events",
            "units_carry_transfer",
            "forced_tens_carries",
            "pointed_first_center",
            "pointed_last_center",
            "source_certified_physical_ticks",
            "arithmetic_relation",
            "safety_relation",
            "target_source",
            "pointed_endpoint",
            "primality_authority",
            "physical_repeat_certified",
            "temporal_repeat_certified",
            "source_guard_admitted",
        )
        return (
            matrix.get("source"),
            matrix.get("endpoint"),
            {key: matrix[key] for key in keys if key in matrix},
        )
    if family == "reverse-add":
        relation_endpoints = matrix.get("conditional_endpoint_pairs")
        trace_packet = matrix.get("trace")
        pointed_pair = (
            trace_packet.get("target_pair")
            if trace and _is_object_dict(trace_packet)
            else None
        )
        if pointed_pair is not None and (
            not _is_object_sequence(relation_endpoints)
            or pointed_pair not in relation_endpoints
        ):
            raise AssertionError(
                "exact reverse/add trace endpoint is outside its projected relation"
            )
        facts = {
            "source_width": matrix.get("source_width"),
            "target_width": matrix.get("target_width"),
            "source_width_growth": matrix.get("source_width_growth"),
            "conditional_endpoint_pairs": relation_endpoints,
        }
        return source_pair, pointed_pair, facts

    facts = {
        "source_width": matrix.get("source_width"),
        "target_width": matrix.get("target_width"),
        "source_mod99": matrix.get("source_mod99"),
        "target_mod99": matrix.get("target_mod99"),
        "source_mod198": matrix.get("source_mod198"),
        "target_mod198": matrix.get("target_mod198"),
        "possible_target_borders": matrix.get("possible_target_borders"),
        "pointed_target_border": matrix.get("pointed_target_border"),
    }
    return source_pair, matrix.get("pointed_target_pair"), facts


def _semantic_signature(sample: MatrixSample) -> tuple[object, ...]:
    return (
        sample["status"],
        sample["unavailable_reason"],
        sample["relation_semantics"],
        sample["source_endpoint"],
        sample["pointed_endpoint"],
        sample["endpoint_facts"],
    )


def compare_matrix_routes(
    family: str,
    seed: int,
    selected_term_index: int,
    horizons: tuple[int, ...],
    trials: int,
    *,
    trace_max: int = 128,
    save_sample: Callable[[MatrixSample], None] | None = None,
) -> list[MatrixSample]:
    """Retain refusals and timings; do not equate projected with exact rows."""
    spec = family_spec(family_id(family))
    capability = spec.matrix
    if capability is None:
        raise ValueError("family has no source matrix observation")
    if type(seed) is not int or seed < 0:
        raise ValueError("seed must be a nonnegative integer")
    if type(selected_term_index) is not int or selected_term_index < 0:
        raise ValueError("term index must be a nonnegative integer")
    if not horizons or any(
        type(horizon) is not int or horizon <= 0 for horizon in horizons
    ):
        raise ValueError("matrix horizons must be positive exact integers")
    if type(trials) is not int or trials < 1:
        raise ValueError("trial count must be positive")
    if type(trace_max) is not int or trace_max < 1:
        raise ValueError("trace bound must be positive")

    retained: list[MatrixSample] = []
    semantic_results: dict[tuple[int, bool, int], dict[Mode, tuple[object, ...]]] = {}
    source_args = option_argv("seed", seed) if "seed" in spec.parameters else []
    coordinate_args = (
        option_argv(capability.coordinate_option, capability.default_coordinate)
        if capability.default_coordinate is not None
        else []
    )
    for horizon in horizons:
        if horizon > capability.max_steps or horizon % capability.step_multiple:
            raise ValueError("matrix horizon is outside the family admission")
        for trace in (False, True):
            if trace and (
                ObservationId.TEMPORAL_MATRIX_TRACE not in spec.nth_info
                or horizon
                > min(trace_max, capability.max_trace_steps or capability.max_steps)
            ):
                continue
            observation = "temporal.matrix.trace" if trace else "temporal.matrix"
            arguments = [
                family,
                *option_argv("nth", selected_term_index),
                *source_args,
                *option_argv("info", observation),
                *option_argv("temporal_matrix_steps", horizon),
                *coordinate_args,
                *option_argv("no_value", True),
                *option_argv("format", "json"),
            ]
            for mode in ("cold", "warm", "bypass"):
                NumberCompiler.clear_shared_cache()
                if mode == "warm":
                    _sample(arguments, fresh=False)
                for trial in range(trials):
                    if mode == "bypass":
                        NumberCompiler.clear_shared_cache()
                    seconds, packet, exit_code = _sample(
                        arguments, fresh=mode == "cold", shared_cache=mode != "bypass"
                    )
                    info = packet.get("info")
                    if not _is_object_dict(info) or set(info) != {observation}:
                        raise AssertionError("CLI returned an unexpected matrix packet")
                    matrix = info[observation]
                    if not _is_object_dict(matrix):
                        raise TypeError("matrix observation must be a mapping")
                    status = matrix.get("status")
                    if status not in {"available", "unavailable"}:
                        raise AssertionError("matrix has no explicit admission result")
                    if (status == "available") != (exit_code == 0):
                        raise AssertionError(
                            "CLI exit status disagrees with matrix status"
                        )
                    source_endpoint, pointed_endpoint, endpoint_facts = _endpoint_facts(
                        family, matrix, trace
                    )
                    sample: MatrixSample = {
                        "family": family,
                        "seed": seed,
                        "selected_term_index": selected_term_index,
                        "horizon_ticks": horizon,
                        "mode": mode,
                        "clock_unit": capability.clock.value,
                        "trace": trace,
                        "trial": trial,
                        "seconds": seconds,
                        "exit_code": exit_code,
                        "status": status,
                        "unavailable_reason": matrix.get("reason"),
                        "relation_semantics": matrix.get("matrix_semantics"),
                        "source_endpoint": source_endpoint,
                        "pointed_endpoint": pointed_endpoint,
                        "endpoint_facts": endpoint_facts,
                        "shared_cache_policy": (
                            "bypass disables process-cache retrieval and publication; "
                            "request-local memoization remains enabled"
                        ),
                        "future_q19_roots_constructed": matrix.get(
                            "future_q19_roots_constructed"
                        ),
                        "chronological_future_roots_constructed": matrix.get(
                            "chronological_future_roots_constructed"
                        ),
                        "trace_present": isinstance(matrix.get("trace"), dict),
                        "packet": matrix,
                    }
                    semantic_key = (horizon, trace, trial)
                    by_mode = semantic_results.setdefault(semantic_key, {})
                    signature = _semantic_signature(sample)
                    if by_mode and any(
                        previous != signature for previous in by_mode.values()
                    ):
                        raise AssertionError(
                            "cache mode changed the matrix admission or endpoint result"
                        )
                    by_mode[mode] = signature
                    retained.append(sample)
                    if save_sample is not None:
                        save_sample(sample)
    return retained


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--family",
        choices=tuple(name.value for name, spec in CAPABILITIES.items() if spec.matrix),
        required=True,
    )
    parser.add_argument("--seed", type=int, default=196)
    parser.add_argument("--term-index", type=int, required=True)
    parser.add_argument("--horizons", type=int, nargs="+", required=True)
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--trace-max", type=int, default=128)
    options = parser.parse_args()
    rows: list[MatrixSample] = []
    capability = family_spec(family_id(options.family)).matrix
    assert capability is not None

    horizons = cast(tuple[int, ...], tuple(options.horizons))
    configuration: dict[str, object] = {
        "family": cast(str, options.family),
        "seed": cast(int, options.seed),
        "selected_term_index": cast(int, options.term_index),
        "horizons_ticks": horizons,
        "trace_max_ticks": cast(int, options.trace_max),
        "trials": cast(int, options.trials),
        "modes": ("cold", "warm", "bypass"),
        "bypass_policy": (
            "disable process-cache retrieval and publication; request-local "
            "memoization remains enabled"
        ),
        "output_rendering": False,
        "clock_unit": capability.clock.value,
        "reverse_default_relation_scope": "projected source-word overapproximation; not an exact full matrix",
    }

    def run(save_row: Callable[[MatrixSample], None]) -> dict[str, object]:
        def record(sample: MatrixSample) -> None:
            rows.append(sample)
            save_row(sample)

        compare_matrix_routes(
            options.family,
            options.seed,
            options.term_index,
            horizons,
            cast(int, options.trials),
            trace_max=cast(int, options.trace_max),
            save_sample=record,
        )
        summary: list[dict[str, object]] = []
        keys = sorted(
            {(row["horizon_ticks"], row["trace"], row["mode"]) for row in rows}
        )
        for horizon, trace, mode in keys:
            selected = [
                row
                for row in rows
                if (row["horizon_ticks"], row["trace"], row["mode"])
                == (horizon, trace, mode)
            ]
            durations = [row["seconds"] for row in selected]
            summary.append(
                {
                    "horizon_ticks": horizon,
                    "trace": trace,
                    "mode": mode,
                    "trials": len(selected),
                    "available_trials": sum(
                        row["status"] == "available" for row in selected
                    ),
                    "median_seconds": median(durations),
                    "min_seconds": min(durations),
                    "max_seconds": max(durations),
                }
            )
        return {"summary": summary, "sample_count": len(rows)}

    return run_jsonl_report(
        "devtools.benchmarks.temporal_matrix_cli_comparison",
        "comparison.json",
        "powered-and-trace-matrix-cli",
        configuration,
        run,
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
