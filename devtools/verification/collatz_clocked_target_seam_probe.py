"""Bounded exact endpoint audit for the accelerated Collatz target seam."""

from __future__ import annotations

import json

from devtools.verification.endpoint_seam_audit import (
    BoundedEndpointPowerArena,
    audit_endpoint_frontier,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


def _step(value: int) -> int:
    return accelerated_odd_collatz(value).target


def build_report(*, bits: int = 16) -> dict[str, object]:
    if type(bits) is not int or not 2 <= bits <= 16:
        raise ValueError("Collatz seam audit width must lie in 2..16")
    report = audit_endpoint_frontier(
        range(1, 1 << bits, 2),
        _step,
        horizons=(1, 2, 4, 8, 16),
        spatial_size=lambda value: max(1, (value.bit_length() + 5) // 6),
    )
    arena = BoundedEndpointPowerArena(_step)
    cold = arena.power(27, 4)
    cold_primitives = arena.primitive_successors
    warm = arena.power(27, 4)
    report.update(
        {
            "clock_kind": "exact accelerated event tick",
            "clock_is_physical_tick": False,
            "exact_target_payload_retained": True,
            "transition_provenance_retained": False,
            "warm_power_target": warm,
            "warm_power_matches_cold": warm == cold,
            "cold_power_primitive_successors": cold_primitives,
            "warm_power_added_primitive_successors": (
                arena.primitive_successors - cold_primitives
            ),
            "power_memo_hits": arena.memo_hits,
            "power_endpoint_intern_hits": arena.endpoint_intern_hits,
            "power_retained_results": arena.retained_results,
        }
    )
    return report


def main() -> None:
    print(json.dumps(build_report(), indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
