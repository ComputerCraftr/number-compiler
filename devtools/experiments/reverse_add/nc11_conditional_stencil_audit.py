"""Check source-owned reverse/add moments and conditional stencil readouts.

Run from the repository root with ``PYTHONPATH=src python
devtools/experiments/reverse_add/nc11_conditional_stencil_audit.py``.
This reports a source-owned modular endpoint and a bounded stencil; production
execution remains owned by the term's TileScheduler/Q19 source publisher.
"""

from __future__ import annotations

import json
from time import perf_counter

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def reverse10(value: int) -> int:
    return int(str(value)[::-1])


def run() -> dict[str, object]:
    term = ReverseAddPoweredTerm(196, 4096)
    start = perf_counter()
    try:
        moment = term.temporal_moments(modulus=1009)
        width = term.width()
        assert (moment.U, moment.V) == (10, 904)
        assert moment.apply(196, 691) == (182, 701)
        assert width == 1712
        # This is a non-materializing modular endpoint demand, not a
        # complete-root temporal closure proof.
        modular_seconds = perf_counter() - start
        counters = {
            name: value
            for name, value in term.resource_ledger.counters.items()
            if name.startswith(
                (
                    "reverse_q19_numeric_port_",
                    "reverse_q19_temporal_stencil_",
                )
            )
            or name == "recursive_output_stream_emitted_digits"
        }
        assert counters.get("recursive_output_stream_emitted_digits", 0) == 0
    finally:
        if term._workspace is not None:
            term._workspace.dispose()
    assert term.resource_ledger.entries == term.resource_ledger.nodes == 0

    observed_term = ReverseAddPoweredTerm(196, 97)
    stencil_start = perf_counter()
    try:
        endpoint = observed_term.temporal_matrix(max_bits=16384)
        bank = observed_term.temporal_stencil(max_bits=16384, max_digits=8192)
        assert bank.masks_partition()
        assert bank.width == endpoint.target_width
        next_value = endpoint.target + reverse10(endpoint.target)
        next_sign = (reverse10(next_value) > reverse10(endpoint.target)) - (
            reverse10(next_value) < reverse10(endpoint.target)
        )
        assert bank.future_innovation_sign == next_sign
        stencil_counters = {
            name: value
            for name, value in observed_term.resource_ledger.counters.items()
            if name.startswith("reverse_q19_temporal_stencil_")
        }
    finally:
        if observed_term._workspace is not None:
            observed_term._workspace.dispose()
    assert (
        observed_term.resource_ledger.entries
        == observed_term.resource_ledger.nodes
        == 0
    )
    return {
        "scope": "endpoint observations and source-owned modular moments",
        "seed": 196,
        "depth": 4096,
        "width": width,
        "modulus": 1009,
        "modular_moment": {"duration": moment.duration, "U": moment.U, "V": moment.V},
        "modular_seconds": round(modular_seconds, 3),
        "stencil_width_at_97": bank.width,
        "stencil_seconds": round(perf_counter() - stencil_start, 3),
        "numeric_port_counters": counters,
        "stencil_counters": stencil_counters,
        "complete_root_temporal_closure": False,
    }


def main() -> None:
    """Emit the bounded moment and stencil report as reproducible JSON."""
    print(json.dumps(run(), indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
