"""Demanded finite Collatz fields from the query's already issued run action."""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.api.json_output import json_value
from number_compiler.api.output_schema import CollatzDiagonalPacket
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def diagonal_packet(
    term: PoweredCollatzTerm, *, max_width: int
) -> CollatzDiagonalPacket:
    """Publish bounded rows without replaying temporal actions or parity choices."""
    scratch = RunArithmeticWorkspace.for_ledger(
        term.resource_ledger, "collatz_diagonal"
    )
    with scratch.scope():
        seam = term.diagonal_carry_seam()
        required_width = max(seam.required_field_width, seam.required_macro_width)
        width = min(required_width, max_width)
        field = seam.field(
            width, reserve_bits=scratch.require_bits, max_width=max_width
        )
        macro_carries = seam.macro_carries(
            width, reserve_bits=scratch.require_bits, max_width=max_width
        )
        # This is an aggregate of numeric ledgers, not the historical carry sum.
        aggregate_bound = seam.source.bit_length() + 2 * seam.physical_ticks + 8
        weighted = (
            seam.weighted_laurent_defect(
                moving_cut=seam.normalized_steps,
                reserve_bits=scratch.require_bits,
                max_width=max_width,
            )
            if max(aggregate_bound, seam.normalized_steps) <= max_width
            else None
        )
        return {
            "family": "collatz",
            "kind": "temporal.diagonal-carry",
            "source": seam.source,
            "normalized_endpoint": seam.normalized_endpoint,
            "physical_endpoint": seam.physical_endpoint,
            "normalized_steps": seam.normalized_steps,
            "physical_ticks": seam.physical_ticks,
            "phase": seam.phase,
            "clock_unit": "physical_iterations",
            "moving_cut": "binary-normalized",
            "field_width": width,
            "complete": width >= required_width,
            "field": json_value(asdict(field)),
            "macro_affine_carries_lsb": macro_carries,
            "macro_laurent_carry_lsb": seam.macro_laurent_defect_from_carries(
                macro_carries, max_width=max_width
            ),
            "macro_laurent_factor": "z-2",
            "weighted_laurent_complete": weighted is not None,
            "weighted_laurent_aggregate": (
                None if weighted is None else json_value(asdict(weighted))
            ),
            "all_time_claim": False,
        }
