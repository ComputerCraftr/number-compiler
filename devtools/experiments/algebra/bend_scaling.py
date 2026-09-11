"""Bend scaling with one canonical implementation owner."""

from __future__ import annotations

from dataclasses import dataclass
from math import log2


@dataclass(frozen=True, slots=True)
class BendScalingRow:
    span: int
    baby_width: int
    full_blocks: int
    charged_scalar_multiplications: int
    charged_total_ring_ops: int
    direct_linear_multiplications: int
    state_entries: int
    scalar_multiplications_beat_linear: bool
    total_ring_ops_beat_linear: bool
    exact: bool


@dataclass(frozen=True, slots=True)
class BendScalingAudit:
    family: str
    parameter: int
    rows: tuple[BendScalingRow, ...]
    all_exact: bool
    all_state_sublinear_on_controls: bool
    measured_total_ring_ops_beat_linear: bool
    measured_scalar_multiplications_beat_linear: bool
    theoretical_karatsuba_exponent_in_span: float


def bend_scaling_audit(
    family: str,
    parameter: int,
    spans: tuple[int, ...],
    *,
    start: int = 1,
) -> BendScalingAudit:
    from devtools.experiments.algebra.residue_refined_bend import (
        fast_multipoint_bend_audit,
    )

    rows: list[BendScalingRow] = []
    for span in spans:
        audit = fast_multipoint_bend_audit(family, parameter, start=start, span=span)
        rows.append(
            BendScalingRow(
                span,
                audit.baby_width,
                audit.full_blocks,
                audit.charged_scalar_multiplications,
                audit.charged_total_ring_ops,
                audit.direct_linear_multiplications,
                audit.structural_state_entries,
                audit.scalar_multiplication_count_beats_linear_on_control,
                audit.total_ring_ops_beat_linear_on_control,
                audit.exact,
            )
        )
    exponent = log2(3.0) / 2.0
    return BendScalingAudit(
        family,
        int(parameter),
        tuple(rows),
        all(row.exact for row in rows),
        all(row.state_entries < row.span for row in rows if row.span >= 256),
        any(row.total_ring_ops_beat_linear for row in rows),
        any(row.scalar_multiplications_beat_linear for row in rows),
        exponent,
    )
