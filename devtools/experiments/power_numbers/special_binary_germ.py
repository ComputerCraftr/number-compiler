"""Factor-backed audit for the binary special-germ support architecture.

Nothing in this module is a production selector.  Factor truth is used only to
construct the support defect that a future candidate-derived observer must
produce.  The audit checks three independent claims:

1. dyadic transport for an r-level chunk is binary-powered in O(log r)
   semantic compositions;
2. one endpoint support defect is sufficient for prime/composite classification;
3. composing level packets by gcd gives the same support as the endpoint packet,
   including the F5/M11 even-packet adversaries where scalar characters cancel.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import prod
from typing import TYPE_CHECKING

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    AmbientCapacityTruth,
    ambient_capacity_truth,
)
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkResult,
    SpecialFrobeniusDefectPacket,
)
from number_compiler.sequences.power_numbers.germ import (
    SpecialGermPlan,
    build_special_germ_plan,
    compose_support_packets,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.frobenius_chunk import (
        SpecialFrobeniusChunkSpec,
    )


@dataclass(frozen=True, slots=True)
class SpecialBinaryGermAudit:
    family: str
    parameter: int
    plan: SpecialGermPlan
    truth: AmbientCapacityTruth
    endpoint_defect: int
    endpoint_result: SpecialFrobeniusChunkResult
    composed_result: SpecialFrobeniusChunkResult
    factor_enumeration: int
    source_support_observations: int

    @property
    def exact(self) -> bool:
        return (
            self.endpoint_result.status == self.composed_result.status
            and self.endpoint_result.gcd_packet == self.composed_result.gcd_packet
        )

    @property
    def binary_transport_is_logarithmic(self) -> bool:
        span = self.plan.spec.span
        return self.plan.binary_compositions <= 2 * max(1, span.bit_length())


def _truth_support_defect(truth: AmbientCapacityTruth, level: int) -> int:
    """Return the factor-backed zero/unit support generator at one depth.

    The product contains every prime-factor occurrence whose local lift depth
    reaches ``level``.  Therefore it is zero modulo a passing prime-power
    component and a unit modulo a failing one.  This is deliberately audit-only.
    """
    level = int(level)
    if level < 1:
        raise ValueError(level)
    passing = [
        q
        for q, depth in zip(truth.local_factors, truth.local_lift_depths, strict=True)
        if depth >= level
    ]
    return prod(passing, start=1) % truth.modulus


def _truth_packet(
    truth: AmbientCapacityTruth,
    spec: SpecialFrobeniusChunkSpec,
) -> SpecialFrobeniusDefectPacket:
    return SpecialFrobeniusDefectPacket(
        spec,
        truth.modulus,
        _truth_support_defect(truth, spec.end_level),
        "factor-truth-support-germ",
        candidate_derived=False,
    )


def special_binary_germ_truth_audit(
    family: str, parameter: int
) -> SpecialBinaryGermAudit:
    family = str(family)
    parameter = int(parameter)
    threshold = terminal_threshold_spec(family, parameter)
    if threshold.prime_decision_level <= 0:
        raise ValueError((family, parameter, "no-unresolved-germ-chunk"))
    spec = prime_decision_chunk_spec(threshold)
    plan = build_special_germ_plan(spec)
    truth = ambient_capacity_truth(family, parameter)

    endpoint = _truth_packet(truth, spec)
    endpoint_result = endpoint.classify()

    packet = None
    for level in range(spec.start_level, spec.end_level + 1):
        level_spec = type(spec)(
            spec.family,
            spec.parameter,
            level,
            1,
            spec.baseline_local_v2,
            spec.modulus_bits,
        )
        current = _truth_packet(truth, level_spec)
        packet = current if packet is None else compose_support_packets(packet, current)
    if packet is None:
        raise AssertionError(spec)
    composed_result = packet.classify()

    return SpecialBinaryGermAudit(
        family,
        parameter,
        plan,
        truth,
        endpoint.defect,
        endpoint_result,
        composed_result,
        len(truth.local_factors),
        1,
    )


__all__ = ["SpecialBinaryGermAudit", "special_binary_germ_truth_audit"]
