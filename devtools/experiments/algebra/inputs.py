"""Shared argument validation for algebraic research audits."""

from __future__ import annotations

from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    TransverseJetSingularityAudit,
    first_special_transverse_singularity,
)


def bounded_jet_spec(
    family: str, parameter: int, start: int, span: int
) -> tuple[SpecialJetProgressionSpec, int, int]:
    """Build a progression spec and validate an in-range positive interval."""
    spec = SpecialJetProgressionSpec.build(family, parameter)
    start, span = int(start), int(span)
    if start < 1 or span < 1 or start + span - 1 > spec.max_slot:
        raise ValueError((start, span, spec.max_slot))
    return spec, start, span


def required_singularity(
    family: str, parameter: int
) -> tuple[SpecialJetProgressionSpec, TransverseJetSingularityAudit]:
    """Return a progression and its first proper denominator singularity."""
    singular = first_special_transverse_singularity(family, parameter)
    if (
        not singular.found
        or singular.first_slot is None
        or singular.denominator_gcd <= 1
    ):
        raise ValueError("bounded composite singular control required")
    return SpecialJetProgressionSpec.build(family, parameter), singular
