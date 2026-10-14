"""Read-only typed cache measurements; retrieval is distinct from application."""

from collections.abc import Mapping
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class TemporalReuseLane:
    """One owner's requests, reuse and publications in their original units."""

    requests: int | None = None
    attempts: int | None = None
    # Exact and transported hits are producer-classified disjoint outcomes.
    exact_hits: int | None = None
    transported_hits: int | None = None
    local_hits: int | None = None
    process_hits: int | None = None
    applied_hits: int | None = None
    applied_parent_hits: int | None = None
    rejected_fit: int | None = None
    admission_rejections: int | None = None
    key_operand_bits: int | None = None
    # Some older owner lanes have only a literal hit counter. Keep it separate
    # until that producer classifies the returned value.
    unclassified_hits: int | None = None
    misses: int | None = None
    publications: int | None = None
    bypasses: int | None = None
    disabled_bypasses: int | None = None
    policy_bypasses: int | None = None
    capacity_bypasses: int | None = None
    evictions: int | None = None


@dataclass(frozen=True, slots=True)
class CompleteActionReuse:
    """Complete mixed-action admission and actual consumer application counts."""

    lookups: int | None = None
    retrieved: int | None = None
    admitted: int | None = None
    inapplicable: int | None = None
    misses: int | None = None
    publications: int | None = None
    applied_hits: int | None = None
    rejected_fit: int | None = None
    root_tail_rejections: int | None = None
    bypasses: int | None = None
    invalid_records: int | None = None
    key_operand_bits: int | None = None
    payload_operand_bits: int | None = None
    validation_operand_bits: int | None = None


def collect_complete_action_reuse(
    counters: Mapping[str, int], prefix: str
) -> CompleteActionReuse:
    """Project counters without looking up or validating any cached action."""
    values = {}
    for name in CompleteActionReuse.__dataclass_fields__:
        value = counters.get(prefix + name)
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(f"{prefix}{name} must be a nonnegative measured count")
        values[name] = value
    lane = CompleteActionReuse(**values)
    for smaller, larger in (
        (lane.applied_hits, lane.admitted),
        (lane.admitted, lane.retrieved),
        (lane.retrieved, lane.lookups),
    ):
        if smaller is not None and larger is not None and smaller > larger:
            raise ValueError(
                f"{prefix} application/admission/retrieval counts disagree"
            )
    return lane
