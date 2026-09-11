"""Hard production guard and instrumentation for powered jump execution.

A full binary jump is not allowed to hide ordinary successor replay, growth-bit
queries, per-position evaluation, or materialization.  This module provides the
single context used by :mod:`number_compiler.hashlife.actions.jump` and by all forbidden runtime
helpers.
"""

from __future__ import annotations

from collections import Counter
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Iterator, Mapping


class JumpGuardViolation(RuntimeError):
    """Raised immediately when a powered jump attempts a forbidden operation."""


@dataclass(slots=True)
class JumpAudit:
    jump_calls: int = 0
    forbidden_attempts: Counter[str] = field(default_factory=Counter)
    summary_queries: int = 0
    summary_hits: int = 0
    symbolic_ops: Counter[str] = field(default_factory=Counter)
    cascade_sections: int = 0
    cascade_dependency_groups: int = 0
    cascade_selector_bits: int = 0
    residual_states: int = 0
    residual_output_probes: int = 0
    residual_decision_nodes: int = 0
    residual_dependency_groups: int = 0
    residual_selector_bits: int = 0
    residual_description_bits: int = 0
    residual_generator_boxes: int = 0
    residual_canonical_regions: int = 0
    residual_late_merges: int = 0
    slp_nodes: int = 0
    slp_sections: int = 0
    tropical_ops: int = 0

    def snapshot(self) -> "JumpAuditSnapshot":
        return JumpAuditSnapshot(
            jump_calls=self.jump_calls,
            forbidden_attempts=dict(self.forbidden_attempts),
            summary_queries=self.summary_queries,
            summary_hits=self.summary_hits,
            symbolic_ops=dict(self.symbolic_ops),
            cascade_sections=self.cascade_sections,
            cascade_dependency_groups=self.cascade_dependency_groups,
            cascade_selector_bits=self.cascade_selector_bits,
            residual_states=self.residual_states,
            residual_output_probes=self.residual_output_probes,
            residual_decision_nodes=self.residual_decision_nodes,
            residual_dependency_groups=self.residual_dependency_groups,
            residual_selector_bits=self.residual_selector_bits,
            residual_description_bits=self.residual_description_bits,
            residual_generator_boxes=self.residual_generator_boxes,
            residual_canonical_regions=self.residual_canonical_regions,
            residual_late_merges=self.residual_late_merges,
            slp_nodes=self.slp_nodes,
            slp_sections=self.slp_sections,
            tropical_ops=self.tropical_ops,
        )


@dataclass(frozen=True, slots=True)
class JumpAuditSnapshot:
    jump_calls: int
    forbidden_attempts: Mapping[str, int]
    summary_queries: int
    summary_hits: int
    symbolic_ops: Mapping[str, int]
    cascade_sections: int
    cascade_dependency_groups: int
    cascade_selector_bits: int
    residual_states: int
    residual_output_probes: int
    residual_decision_nodes: int
    residual_dependency_groups: int
    residual_selector_bits: int
    residual_description_bits: int
    residual_generator_boxes: int
    residual_canonical_regions: int
    residual_late_merges: int
    slp_nodes: int
    slp_sections: int
    tropical_ops: int

    @property
    def clean(self) -> bool:
        return not any(self.forbidden_attempts.values())


_ACTIVE_AUDIT: ContextVar[JumpAudit | None] = ContextVar(
    "reverse_add_jump_audit", default=None
)


def in_powered_jump() -> bool:
    return _ACTIVE_AUDIT.get() is not None


@contextmanager
def powered_jump_scope(audit: JumpAudit) -> Iterator[None]:
    if _ACTIVE_AUDIT.get() is not None:
        # Nested powered calls share one audit and should not reset it.
        yield
        return
    token = _ACTIVE_AUDIT.set(audit)
    try:
        yield
    finally:
        _ACTIVE_AUDIT.reset(token)


def forbid_in_powered_jump(operation: str) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is None:
        return
    name = str(operation)
    audit.forbidden_attempts[name] += 1
    raise JumpGuardViolation(
        f"powered jump attempted forbidden operation {name!r}; "
        "full J must remain symbolic/event-selective"
    )


def record_summary_query(hit: bool) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is None:
        return
    audit.summary_queries += 1
    if hit:
        audit.summary_hits += 1


def record_cascade_metrics(
    *, sections: int = 0, dependency_groups: int = 0, selector_bits: int = 0
) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is None:
        return
    audit.cascade_sections += int(sections)
    audit.cascade_dependency_groups += int(dependency_groups)
    audit.cascade_selector_bits += int(selector_bits)


def record_residual_metrics(
    *,
    states: int = 0,
    output_probes: int = 0,
    decision_nodes: int = 0,
    dependency_groups: int = 0,
    selector_bits: int = 0,
    description_bits: int = 0,
    generator_boxes: int = 0,
    canonical_regions: int = 0,
    late_merges: int = 0,
) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is not None:
        audit.residual_states += int(states)
        audit.residual_output_probes += int(output_probes)
        audit.residual_decision_nodes += int(decision_nodes)
        audit.residual_dependency_groups += int(dependency_groups)
        audit.residual_selector_bits += int(selector_bits)
        audit.residual_description_bits += int(description_bits)
        audit.residual_generator_boxes += int(generator_boxes)
        audit.residual_canonical_regions += int(canonical_regions)
        audit.residual_late_merges += int(late_merges)


def record_slp_metrics(*, nodes: int = 0, sections: int = 0) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is not None:
        audit.slp_nodes += int(nodes)
        audit.slp_sections += int(sections)


def record_tropical_op(count: int = 1) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is not None:
        audit.tropical_ops += int(count)


def record_symbolic_op(name: str, count: int = 1) -> None:
    audit = _ACTIVE_AUDIT.get()
    if audit is not None:
        audit.symbolic_ops[str(name)] += int(count)


__all__ = [
    "JumpGuardViolation",
    "JumpAudit",
    "JumpAuditSnapshot",
    "in_powered_jump",
    "powered_jump_scope",
    "forbid_in_powered_jump",
    "record_summary_query",
    "record_cascade_metrics",
    "record_residual_metrics",
    "record_slp_metrics",
    "record_tropical_op",
    "record_symbolic_op",
]
