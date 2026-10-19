"""Fail-closed release gate for the full exact binary jump."""

from __future__ import annotations

import logging
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import Protocol, TypeGuard, runtime_checkable

from number_compiler.arithmetic.automata.guard import JumpGuardViolation
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    formula_metrics,
)
from number_compiler.arithmetic.formula.summary import get_summary
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.actions.jump import (
    ExactJumpBackend,
    MissingJumpBackend,
    NoExactJumpBackend,
    StrictBinaryRootBuilder,
)


class FullJumpReleaseBlocked(RuntimeError):
    pass


@runtime_checkable
class FullStateJumpBackend(ExactJumpBackend[FormulaRoot], Protocol):
    """Backend shape required by the public full-state release gate."""

    full_state_exact: bool
    arena: FormulaArena
    spec: RadixSpec


def _has_formula_inputs(arena: object, spec: object) -> bool:
    """Keep the runtime owner checks at the untrusted backend boundary."""
    return isinstance(arena, FormulaArena) and isinstance(spec, RadixSpec)


def _is_formula_root(value: object) -> TypeGuard[FormulaRoot]:
    """Validate roots returned across the runtime-checkable backend protocol."""
    return isinstance(value, FormulaRoot)


@dataclass(frozen=True, slots=True)
class ReleaseComplexityPolicy:
    """Fail-closed empirical complexity budget for release probes.

    Budgets are deliberately functions of index bit length, never represented
    digit width.  They do not prove an asymptotic bound, but prevent a backend
    from passing certification by building a width- or time-linear symbolic DAG.
    """

    degree: int = 4
    symbolic_op_factor: int = 4096
    description_bit_factor: int = 16384
    node_factor: int = 2048
    depth_factor: int = 512
    cascade_section_factor: int = 512
    cascade_group_factor: int = 4096
    cascade_selector_bit_factor: int = 32768
    residual_state_factor: int = 2048
    residual_probe_factor: int = 16384
    residual_decision_node_factor: int = 4096
    residual_dependency_group_factor: int = 16384
    residual_selector_bit_factor: int = 131072
    residual_description_bit_factor: int = 131072
    residual_generator_box_factor: int = 32768
    residual_canonical_region_factor: int = 8192
    slp_node_factor: int = 4096
    slp_section_factor: int = 8192
    tropical_op_factor: int = 32768

    def budget(self, factor: int, n: int) -> int:
        levels = max(1, int(n).bit_length())
        return int(int(factor) * (levels ** int(self.degree)))


@dataclass(frozen=True, slots=True)
class ReleaseProbeResult:
    index: int
    jump_calls: int
    symbolic_ops: int
    summary_queries: int
    formula_nodes: int
    description_bits: int
    formula_depth: int
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


@dataclass(frozen=True, slots=True)
class FullJumpReleaseReport:
    ready: bool
    probes: tuple[ReleaseProbeResult, ...]
    reason: str = ""


def _validated_backend(
    candidate: object,
) -> tuple[FullStateJumpBackend | None, str | None]:
    if isinstance(candidate, MissingJumpBackend):
        return None, "full exact J_0/J_1 backend is missing"
    if not isinstance(candidate, FullStateJumpBackend):
        return (
            None,
            "backend does not implement the full exact FormulaRoot jump contract",
        )
    if candidate.full_state_exact is not True:
        return (
            None,
            "backend is not explicitly certified as a full exact FormulaRoot jump",
        )
    if not _has_formula_inputs(candidate.arena, candidate.spec):
        return (
            None,
            "full-state backend must own compiler arena/spec for summary validation",
        )
    try:
        seed = candidate.seed_root()
    except Exception as exc:  # pragma: no cover - defensive release path
        logging.getLogger(__name__).debug("Backend seed failed", exc_info=True)
        return None, f"seed_root failed: {exc}"
    if not _is_formula_root(seed):
        return None, "full-state backend seed is not FormulaRoot"
    try:
        get_summary(candidate.arena, seed, candidate.spec, required=True)
    except Exception as exc:
        logging.getLogger(__name__).debug("Backend summary failed", exc_info=True)
        return None, f"seed compiler summary unavailable: {exc}"
    return candidate, None


_DEFAULT_RELEASE_COMPLEXITY_POLICY_1 = ReleaseComplexityPolicy()


def certify_full_jump_backend(
    backend: object,
    *,
    probes: Iterable[int] = (0, 1, 2, 3, 7, 31, 63),
    exact_checker: Callable[[int, FormulaRoot], bool] | None = None,
    complexity: ReleaseComplexityPolicy | None = _DEFAULT_RELEASE_COMPLEXITY_POLICY_1,
) -> FullJumpReleaseReport:
    checked_backend, error = _validated_backend(backend)
    if error:
        return FullJumpReleaseReport(False, (), error)
    if checked_backend is None:
        raise AssertionError("validated release backend was not returned")
    builder = StrictBinaryRootBuilder(checked_backend)
    results: list[ReleaseProbeResult] = []
    try:
        for n in tuple(map(int, probes)):
            got = builder.root_at(n)
            if not _is_formula_root(got.root):
                return FullJumpReleaseReport(
                    False, tuple(results), f"jump n={n} did not return FormulaRoot"
                )
            # This is a metadata lookup only. Missing summary is a release blocker;
            # it must have been propagated by jump compilation, not synthesized now.
            get_summary(
                checked_backend.arena, got.root, checked_backend.spec, required=True
            )
            if not got.audit.clean:
                return FullJumpReleaseReport(
                    False, tuple(results), "powered jump audit is dirty"
                )
            if exact_checker is not None and not exact_checker(n, got.root):
                return FullJumpReleaseReport(
                    False, tuple(results), f"exactness probe failed at n={n}"
                )
            ops = sum(got.audit.symbolic_ops.values())
            fm = formula_metrics(got.root)
            expected_calls = 0 if n == 0 else n.bit_length()
            if got.jump_calls != expected_calls:
                return FullJumpReleaseReport(
                    False,
                    tuple(results),
                    f"jump-call complexity violation at n={n}: {got.jump_calls} != {expected_calls}",
                )
            if got.audit.summary_hits != got.audit.summary_queries:
                return FullJumpReleaseReport(
                    False,
                    tuple(results),
                    f"summary cache miss during powered probe n={n}",
                )
            if got.audit.residual_late_merges:
                return FullJumpReleaseReport(
                    False,
                    tuple(results),
                    f"late semantic quotient regression at n={n}: "
                    f"{got.audit.residual_late_merges} states merged after canonical construction",
                )
            if complexity is not None:
                checks = (
                    (
                        "symbolic ops",
                        ops,
                        complexity.budget(complexity.symbolic_op_factor, n),
                    ),
                    (
                        "formula nodes",
                        fm["nodes"],
                        complexity.budget(complexity.node_factor, n),
                    ),
                    (
                        "description bits",
                        fm["description_bits"],
                        complexity.budget(complexity.description_bit_factor, n),
                    ),
                    (
                        "formula depth",
                        fm["depth"],
                        complexity.budget(complexity.depth_factor, n),
                    ),
                    (
                        "cascade sections",
                        got.audit.cascade_sections,
                        complexity.budget(complexity.cascade_section_factor, n),
                    ),
                    (
                        "cascade dependency groups",
                        got.audit.cascade_dependency_groups,
                        complexity.budget(complexity.cascade_group_factor, n),
                    ),
                    (
                        "cascade selector bits",
                        got.audit.cascade_selector_bits,
                        complexity.budget(complexity.cascade_selector_bit_factor, n),
                    ),
                    (
                        "residual states",
                        got.audit.residual_states,
                        complexity.budget(complexity.residual_state_factor, n),
                    ),
                    (
                        "residual output probes",
                        got.audit.residual_output_probes,
                        complexity.budget(complexity.residual_probe_factor, n),
                    ),
                    (
                        "residual decision nodes",
                        got.audit.residual_decision_nodes,
                        complexity.budget(complexity.residual_decision_node_factor, n),
                    ),
                    (
                        "residual dependency groups",
                        got.audit.residual_dependency_groups,
                        complexity.budget(
                            complexity.residual_dependency_group_factor, n
                        ),
                    ),
                    (
                        "residual selector bits",
                        got.audit.residual_selector_bits,
                        complexity.budget(complexity.residual_selector_bit_factor, n),
                    ),
                    (
                        "residual description bits",
                        got.audit.residual_description_bits,
                        complexity.budget(
                            complexity.residual_description_bit_factor, n
                        ),
                    ),
                    (
                        "residual generator boxes",
                        got.audit.residual_generator_boxes,
                        complexity.budget(complexity.residual_generator_box_factor, n),
                    ),
                    (
                        "residual canonical regions",
                        got.audit.residual_canonical_regions,
                        complexity.budget(
                            complexity.residual_canonical_region_factor, n
                        ),
                    ),
                    (
                        "SLP nodes",
                        got.audit.slp_nodes,
                        complexity.budget(complexity.slp_node_factor, n),
                    ),
                    (
                        "SLP sections",
                        got.audit.slp_sections,
                        complexity.budget(complexity.slp_section_factor, n),
                    ),
                    (
                        "tropical ops",
                        got.audit.tropical_ops,
                        complexity.budget(complexity.tropical_op_factor, n),
                    ),
                )
                for label, value, budget in checks:
                    if value > budget:
                        return FullJumpReleaseReport(
                            False,
                            tuple(results),
                            f"{label} complexity budget exceeded at n={n}: {value} > {budget}",
                        )
            results.append(
                ReleaseProbeResult(
                    n,
                    got.jump_calls,
                    ops,
                    got.audit.summary_queries,
                    fm["nodes"],
                    fm["description_bits"],
                    fm["depth"],
                    got.audit.cascade_sections,
                    got.audit.cascade_dependency_groups,
                    got.audit.cascade_selector_bits,
                    got.audit.residual_states,
                    got.audit.residual_output_probes,
                    got.audit.residual_decision_nodes,
                    got.audit.residual_dependency_groups,
                    got.audit.residual_selector_bits,
                    got.audit.residual_description_bits,
                    got.audit.residual_generator_boxes,
                    got.audit.residual_canonical_regions,
                    got.audit.residual_late_merges,
                    got.audit.slp_nodes,
                    got.audit.slp_sections,
                    got.audit.tropical_ops,
                )
            )
    except (JumpGuardViolation, NoExactJumpBackend, KeyError) as exc:
        return FullJumpReleaseReport(False, tuple(results), str(exc))
    return FullJumpReleaseReport(True, tuple(results))


def require_full_jump_release(
    backend: object,
    *,
    probes: Iterable[int] = (0, 1, 2, 3, 7, 31, 63),
    exact_checker: Callable[[int, FormulaRoot], bool] | None = None,
    complexity: ReleaseComplexityPolicy | None = _DEFAULT_RELEASE_COMPLEXITY_POLICY_1,
) -> FullJumpReleaseReport:
    report = certify_full_jump_backend(
        backend, probes=probes, exact_checker=exact_checker, complexity=complexity
    )
    if not report.ready:
        raise FullJumpReleaseBlocked(report.reason)
    return report


__all__ = [
    "FullJumpReleaseBlocked",
    "FullJumpReleaseReport",
    "ReleaseComplexityPolicy",
    "ReleaseProbeResult",
    "certify_full_jump_backend",
    "require_full_jump_release",
]
