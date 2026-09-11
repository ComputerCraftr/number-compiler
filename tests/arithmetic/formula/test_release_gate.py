from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.api.release import (
    FullJumpReleaseBlocked,
    certify_full_jump_backend,
    require_full_jump_release,
)
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.actions.jump import MissingJumpBackend

if TYPE_CHECKING:
    from number_compiler.arithmetic.formula.formula import FormulaRoot


def test_release_fails_closed_without_full_j() -> None:
    a = FormulaArena()
    root = root_from_values((7, 18, 7), a, RadixSpec(10))
    backend = MissingJumpBackend(root)
    report = certify_full_jump_backend(backend)
    assert not report.ready
    with pytest.raises(FullJumpReleaseBlocked):
        require_full_jump_release(backend)


class ToyBackend:
    def seed_root(self) -> int:
        return 0

    def jump_bit(self, prefix_index: object, root: int, bit: int) -> int:
        return 2 * root + bit


def test_release_rejects_non_formula_or_quotient_like_backend() -> None:
    report = certify_full_jump_backend(ToyBackend())
    assert not report.ready
    assert "full exact" in report.reason


class SymbolicExplosionBackend:
    full_state_exact = True

    def __init__(self) -> None:
        self.arena = FormulaArena()
        self.spec = RadixSpec(10)
        self._seed = root_from_values((7, 18, 7), self.arena, self.spec)

    def seed_root(self) -> FormulaRoot:
        return self._seed

    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: int
    ) -> FormulaRoot:
        from number_compiler.arithmetic.formula.formula import FormulaRoot
        from number_compiler.arithmetic.formula.summary import (
            get_summary,
            register_summary,
        )

        planes = []
        for p in root.planes:
            q = p
            # Symbolic-only blow-up: no forbidden evaluator/materializer calls.
            for i in range(2500):
                q = self.arena._raw("EXPLODE", q.width, args=(q,), param=(i, bit))
            planes.append(q)
        out = FormulaRoot(tuple(planes))
        register_summary(
            self.arena,
            out,
            self.spec,
            get_summary(self.arena, root, self.spec, required=True),
        )
        return out


def test_release_rejects_symbolic_dag_blowup_even_when_guard_clean() -> None:
    from number_compiler.api.release import ReleaseComplexityPolicy

    b = SymbolicExplosionBackend()
    policy = ReleaseComplexityPolicy(
        degree=1,
        symbolic_op_factor=100,
        description_bit_factor=1000,
        node_factor=100,
        depth_factor=100,
    )
    report = certify_full_jump_backend(b, probes=(1,), complexity=policy)
    assert not report.ready
    assert "complexity budget" in report.reason


class CascadeExplosionBackend:
    full_state_exact = True

    def __init__(self) -> None:
        self.arena = FormulaArena()
        self.spec = RadixSpec(10)
        self._seed = root_from_values((7, 18, 7), self.arena, self.spec)

    def seed_root(self) -> FormulaRoot:
        return self._seed

    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        from number_compiler.arithmetic.formula.summary import (
            get_summary,
            register_summary,
        )
        from number_compiler.hashlife.execution.cascade import (
            GroupedDependencyCascadeArena,
        )

        c = GroupedDependencyCascadeArena(3)
        # Exact symbolic dependency explosion without forbidden materialization.
        for k in range(300):
            c.encode_boxes((((1 << (20 + (k % 5))) - 1, 3, 7),))
        register_summary(
            self.arena,
            root,
            self.spec,
            get_summary(self.arena, root, self.spec, required=True),
        )
        return root


def test_release_rejects_cascade_dependency_blowup() -> None:
    from number_compiler.api.release import ReleaseComplexityPolicy

    b = CascadeExplosionBackend()
    policy = ReleaseComplexityPolicy(
        degree=1,
        cascade_section_factor=10,
        cascade_group_factor=10,
        cascade_selector_bit_factor=20,
    )
    report = certify_full_jump_backend(b, probes=(1,), complexity=policy)
    assert not report.ready
    assert "cascade" in report.reason


class LateSemanticMergeBackend:
    full_state_exact = True

    def __init__(self) -> None:
        self.arena = FormulaArena()
        self.spec = RadixSpec(10)
        self._seed = root_from_values((7, 18, 7), self.arena, self.spec)

    def seed_root(self) -> FormulaRoot:
        return self._seed

    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        from number_compiler.arithmetic.automata.guard import record_residual_metrics
        from number_compiler.arithmetic.formula.summary import (
            get_summary,
            register_summary,
        )

        # Simulate a powered compiler that constructs noncanonical states and
        # only discovers one equivalence in a downstream minimizer.
        record_residual_metrics(late_merges=1)
        register_summary(
            self.arena,
            root,
            self.spec,
            get_summary(self.arena, root, self.spec, required=True),
        )
        return root


def test_release_rejects_late_semantic_quotient_even_when_other_guards_are_clean() -> (
    None
):
    report = certify_full_jump_backend(
        LateSemanticMergeBackend(), probes=(1,), complexity=None
    )
    assert not report.ready
    assert "late semantic quotient regression" in report.reason
