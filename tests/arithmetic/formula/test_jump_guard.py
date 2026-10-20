from __future__ import annotations

from collections.abc import Callable

import pytest

from number_compiler.arithmetic.automata.guard import JumpGuardViolation
from number_compiler.arithmetic.formula.derived import (
    carry_out,
    compile_branch,
    growth_bit,
    successor,
)
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    root_from_values,
)
from number_compiler.arithmetic.formula.summary import get_summary
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.actions.jump import (
    ExactJumpBackend,
    StrictBinaryRootBuilder,
)
from number_compiler.hashlife.execution.evaluator import materialize_values, value_at


class _BaseBackend:
    def __init__(self) -> None:
        self.arena = FormulaArena()
        self.spec = RadixSpec(10)
        self.seed = root_from_values((7, 18, 7), self.arena, self.spec)

    def seed_root(self) -> FormulaRoot:
        return self.seed


class SuccessorBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        return successor(self.arena, root, self.spec)


class GrowthBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        growth_bit(self.arena, root, self.spec)
        return root


class CarryBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        carry_out(self.arena, root, self.spec)
        return root


class BranchBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        return compile_branch(self.arena, root, 0, self.spec)


class MaterializeBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        materialize_values(root)
        return root


class PointBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        value_at(root, 0)
        return root


class ClosedBitBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        self.arena.eval_closed_bit(root.planes[0], 0)
        return root


@pytest.mark.parametrize(
    "backend",
    [
        SuccessorBackend,
        GrowthBackend,
        CarryBackend,
        BranchBackend,
        MaterializeBackend,
        PointBackend,
        ClosedBitBackend,
    ],
)
def test_powered_jump_forbidden_paths_raise(
    backend: Callable[[], ExactJumpBackend[FormulaRoot]],
) -> None:
    with pytest.raises(JumpGuardViolation):
        StrictBinaryRootBuilder(backend()).root_at(1)


class SummaryOnlyBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        # Reading already-propagated compiler metadata is allowed.
        assert get_summary(self.arena, root, self.spec, required=True) is not None
        return root


def test_cached_summary_is_allowed_and_audited() -> None:
    got = StrictBinaryRootBuilder[FormulaRoot](SummaryOnlyBackend()).root_at(7)
    assert got.jump_calls == 3
    assert got.audit.clean
    assert got.audit.summary_queries == 3
    assert got.audit.summary_hits == 3


class LiteralBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        self.arena.literal(1, root.width)
        return root


class RebuildBackend(_BaseBackend):
    def jump_bit(self, prefix_index: object, root: object, bit: object) -> FormulaRoot:
        return root_from_values((7, 18, 7), self.arena, self.spec)


def test_jump_cannot_smuggle_materialized_literal_or_rebuild() -> None:
    for backend in (LiteralBackend, RebuildBackend):
        with pytest.raises(JumpGuardViolation):
            StrictBinaryRootBuilder(backend()).root_at(1)


class BlockProjectionBackend(_BaseBackend):
    def jump_bit(
        self, prefix_index: object, root: FormulaRoot, bit: object
    ) -> FormulaRoot:
        from devtools.verification.block_power import (
            apply_block_power,
            power_block_effect,
        )

        apply_block_power(power_block_effect(base=10, exponent=1), (7, 18, 7))
        return root


def test_powered_jump_cannot_project_block_power_to_concrete_pair_word() -> None:
    with pytest.raises(JumpGuardViolation):
        StrictBinaryRootBuilder(BlockProjectionBackend()).root_at(1)
