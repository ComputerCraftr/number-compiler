"""Production binary compilation of the primitive physical Collatz law."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.diamond_actions import TemporalActionArena
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def compile_collatz_physical_power(compiler: LazyCompiler, steps: int) -> BlockPower:
    """Compile C**steps without importing the proof-only C4 state domain."""
    if type(steps) is not int or steps < 0:
        raise ValueError("physical step count must be nonnegative")
    from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget

    if not steps:
        return BlockPower(2, 0, None, 0, 0, 0, BlockContextBudget())
    from number_compiler.sequences.collatz.tile_family_hooks import (
        collatz_runtime_tile_hooks,
        is_collatz_tile_hooks,
    )

    if compiler.family_hooks is None:
        compiler.bind_family_hooks(collatz_runtime_tile_hooks())
    elif not is_collatz_tile_hooks(compiler.family_hooks):
        raise ValueError("Collatz power compiler has another family adapter")
    powered = compiler.power(CollatzPhysicalBlockEffect(), steps)
    root = powered.root
    if root is None or root.exponent != steps:
        raise AssertionError("physical power lost its exact exponent")
    return BlockPower(
        2,
        steps,
        root,
        root.operator_nodes(),
        powered.compose_operations,
        getattr(root, "depth", 1),
        BlockContextBudget(),
    )


def compile_physical_diamond(
    compiler: LazyCompiler, actions: TemporalActionArena, steps: int
) -> ActionProgramID:
    """Import the physical Collatz power into its owning temporal arena."""
    if actions.compiler is not compiler:
        raise ValueError("temporal actions belong to another compiler")
    power = compile_collatz_physical_power(compiler, steps)
    return actions.identity if power.root is None else actions.intern(power.root)


__all__ = ["compile_collatz_physical_power", "compile_physical_diamond"]
