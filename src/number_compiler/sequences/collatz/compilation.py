"""Production binary compilation of the primitive physical Collatz law."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def compile_collatz_physical_power(compiler: LazyCompiler, steps: int) -> BlockPower:
    """Compile C**steps without importing the proof-only C4 state domain."""
    if type(steps) is not int or steps < 0:
        raise ValueError("physical step count must be nonnegative")
    from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget

    if not steps:
        return BlockPower(2, 0, None, 0, 0, 0, BlockContextBudget())
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


__all__ = ["compile_collatz_physical_power"]
