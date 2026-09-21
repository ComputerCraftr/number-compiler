"""Binary reverse/add compilation from the primitive algebraic leaf law."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler


def compile_reverse_pair_power(
    compiler: LazyCompiler, base: int, exponent: int
) -> BlockPower:
    """Compile T**exponent with physical pair steps preserved in the result."""
    if type(base) is not int or base < 2 or type(exponent) is not int or exponent < 0:
        raise ValueError(
            "reverse compilation requires a radix and nonnegative exponent"
        )
    if not exponent:
        return BlockPower(base, 0, None, 0, 0, 0, BlockContextBudget())
    return compiler.power(BaseBlockEffect(base), exponent)
