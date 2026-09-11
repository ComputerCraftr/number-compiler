"""Binary reverse/add compilation from the primitive algebraic leaf law."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockEffect,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler


def is_verified_decimal_pair_kernel(effect: BlockEffect) -> bool:
    """Compare complete immutable semantics against the SHA-verified artifact.

    Names, compressed sizes, and digest equality alone do not grant arithmetic
    authority. SemanticIdentity also compares the complete kernel definition.
    """
    from number_compiler.arithmetic.contracts.block_effect import _effect_key
    from number_compiler.arithmetic.contracts.block_kernel import (
        FiniteBlockEffect,
        _load_base10_t2_kernel,
    )

    return (
        type(effect) is FiniteBlockEffect
        and effect.base == 10
        and effect.exponent == 2
        and _effect_key(effect) == _effect_key(_load_base10_t2_kernel())
    )


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
    # The 757/179 T2 machine is a differential proof certificate. It must not
    # become a production port, cache key, or powered temporal leaf.
    return compiler.power(BaseBlockEffect(base), exponent)
