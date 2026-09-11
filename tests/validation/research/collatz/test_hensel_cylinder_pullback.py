"""Independent 16-bit extensional pullback checks, partitioned for process guards."""

import pytest

from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselAffineBlock,
    HenselCylinder,
)


@pytest.mark.parametrize("shard", range(8))
def test_cylinder_pullback_all_sixteen_bit_inputs(shard: int) -> None:
    blocks = (
        HenselAffineBlock(1, 1, 1),
        HenselAffineBlock(2, 3, 5),
        HenselAffineBlock(3, 4, 19),
        HenselAffineBlock(0, 2, 0),
    )
    targets = (
        HenselCylinder(0, 0),
        HenselCylinder(1, 1),
        HenselCylinder(6, 21),
        HenselCylinder(12, 385),
    )
    for block in blocks:
        pulled = tuple(c.pullback(block) for c in targets)
        for value in range(shard * 8192, (shard + 1) * 8192):
            numerator = 3**block.steps * value + block.offset
            integral = numerator % (1 << block.divisions) == 0
            for target, source in zip(targets, pulled, strict=True):
                expected = integral and target.contains(numerator >> block.divisions)
                assert source.contains(value) == expected
