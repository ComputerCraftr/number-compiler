"""A non-dyadic power begins with the largest shared source macrocell."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from tests.support.diamond_query import oracle


@pytest.mark.parametrize("count", [3, 5, 7, 15, 20, 31])
def test_compiler_and_temporal_arena_preserve_largest_power_prefix(count: int) -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(BaseBlockEffect(3))
    powered = compiler.power(atom, count)
    assert type(powered.root) is ProgramComposition
    assert powered.root.first.exponent == 1 << (count.bit_length() - 1)
    assert powered.root.second.exponent == count - powered.root.first.exponent
    source = SourceGeometry(
        ledger, ExactSource((2, 4, 2), 3, blank=5, extent=8, alphabet_size=5)
    )
    source.span((2, 4, 2), 5, 8)
    runtime = DiamondRuntime(compiler, source)
    imported = runtime.actions.intern(powered.root)
    direct = runtime.actions.power(runtime.actions.intern(atom), count)
    assert imported == direct
    assert powered.operator_nodes <= 2 * count.bit_length()


def test_reordering_powers_does_not_reorder_noncommuting_atoms_inside_the_base() -> (
    None
):
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    a, b = BaseBlockEffect(3), DigitNormalizeBlockEffect(3)
    composite = compiler.compose(a, b)
    power = compiler.power(composite, 3)
    assert power.root is not None
    values = (2, 4, 2)
    source = SourceGeometry(
        ledger, ExactSource(values, 3, blank=5, extent=8, alphabet_size=5)
    )
    source.span(values, 5, 8)
    runtime = DiamondRuntime(compiler, source)
    root = runtime.actions.intern(power.root)
    expected = list(values) + [5] * 5
    for effect in (a, b, a, b, a, b):
        expected = oracle(effect, tuple(expected), len(expected), 1)
    assert [runtime.point(root, i) for i in range(8)] == expected
    # The two kernels are not interchangeable; this test would detect moving
    # individual atoms rather than commuting powers of the fixed AB program.
    assert a.advance(BoundarySide.LEFT, a.initial(BoundarySide.LEFT), 2) != b.advance(
        BoundarySide.LEFT, b.initial(BoundarySide.LEFT), 2
    )
