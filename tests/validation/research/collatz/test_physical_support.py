from collections.abc import Callable
from dataclasses import replace
from itertools import product

import pytest

from devtools.experiments.collatz.free_cylinder_residual import (
    FreeCylinderResidualArena,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.collatz.hensel_cylinders import HenselAffineBlock
from number_compiler.sequences.collatz.physical_support import PhysicalSupportArena


def _bits(source: int) -> Callable[[int], int]:
    return lambda bit: (source >> bit) & 1


def test_guard_consumption_preserves_support_when_output_and_clock_coincide() -> None:
    arena = FreeCylinderResidualArena(max_precision=32)
    action = arena.power_physical(3, 3)
    selected = [
        arena.select(action, source_bits=3, source_bit=_bits(x)) for x in (4, 5)
    ]
    a, b = selected
    assert a.apply_exact(4) == b.apply_exact(5) == 4
    assert (
        (a.accelerated_events, a.physical_ticks)
        == (b.accelerated_events, b.physical_ticks)
        == (1, 3)
    )
    assert a.support is not b.support
    assert [a.support.tick(i) for i in range(3)] == [False, False, True]
    assert [b.support.tick(i) for i in range(3)] == [True, False, False]
    assert a.support.specialize(s=1, z=2, modulus=257).offset == 4
    assert b.support.specialize(s=1, z=2, modulus=257).offset == 1
    before = arena.supports.node_count
    for modulus in (16, 27, 35, 257):
        for s, z in ((1, 1), (3, 2), (-1, -1)):
            a.support.specialize(s=s, z=z, modulus=modulus)
    assert arena.supports.node_count == before
    assert (
        arena.select(
            action, source_bits=3, source_bit=lambda bit: (4 >> bit) & 1
        ).support
        is a.support
    )


def test_constant_output_consumers_retain_distinct_support() -> None:
    arena = FreeCylinderResidualArena(max_precision=32)
    action = arena.power_physical(8, 3)
    a, b = [arena.select(action, source_bits=3, source_bit=_bits(x)) for x in (4, 5)]
    assert a.constant_target == b.constant_target == 1
    assert a.transport is b.transport is None
    assert (
        (a.accelerated_events, a.physical_ticks)
        == (b.accelerated_events, b.physical_ticks)
        == (2, 8)
    )
    assert a.support is not b.support
    assert a.support.specialize(s=1, z=2, modulus=257).offset == 20
    assert b.support.specialize(s=1, z=2, modulus=257).offset == 17


@pytest.mark.parametrize("ticks", [1, 2, 3, 4, 8, 16, 32, 1024])
def test_source_generated_support_matches_every_physical_tick(ticks: int) -> None:
    arena = FreeCylinderResidualArena(max_precision=2048)
    action = arena.power_physical(ticks, 3)
    for source in range(1, 8):

        def source_bit(bit: int, source: int = source) -> int:
            return (source >> bit) & 1

        selected = arena.select(
            action,
            source_bits=source.bit_length(),
            source_bit=source_bit,
        )
        value = source
        odds = 0
        for i in range(ticks):
            odd = bool(value & 1)
            assert selected.support.tick(i) is odd
            value = 3 * value + 1 if odd else value // 2
            odds += odd
        assert (selected.physical_ticks, selected.accelerated_events) == (ticks, odds)
        assert selected.apply_exact(source) == value
        matrix = selected.support.specialize(s=3, z=2, modulus=257)
        assert (matrix.upper * source + matrix.offset - matrix.lower * value) % 257 == 0


def test_support_composition_does_not_lower_an_affine_history(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("support observation lowered a concrete transport")

    monkeypatch.setattr(HenselAffineBlock, "apply_exact", forbidden)
    arena = PhysicalSupportArena(max_nodes=1024)
    count = 1 << 100
    node = arena.concat(arena.run(False, count), arena.odd)
    assert node.ticks == count + 1
    assert not node.tick(0) and not node.tick(count - 1) and node.tick(count)
    assert node.specialize(s=3, z=2, modulus=257).offset == pow(2, count, 257)
    assert arena.node_count < 210
    with pytest.raises(ValueError):
        arena.concat(node, PhysicalSupportArena(max_nodes=3).odd)
    with pytest.raises(BlockContextBudgetExceeded):
        PhysicalSupportArena(max_nodes=3).run(False, 2)
    with pytest.raises(BlockContextBudgetExceeded):
        PhysicalSupportArena(max_nodes=3).run(False, 1 << 100)
    with pytest.raises(BlockContextBudgetExceeded):
        node.specialize(s=1, z=2, modulus=1 << 4097)
    forged = replace(node)
    with pytest.raises(ValueError, match="another arena"):
        forged.specialize(s=1, z=2, modulus=257)
    with pytest.raises(ValueError, match="another arena"):
        forged.tick(0)


def test_canonical_support_concatenation_preserves_association_and_word() -> None:
    arena = PhysicalSupportArena(max_nodes=10000)
    for word in product((False, True), repeat=7):
        prefixes = [arena.identity]
        for parity in word:
            prefixes.append(
                arena.concat(prefixes[-1], arena.odd if parity else arena.even)
            )
        for split in range(8):
            suffix = arena.identity
            for parity in word[split:]:
                suffix = arena.concat(suffix, arena.odd if parity else arena.even)
            assert arena.concat(prefixes[split], suffix) is prefixes[-1]
        assert tuple(prefixes[-1].tick(i) for i in range(7)) == word
