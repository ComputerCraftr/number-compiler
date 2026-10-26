from __future__ import annotations

import random

import pytest

from number_compiler.arithmetic.formula.derived import carry_out, growth_bit, successor
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.hashlife.execution.evaluator import materialize_values
from tests.support.reverse_pair_oracle import (
    symmetric_reference_successor as reference_successor,
)


def test_canonical_state_has_no_duplicate_state() -> None:
    A = FormulaArena()
    root = root_from_values((7, 18, 7), A, RadixSpec(10))
    assert set(root.__slots__) == {"planes"}
    assert root.width == 3 and root.parity == 1 and root.half_length == 2
    _ = carry_out(A, root, RadixSpec(10))
    assert (
        not hasattr(root, "scale")
        and not hasattr(root, "carry")
        and not hasattr(root, "growth")
    )


@pytest.mark.validation  # Complete hundred-step formula-orbit differential.
def test_synthesized_growth_and_successor_real_orbit() -> None:
    spec = RadixSpec(10)
    A = FormulaArena()
    values: tuple[int, ...] = (7, 18, 7)
    root = root_from_values(values, A, spec)
    for _ in range(100):
        target = reference_successor(values)
        assert growth_bit(A, root, spec) == len(target) - len(values)
        root = successor(A, root, spec)
        assert materialize_values(root) == target
        values = target


@pytest.mark.validation  # Broad seeded fuzzing across bases and digit lengths.
def test_random_bases() -> None:
    rng = random.Random(0x196)
    for base in range(2, 17):
        spec = RadixSpec(base)
        for _ in range(50):
            d = rng.randint(1, 15)
            half = [rng.randint(0, 2 * (base - 1)) for _ in range((d + 1) // 2)]
            if half[0] == 0:
                half[0] = 1
            full = tuple(half + (half[-2::-1] if d & 1 else half[::-1]))
            A = FormulaArena()
            root = root_from_values(full, A, spec)
            assert materialize_values(successor(A, root, spec)) == reference_successor(
                full, base
            )


def test_deep_lazy_growth_has_no_recursion_failure() -> None:
    spec = RadixSpec(10)
    A = FormulaArena()
    root = root_from_values((7, 18, 7), A, spec)
    for _ in range(200):
        root = successor(A, root, spec)
    assert root.width > 80
    assert A.cached_closed_bits > 0
