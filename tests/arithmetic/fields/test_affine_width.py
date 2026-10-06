"""Exact affine width decisions, including ambiguous power-of-two boundaries."""

import random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.affine_width import nonnegative_affine_width
from number_compiler.resources.ledger import ResourceLedger


def test_affine_width_matches_independent_integer_arithmetic() -> None:
    rng = random.Random(7019)
    ledger = ResourceLedger()
    for _ in range(256):
        source = rng.getrandbits(rng.randrange(300))
        shift = rng.randrange(320)
        gain = rng.randrange(3**8)
        offset = rng.getrandbits(rng.randrange(300))
        assert (
            nonnegative_affine_width(source, shift, gain, offset, ledger)
            == (gain * (source >> shift) + offset).bit_length()
        )
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("delta", (-1, 0, 1))
def test_exact_boundary_refines_without_approximating(delta: int) -> None:
    source = (1 << 256) + delta
    ledger = ResourceLedger()
    assert (
        nonnegative_affine_width(source, 0, 1, 1, ledger) == (source + 1).bit_length()
    )
    assert ledger.nodes == 0


def test_wide_source_width_uses_a_small_leading_interval() -> None:
    ledger = ResourceLedger()
    source = (3 << 99_998) + 17
    assert nonnegative_affine_width(source, 7, 3, 1, ledger) == 99_995
    assert ledger.counters["affine_width_operand_bits"] < 128
    assert ledger.counters.get("affine_width_refinements", 0) == 0
    assert ledger.nodes == 0


def test_affine_width_rejects_inexact_or_negative_inputs() -> None:
    ledger = ResourceLedger()
    with pytest.raises(TypeError):
        nonnegative_affine_width(1, True, 3, 0, ledger)
    with pytest.raises(ValueError):
        nonnegative_affine_width(1, 0, 3, -1, ledger)


def test_affine_width_budget_refuses_before_interval_allocation() -> None:
    ledger = ResourceLedger(max_nodes=1)
    with pytest.raises(BlockContextBudgetExceeded):
        nonnegative_affine_width(1 << 4096, 0, 3, 1, ledger)
    assert ledger.nodes == ledger.entries == 0
    assert ledger.counters["affine_width_failures"] == 1
    assert ledger.counters["affine_width_interval_checks"] == 0
