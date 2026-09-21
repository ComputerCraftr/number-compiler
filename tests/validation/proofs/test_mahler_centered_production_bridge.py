"""Exact centered-chart bridge to the production Antihydra cylinder algebra."""

from fractions import Fraction

import pytest

from devtools.experiments.antihydra.source_safety import (
    SourceBlockID,
    SourceSafetyWorkspace,
)
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    admitted_arithmetic_cylinder,
)


def _production_cylinder(
    workspace: SourceSafetyWorkspace, handle: SourceBlockID
) -> ArithmeticCylinder:
    """Independent bounded production view of the chart ``h=D+1``."""
    block = workspace.view(handle)
    if not 1 <= block.width <= 64:
        raise ValueError("production arithmetic cylinders have width 1..64")
    residue, _high = workspace.antihydra_chart(handle, 0)
    return admitted_arithmetic_cylinder(residue, block.width)


def _assert_centered_bridge(
    workspace: SourceSafetyWorkspace, handle: SourceBlockID, high_fiber: int
) -> None:
    block = workspace.view(handle)
    core = _production_cylinder(workspace, handle)
    modulus, gain = 1 << block.width, 3**block.width
    chart_carry = (block.residue + 1) // modulus
    chart_residue, chart_high = workspace.antihydra_chart(handle, high_fiber)
    assert chart_residue == core.residue
    assert chart_high == high_fiber + chart_carry
    assert block.endpoint == core.output + gain * chart_carry - 1
    assert (block.ledger_delta, block.ledger_minimum) == (
        core.delta,
        core.minimum,
    )
    assert block.skew.upper == core.skew.upper
    assert block.skew.lower == core.skew.lower
    assert block.skew.offset == core.skew.offset + gain - modulus

    centered_source = block.residue + modulus * high_fiber
    physical_source = centered_source + 1
    physical_after, ledger_after = core.advance(physical_source, 11)
    assert physical_after == block.endpoint + gain * high_fiber + 1
    assert ledger_after == 11 + block.ledger_delta

    for fraction in (Q(0), Q(1, 7), Q(1, 2)):
        after = block.fractional.apply(fraction)
        assert after is not None
        expected = (
            Fraction(gain, modulus)
            * (
                Fraction(block.residue)
                + Fraction(fraction.numerator, fraction.denominator)
            )
            - block.endpoint
        )
        assert Fraction(after.numerator, after.denominator) == expected


@pytest.mark.parametrize("width", range(1, 9))
def test_every_small_centered_cylinder_is_the_production_h_chart(width: int) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=64)
    for residue in range(1 << width):
        handle = workspace.cylinder(width, residue)
        _assert_centered_bridge(workspace, handle, max(4, residue + 3))


@pytest.mark.parametrize(
    ("width", "residue"),
    ((16, 0), (16, 65535), (32, 0xDEADBEEF), (64, 0), (64, 2**64 - 1)),
)
def test_centered_chart_wrap_and_large_high_fibers(width: int, residue: int) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=64)
    handle = workspace.cylinder(width, residue)
    _assert_centered_bridge(workspace, handle, 2**80 + 37)


@pytest.mark.parametrize("width", range(2, 9))
def test_chronological_source_composition_is_production_cylinder_composition(
    width: int,
) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=64)
    for source in range(1 << width):
        whole_id = workspace.cylinder(width, source)
        for split in range(1, width):
            first_id = workspace.cylinder(split, source % (1 << split))
            first = workspace.view(first_id)
            middle = first.endpoint + 3**split * (source >> split)
            second_id = workspace.cylinder(
                width - split, middle % (1 << (width - split))
            )
            assert workspace.compose(first_id, second_id) == whole_id
            assert _production_cylinder(workspace, first_id).then(
                _production_cylinder(workspace, second_id)
            ) == _production_cylinder(workspace, whole_id)


def test_fractional_guard_and_antihydra_ledger_admission_remain_distinct() -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger())
    ledger_unsafe = workspace.view(workspace.cylinder(1, 0))
    assert ledger_unsafe.ledger_minimum == -1
    assert not ledger_unsafe.guard.empty

    fractional_unsafe = workspace.view(workspace.cylinder(2, 3))
    assert fractional_unsafe.ledger_minimum == 0
    assert fractional_unsafe.guard.empty


def test_centered_chart_authenticates_its_source_handle() -> None:
    first = SourceSafetyWorkspace(ResourceLedger())
    second = SourceSafetyWorkspace(ResourceLedger())
    foreign = first.cylinder(1, 0)
    with pytest.raises(ValueError, match="different arena"):
        second.antihydra_chart(foreign, 0)
    with pytest.raises(ValueError, match="natural centered high fiber"):
        first.antihydra_chart(foreign, -1)


def test_retention_accounting_counts_only_stored_source_block_integers() -> None:
    ledger = ResourceLedger()
    workspace = SourceSafetyWorkspace(ledger)
    block = workspace.view(workspace.cylinder(1, 0))
    stored = (
        block.residue,
        block.endpoint,
        block.width,
        block.guard.lower.numerator,
        block.guard.lower.denominator,
        block.guard.upper.numerator,
        block.guard.upper.denominator,
        block.ledger_delta,
        block.ledger_minimum,
    )
    assert ledger.counters["safety_retained_integer_bits"] == sum(
        abs(value).bit_length() for value in stored
    )
