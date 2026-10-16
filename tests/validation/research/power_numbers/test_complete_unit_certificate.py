"""Explicit large source-width Fermat control; never part of default units."""

from __future__ import annotations

import pytest

from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    demand_dyadic_boolean_counter,
)

pytestmark = pytest.mark.validation


def test_f4_complete_unit_and_last_signed_class_action() -> None:
    certificate = FermatNumberSpec(4).demand_bounded_complete_unit_certificate()
    assert certificate.producer_verified
    assert certificate.complete_source_verified
    assert certificate.level == 15
    assert certificate.precision == 51_921
    assert certificate.term_count == 25_968
    assert certificate.unit.bit_length() == 51_920
    assert certificate.terminal_residue == 1
    assert certificate.verdict == "PRIME"

    complete_action = certificate.complete_last_counter_action()
    carry, classes, correction, _harmonic = complete_action.apply(0)
    assert carry == 0
    assert correction == 65_281
    assert len(classes) == 16

    partial_window = demand_dyadic_boolean_counter(14, 128, fermat_width=16)
    assert partial_window.signed_fermat_correction == 56_657
    assert (correction - partial_window.signed_fermat_correction) % 65_537 == 8_624
