"""The Antihydra Mahler source action and rotation readout share a scale."""

from __future__ import annotations

from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def test_mahler_source_normal_form_reuses_radial_clock() -> None:
    normal = MahlerSourceBoundSafetyAction.one_bit(1).then_bit(0).then_bit(1)
    assert normal.radial_sturmian_clock.scale == HomogeneousGrowthScale(3, 3)
    with GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=2_000_000) as e:
        assert normal.radial_sturmian_clock.leading_binary(e).prefix_binary == (
            "11011000"
        )


def test_admitted_mahler_radial_bits_are_not_affine_endpoint_bits() -> None:
    for count in (1, 2, 3, 8, 64):
        result = AntihydraArithmeticTerm(count, shared_cache=False).result()
        packet = associated_action(result)
        radial = packet["radial_sturmian"]
        assert isinstance(radial, dict)
        assert packet["first_failure"] == (2 if count >= 2 else None)
        assert packet["source_binding"] == result.source_binding
        assert (radial["growths"], radial["halvings"]) == (count, count)
        assert radial["prefix_value"] == int(bin(3**count)[2:][:8].ljust(8, "0"), 2)
        assert "affine endpoint is not inferred" in radial["scope"]
        assert packet["all_time_claim"] is False
