"""Bounded powered-germ checks without promoting research keys to actions."""

from __future__ import annotations

from fractions import Fraction

from devtools.experiments.collatz.powered_boundary_germs import (
    audit_horizon,
    memo_opportunity_audit,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    SaturatingAffineAction,
)
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_transport import (
    balanced_residue_effect,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.collatz.physical_images import (
    COLLATZ_PHYSICAL_LAW,
    CollatzPhysicalImageWorkspace,
)


def test_actual_powered_germs_check_doubling_and_keep_occurrences_distinct() -> None:
    sources = (*range(32), (1 << 97) + 3, (1 << 97) + 7)
    for law in (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW):
        for horizon in (2, 4, 8):
            row = audit_horizon(law, horizon, sources)
            assert row["source_occurrences"] == len(sources)
            assert row["right_occurrences"] == len(sources)
            assert row["scalar_to_branch_conflicts"] == 0
            assert row["high_fiber_checks"] == 8
            assert isinstance(row["retained_support_records"], int)
            assert row["retained_support_records"] > 0


def test_collatz_has_more_aliases_within_low_cylinders_than_antihydra() -> None:
    sources = range(32)
    collatz = audit_horizon(COLLATZ_PHYSICAL_LAW, 4, sources)
    antihydra = audit_horizon(ANTIHYDRA_ARITHMETIC_LAW, 4, sources)
    assert isinstance(collatz["complete_effect_alias_classes"], int)
    assert isinstance(collatz["largest_complete_effect_fiber"], int)
    assert collatz["complete_effect_alias_classes"] > 0
    assert collatz["largest_complete_effect_fiber"] > 1
    assert antihydra["complete_effect_classes"] == 16
    assert antihydra["complete_effect_alias_classes"] == 16
    # The high bits create repeated occurrences, not a second action identity.
    assert antihydra["largest_complete_effect_fiber"] == 2


def test_three_edge_cells_still_have_concrete_d16_output_conflicts() -> None:
    collatz = audit_horizon(COLLATZ_PHYSICAL_LAW, 16, (16, 24))
    assert collatz["edge_to_scalar_conflicts"] == 1
    witness = collatz["edge_witness"]
    assert isinstance(witness, dict)
    assert {witness["left_source"], witness["right_source"]} == {16, 24}
    assert witness["left_effect"] != witness["right_effect"]
    antihydra = audit_horizon(ANTIHYDRA_ARITHMETIC_LAW, 16, (81, 121))
    assert antihydra["edge_to_scalar_conflicts"] == 1
    witness = antihydra["edge_witness"]
    assert isinstance(witness, dict)
    assert {witness["left_source"], witness["right_source"]} == {81, 121}
    assert witness["left_effect"] != witness["right_effect"]


def test_reduced_collatz_precision_preserves_effects_and_high_fibers() -> None:
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 0, 0, COLLATZ_PHYSICAL_LAW)
    try:
        for width in range(1, 9):
            effects = [
                balanced_residue_effect(workspace, width, residue)
                for residue in range(1 << width)
            ]
            for residue, effect in enumerate(effects):
                p = min(width, width - effect.odd_steps + 1)
                assert p >= 1
                signature = (
                    effect.transfer,
                    effect.odd_steps,
                    effect.delta,
                    effect.minimum,
                    effect.branch_word,
                )
                for peer in range(residue % (1 << p), 1 << width, 1 << p):
                    other = effects[peer]
                    assert signature == (
                        other.transfer,
                        other.odd_steps,
                        other.delta,
                        other.minimum,
                        other.branch_word,
                    )
                lifted = residue + (1 << (width + 73))
                transfer = effect.transfer
                assert (transfer.upper * lifted + transfer.offset) % transfer.lower == 0
    finally:
        workspace.dispose()


def test_real_leaf_memo_alias_opportunities_charge_scanning_cost() -> None:
    roots = ((1 << 256) + 3, (1 << 256) + 7, 27, 1 << 4096)
    result = memo_opportunity_audit(roots, steps=512)
    assert result["leaf_requests"] == 32
    assert result["exact_leaf_key_repeats"] > 0
    assert result["hypothetical_unindexed_comparisons"] > 0
    assert result["hypothetical_verified_nonexact_leaf_aliases"] == 0


def test_saturated_collatz_image_preserves_scalar_output_and_safety() -> None:
    seed, steps = (1 << 181) + 27, 129
    retained = CollatzPhysicalImageWorkspace(ResourceLedger(), seed, steps)
    saturated = CollatzPhysicalImageWorkspace(
        ResourceLedger(), seed, steps, retain_chronology=False
    )
    try:
        assert retained.endpoint() == saturated.endpoint()
        assert retained.odd_steps() == saturated.odd_steps()
        assert retained.delta() == saturated.delta()
        assert retained.minimum() == saturated.minimum()
        assert retained.image_node(retained.root_payload).summary.support is not None
        assert saturated.image_node(saturated.root_payload).summary.support is not None
        retained.validate()
        saturated.validate()
    finally:
        retained.dispose()
        saturated.dispose()


def test_mahler_action_reads_same_admitted_antihydra_image() -> None:
    for width in (0, 1, 2, 4, 8, 16):
        workspace = AntihydraArithmeticImageWorkspace(ResourceLedger(), width)
        try:
            node = workspace.image_node(workspace.root_payload)
            assert node.source == workspace.root_source
            assert node.action == workspace.root_action
            demand = SourceImageDemand("mahler-associated-action")
            projected = workspace.scheduler.source_projection(
                workspace, workspace.root_image, demand
            ).value
            assert isinstance(projected, SaturatingAffineAction)
            transfer = node.summary.transfer
            expected_scale = ExactRational(transfer.upper, transfer.lower)
            expected_offset = ExactRational(
                -3 * (transfer.upper + transfer.offset - transfer.lower),
                transfer.lower,
            )
            assert projected.scale == expected_scale
            assert projected.offset == expected_offset
            # Independent literal source recurrence and exact Fraction fold.
            value = 8
            scale = Fraction(1)
            offset = Fraction(0)
            cap: Fraction | None = None
            for _ in range(width):
                centered_odd = 1 - (value & 1)
                bit_offset = Fraction(-3 * centered_odd, 2)
                bit_cap = Fraction(3, 4) if centered_odd else Fraction(9, 4)
                transported_cap = (
                    None if cap is None else Fraction(3, 2) * cap + bit_offset
                )
                cap = (
                    bit_cap
                    if transported_cap is None
                    else min(bit_cap, transported_cap)
                )
                offset = Fraction(3, 2) * offset + bit_offset
                scale = Fraction(3, 2) * scale
                value = (3 * value - (value & 1)) // 2
            assert (
                Fraction(projected.scale.numerator, projected.scale.denominator)
                == scale
            )
            assert (
                Fraction(projected.offset.numerator, projected.offset.denominator)
                == offset
            )
            assert (
                None
                if projected.cap is None
                else Fraction(projected.cap.numerator, projected.cap.denominator)
            ) == cap
            if width == 0:
                assert projected.cap is None
            elif width == 1:
                assert projected.cap == ExactRational(3, 4)
            else:
                assert (
                    projected.cap
                    == ExactRational(3, 2) * expected_scale + expected_offset
                )
                assert projected.cap < ExactRational(0)
            workspace.validate()
        finally:
            workspace.dispose()
