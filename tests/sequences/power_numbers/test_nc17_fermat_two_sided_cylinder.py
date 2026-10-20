"""Exact NC17 Fermat CRT/sturmian/2w source join and failure-to-close gates."""

from dataclasses import replace
from unittest.mock import patch

import pytest

from number_compiler.arithmetic.carry.signed_phase import signed_phase_fold
from number_compiler.arithmetic.fields.integer_cylinder import IntegerCylinder
from number_compiler.sequences.power_numbers import (
    three_power_two_sided_cylinder as two_sided_cylinder,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.terminal_source_demand import (
    SourceTerminalDemand,
)
from number_compiler.sequences.power_numbers.three_power_temporal_source_morphism import (
    FermatSourceOptions,
)
from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
    ExactAffineSourceCylinder,
    FermatTwoSidedSourceCylinder,
    SignedCylinderFiber,
    crt_join,
)
from tests.support.exact_integer_power import exact_integer_power

_SMALL_TERMINAL: FermatSourceOptions = {
    "phase_binary_places": 8,
    "phase_decimal_places": 2,
    "low_binary_places": 4,
    "low_decimal_places": 2,
    "high_binary_places": 4,
    "high_decimal_places": 2,
}
_SMALL_AMBIGUOUS: FermatSourceOptions = {
    "phase_binary_places": 4,
    "phase_decimal_places": 1,
    "low_binary_places": 3,
    "low_decimal_places": 1,
    "high_binary_places": 2,
    "high_decimal_places": 1,
}


def test_exact_crt_and_affine_cylinder_do_not_invent_sources() -> None:
    for a, m, b, n in ((1, 8, 1, 10), (3, 16, 3, 100), (7, 8, 5, 9)):
        residue, modulus = crt_join(a, m, b, n)
        assert all(
            (x % modulus == residue) == (x % m == a and x % n == b) for x in range(2000)
        )
    with pytest.raises(ArithmeticError, match="disagree"):
        crt_join(0, 4, 1, 2)
    for modulus in (1, 3, 5, 8, 15, 30):
        for residue in range(modulus):
            c = ExactAffineSourceCylinder(1, 120, residue, modulus)
            assert not hasattr(c, "__dict__")
            expected = tuple(i for i in range(1, 121) if i % modulus == residue)
            assert c.enumerated(4096) == expected
            translated = c.multiply_three()
            assert translated.modulus == 3 * modulus
            assert translated.count == len(expected)
            assert translated.enumerated(4096) == tuple(3 * x for x in expected)
            narrowed = translated.intersect_interval(25, 210)
            assert (narrowed.enumerated(4096) if narrowed else ()) == tuple(
                3 * x for x in expected if 25 <= 3 * x <= 210
            )
            joined = c.intersect_congruence(5, 7)
            assert (joined.enumerated(4096) if joined else ()) == tuple(
                x for x in expected if x % 7 == 5
            )


def test_terminal_small_fiber_reconstructs_signed_phase_without_pepin_replay() -> None:
    cylinder = FermatNumberSpec(2).demand_three_power_two_sided_source_cylinder(
        3, **_SMALL_TERMINAL
    )
    assert cylinder.producer_verified
    assert cylinder.exact_interval is not None and cylinder.exact_interval.count == 1
    assert cylinder.exact_interval.first == 3**8
    fibers = cylinder.bounded_phase_fibers()
    assert fibers is not None and len(fibers) == 1
    assert fibers[0].signed_source == 16 and fibers[0].signed_output == (3 * 16) % 17
    assert cylinder.signed_fold_if_forced() == 16
    assert cylinder.terminal_predicate() == "PRIME"
    for boundary in range((3**8).bit_length() + 1):
        # The incoming carry is determined from the exact suffix.
        assert cylinder.ingress_options(boundary) == (
            3 * ((3**8) % (1 << boundary)) >> boundary,
        )
    moved = cylinder.transported_target()
    assert moved is not None and moved.modulus == 3 * cylinder.combined_modulus
    assert moved.contains(3**9) and moved.count == 1
    joint = FermatNumberSpec(2).demand_three_power_source_restricted_phase(
        3, **_SMALL_TERMINAL
    )
    assert joint.producer_verified and joint.source_to_global_fold_proven
    assert joint.complete_signed_fold == 16 and joint.terminal_status == "PRIME"
    complete_histograms = joint.complete_histograms
    assert complete_histograms is not None
    assert signed_phase_fold(complete_histograms[0], 4) == 16


def test_ambiguous_small_fiber_rejects_false_moore_merge() -> None:
    action = FermatNumberSpec(3).demand_three_power_signed_border_action(
        3, **_SMALL_AMBIGUOUS
    )
    cylinder = action.demand_two_sided_source_cylinder()
    assert cylinder.exact_interval is not None
    # The global mod-99 clock rejects ten former low-CRT alternatives.
    # This finite cylinder becomes a singleton, unlike the older observer.
    assert cylinder.candidate_count == 1
    fibers = cylinder.bounded_phase_fibers()
    assert fibers is not None and len(fibers) == 1
    assert fibers[0].signed_source == 3**8 % 257
    assert cylinder.signed_fold_if_forced() == 3**8 % 257
    assert cylinder.terminal_predicate() == "UNKNOWN"  # not terminal level
    joint = action.demand_source_restricted_phase_relation()
    assert joint.producer_verified and joint.source_to_global_fold_proven
    assert joint.complete_signed_fold == 3**8 % 257


def test_f4_f5_open_interior_and_binary_65_carry_forcing() -> None:
    for n, level in ((4, 14), (4, 15), (5, 30), (5, 31)):
        source = FermatNumberSpec(n).demand_three_power_signed_border_action(level)
        joint = source.demand_source_restricted_phase_relation()
        assert joint.producer_verified
        assert not joint.source_to_global_fold_proven
        assert joint.complete_histograms is None
        assert joint.complete_signed_fold is None
        assert joint.terminal_status == "UNKNOWN"
        assert joint.cylinder.combined_modulus == (1 << 64) * 5**6 * 99
        binary_bank = source.origin.binary_phase_bank
        decimal_bank = source.origin.decimal_phase_bank
        assert binary_bank is not None and decimal_bank is not None
        assert joint.cylinder.combined_residue % (1 << 64) == binary_bank.source_prefix
        assert joint.cylinder.combined_residue % 10**6 == decimal_bank.source_prefix
        assert joint.phase.symbolic_unknown_site_count > 1000
        assert (
            source.blocks[-1].start,
            joint.cylinder.ingress_options(source.blocks[-1].start),
        ) in joint.boundary_domains
    f5 = FermatNumberSpec(5).demand_three_power_source_restricted_phase(31)
    assert (
        f5.cylinder.exact_interval is None
    )  # never constructs billions of source bits
    assert f5.cylinder.ingress_options(64) == (1,)
    assert f5.cylinder.ingress_options(65) == (0, 2)
    assert f5.cylinder.ingress_options(66) == (0, 1, 2)
    with patch.object(
        FermatTwoSidedSourceCylinder,
        "bounded_phase_fibers",
        side_effect=AssertionError("carry projection built phase histories"),
    ):
        assert f5.cylinder.ingress_options(65) == (0, 2)
    assert f5.cylinder.transported_target() is None
    assert f5.cylinder.terminal_predicate() == "UNKNOWN"
    assert (65, (0, 2)) in f5.boundary_domains
    assert f5.cylinder.source.leading_resets_carry
    assert len(f5.cylinder.source.admissible_edges[-1]) == 2
    assert f5.cylinder.source.blocks[-1].emitted_value(
        0, 2
    ) != f5.cylinder.source.blocks[-1].emitted_value(1, 2)
    with pytest.raises(ValueError, match="limit"):
        f5.cylinder.bounded_phase_fibers(0)
    with pytest.raises(ValueError, match="limit"):
        f5.cylinder.ingress_options(64, 0)


def test_unissued_mutation_is_rejected_at_both_ports() -> None:
    joint = FermatNumberSpec(3).demand_three_power_source_restricted_phase(
        3, **_SMALL_AMBIGUOUS
    )
    assert joint.producer_verified
    fake = replace(joint)
    assert not fake.producer_verified
    with pytest.raises(ValueError, match="unissued"):
        _ = fake.complete_signed_fold
    cylinder = joint.cylinder
    assert not replace(cylinder).producer_verified
    assert not replace(
        cylinder,
        combined_residue=(cylinder.combined_residue + 1) % cylinder.combined_modulus,
    ).producer_verified
    with pytest.raises(ValueError, match="unissued"):
        replace(cylinder).bounded_phase_fibers()


@pytest.mark.parametrize(
    "candidate",
    (4, pytest.param(5, marks=pytest.mark.validation)),
)
def test_terminal_last_five_join_does_not_promote_source_harmonic_to_prime(
    candidate: int,
) -> None:
    demand = SourceTerminalDemand.for_candidate("fermat", candidate)
    rows = demand.observe_fermat_source_restricted_phase()
    assert len(rows) == 5 and all(row.producer_verified for row in rows)
    assert [row.phase.source_level for row in rows] == list(
        range(demand.source_level - 4, demand.source_level + 1)
    )
    assert all(row.terminal_status == "UNKNOWN" for row in rows)
    assert all(not row.source_to_global_fold_proven for row in rows)
    for row in rows:
        decimal_bank = row.cylinder.source.origin.decimal_phase_bank
        assert decimal_bank is not None
        assert row.cylinder.combined_residue % 10**6 == decimal_bank.source_prefix


def test_terminal_status_uses_complete_histograms_beyond_default_fiber_limit() -> None:
    bounded_fibers = FermatTwoSidedSourceCylinder.bounded_phase_fibers
    fiber_query_count = 0

    def count_fiber_queries(
        cylinder: FermatTwoSidedSourceCylinder, limit: int = 64
    ) -> tuple[SignedCylinderFiber, ...] | None:
        nonlocal fiber_query_count
        fiber_query_count += 1
        return bounded_fibers(cylinder, limit)

    with patch.object(
        FermatTwoSidedSourceCylinder,
        "bounded_phase_fibers",
        count_fiber_queries,
    ):
        joint = FermatNumberSpec(3).demand_three_power_source_restricted_phase(
            7,
            max_fibers=4096,
            inward_boundaries=0,
            phase_binary_places=178,
            phase_decimal_places=1,
            low_binary_places=12,
            low_decimal_places=1,
            high_binary_places=1,
            high_decimal_places=1,
        )
    assert joint.producer_verified
    assert fiber_query_count == 1
    histograms = joint.complete_histograms
    assert histograms is not None and len(histograms) > 64

    # If candidate×source-width exceeds the existing operand-work ceiling,
    # carry projection must keep its conservative port set without allocating
    # every represented source integer.
    with (
        patch.object(two_sided_cylinder, "MAX_PHASE_FIBER_BIT_WORK", 0),
        patch.object(
            IntegerCylinder,
            "enumerated",
            side_effect=AssertionError("over-budget source cylinder was enumerated"),
        ),
    ):
        assert joint.cylinder.ingress_options(179, 4096)

    signed_folds = tuple(
        signed_phase_fold(row, joint.phase.fold_width) for row in histograms
    )
    terminal_residue = 1 << joint.phase.fold_width
    if all(value == terminal_residue for value in signed_folds):
        expected = "PRIME"
    elif all(value != terminal_residue for value in signed_folds):
        expected = "COMPOSITE"
    else:
        expected = "UNKNOWN"

    # The relation has already authenticated these complete rows. Its status
    # query must consume them, not silently re-enumerate the cylinder with the
    # unrelated default limit of 64.
    with patch.object(
        FermatTwoSidedSourceCylinder,
        "bounded_phase_fibers",
        side_effect=AssertionError("terminal status re-enumerated source fibers"),
    ):
        assert joint.terminal_status == expected


def test_only_source_bound_actions_run_no_candidate_squares() -> None:
    import builtins

    original_pow = exact_integer_power
    candidate = (1 << 32) + 1

    def guarded_pow(base: int, exponent: int, modulus: int | None = None) -> int:
        if modulus == candidate and (base != 2 or exponent > 64):
            raise AssertionError("candidate-modulus source exponentiation is forbidden")
        return (
            original_pow(base, exponent)
            if modulus is None
            else original_pow(base, exponent, modulus)
        )

    with patch.object(builtins, "pow", guarded_pow):
        joint = FermatNumberSpec(5).demand_three_power_source_restricted_phase(31)
        assert joint.producer_verified and joint.terminal_status == "UNKNOWN"
        assert (65, (0, 2)) in joint.boundary_domains


def test_demanded_inward_refinement_fixes_binary_carry_without_f5_source_replay() -> (
    None
):
    initial = FermatNumberSpec(5).demand_three_power_source_restricted_phase(31)
    assert initial.cylinder.ingress_options(65) == (0, 2)
    nxt = initial.refine_inward()
    assert nxt.producer_verified
    assert nxt.cylinder.binary_low_bits == 65
    assert nxt.cylinder.ingress_options(65) == (2,)
    # Independent *small-modulus* cyclotomic oracle, not candidate modulus.
    residue = pow(3, 1 << 31, 1 << 65)
    assert nxt.cylinder.ingress_options(65) == ((3 * residue) >> 65,)
    assert (
        nxt.phase.symbolic_unknown_site_count
        == initial.phase.symbolic_unknown_site_count - 1
    )
    deeper = nxt.refine_inward(additional_binary_places=7)
    assert deeper.cylinder.binary_low_bits == 72
    assert deeper.cylinder.ingress_options(72) == (1,)
    assert deeper.terminal_status == "UNKNOWN"
    assert deeper.complete_signed_fold is None
    with pytest.raises(ValueError, match="unissued"):
        replace(initial).refine_inward()
    with pytest.raises(ValueError, match="budget"):
        deeper.refine_inward(additional_binary_places=257)


def test_inward_refinement_preserves_requested_interior_islands() -> None:
    source = FermatNumberSpec(4).demand_three_power_signed_border_action(
        14,
        binary_windows=((512, 8),),
        decimal_windows=((60, 3),),
    )
    known_before = {
        b.start: (b.width, b.source_value) for b in source.blocks if b.known
    }
    assert 512 in known_before
    refined = source.demand_inward_source_refinement(additional_binary_places=5)
    assert refined.producer_verified
    refined_binary_bank = refined.origin.binary_phase_bank
    refined_decimal_bank = refined.origin.decimal_phase_bank
    source_decimal_bank = source.origin.decimal_phase_bank
    assert refined_binary_bank is not None
    assert refined_decimal_bank is not None and source_decimal_bank is not None
    assert refined_binary_bank.depth == 69
    assert any(
        b.start <= 512 and b.start + b.width >= 520 and b.known for b in refined.blocks
    )
    assert refined_decimal_bank.depth == source_decimal_bank.depth
    j = refined.demand_source_restricted_phase_relation()
    assert j.producer_verified and not j.source_to_global_fold_proven
