from collections.abc import Iterable, Sequence
from typing import cast

import pytest

from number_compiler.arithmetic.fields.idempotent_output import (
    IdempotentCyclotomicDigitBlock,
    IdempotentModElement,
    IdempotentSpecialDigitBlock,
)
from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.projection.output_quotient import (
    BinaryOutputCoordinate,
    SpecialOutputMode,
    audit_binary_source_factor,
    minimize_projection_machine,
    output_fiber_quotient,
)


def test_idempotent_rank_two_arithmetic_specializes_exactly_on_all_crt_sheets() -> None:
    modulus = 15
    x = IdempotentModElement(modulus, 4, 7)
    y = IdempotentModElement(modulus, 8, 11)
    for e in (0, 1, 6, 10):
        xv = x.specialize_idempotent(e)
        yv = y.specialize_idempotent(e)
        assert x.add(y).specialize_idempotent(e) == (xv + yv) % modulus
        assert x.subtract(y).specialize_idempotent(e) == (xv - yv) % modulus
        assert x.multiply(y).specialize_idempotent(e) == xv * yv % modulus
        assert x.square().specialize_idempotent(e) == xv * xv % modulus
    with pytest.raises(ValueError, match="not-idempotent"):
        x.specialize_idempotent(2)


def test_sheet_conversion_and_shared_quadratic_power_need_no_parallel_power_kernel() -> (
    None
):
    modulus = 65537
    value = IdempotentModElement.from_sheets(modulus, 3, 5)
    assert value.sheets == (3, 5)
    powered = QuadraticPower(4).apply_iterated(value, step=lambda item: item.square())
    assert powered.sheets == (
        pow(3, 1 << 4, modulus),
        pow(5, 1 << 4, modulus),
    )


def test_unified_cyclotomic_digit_block_lifts_componentwise_and_specializes() -> None:
    zero = CyclotomicDigitBlock.from_coefficients((2, 3), order=2, modulus=15)
    one = CyclotomicDigitBlock.from_coefficients((7, 4), order=2, modulus=15)
    lifted = IdempotentCyclotomicDigitBlock(zero, one)
    squared = lifted.square().add_constant(3)
    assert squared.zero_sheet.residue == zero.square().add_constant(3).residue
    assert squared.one_sheet.residue == one.square().add_constant(3).residue

    # e=6 is a genuine nontrivial idempotent modulo 15.  Specialization is
    # coefficientwise interpolation in the existing cyclotomic ring.
    specialized = lifted.specialize_idempotent(6)
    expected = zero.add(one.subtract(zero).scale_coefficients(6))
    assert specialized.residue == expected.residue


def test_output_fibers_are_minimal_for_one_shot_projection_but_not_assumed_temporal_state() -> (
    None
):
    quotient = output_fiber_quotient((3, 3, 7, 3, 7))
    assert quotient.state_count == 2
    assert quotient.fibers == ((0, 1, 3), (2, 4))

    # State 0 and 1 emit the same value now, but their successors emit different
    # values.  Successor refinement must split them before powering.
    machine = minimize_projection_machine((1, 1, 1, 0), (2, 3, 2, 3))
    assert machine.initial_state_count == 2
    assert machine.state_count == 3
    assert machine.refinements == 1
    assert not machine.output_fibers_successor_closed


def test_boolean_output_coordinate_requires_factor_through_proof_and_has_three_modes() -> (
    None
):
    separating = audit_binary_source_factor((False, False, True, True), (3, 3, 7, 7))
    coordinate = BinaryOutputCoordinate.from_factor_audit(separating)
    assert coordinate.mode is SpecialOutputMode.GUARDED
    assert coordinate.derivative == 4
    assert coordinate.quotient_states == 2
    assert coordinate.recover_source_bit(3) is False
    assert coordinate.recover_source_bit(7) is True
    assert coordinate.resolve(True).mode is SpecialOutputMode.RESOLVED
    assert coordinate.resolve(True).value == 7
    with pytest.raises(ValueError, match="no concrete value"):
        _ = coordinate.value

    collapsed = BinaryOutputCoordinate.from_factor_audit(
        audit_binary_source_factor((False, True), (5, 5))
    )
    assert collapsed.mode is SpecialOutputMode.CONCRETE
    assert collapsed.quotient_states == 1
    assert collapsed.derivative == 0
    assert collapsed.value == 5

    insufficient = audit_binary_source_factor((False, False, True), (3, 4, 7))
    assert not insufficient.factors_through_source_bit
    with pytest.raises(ValueError, match="not proved to factor"):
        BinaryOutputCoordinate.from_factor_audit(insufficient)

    # Keep arbitrary CRT idempotents out of the global Boolean sheet API.
    with pytest.raises(TypeError, match="literal bool"):
        audit_binary_source_factor(
            cast("Sequence[bool] | Iterable[bool]", (False, 6)), (3, 7)
        )
    with pytest.raises(TypeError, match="failure_bit"):
        from number_compiler.projection.output_quotient import SpecialSourceGuard

        SpecialSourceGuard(
            "mersenne", 11, cast("bool | None", 6), "invalid-crt-as-boolean"
        )
    with pytest.raises(TypeError, match="resolved_bit"):
        BinaryOutputCoordinate(3, 7, cast("bool | None", 6))
    with pytest.raises(TypeError, match="source_bit"):
        coordinate.resolve(cast("bool", 6))


def test_digit_length_and_carry_are_evaluated_after_nontrivial_idempotent_specialization() -> (
    None
):
    # M11 = 23*89.  This idempotent is 1 mod 23 and 0 mod 89.
    modulus = 2047
    e = 1335
    assert e * e % modulus == e
    block = IdempotentSpecialDigitBlock(
        "mersenne",
        11,
        IdempotentModElement.generator(modulus),
    )

    # For the formal generator E, Boolean endpoints are 0 and 1.  They agree
    # on bit 10, canonical length, and LL end-around carry.  The nontrivial CRT
    # specialization disagrees on all three, so endpoint equality alone is not
    # a valid nonlinear-observer quotient.
    assert block.endpoint_digit_pair(10) == (0, 0)
    assert block.digit_at_idempotent(10, e) == 1
    assert block.endpoint_length_pair() == (1, 1)
    assert block.length_at_idempotent(e) == 11
    assert block.endpoint_square_boundary_carries() == (-1, -1)
    assert block.square_boundary_carry_at_idempotent(e) == 4


def test_source_compiler_is_theorem_free_and_cheap_shapes_resolve_impossible_sheets_first() -> (
    None
):
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.api.sequence_types import (
        FermatSequenceSpec,
        MersenneSequenceSpec,
    )
    from number_compiler.projection.output_quotient import SpecialSourceShape

    compiler = CanonicalSequenceCompiler()
    f2, f4, f5 = compiler.compile(FermatSequenceSpec((2, 4, 5), test_through=5)).terms
    for term in (f2, f4, f5):
        assert term.primality is None and term.factor_witness is None
        assert term.source_guard is None and term.projection_method == "deferred"
    assert compiler.theorem_cache_size == 0

    # F4 has length 17 and binary support {0,16}.  If a lifted branch claims a
    # different source digit or length, the source geometry kills it before a
    # primality query exists.
    shape = SpecialSourceShape("fermat", 4)
    assert shape.bit_length == 17 and shape.boundary_sign == -1
    assert [shape.digit(i) for i in (0, 1, 15, 16, 17)] == [1, 0, 0, 1, 0]
    digit = compiler.project_special_digit("fermat", 4, 16, 1, 0)
    assert digit.mode is SpecialOutputMode.RESOLVED and digit.value == 1
    parity = compiler.project_special_parity("fermat", 4, 17, 16)
    assert parity.mode is SpecialOutputMode.RESOLVED and parity.value == 1
    length = compiler.project_special_length("fermat", 4, 17, 16)
    assert length.mode is SpecialOutputMode.RESOLVED and length.value == 17
    carry = compiler.project_special_carry("fermat", 4, 2, 2, 9)
    assert carry.mode is SpecialOutputMode.RESOLVED and carry.value == 2
    boundary = compiler.project_special_boundary_sign("fermat", 4, -1, 1)
    assert boundary.mode is SpecialOutputMode.RESOLVED and boundary.value == -1
    assert compiler.theorem_cache_size == 0

    # The first cheap digit constraint resolved the PASS sheet and is retained as
    # the source's two-bit tropical kernel.  Later separating coordinates reuse
    # that proof immediately instead of asking the theorem again.
    reused = compiler.project_special_branch_values("fermat", 4, 3, 7)
    assert reused.mode is SpecialOutputMode.RESOLVED and reused.value == 3
    assert compiler.theorem_cache_size == 0
    assert compiler.special_constraint_cache_size >= 1
    pulled = compiler.resolve_special_theorem("fermat", 4)
    assert pulled.projection_method == "pulled-back-output-constraint"
    assert pulled.primality is None and pulled.source_guard.failure_bit is False
    assert compiler.theorem_cache_size == 0

    # A powered theorem-sensitive block may instead expose a candidate-ring
    # defect.  Its support is accumulated as one gcd, not a list of factor
    # slots.  F5 = 641 * 6700417, so this proved support packet resolves the
    # composite sheet with zero Pépin work and persists for later outputs.
    support = CanonicalSequenceCompiler()
    f5_modulus = (1 << 32) + 1
    state = support.pullback_special_defect(
        "fermat",
        5,
        f5_modulus,
        641,
        method="powered-target-defect",
    )
    assert state.support_gcd == 641 and state.support_modulus == f5_modulus
    support_result = support.resolve_special_theorem("fermat", 5)
    assert support_result.projection_method == "pulled-back-support-defect"
    assert support_result.source_guard.failure_bit is True
    assert support_result.factor_witness == 641
    assert support.theorem_cache_size == 0
    assert support.project_special_branch_values("fermat", 5, 3, 7).value == 7

    # With no previously accumulated constraint, the same coordinate remains
    # guarded until a concrete answer is explicitly demanded.
    fresh = CanonicalSequenceCompiler()
    guarded = fresh.project_special_branch_values("fermat", 4, 3, 7)
    assert guarded.mode is SpecialOutputMode.GUARDED
    assert fresh.theorem_cache_size == 0
    resolved = fresh.project_special_branch_values(
        "fermat",
        4,
        3,
        7,
        require_concrete=True,
    )
    assert resolved.mode is SpecialOutputMode.RESOLVED and resolved.value == 3
    assert fresh.theorem_cache_size == 1

    m11, m13, m15 = compiler.compile(
        MersenneSequenceSpec((11, 13, 15), test_through=15)
    ).terms
    for mersenne_term in (m11, m13, m15):
        assert mersenne_term.source_guard is None and mersenne_term.primality is None
    mshape = SpecialSourceShape("mersenne", 13)
    assert mshape.bit_length == 13 and mshape.boundary_sign == 1
    assert all(mshape.digit(i) == 1 for i in range(13)) and mshape.digit(13) == 0

    # The old theorem outcomes are still available, but only through the
    # separately cached demand boundary.
    assert (
        compiler.resolve_special_theorem("fermat", 2).source_guard.failure_bit is False
    )
    assert (
        compiler.resolve_special_theorem("fermat", 5).source_guard.failure_bit is True
    )
    assert (
        compiler.resolve_special_theorem("mersenne", 11).source_guard.failure_bit
        is True
    )
    assert (
        compiler.resolve_special_theorem("mersenne", 13).source_guard.failure_bit
        is False
    )
    assert (
        compiler.resolve_special_theorem("mersenne", 15).source_guard.failure_bit
        is True
    )
