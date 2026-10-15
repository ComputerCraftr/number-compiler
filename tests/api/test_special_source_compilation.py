"""Fermat/Mersenne compiler demand ordering and exact output admission."""

from number_compiler.projection.output_quotient import SpecialOutputMode


def test_special_source_compiler_defers_theorems_until_concrete_output_is_demanded() -> (
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

    # Local source geometry resolves only the requested coordinate. Its branch
    # labels carry no proof connecting an arbitrary later value to primality.
    reused = compiler.project_special_branch_values("fermat", 4, 3, 7)
    assert reused.mode is SpecialOutputMode.GUARDED
    assert compiler.theorem_cache_size == 0
    assert compiler.special_constraint_cache_size == 0
    pulled = compiler.resolve_special_theorem("fermat", 4)
    assert pulled.source_guard.failure_bit is None
    assert pulled.primality is not None and pulled.primality.status == "unknown"
    assert compiler.theorem_cache_size == 1

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
