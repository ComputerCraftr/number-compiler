"""Local digit/halo labels cannot authenticate a primality result."""

import pytest

from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.projection.output_quotient import (
    SpecialBranchMask,
    SpecialOutputMode,
)


@pytest.mark.parametrize("family,parameter", [("fermat", 5), ("mersenne", 11)])
def test_relabelled_source_digits_do_not_publish_theorem_evidence(
    family: str,
    parameter: int,
) -> None:
    compiler = CanonicalSequenceCompiler()
    for pass_digit, fail_digit in ((1, 0), (0, 1)):
        digit = compiler.project_special_digit(
            family, parameter, 0, pass_digit, fail_digit
        )
        assert digit.value == 1
        assert compiler.special_constraint_cache_size == 0
        assert compiler.theorem_cache_size == 0
        assert (
            compiler.project_special_branch_values(family, parameter, 3, 7).mode
            is SpecialOutputMode.GUARDED
        )


def test_local_mask_cannot_poison_a_verified_composite_support() -> None:
    compiler = CanonicalSequenceCompiler()
    compiler.pullback_special_defect(
        "fermat", 5, (1 << 32) + 1, 641, method="proper-divisor"
    )
    for bits in (1, 2):
        local = compiler.project_special_branch_values(
            "fermat", 5, 10, 20, mask=SpecialBranchMask(bits)
        )
        assert local.value == (10 if bits == 1 else 20)
        assert compiler.project_special_branch_values("fermat", 5, 3, 7).value == 7
    result = compiler.resolve_special_theorem("fermat", 5)
    assert result.source_guard.failure_bit is True
    assert result.factor_witness == 641


@pytest.mark.parametrize("defect", [0, 1, 3, 65537])
def test_arbitrary_defects_cannot_authenticate_a_prime_branch(defect: int) -> None:
    compiler = CanonicalSequenceCompiler()
    with pytest.raises(ValueError, match="proper candidate divisor"):
        compiler.pullback_special_defect(
            "fermat", 4, 65537, defect, method="claimed-certified-recurrence"
        )
    assert compiler.special_constraint_cache_size == 0
    assert compiler.theorem_cache_size == 0
    assert compiler.project_special_branch_values("fermat", 4, 3, 7).mode is (
        SpecialOutputMode.GUARDED
    )
