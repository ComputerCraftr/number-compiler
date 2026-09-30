from __future__ import annotations

import pytest

from devtools.verification.decimal_clock_cylinder_audit import (
    audit_decimal_clock_cylinder,
    audit_seed_196_births,
)


@pytest.mark.validation
def test_broad_decimal_clock_cylinder_recurrence_and_source_death() -> None:
    audit = audit_decimal_clock_cylinder()
    assert audit.seeds == 41
    assert audit.transitions == audit.events == 3_936
    assert audit.source_positions == 88_930
    assert audit.spatial_compositions == 84_994
    assert audit.leaf_cylinder_classes == 3
    # The first number is trajectory-specific. The second is the stronger,
    # phase-neutral statement about the operator itself and differs by one.
    assert audit.evaluated_source_death_max == 8
    assert audit.neutral_kernel_death_max == 9


@pytest.mark.validation
def test_seed_196_has_4096_carry_owned_births() -> None:
    audit_seed_196_births()
