"""Root normalization preserves transport but does not prove a quotient."""

from itertools import product

import pytest

from devtools.verification.decimal_root_tangent_audit import audit_decimal_root_tangent

pytestmark = pytest.mark.validation


def test_all_port_fixed_roots_and_growth_phase_rebase() -> None:
    pairs = tuple(left + left[::-1] for left in product(range(19), repeat=2))
    result = audit_decimal_root_tangent(pairs)
    assert result.source_states == 361
    assert result.fixed_point_checks == result.temporal_rebase_checks == 722
    assert result.phase_rebase_checks == 722
    assert result.fixed_point_failures == 0
    assert result.temporal_rebase_failures == 0
    assert result.phase_rebase_failures == 0


def test_exact_tangent_alias_still_splits_under_successor() -> None:
    result = audit_decimal_root_tangent(
        (
            (0, 0, 0, 0, 0, 0),
            (5, 17, 14, 14, 17, 5),
            (7, 3, 6, 6, 3, 7),
        )
    )
    assert result.alias_fibers == 1
    assert result.exact_successor_conflict_fibers == 1
    assert result.successor_conflict_fibers == 1
    assert result.witness is not None
    assert result.phase_rebase_failures == 0
