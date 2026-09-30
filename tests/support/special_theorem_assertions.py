"""Fail-closed classification assertions for explicitly deferred special queries."""

from number_compiler.api.sequence_types import SpecialDepthCertificateSummary
from number_compiler.sequences.power_numbers.theorem_query import (
    SpecialTheoremResolution,
)


def assert_unknown_resolution(
    result: SpecialTheoremResolution,
) -> SpecialDepthCertificateSummary:
    assert result.primality is not None and result.primality.status == "unknown"
    assert result.primality.specialization_raw_squarings == 0
    assert not result.primality.decided and result.primality.target_depth is None
    return result.primality
