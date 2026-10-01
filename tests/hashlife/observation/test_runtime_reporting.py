"""Runtime accounting for generic HashLife point-response reuse."""

from __future__ import annotations

import pytest


@pytest.mark.validation
def test_generic_tile_point_retains_response_and_preserves_replay() -> None:
    from array import array

    from devtools.verification.block_power import compose_block_effects
    from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )
    from number_compiler.hashlife.observation.tile_projection import LazyProjection
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    identity = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0] * 4),
        outputs=bytes(range(4)),
        kernel_name="runtime-image-audit",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    effect = compose_block_effects(
        identity, DigitNormalizeBlockEffect(2), budget=BlockContextBudget()
    )
    index = HashLifeBlockIndex(effect, (1, 2), logical_length=4)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    assert index.direct_powered_point(0) == 1
    cold = index.metrics()
    cold_counters = cold.resource_work_counters
    assert cold_counters["point_response_requests"] == 1
    assert cold_counters["point_response_evaluations"] == 1
    assert cold_counters.get("point_response_cache_hits", 0) == 0
    assert cold.retained_point_response_scalars == 1
    assert collect_ledger_metrics(index._ledger).resource_audit_complete == 1
    assert cold.resource_accounting_mismatch == 0
    before = dict(index._ledger.counters)
    assert index.direct_powered_point(0) == 1
    after = index._ledger.counters
    assert after["point_response_requests"] == before["point_response_requests"] + 1
    assert (
        after["point_response_cache_hits"]
        == before.get("point_response_cache_hits", 0) + 1
    )
    assert after["point_response_evaluations"] == before["point_response_evaluations"]
