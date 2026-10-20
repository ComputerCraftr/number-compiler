"""The former recursive radix replay backend must stay deleted."""

from typing import cast

import pytest

from number_compiler.projection.lazy_radix import RadixProjection, collatz_radix_digit
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.performance_assertions import performance_bound
from tests.support.radix_projection import microblock_cache, radix_projection


def test_recursive_radix_replay_backend_is_absent() -> None:
    forbidden = (
        "_program",
        "_point",
        "_range",
        "_evaluate",
        "_memoizable",
        "_remember",
        "_programs",
        "_ranges",
    )
    assert all(not hasattr(RadixProjection, name) for name in forbidden)


@pytest.mark.validation
def test_former_134m_request_fixture_is_bounded_block_work() -> None:
    """Run the complete 14-digit public regression and accounting audit."""
    term = PoweredCollatzTerm(140137, 11)
    with performance_bound(35, "seed 140137 step 11 radix-3 bounded block projection"):
        digits: list[int | str] = []
        for index in range(14):
            try:
                digits.append(collatz_radix_digit(term, 3, index))
            except IndexError:
                digits.append("exterior")
    assert digits == [2, 2, 2, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, "exterior"]
    counters = term.resource_ledger.counters
    assert counters.get("radix_microblock_source_bits", 0) == 0
    assert counters.get("radix_microblock_division_bits", 0) == 0
    assert counters.get("radix_division_input_bits_covered", 0) == 0
    assert counters.get("radix_microblock_limb_divisions", 0) == 0
    assert counters.get("radix_microblock_stage_evaluations", 0) == 0
    assert counters.get("radix_provider_digit_evaluations", 0) == 13
    assert counters.get("radix_provider_digit_requests", 0) == 14
    assert counters.get("radix_source_bit_visits", 0) == 0
    assert counters.get("collatz_image_radix_demands", 0) > 0
    assert counters.get("collatz_image_projection_operand_bits", 0) > 0
    assert counters.get("source_image_publications", 0) > 0
    assert counters.get("concrete_virtual_interface_evaluations", 0) == 0
    assert counters.get("higher_runtime_summary_publications", 0) == 0
    projection = radix_projection(term, 3)
    observation = object.__getattribute__(projection, "_tile_observation")
    assert observation is None
    assert term.operator_nodes == 0
    assert counters.get("source_image_primitive_applications", 0) > 0
    assert counters.get("microblock_entry_high_water", 0) <= 64
    cache_owner = microblock_cache(term)
    cache = cache_owner.audit_snapshot()
    assert cache.payload_bytes <= cache_owner.MAX_PAYLOAD_BYTES
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1


def test_repeat_digit_is_a_microblock_hit_without_stage_replay() -> None:
    term = PoweredCollatzTerm(140137, 11)
    assert collatz_radix_digit(term, 3, 12) == 1
    before = term.resource_ledger.counters.copy()
    assert collatz_radix_digit(term, 3, 12) == 1
    after = term.resource_ledger.counters
    assert after.get("radix_provider_digit_evaluations", 0) == before.get(
        "radix_provider_digit_evaluations", 0
    )
    assert after.get("radix_microblock_division_bits", 0) == before.get(
        "radix_microblock_division_bits", 0
    )
    assert after.get("radix_microblock_limb_divisions", 0) == before.get(
        "radix_microblock_limb_divisions", 0
    )
    assert after.get("microblock_hits", 0) > before.get("microblock_hits", 0)


def test_projection_constructor_still_rejects_invalid_dimensions() -> None:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
    from number_compiler.resources.ledger import ResourceLedger

    for radix, width, error in (
        (True, 3, TypeError),
        (3.0, 3, TypeError),
        (3, True, TypeError),
        (1, 3, UnsupportedInterfaceError),
        (3, 0, ValueError),
        (3, -1, ValueError),
    ):
        with pytest.raises(error):
            RadixProjection(cast("int", radix), width, ResourceLedger())
