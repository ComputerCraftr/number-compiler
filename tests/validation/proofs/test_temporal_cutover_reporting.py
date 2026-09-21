"""Production cutover reporting attests the issued canonical-tile executor."""

from __future__ import annotations

from array import array
from collections.abc import Callable
from typing import Never

import pytest

from devtools.proofs.block_power import compose_block_effects
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.behavior_metrics import _cutover_blocker
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _generic_index() -> HashLifeBlockIndex:
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
        kernel_name="cutover-audit",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    effect = compose_block_effects(
        identity, DigitNormalizeBlockEffect(2), budget=BlockContextBudget()
    )
    return HashLifeBlockIndex(effect, (1, 2), logical_length=4)


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("retired production executor was reached")


def test_generic_composition_reports_issued_tile_executor_cutover() -> None:
    index = _generic_index()
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    assert type(projection._application) is TileApplication
    assert index.direct_powered_point(0) == 1
    before = index._ledger.snapshot()
    report = index.behavior_metrics()
    assert index._ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    assert report.bimachine_composition_certified == 1
    assert report.sequential_generation_advances == 0
    assert report.bounded_temporal_runtime_cutover_complete == 1
    assert report.bounded_temporal_runtime_cutover_blocker == ""
    assert report.temporal_quotient_family == "generic-tile-hashlife"


@pytest.mark.parametrize(
    "constructor,seed,family",
    (
        (ReverseAddPoweredTerm, 196, "reverse-add-tile-hashlife"),
        (PoweredCollatzTerm, 27, "collatz-tile-hashlife"),
    ),
)
def test_certified_family_uses_tile_scheduler_without_legacy_construction(
    constructor: Callable[[int, int], PoweredCollatzTerm | ReverseAddPoweredTerm],
    seed: int,
    family: str,
) -> None:
    term = constructor(seed, 8)
    assert term.digit(0) >= 0
    report = term.behavior_metrics()
    assert report.temporal_quotient_family == family
    assert report.bounded_temporal_runtime_cutover_complete == 1
    assert report.bounded_temporal_runtime_cutover_blocker == ""
    metrics = term.metrics()
    if family == "reverse-add-tile-hashlife":
        assert metrics.tile_causal_direct_parent_transfers > 0
    else:
        assert metrics.tile_scheduler_leaf_function_applications > 0


def test_reverse_tile_route_reports_no_retired_execution_work() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    assert 0 <= term.digit(0) <= 9
    counters = term._ledger.snapshot().counters
    assert counters.get("whole_word_sweeps", 0) == 0
    assert counters.get("sequential_generation_advances", 0) == 0
    assert counters.get("higher_concrete_operation_evaluations", 0) == 0


def test_actual_sequential_work_is_an_independent_cutover_blocker() -> None:
    index = _generic_index()
    index._ledger.bump("sequential_generation_advances")
    report = index.behavior_metrics()
    assert report.bimachine_composition_certified == 1
    assert report.bounded_temporal_runtime_cutover_complete == 0
    assert (
        report.bounded_temporal_runtime_cutover_blocker
        == "sequential_generation_advances"
    )


def test_actual_higher_continuation_work_is_an_independent_cutover_blocker() -> None:
    index = _generic_index()
    index._ledger.bump("higher_concrete_operation_evaluations")
    report = index.behavior_metrics()
    assert report.bounded_temporal_runtime_cutover_complete == 0
    assert report.bounded_temporal_runtime_cutover_blocker == (
        "higher_continuation_execution"
    )


def test_unknown_carrier_cannot_self_attest_with_cutover_attributes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    index = _generic_index()

    class Claim:
        bounded_temporal_runtime_cutover_complete = True

    monkeypatch.setattr(index, "_lazy_application", Claim())
    before = index._ledger.snapshot()
    assert _cutover_blocker(index, 0) == "unattested_execution_carrier"
    assert index._ledger.snapshot() == before
