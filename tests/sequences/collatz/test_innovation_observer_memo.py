from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    select_boundary_macro,
)
from number_compiler.sequences.collatz.innovation_future_moore import (
    innovation_future_moore,
)
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    InnovationObserverMemo,
    innovation_macro_tape,
    innovation_moore_clock,
    observed_innovation_macro_tape,
)


def _macro() -> CollatzBoundaryMacro:
    macro = select_boundary_macro(164, 7)
    assert macro is not None
    return macro


def test_observer_memo_reuses_only_within_its_ledger_scope() -> None:
    ledger = ResourceLedger()
    memo = InnovationObserverMemo(ledger)
    try:
        first = innovation_macro_tape(_macro(), 49, memo=memo)
        hits_before = ledger.counters["collatz_query_local_innovation_observer_hits"]
        second = observed_innovation_macro_tape(_macro(), 49, ledger=ledger, memo=memo)
        assert second == first
        assert (
            ledger.counters["collatz_query_local_innovation_observer_hits"]
            > hits_before
        )
        assert "no cross-query retention" in str(first["cache_scope"])
    finally:
        memo.dispose()

    assert ledger.entries == 0
    assert ledger.nodes == 0
    assert ledger.inventory_owner(memo._owner).disposed
    assert ledger.inventory_owner(memo._scratch_owner).disposed
    with pytest.raises(RuntimeError, match="closed"):
        innovation_macro_tape(_macro(), 49, memo=memo)


def test_observer_budget_refuses_before_constructing_the_clock(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger(max_nodes=1)
    memo = InnovationObserverMemo(ledger)

    def forbidden(*_args: object, **_kwargs: object) -> tuple[str, ...]:
        raise AssertionError("clock construction ran before budget admission")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.innovation_temporal_tape._core_symbols",
        forbidden,
    )
    try:
        with pytest.raises(BlockContextBudgetExceeded):
            innovation_moore_clock("421", 7, memo=memo)
    finally:
        memo.dispose()
    assert ledger.nodes == 0
    assert ledger.entries == 0


@pytest.mark.parametrize("bad_phase", (True, 1.0))
def test_phase_inputs_reject_aliasing_bool_and_float_values(bad_phase: object) -> None:
    clock = innovation_moore_clock("630", 7)
    with pytest.raises(TypeError, match="innovation phase"):
        clock.class_id(cast(int, bad_phase))
    with pytest.raises(TypeError, match="innovation phase"):
        clock.advance(cast(int, bad_phase), 0)
    with pytest.raises(TypeError, match="innovation phase"):
        clock.powered(cast(int, bad_phase), 0)

    future = innovation_future_moore(7)
    with pytest.raises(TypeError, match="innovation phase"):
        future.global_id("630", cast(int, bad_phase))
    with pytest.raises(TypeError, match="innovation phase"):
        future.finite_id("630", cast(int, bad_phase), 0)
    with pytest.raises(TypeError, match="finite Moore control ID"):
        future.finite_representative(0, cast(int, bad_phase))


def test_finite_refinement_uses_global_quotient_dimensions() -> None:
    future = innovation_future_moore(49)
    assert future.class_count == len(future.global_outputs)
    assert future.finite_count(8) > 0
    clock = innovation_moore_clock("421", 49)
    control = future.global_id("421", 10)
    finite_id = future.finite_id("421", 10, 3)
    representative = future.finite_representative(3, finite_id)
    assert future.global_outputs[representative] == future.global_outputs[control]
    assert clock.class_id(10) >= 0


def test_finite_future_horizon_zero_is_the_unobserved_partition() -> None:
    future = innovation_future_moore(7)
    assert future.finite_count(0) == 1
    assert future.finite_id("421", 0, 0) == future.finite_id("989", 6, 0)
    assert future.finite_count(1) == len(set(future.global_outputs))


def test_unissued_dataclass_copies_cannot_alias_or_poison_memo_keys() -> None:
    ledger = ResourceLedger()
    memo = InnovationObserverMemo(ledger)
    try:
        future = innovation_future_moore(7, memo=memo)
        count = future.finite_count(1, memo=memo)
        forged_future = replace(future, global_outputs=((),))
        with pytest.raises(ValueError, match="not issued"):
            forged_future.finite_count(1, memo=memo)
        assert future.finite_count(1, memo=memo) == count

        clock = innovation_moore_clock("630", 7, memo=memo)
        forged_clock = replace(clock, outputs=((),))
        with pytest.raises(ValueError, match="not issued"):
            forged_clock.class_id(0)
        assert clock.class_id(0) >= 0
    finally:
        memo.dispose()
