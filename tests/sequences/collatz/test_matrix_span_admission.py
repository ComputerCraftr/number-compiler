"""Lifecycle checks for the Collatz single-macro matrix workspace."""

from __future__ import annotations

from contextlib import ExitStack

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import (
    AdmittedBoundaryMacroPlan,
)
from number_compiler.sequences.collatz.matrix_span_admission import (
    retain_single_macro_scratch,
)
from number_compiler.sequences.collatz.temporal_border_return_execution import (
    admit_physical_matrix_boundary_plan,
)


def _assert_single_scratch_released(ledger: ResourceLedger) -> None:
    scratch = tuple(
        item
        for item in ledger.snapshot().inventory
        if item.name.startswith("collatz-single-matrix-scratch-")
    )
    assert len(scratch) == 1
    assert scratch[0].disposed
    assert scratch[0].entries == scratch[0].nodes == 0
    assert ledger.entries == ledger.nodes == 0


def test_single_macro_scratch_reservation_refusal_disposes_owner() -> None:
    ledger = ResourceLedger(max_nodes=0)
    plan = admit_physical_matrix_boundary_plan(7, 2, ledger)
    assert plan is not None

    with pytest.raises(BlockContextBudgetExceeded):
        with ExitStack() as scope:
            retain_single_macro_scratch(scope, ledger, 7, plan)

    _assert_single_scratch_released(ledger)


def test_single_macro_scratch_remains_charged_through_construction() -> None:
    ledger = ResourceLedger()
    plan = admit_physical_matrix_boundary_plan(7, 2, ledger)
    assert plan is not None
    with ExitStack() as scope:
        retain_single_macro_scratch(scope, ledger, 7, plan)
        scratch = tuple(
            item
            for item in ledger.snapshot().inventory
            if item.name.startswith("collatz-single-matrix-scratch-")
        )
        assert len(scratch) == 1
        assert not scratch[0].disposed
        assert scratch[0].entries > 0
        assert scratch[0].nodes > 0
    assert ledger.entries == ledger.nodes == 0
    assert all(
        item.disposed
        for item in ledger.snapshot().inventory
        if item.name.startswith("collatz-single-matrix-scratch-")
    )


def test_matrix_span_charges_scratch_before_tape_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import named_border_carry_matrix
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )
    from number_compiler.sequences.collatz.collatz_two_sided_ring import (
        CollatzTwoSidedCylinder,
    )
    from number_compiler.sequences.collatz.matrix_span_admission import (
        admit_matrix_span,
    )
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        NamedBorderCarryMatrix,
    )
    from number_compiler.sequences.collatz.parity_carry_tape_actions import (
        LedgeredParityTapeActions,
    )

    class ConstructionInterrupted(RuntimeError):
        pass

    ledger = ResourceLedger()

    def inspect_workspace(
        _macro: CollatzBoundaryMacro | BorderReturnMacro,
        *,
        source: CollatzTwoSidedCylinder | None = None,
        ledger: ResourceLedger | None = None,
        parity_actions: LedgeredParityTapeActions | None = None,
    ) -> NamedBorderCarryMatrix:
        del source, parity_actions
        assert ledger is not None
        accounts = tuple(
            item
            for item in ledger.snapshot().inventory
            if item.name.startswith("collatz-single-matrix-scratch-")
        )
        assert len(accounts) == 1
        assert accounts[0].entries > 0 and accounts[0].nodes > 0
        raise ConstructionInterrupted("checked reservation before tape binding")

    monkeypatch.setattr(
        named_border_carry_matrix,
        "certify_named_border_carry_matrix",
        inspect_workspace,
    )
    with ExitStack() as scope:
        with pytest.raises(ConstructionInterrupted):
            admit_matrix_span(
                7,
                ledger,
                2,
                parity_actions_factory=lambda: pytest.fail(
                    "single-macro summary must not allocate the parity owner"
                ),
                single_macro_scope=scope,
            )
    assert ledger.entries == ledger.nodes == 0
    assert all(
        item.disposed
        for item in ledger.snapshot().inventory
        if item.name.startswith("collatz-single-matrix-scratch-")
    )


@pytest.mark.parametrize("after_commit", [False, True])
def test_single_macro_scratch_retries_transient_close_failure(
    after_commit: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    plan = admit_physical_matrix_boundary_plan(7, 2, ledger)
    assert plan is not None
    release = ledger.release
    failed = False

    def fail_once(owner: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal failed
        if not failed:
            failed = True
            if after_commit:
                release(owner, entries=entries, nodes=nodes)
            raise RuntimeError("injected reservation release failure")
        release(owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "release", fail_once)
    with pytest.raises(RuntimeError, match="injected reservation release failure"):
        with ExitStack() as scope:
            retain_single_macro_scratch(scope, ledger, 7, plan)

    _assert_single_scratch_released(ledger)


def test_matrix_span_reuses_admission_after_scratch_budget_refusal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import matrix_span_admission
    from number_compiler.sequences.collatz.parity_carry_tape_actions import (
        LedgeredParityTapeActions,
    )

    ledger = ResourceLedger()
    original_admit = admit_physical_matrix_boundary_plan
    admission_count = 0
    factory_count = 0

    def count_admission(
        source: int, remaining: int, owner: ResourceLedger
    ) -> AdmittedBoundaryMacroPlan | None:
        nonlocal admission_count
        admission_count += 1
        return original_admit(source, remaining, owner)

    def refuse_scratch(*_args: object, **_kwargs: object) -> None:
        raise BlockContextBudgetExceeded("injected conservative scratch refusal")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.temporal_border_return_execution.admit_physical_matrix_boundary_plan",
        count_admission,
    )
    monkeypatch.setattr(
        matrix_span_admission, "retain_single_macro_scratch", refuse_scratch
    )

    with LedgeredParityTapeActions(ledger) as actions, ExitStack() as scope:

        def acquire_actions() -> LedgeredParityTapeActions:
            nonlocal factory_count
            factory_count += 1
            return actions

        result = matrix_span_admission.admit_matrix_span(
            7,
            ledger,
            2,
            parity_actions_factory=acquire_actions,
            single_macro_scope=scope,
        )
        assert result is not None
        assert (result.source, result.endpoint) == (7, 11)
        assert admission_count == 1
        assert factory_count == 1
