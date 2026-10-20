"""Universal interface facts cache no source-dependent argument observations."""

from functools import partial

import pytest

from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_finite_admission import (
    FiniteFunctionAdmission,
)
from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import input_expression
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import collatz_continuation_runtime


def test_warm_interface_proof_avoids_range_revalidation() -> None:
    runtime, action = collatz_continuation_runtime()
    admission = runtime.primitive_continuations.admission
    sort = StateSort(action, 1)
    function = input_expression(
        runtime.kernels, runtime.kernel(action).right_count, RIGHT_A
    )
    first = admission.validate(sort, sort, function)
    assert first > 0
    before = runtime.ledger.counters["finite_interface_admission_proof_visits"]
    assert admission.validate(sort, sort, function) == 0
    assert runtime.ledger.counters["finite_interface_admission_proof_visits"] == before
    assert len(admission.memo) == 1
    key = next(iter(admission.memo))
    assert (key.source, key.target, key.function) == (sort, sort, function)


@pytest.mark.parametrize("warm", (False, True))
def test_foreign_and_wrong_port_reject_before_telemetry_or_retention(
    warm: bool,
) -> None:
    runtime, action = collatz_continuation_runtime()
    foreign, foreign_action = collatz_continuation_runtime()
    admission = runtime.primitive_continuations.admission
    sort = StateSort(action, 1)
    valid = input_expression(
        runtime.kernels, runtime.kernel(action).right_count, RIGHT_A
    )
    if warm:
        admission.validate(sort, sort, valid)
    wrong_port = input_expression(
        runtime.kernels, runtime.kernel(action).right_count, LEFT_A
    )
    foreign_function = foreign.kernels.constant(runtime.kernel(action).right_count, 0)
    cases = (
        (sort, sort, foreign_function),
        (StateSort(foreign_action, 1), sort, valid),
        (sort, sort, wrong_port),
        (StateSort(action, True), sort, valid),
        (sort, SymbolSort(3, 2), valid),
    )
    for source, target, function in cases:
        assert_rejected_atomically(
            runtime.ledger,
            partial(admission.validate, source, target, function),
            ValueError,
        )


def test_invalid_admissible_output_code_is_not_certified() -> None:
    runtime, action = collatz_continuation_runtime()
    admission = runtime.primitive_continuations.admission
    sort = StateSort(action, 1)
    assert runtime.kernel(action).right_count == 3
    true = runtime.kernels.functions.constant(True)
    invalid = runtime.kernels.intern_expression(FiniteExpression(3, (true, true)))
    assert_rejected_atomically(
        runtime.ledger, lambda: admission.validate(sort, sort, invalid), ValueError
    )


def test_exhausted_budget_validates_without_retaining_and_eviction_revalidates() -> (
    None
):
    runtime, action = collatz_continuation_runtime()
    admission = FiniteFunctionAdmission(runtime.higher.expressions)
    sort = StateSort(action, 1)
    function = input_expression(
        runtime.kernels, runtime.kernel(action).right_count, RIGHT_A
    )
    runtime.ledger.max_cache_entries = runtime.ledger.entries
    entries = runtime.ledger.entries
    assert admission.validate(sort, sort, function) > 0
    assert len(admission.memo) == 0
    assert runtime.ledger.entries == entries
    runtime.ledger.max_cache_entries = None
    admission.validate(sort, sort, function)
    assert len(admission.memo) == 1
    runtime.ledger.evict_query_memos()
    assert len(admission.memo) == 0
    assert admission.validate(sort, sort, function) > 0
