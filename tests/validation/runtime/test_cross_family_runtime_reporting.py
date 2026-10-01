"""Cross-family scheduler paths whose work owners remain family-specific."""

from __future__ import annotations

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.collatz_images import projected_collatz_runtime_term
from tests.support.reference_arithmetic import literal_reverse_add


def test_public_family_and_radix_paths_report_no_sequential_backend_work() -> None:
    reverse = ReverseAddPoweredTerm(196, 64)
    assert reverse.materialize(max_bits=10_000) == literal_reverse_add(196, 64)
    assert reverse.width() > 0
    assert 0 <= reverse.digit(0) <= 9
    collatz = PoweredCollatzTerm(140137, 11)
    assert collatz.width() > 0
    assert collatz.digit(0) in (0, 1)
    projected_term = projected_collatz_runtime_term(
        seed=140137, index=11, radix=3, checked_position=3
    )
    for term in (reverse, collatz, projected_term):
        metrics = term.metrics()
        assert metrics.sequential_generation_advances == 0
        assert metrics.higher_concrete_operation_evaluations == 0
    assert collect_ledger_metrics(projected_term._ledger).forbidden_future_payloads == 0
