"""Independent checks for the gated packed five-reversal candidate."""

from __future__ import annotations

import sys
from collections.abc import Callable

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import five_reverse as metrics
from number_compiler.sequences.five_reverse.bitplane_two_step import (
    execute_bitplane_five,
)
from number_compiler.sequences.five_reverse.packed_two_step import (
    PackedFiveWork,
    execute_packed_five,
)
from number_compiler.sequences.five_reverse.source_adapter import (
    FiveReverseAction,
    FiveReverseSource,
    FiveReverseSourceAdapter,
)
from number_compiler.sequences.five_reverse.term import FiveReverseTerm


def _literal(seed: int, steps: int) -> tuple[int, int]:
    value = seed
    reads = 0
    for _ in range(steps):
        digits = str(value)
        reads += len(digits)
        value = 5 * int(digits[::-1])
    return value, reads


@pytest.mark.parametrize("seed", [0, 1, 6, 10, 30, 50, 73, 196, 250, 909090])
@pytest.mark.parametrize("steps", [0, 1, 2, 3, 16, 17, 64, 65, 128, 129])
@pytest.mark.parametrize("execute", [execute_packed_five, execute_bitplane_five])
def test_packed_candidate_matches_literal(
    seed: int,
    steps: int,
    execute: Callable[[int, int, int, PackedFiveWork], int],
) -> None:
    expected, reads = _literal(seed, steps)
    work = PackedFiveWork()
    assert execute(seed, steps, 4096, work) == expected
    assert (work.attempted, work.digit_reads) == (steps, reads)


@pytest.mark.parametrize(
    ("seed", "bits", "attempted", "reads"), [(6, 4, 1, 0), (1, 3, 2, 1)]
)
def test_packed_candidate_checks_every_physical_intermediate(
    seed: int, bits: int, attempted: int, reads: int
) -> None:
    work = PackedFiveWork()
    with pytest.raises(BlockContextBudgetExceeded):
        execute_packed_five(seed, 64, bits, work)
    assert (work.attempted, work.digit_reads) == (attempted, reads)


def test_packed_conversion_preserves_interpreter_digit_limit() -> None:
    limit = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640)
        work = PackedFiveWork()
        assert execute_packed_five(10**699, 2, 4096, work) == 25
        assert sys.get_int_max_str_digits() == 640
    finally:
        sys.set_int_max_str_digits(limit)


@pytest.mark.parametrize("steps", [64, 128, 256, 512, 1024, 2048])
def test_wide_source_does_not_select_padded_h_before_packed(
    monkeypatch: pytest.MonkeyPatch, steps: int
) -> None:
    seed = int("123456789" * 17)
    expected, _ = _literal(seed, steps)

    def reject(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("unmeasured padded-H selection")

    monkeypatch.setattr(FiveReverseSourceAdapter, "padded_source_candidate", reject)
    with FiveReverseTerm(seed, steps, max_steps=steps, max_state_bits=16384) as term:
        assert term.materialize(max_bits=16384) == expected
        assert (
            term.resource_ledger.counters[metrics.FIVE_REVERSE_PACKED_EXECUTED_PAIRS]
            == steps // 2
        )


def test_source_owned_candidate_releases_scratch_and_reports_physical_work() -> None:
    with FiveReverseTerm(73, 128, max_steps=128) as term:
        expected, reads = _literal(73, 128)
        assert term.packed_value(73, 128) == expected
        assert term.resource_ledger.counters[metrics.FIVE_REVERSE_EXACT_STEPS] == 128
        assert (
            term.resource_ledger.counters[
                metrics.FIVE_REVERSE_PACKED_LOGICAL_DIGIT_READS
            ]
            == reads
        )
        assert (
            term.resource_ledger.counters[metrics.FIVE_REVERSE_PACKED_EXECUTED_PAIRS]
            == 64
        )
        ledger = term.resource_ledger
    assert ledger.entries == ledger.nodes == 0


def test_source_owned_candidate_accounts_for_intermediate_refusal() -> None:
    with FiveReverseTerm(6, 64, max_steps=64, max_state_bits=4) as term:
        with pytest.raises(BlockContextBudgetExceeded):
            term.packed_value(6, 64)
        assert term.resource_ledger.counters[metrics.FIVE_REVERSE_EXACT_STEPS] == 1
        assert term.resource_ledger.counters[metrics.FIVE_REVERSE_FAILED_STEPS] == 1
        assert (
            term.resource_ledger.counters.get(
                metrics.FIVE_REVERSE_PACKED_LOGICAL_DIGIT_READS, 0
            )
            == 0
        )
        ledger = term.resource_ledger
    assert ledger.entries == ledger.nodes == 0


def test_candidate_attempts_both_counters_when_accounting_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with FiveReverseTerm(73, 64, max_steps=64) as term:
        ledger = term.resource_ledger
        bump = ResourceLedger.bump
        seen: list[str] = []

        def fail_first(owner: ResourceLedger, counter: str, amount: int = 1) -> None:
            seen.append(counter)
            if counter == metrics.FIVE_REVERSE_EXACT_STEPS:
                raise RuntimeError("counter fault")
            bump(owner, counter, amount)

        monkeypatch.setattr(ResourceLedger, "bump", fail_first)
        with pytest.raises(RuntimeError, match="counter fault"):
            term.packed_value(73, 64)
        assert metrics.FIVE_REVERSE_PACKED_LOGICAL_DIGIT_READS in seen
        assert metrics.FIVE_REVERSE_PACKED_EXECUTED_PAIRS in seen
        assert metrics.FIVE_REVERSE_FAILED_STEPS in seen
        monkeypatch.setattr(ResourceLedger, "bump", bump)
    assert ledger.entries == ledger.nodes == 0


def test_production_packed_consumer_uses_authenticated_receiving_image(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with FiveReverseTerm(73, 1, max_steps=1025) as term:
        initial = term.issued_endpoint_view()
        source = initial.binding.source
        assert type(source) is FiveReverseSource
        assert type(initial.payload) is int
        expected, _ = _literal(initial.payload, 1024)
        adapter = FiveReverseSourceAdapter(
            term, term.resource_ledger, source, source.issuer
        )

        def reject_replay(_term: FiveReverseTerm, _value: int) -> int:
            raise AssertionError("packed action replayed scalar successors")

        monkeypatch.setattr(FiveReverseTerm, "step_value", reject_replay)
        candidate = adapter.apply_composite(FiveReverseAction(1024), initial, None)
        assert candidate is not None
        assert candidate.payload == expected
        assert candidate.extent == 1025
        assert (
            term.resource_ledger.counters[metrics.FIVE_REVERSE_PACKED_EXECUTED_PAIRS]
            == 512
        )


@pytest.mark.parametrize("capped", [False, True])
def test_short_or_capped_production_keeps_scalar_fallback(
    monkeypatch: pytest.MonkeyPatch, capped: bool
) -> None:
    steps = 1024 if capped else 63

    def reject_packed(_term: FiveReverseTerm, _value: int, _steps: int) -> int:
        raise AssertionError("fallback unexpectedly admitted packed execution")

    monkeypatch.setattr(FiveReverseTerm, "packed_value", reject_packed)
    with FiveReverseTerm(0, steps, max_steps=steps) as term:
        if capped:
            ledger = term.resource_ledger
            ledger.tighten_limits(ledger.nodes + 256, ledger.entries + 256)
        assert term.materialize(max_bits=4096) == 0


def test_native_failure_is_counted_and_propagated(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", "1")

    def interrupted(*_args: object, **_kwargs: object) -> None:
        raise KeyboardInterrupt

    monkeypatch.setattr(native_reverse_actions, "diagonal_endpoint", interrupted)
    with FiveReverseTerm(73, 512, max_steps=512, max_state_bits=8192) as term:
        with pytest.raises(KeyboardInterrupt):
            term.packed_value(73, 512)
        assert term.resource_ledger.counters[metrics.FIVE_REVERSE_FAILED_STEPS] == 1
        assert (
            term.resource_ledger.counters.get(metrics.FIVE_REVERSE_EXACT_STEPS, 0) == 0
        )
        ledger = term.resource_ledger
    assert ledger.entries == ledger.nodes == 0


def test_native_unavailable_uses_exact_packed_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", "1")
    monkeypatch.setattr(native_reverse_actions, "_load", lambda: None)
    with FiveReverseTerm(73, 512, max_steps=512, max_state_bits=8192) as term:
        assert term.packed_value(73, 512) == _literal(73, 512)[0]
        assert (
            term.resource_ledger.counters[metrics.FIVE_REVERSE_PACKED_EXECUTED_PAIRS]
            == 256
        )
        ledger = term.resource_ledger
    assert ledger.entries == ledger.nodes == 0


def test_native_output_obeys_python_decimal_conversion_limit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions
    from number_compiler.arithmetic.fields.radix import value_from_lsd_digits

    class Native:
        @staticmethod
        def multiply(
            source: str, multiplier: int, steps: int, side: int
        ) -> tuple[object, ...]:
            assert (source, multiplier, steps, side) == ("73", 5, 1024, 3)
            return "9" * 700, (1, 1, 0, 0, 1, 1, 0.0, 0.0)

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", "1")
    monkeypatch.setattr(native_reverse_actions, "_load", lambda: Native())
    expected = value_from_lsd_digits((9 for _ in range(700)), 10)
    limit = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640)
        with FiveReverseTerm(73, 1024, max_steps=1024, max_state_bits=8192) as term:
            assert term.packed_value(73, 1024) == expected
    finally:
        sys.set_int_max_str_digits(limit)
