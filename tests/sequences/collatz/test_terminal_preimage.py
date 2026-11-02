"""Exact admission and consumer binding for power-of-two preimages."""

import pytest

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import terminal_preimage
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.innovation_input_tape import (
    ParityFactor,
    ParityProgramBuilder,
)
from number_compiler.sequences.collatz.terminal_preimage import (
    probe_terminal_power2_macro,
    select_terminal_power2_macro,
    validate_terminal_power2_macro,
)


def test_small_power_two_preimage_has_exact_word_endpoint_and_physical_extent() -> None:
    macro = select_terminal_power2_macro(5, 5)
    assert macro is not None
    validate_terminal_power2_macro(macro)
    assert (
        macro.exponent,
        macro.normalized_symbols,
        macro.odd_symbols,
    ) == (4, 4, 1)
    assert macro.physical_ticks == 5
    assert 3 * macro.source + 1 == 1 << macro.exponent
    assert macro.fields.endpoint(macro.source) == macro.endpoint == 1
    assert macro.fields.certifies(macro.source)
    assert macro.width_blank == BlankLedger(-2, -2, 2)

    with ParityProgramBuilder(macro.source, ResourceLedger()) as builder:
        builder.append_terminal_power2_macro(macro)
        program = builder.finish(
            macro.endpoint,
            steps=macro.normalized_symbols,
            one_symbols=macro.odd_symbols,
        )
        assert program.producer_issued
        assert program.endpoint == 1
        assert program.steps == 4
        assert program.one_symbols == 1
        assert program.factors == (ParityFactor((1,), 1), ParityFactor((0,), 3))


def test_nonpreimage_and_insufficient_physical_budget_are_not_admitted() -> None:
    assert select_terminal_power2_macro(13, 100) is None
    assert select_terminal_power2_macro(5, 4) is None
    assert select_terminal_power2_macro(5, 5) is not None


def test_large_odd_power_two_preimage_keeps_compact_normalized_action() -> None:
    exponent = 128
    source = ((1 << exponent) - 1) // 3
    assert source > 1 and source & 1 == 1

    macro = select_terminal_power2_macro(source, exponent + 1)
    assert macro is not None
    assert macro.exponent == exponent
    assert macro.physical_ticks == exponent + 1
    assert macro.fields.steps == exponent
    assert macro.fields.endpoint(source) == macro.endpoint == 1
    assert macro.width_blank == BlankLedger(
        1 - source.bit_length(),
        1 - source.bit_length(),
        exponent + 1 - source.bit_length(),
    )


@pytest.mark.parametrize(
    ("coefficients", "expected_endpoint"),
    (
        ((1, 27, 0, 0, 1, 0), 2),
        # This rebound producer-issued action has the correct endpoint and
        # source residue, but its emitted sums are not those of 1,0,0,0.
        ((3, 1, 0, 0, 3, 1), 1),
    ),
)
def test_validator_rejects_rebound_issued_field_payload(
    coefficients: tuple[int, int, int, int, int, int], expected_endpoint: int
) -> None:
    macro = select_terminal_power2_macro(5, 5)
    assert macro is not None

    # Integer-only restoration preserves coefficient shape but carries no
    # source-word producer authority, even when endpoint and cylinder agree.
    altered_fields = DyadicTerminalFieldAction.restore_untrusted_cache_payload(
        4, coefficients
    )
    assert not altered_fields.producer_issued
    assert altered_fields.certifies(5)
    assert (altered_fields.gain * 5 + altered_fields.offset) // (
        1 << altered_fields.steps
    ) == expected_endpoint

    object.__setattr__(macro, "fields", altered_fields)
    object.__setattr__(
        macro,
        "_binding",
        (
            macro.source,
            macro.exponent,
            macro.physical_ticks,
            altered_fields,
            macro.endpoint,
            macro.width_blank,
        ),
    )
    with pytest.raises(ValueError, match="payload changed after admission"):
        validate_terminal_power2_macro(macro)


def test_probe_preflights_scratch_before_attempting_power_classification(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace(ledger, "terminal-preimage-test")

    def reject_preflight(_bits: int) -> None:
        raise RuntimeError("scratch preflight rejected")

    def forbidden_classification(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("power classification ran before scratch admission")

    monkeypatch.setattr(scratch, "require_bits", reject_preflight)
    monkeypatch.setattr(
        terminal_preimage, "select_terminal_power2_macro", forbidden_classification
    )
    with (
        scratch.scope(),
        pytest.raises(RuntimeError, match="scratch preflight rejected"),
    ):
        probe_terminal_power2_macro(
            5,
            5,
            ledger=ledger,
            scratch=scratch,
            control_bits=1,
        )

    assert "collatz_terminal_power2_probe_attempts" not in ledger.counters
    assert "collatz_terminal_power2_probe_operand_bits" not in ledger.counters
