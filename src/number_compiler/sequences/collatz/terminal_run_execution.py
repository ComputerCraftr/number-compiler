"""Consume an admitted power-of-two terminal action in one run segment."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.tape_width import CollatzWidthSpineAccumulator
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
    _project_dyadic_fields_f5,
)
from number_compiler.sequences.collatz.terminal_preimage import (
    CollatzTerminalPower2Macro,
    probe_terminal_power2_macro,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )


@dataclass(frozen=True, slots=True)
class TerminalRunProgress:
    macro: CollatzTerminalPower2Macro
    remaining: int
    normalized: int
    division_ticks: int
    odd_ticks: int
    one_symbols: int
    zero_symbols: int
    run_actions: int
    normalized_f5: CollatzF5AffineAction | None
    physical_f5: CollatzF5AffineAction | None


def consume_terminal_power_two(
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    include_joint: bool,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
    run_actions: int,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    maximum_tail: int | None = None,
) -> TerminalRunProgress | None:
    if maximum_tail is not None and (type(maximum_tail) is not int or maximum_tail < 0):
        raise ValueError("terminal route tail bound must be a nonnegative integer")
    macro = probe_terminal_power2_macro(
        source,
        remaining,
        ledger=ledger,
        scratch=scratch,
        control_bits=control_bits,
    )
    if macro is None:
        return None
    if maximum_tail is not None and remaining - macro.physical_ticks > maximum_tail:
        ledger.bump("collatz_terminal_power2_route_tail_bypasses")
        return None
    if parity_builder is not None:
        parity_builder.append_terminal_power2_macro(macro)
    if include_joint:
        joint_builder.require_steps(source, macro.normalized_symbols)
        joint_builder.append(
            macro.fields,
            source,
            macro.odd_symbols,
            macro.endpoint,
        )
    if width_spine.complete:
        width_spine.record(macro.width_blank)
    if normalized_f5 is not None and physical_f5 is not None:
        f5 = _project_dyadic_fields_f5(macro.fields)
        normalized_f5 = normalized_f5.then(f5)
        physical_f5 = physical_f5.then(f5)
    ledger.bump("collatz_terminal_power2_preimage_actions")
    ledger.bump(
        "collatz_physical_temporal_run_operand_bits",
        source.bit_length()
        + macro.endpoint.bit_length()
        + macro.fields.gain.bit_length()
        + macro.fields.offset.bit_length(),
    )
    width_spine.reset_segment()
    return TerminalRunProgress(
        macro,
        remaining - macro.physical_ticks,
        normalized + macro.normalized_symbols,
        division_ticks + macro.normalized_symbols,
        odd_ticks + macro.odd_symbols,
        one_symbols + macro.odd_symbols,
        zero_symbols + macro.normalized_symbols - macro.odd_symbols,
        run_actions + 1,
        normalized_f5,
        physical_f5,
    )
