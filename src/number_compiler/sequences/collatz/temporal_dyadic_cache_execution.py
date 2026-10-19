"""Apply a retained dyadic Collatz action inside the temporal executor."""

from __future__ import annotations

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.source_cylinder_cache import CollatzDyadicMacros
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
)
from number_compiler.sequences.collatz.temporal_dyadic import bounded_run_length
from number_compiler.sequences.collatz.temporal_f5_observer import (
    append_dyadic_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedMacroTailNotAdmitted,
    MixedRunExecutorState,
)


def try_consume_cached_dyadic_action(
    state: MixedRunExecutorState,
    lookup_enabled: bool,
    *,
    ledger: ResourceLedger,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    include_innovation_tape: bool,
    include_width_spine: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint_cocycle: bool,
    joint_builder: CollatzJointTemporalBuilder,
    maximum_tail: int | None = None,
) -> tuple[MixedRunExecutorState | None, bool]:
    """Apply one exact cached dyadic parent, preserving consumer authority."""
    current, remaining = state.current, state.remaining
    if not (
        lookup_enabled
        and macros is not None
        and remaining >= 16
        and current.bit_length() >= 64
        and bounded_run_length(current & 255) < 8
        and not include_innovation_tape
    ):
        return None, lookup_enabled

    limit = min(remaining, max(8, current.bit_length()))
    requested_width = 1 << (limit.bit_length() - 1)
    scratch.require_bits(16 * (current.bit_length() + 2 * requested_width + 32))
    joint_record = None
    endpoint = 0
    if include_joint_cocycle:
        paired = joint_builder.lookup_largest_macro(
            macros,
            current,
            requested_width,
            remaining,
            include_width=include_width_spine and width_spine.complete,
        )
        if paired is None:
            cell = None
            macro_width = None
            lookup_enabled = False
        else:
            cell, joint_record, macro_width, endpoint = paired
    elif include_width_spine and width_spine.complete:
        selected_with_width = macros.lookup_largest_with_width(
            current, requested_width, remaining
        )
        if selected_with_width is None:
            cell = None
            macro_width = None
            lookup_enabled = False
        else:
            cell, macro_width = selected_with_width
    else:
        cell = macros.lookup_largest(current, requested_width, remaining)
        macro_width = None
        if cell is None:
            lookup_enabled = False
    if cell is None:
        return None, lookup_enabled
    if maximum_tail is not None:
        if type(maximum_tail) is not int or maximum_tail < 0:
            raise ValueError("root cache tail bound must be a natural number")
        if remaining - cell.width - cell.odd_symbols > maximum_tail:
            raise MixedMacroTailNotAdmitted
    if endpoint == 0:
        endpoint = cell.apply(current)
    if endpoint <= 0 or (include_width_spine and macro_width is None):
        return None, lookup_enabled

    width = cell.width
    if joint_record is not None:
        joint_builder.append(joint_record[0], current, joint_record[1], endpoint)
        joint_builder.applied_cached_macro()
    normalized_f5, physical_f5 = state.normalized_f5, state.physical_f5
    if normalized_f5 is not None and physical_f5 is not None:
        normalized_f5, physical_f5 = append_dyadic_f5(
            normalized_f5,
            physical_f5,
            cell.multiplier,
            cell.target_origin,
            cell.residue,
        )
    if include_width_spine and width_spine.complete:
        if macro_width is None:
            width_spine.invalidate()
        else:
            if (
                macro_width.source_width != current.bit_length()
                or macro_width.normalized_symbols != width
                or macro_width.odd_steps != cell.odd_symbols
                or macro_width.physical_ticks != width + cell.odd_symbols
                or macro_width.target_width != endpoint.bit_length()
            ):
                raise ValueError("cached Collatz width spine differs from macro")
            width_spine.record(macro_width.blank)
    macros.applied()
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        cell.multiplier.bit_length()
        + endpoint.bit_length()
        + cell.residue.bit_length(),
    )
    return (
        MixedRunExecutorState(
            endpoint,
            remaining - width - cell.odd_symbols,
            state.normalized + width,
            state.division_ticks + width,
            state.odd_ticks + cell.odd_symbols,
            state.one_symbols + cell.odd_symbols,
            state.zero_symbols + width - cell.odd_symbols,
            state.run_actions + 1,
            normalized_f5,
            physical_f5,
        ),
        False,
    )
