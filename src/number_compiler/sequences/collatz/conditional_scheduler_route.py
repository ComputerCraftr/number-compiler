"""Lazy handoff from the physical run loop to a conditional source action."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointTemporalBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )
    from number_compiler.sequences.collatz.temporal_mixed_execution import (
        MixedRunExecutorState,
    )


def try_consume_conditional_route(
    state: MixedRunExecutorState,
    *,
    require_mixed_prefix: bool,
    homogeneous_prefix: bool,
    deferred_for_root_checkpoint: bool,
    include_width_spine: bool,
    include_innovation_tape: bool,
    parity_route_requested: bool,
    source: int,
    remaining_ticks: int,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    ledger: ResourceLedger,
    macros: CollatzDyadicMacros | None,
) -> MixedRunExecutorState | None:
    """Import the scheduler only after all legacy publisher gates pass."""
    if (
        require_mixed_prefix
        or homogeneous_prefix
        or deferred_for_root_checkpoint
        or include_width_spine
        or include_innovation_tape
        or parity_route_requested
        or source % 10 != 3
        or source.bit_length() < 256
        or remaining_ticks < 256
    ):
        return None
    from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
        try_consume_conditional_scheduler_candidate,
    )

    return try_consume_conditional_scheduler_candidate(
        state,
        scratch=scratch,
        control_bits=control_bits,
        include_joint=include_joint,
        joint_builder=joint_builder,
        ledger=ledger,
        macros=macros,
    )
