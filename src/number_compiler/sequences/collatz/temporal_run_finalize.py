"""Publish the checked result of one completed Collatz temporal run."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_identity import (
        BoundaryActionIdentity,
    )
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointTemporalBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )
    from number_compiler.sequences.collatz.tape_width import (
        CollatzWidthSpineAccumulator,
    )
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        CollatzF5AffineAction,
        CollatzTemporalRunQuotient,
    )
    from number_compiler.sequences.collatz.unified_skew_chain import (
        UnifiedSkewChain,
    )


def finalize_collatz_temporal_run(
    *,
    seed: int,
    physical_ticks: int,
    current: int,
    phase: int,
    ledger: ResourceLedger,
    macros: CollatzDyadicMacros | None,
    previous_source: int,
    previous_width: int,
    previous_ones: int,
    normalized: int,
    one_symbols: int,
    share_width: int,
    width_spine: CollatzWidthSpineAccumulator,
    division_ticks: int,
    odd_ticks: int,
    run_actions: int,
    include_joint_cocycle: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    innovation_modulus: int | None,
    pending_normalized_source: int | None,
    zero_symbols: int,
    cycle_repetitions: int,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    first_boundary: tuple[int, int, int, BoundaryActionIdentity] | None,
    first_boundary_macro: CollatzBoundaryMacro | BorderReturnMacro | None,
    unified_skew_chain: UnifiedSkewChain | None = None,
) -> CollatzTemporalRunQuotient:
    if macros is not None and phase == 0 and previous_width < normalized <= share_width:
        macros.observe(
            previous_source,
            normalized - previous_width,
            one_symbols - previous_ones,
            current,
            anchor=seed,
            tape_width_summary=width_spine.segment_summary(
                previous_source.bit_length(),
                current.bit_length(),
                normalized - previous_width,
                one_symbols - previous_ones,
            ),
        )

    certificate = None
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_ACTIONS, run_actions)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NORMALIZED_SYMBOLS, normalized)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ODD_TICKS, odd_ticks)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DIVISION_TICKS, division_ticks)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ENDPOINT_OPERAND_BITS,
        current.bit_length(),
    )

    tape_width_summary = width_spine.finish(
        seed.bit_length(),
        current.bit_length(),
        physical_ticks,
        division_ticks,
        odd_ticks,
    )
    joint_action = None
    if include_joint_cocycle:
        normalized_endpoint = current if phase == 0 else (current - 1) // 3
        joint_action = joint_builder.finish(
            seed,
            current,
            normalized_endpoint,
            physical_ticks,
            division_ticks,
            one_symbols,
            phase,
        )

    innovation_observation = None
    if parity_builder is not None:
        from number_compiler.sequences.collatz.innovation_port_moore import (
            observe_parity_program,
        )

        if phase == 0:
            normalized_endpoint = current
        elif pending_normalized_source is None:
            raise AssertionError("pending odd half-step lost its normalized source")
        else:
            normalized_endpoint = pending_normalized_source
        program = parity_builder.finish(
            normalized_endpoint,
            steps=normalized,
            one_symbols=one_symbols,
        )
        if innovation_modulus is None:
            raise AssertionError("complete parity program has no modulus")
        innovation_observation = observe_parity_program(
            program,
            innovation_modulus,
            ledger=ledger,
            physical_endpoint=current,
            physical_ticks=physical_ticks,
            phase=phase,
        )

    from number_compiler.sequences.collatz.temporal_run_result import (
        CollatzTemporalRunQuotient,
    )

    return CollatzTemporalRunQuotient(
        seed,
        physical_ticks,
        current,
        odd_ticks,
        division_ticks,
        normalized,
        phase,
        run_actions,
        zero_symbols,
        one_symbols,
        cycle_repetitions,
        normalized_f5,
        physical_f5,
        certificate,
        tape_width_summary,
        joint_action,
        first_boundary,
        first_boundary_macro,
        innovation_observation,
        unified_skew_chain,
    )


__all__ = ["finalize_collatz_temporal_run"]
