"""Consume one fully certified border/helix skew chain as a single action."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    CycleEntryPhase,
    GuardedBorderPath,
)
from number_compiler.sequences.collatz.boundary_macros import boundary_metric_suffix
from number_compiler.sequences.collatz.skew_cylinder_repeat import (
    GuardedSkewCylinderPower,
)
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
    _project_dyadic_fields_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    UnifiedSkewChain,
    select_unified_skew_chain,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.boundary_macros import (
        BoundaryActionTemplateMemo,
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


def consume_unified_skew_chain(
    seed: int,
    ticks: int,
    *,
    control_bits: int,
    templates: BoundaryActionTemplateMemo,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    include_joint: bool,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    macros: CollatzDyadicMacros | None,
    include_quadratic_clock: bool,
) -> tuple[MixedRunExecutorState, UnifiedSkewChain] | None:
    """Publish one authenticated complete action; a miss changes no consumers."""
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_ATTEMPTS)
    try:
        chain = select_unified_skew_chain(
            seed,
            ticks,
            templates=templates,
            ledger=ledger,
            include_quadratic_clock=include_quadratic_clock,
            preserve_ordinary_mixed_parent=(
                not include_joint and not include_quadratic_clock
            ),
            preflight=lambda steps: scratch.require_bits(
                8 * (seed.bit_length() + 4 * steps + 4 * control_bits + 32)
            ),
        )
    except BlockContextBudgetExceeded:
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_BUDGET_REFUSALS)
        ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS,
            seed.bit_length() + max(1, ticks.bit_length()),
        )
        return None
    if chain is None:
        return None
    # All guards/clock seams were proved before any publisher is mutated.
    try:
        scratch.require_bits(
            8
            * (
                seed.bit_length()
                + chain.fields.gain.bit_length()
                + chain.fields.sum_gain.bit_length()
                + 4 * control_bits
                + 32
            )
        )
    except BlockContextBudgetExceeded:
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_BUDGET_REFUSALS)
        ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS,
            seed.bit_length()
            + chain.fields.gain.bit_length()
            + chain.fields.sum_gain.bit_length(),
        )
        return None
    chain.verify()
    applied_fields = chain.fields
    applied_endpoint = chain.endpoint
    applied_repetitions = 1
    applied_steps = chain.normalized_symbols
    applied_odds = chain.odd_symbols
    applied_ticks = chain.physical_ticks
    power: GuardedSkewCylinderPower | None = None
    maximum_repetitions = ticks // chain.physical_ticks
    # The parity cylinder proves only that the same normalized word repeats.
    # Absolute bit-width extrema depend on the later affine carry, so retain
    # the existing per-segment width owner whenever that richer observer is
    # demanded.
    if maximum_repetitions > 1 and not width_spine.complete:
        try:
            power = GuardedSkewCylinderPower.from_chain_fitting(
                chain,
                maximum_repetitions,
                preflight=lambda bits: scratch.require_bits(8 * bits),
            )
            if power is not None:
                bound = power.materialization_bound_bits
                # Only the joint-observation path pays for complete later
                # seam preimages. If they admit the same repetitions, reuse
                # that exact source-closed action; otherwise the independently
                # valid parity-word cylinder remains the producer authority.
                joint_power = None
                joint_refusal_counted = False
                if include_joint:
                    try:
                        joint_power = chain.source_closed_temporal_power(
                            power.repetitions,
                            max_coefficient_bits=max(bound * 4, 128),
                            ledger=ledger,
                        )
                    except BlockContextBudgetExceeded:
                        joint_power = None
                        ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_POWER_REFUSALS)
                        joint_refusal_counted = True
                use_joint_power = joint_power is not None and joint_power.admits(seed)
                if use_joint_power:
                    try:
                        scratch.require_bits(8 * bound)
                    except BlockContextBudgetExceeded:
                        use_joint_power = False
                        ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_POWER_REFUSALS)
                        joint_refusal_counted = True
                if use_joint_power:
                    assert joint_power is not None
                    applied_fields = joint_power.action
                    applied_endpoint = joint_power.endpoint(seed)
                    ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_TEMPORAL_POWERS)
                    if joint_power.clock is not None:
                        joint_power.clock.verify(applied_fields, seed, applied_endpoint)
                else:
                    if include_joint and not joint_refusal_counted:
                        # Count an incompatible source guard or a nonadmitting
                        # compiled power once; budget refusals were counted at
                        # the exact refusal site above.
                        ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_POWER_REFUSALS)
                    applied_fields, applied_endpoint = power.materialize(
                        max_materialization_bits=bound,
                        preflight=lambda bits: scratch.require_bits(8 * bits),
                    )
                applied_repetitions = power.repetitions
                applied_steps = power.normalized_steps
                applied_odds = power.odd_symbols * power.repetitions
                applied_ticks = power.physical_ticks
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_ADDITIONAL_REPETITIONS,
                    applied_repetitions - 1,
                )
                ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_POWERED_ACTIONS)
        except BlockContextBudgetExceeded:
            power = None
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_POWER_REFUSALS)
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS,
                seed.bit_length()
                + chain.fields.gain.bit_length()
                + chain.fields.offset.bit_length()
                + max(1, maximum_repetitions.bit_length()),
            )
    cacheable_dyadic_chain = (
        applied_steps >= 16 and applied_steps & (applied_steps - 1) == 0
    )
    paired_parent_ready = False
    if macros is not None:
        # The endpoint and joint caches are separate owners. Publish the exact
        # source cylinder here so the joint observation emitted below has its
        # matching endpoint parent. No child discovery is needed: this is the
        # already authenticated root action.
        macros.frontier.clear()
        if cacheable_dyadic_chain:
            summary = (
                CollatzTapeWidthSummary(
                    chain.source.bit_length(),
                    applied_endpoint.bit_length(),
                    applied_ticks,
                    applied_steps,
                    applied_odds,
                    chain.width_blank,
                )
                if width_spine.complete
                else None
            )
            try:
                macros.remember(
                    chain.source,
                    applied_steps,
                    applied_odds,
                    applied_endpoint,
                    tape_width_summary=summary,
                )
                paired_parent_ready = True
            except BlockContextBudgetExceeded:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_OCCURRENCE_PUBLICATION_BYPASSES
                )
    if parity_builder is not None:
        if power is None:
            parity_builder.append_unified_skew_chain(chain)
        else:
            parity_builder.append_guarded_skew_repetitions(
                chain,
                power,
                applied_endpoint,
                preflight=lambda bits: scratch.require_bits(8 * bits),
            )
    if include_joint:
        joint_builder.require_steps(seed, applied_steps)
        joint_builder.append(
            applied_fields,
            seed,
            applied_odds,
            applied_endpoint,
            cache=paired_parent_ready,
        )
    if width_spine.complete:
        width_spine.record(chain.width_blank)
        width_spine.reset_segment()
    if normalized_f5 is not None and physical_f5 is not None:
        f5 = _project_dyadic_fields_f5(applied_fields)
        normalized_f5 = normalized_f5.then(f5)
        physical_f5 = physical_f5.then(f5)
    # Count embedded border-family occurrences without pretending they were
    # separate Hashlife run actions. The composed root action count stays one.
    for identity in chain.segment_identities:
        if isinstance(identity, (CycleEntryPhase, GuardedBorderPath)):
            suffix = boundary_metric_suffix(identity)
            ledger.bump(f"collatz_physical_boundary_{suffix}_macro_actions")
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_COMPOSED_ACTIONS)
    if applied_endpoint == 1:
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_TERMINAL_ACTIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_JOINED_SEGMENTS,
        len(chain.segment_identities),
    )
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_APPLIED_ACTIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        seed.bit_length()
        + applied_fields.gain.bit_length()
        + applied_fields.sum_gain.bit_length(),
    )
    return (
        MixedRunExecutorState(
            applied_endpoint,
            ticks - applied_ticks,
            applied_steps,
            applied_steps,
            applied_odds,
            applied_odds,
            applied_steps - applied_odds,
            1,
            normalized_f5,
            physical_f5,
        ),
        chain,
    )


__all__ = ["consume_unified_skew_chain"]
