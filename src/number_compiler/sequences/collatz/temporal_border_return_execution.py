"""Apply source-admitted 6305 return/exit actions to the Collatz run spine."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    BorderExitPort,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    select_border_return_macro,
)
from number_compiler.sequences.collatz.boundary_macro_prefixes import (
    publish_boundary_macro_prefixes,
)
from number_compiler.sequences.collatz.boundary_macros import (
    AdmittedBoundaryMacroPlan,
    CollatzBoundaryMacro,
    admit_routed_boundary_macro_plan,
    boundary_macro_26847_phase,
    boundary_metric_key,
    select_admitted_boundary_macro,
    validate_admitted_boundary_macro_plan,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)


class _OptionalBorderPreflightRefused(Exception):
    """A better independently admitted edge action can still run."""


def admit_physical_boundary_plan(
    source: int, remaining: int, ledger: ResourceLedger
) -> AdmittedBoundaryMacroPlan | None:
    """Admit and account one source/clock-bound named boundary candidate."""
    plan = admit_routed_boundary_macro_plan(source, remaining)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_PLAN_CHECKS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_PLAN_OPERAND_BITS,
        source.bit_length() + remaining.bit_length(),
    )
    return plan


def minimum_useful_border_extent(plan: AdmittedBoundaryMacroPlan | None) -> int:
    """Let border preflight defer only to an admitted edge-cycle alternative."""
    if plan is not None and (
        plan.identity == ENTRY_0563
        or boundary_macro_26847_phase(plan.identity) is not None
    ):
        return plan.physical_ticks
    return 0


if TYPE_CHECKING:
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
    from number_compiler.sequences.collatz.temporal_f5_observer import (
        CollatzF5AffineAction,
    )


def _compose_f5_actions(
    state: MixedRunExecutorState,
    macro: BorderReturnMacro | CollatzBoundaryMacro,
) -> tuple[CollatzF5AffineAction | None, CollatzF5AffineAction | None]:
    normalized_f5 = state.normalized_f5
    physical_f5 = state.physical_f5
    if normalized_f5 is not None and physical_f5 is not None:
        f5 = macro.f5_action()
        normalized_f5 = normalized_f5.then(f5)
        physical_f5 = physical_f5.then(f5)
    return normalized_f5, physical_f5


def consume_border_return(
    state: MixedRunExecutorState,
    *,
    seed: int,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    include_joint: bool,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    minimum_useful_physical_ticks: int = 0,
) -> tuple[MixedRunExecutorState | None, BorderReturnMacro | None]:
    """Consume the complete authenticated cross-border program in one action.

    Signed innovation bits come from the same compact parity SLP as other
    macros; the 8->9 event is never published without its predecessor guard.
    Cache publication is optional, and cannot invalidate exact advancement.
    """
    before = state.current
    if (
        type(minimum_useful_physical_ticks) is not int
        or minimum_useful_physical_ticks < 0
    ):
        raise ValueError("minimum useful border extent must be nonnegative")

    def preflight(steps: int) -> None:
        try:
            scratch.require_bits(
                8 * (before.bit_length() + 4 * steps + 4 * control_bits + 32)
            )
        except BlockContextBudgetExceeded as exc:
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_ADMISSION_BUDGET_REFUSALS
            )
            if minimum_useful_physical_ticks:
                raise _OptionalBorderPreflightRefused from exc
            raise

    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_ADMISSION_CHECKS)
    try:
        border = select_border_return_macro(
            before,
            state.remaining,
            minimum_useful_physical_ticks=minimum_useful_physical_ticks,
            preflight=preflight,
            ledger=ledger,
        )
    except _OptionalBorderPreflightRefused:
        ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_ALTERNATE_ROUTE_FALLBACKS
        )
        return None, None
    if border is None:
        return None, None
    if state.normalized_f5 is not None or include_joint:
        from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
            certify_pointed_low_border,
        )

        matrix = certify_pointed_low_border(
            before,
            border.endpoint,
            border.fields,
            border.odd_symbols,
            tails=border.zero_tails,
        )
        from number_compiler.sequences.collatz.guarded_port_join import (
            certify_pointed_port_join,
        )

        joined = certify_pointed_port_join(
            before,
            border.fields,
            border.odd_symbols,
            trace=border.zero_tails,
            ledger=ledger,
            macro=border,
            pointed_pair=matrix.pair,
        )
        if (
            matrix.pair.output_pair != border.endpoint % 100
            or joined.port.endpoint(before) != border.endpoint
            or not joined.bridge.target.contains(border.endpoint)
        ):
            raise ArithmeticError("6305 source-punctured port lost its endpoint pair")
        ledger.bump(_collatz_keys.COLLATZ_LOW_BORDER_PAIR_MATRIX_CHECKS)
        if matrix.phase is not None:
            ledger.bump(_collatz_keys.COLLATZ_LOW_BORDER_NUMERATOR_PHASE_CHECKS)
    if parity_builder is not None:
        parity_builder.append_border_return_macro(border)
    if include_joint:
        joint_builder.require_steps(before, border.normalized_symbols)
        joint_builder.append(border.fields, before, border.odd_symbols, border.endpoint)
    if width_spine.complete:
        width_spine.record(border.width_blank)
    normalized_f5, physical_f5 = _compose_f5_actions(state, border)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_6305R_MACRO_ACTIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_6305R_MACRO_REPETITIONS,
        border.repetitions,
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_3_REENTRIES, border.returns
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_ZERO_TAIL_SYMBOLS,
        sum(border.zero_tails),
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_EXIT_8_TO_4,
        int(border.exit_port is BorderExitPort.EIGHT_TO_FOUR),
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_EXIT_8_TO_9,
        int(
            border.exit_port
            in (
                BorderExitPort.EIGHT_TO_NINE,
                BorderExitPort.EIGHT_TO_NINE_TO_EIGHT,
                BorderExitPort.EIGHT_TO_NINE_OPEN,
                BorderExitPort.EIGHT_TO_NINE_PENDING,
            )
        ),
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        before.bit_length()
        + border.endpoint.bit_length()
        + border.fields.gain.bit_length()
        + border.fields.sum_gain.bit_length(),
    )
    if macros is not None:
        try:
            publish_boundary_macro_prefixes(
                border,
                macros,
                scratch,
                anchor=seed,
                normalized_offset=state.normalized,
                odd_offset=state.one_symbols,
            )
        except BlockContextBudgetExceeded:
            macros.frontier.clear()
            ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_PREFIX_BUDGET_BYPASSES)
    return MixedRunExecutorState(
        border.endpoint,
        state.remaining - border.physical_ticks,
        state.normalized + border.normalized_symbols,
        state.division_ticks + border.normalized_symbols,
        state.odd_ticks + border.odd_symbols,
        state.one_symbols + border.odd_symbols,
        state.zero_symbols + border.normalized_symbols - border.odd_symbols,
        state.run_actions + 1,
        normalized_f5,
        physical_f5,
    ), border


def consume_named_boundary(
    state: MixedRunExecutorState,
    plan: AdmittedBoundaryMacroPlan,
    *,
    seed: int,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    templates: BoundaryActionTemplateMemo,
    include_joint: bool,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    prior_lookup_enabled: bool,
    issued_boundary: CollatzBoundaryMacro | None = None,
) -> tuple[MixedRunExecutorState, CollatzBoundaryMacro, bool]:
    """Use a legacy named boundary macro after exact plan admission."""
    if type(plan) is not AdmittedBoundaryMacroPlan:
        raise TypeError("named boundary execution requires an admitted plan")
    validate_admitted_boundary_macro_plan(plan)
    if plan.source != state.current or plan.available_physical_ticks != state.remaining:
        raise ValueError("named boundary plan belongs to another source or clock")
    scratch.require_bits(
        8
        * (
            state.current.bit_length()
            + 4 * plan.normalized_symbols
            + 4 * control_bits
            + 32
        )
    )
    if issued_boundary is None:
        boundary = select_admitted_boundary_macro(plan, templates=templates)
    else:
        from number_compiler.sequences.collatz.boundary_macros import (
            validate_boundary_macro,
        )

        validate_boundary_macro(issued_boundary)
        if issued_boundary.source != state.current:
            raise ValueError("preissued boundary belongs to another source")
        boundary = issued_boundary
    if (
        boundary.identity != plan.identity
        or boundary.repetitions != plan.repetitions
        or boundary.normalized_symbols != plan.normalized_symbols
    ):
        raise AssertionError("Collatz boundary changed after admission")
    if state.normalized_f5 is not None or include_joint:
        from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
            certify_pointed_low_border,
        )

        matrix = certify_pointed_low_border(
            state.current,
            boundary.endpoint,
            boundary.fields,
            boundary.odd_symbols,
        )
        from number_compiler.sequences.collatz.guarded_port_join import (
            certify_pointed_port_join,
        )

        joined = certify_pointed_port_join(
            state.current,
            boundary.fields,
            boundary.odd_symbols,
            ledger=ledger,
            macro=boundary,
            pointed_pair=matrix.pair,
        )
        if (
            matrix.pair.output_pair != boundary.endpoint % 100
            or joined.port.endpoint(state.current) != boundary.endpoint
            or not joined.bridge.target.contains(boundary.endpoint)
        ):
            raise ArithmeticError("named source-punctured port lost its endpoint pair")
        ledger.bump(_collatz_keys.COLLATZ_LOW_BORDER_PAIR_MATRIX_CHECKS)
        if matrix.phase is not None:
            ledger.bump(_collatz_keys.COLLATZ_LOW_BORDER_NUMERATOR_PHASE_CHECKS)
    if parity_builder is not None:
        parity_builder.append_boundary_macro(boundary)
    if include_joint:
        joint_builder.require_steps(state.current, boundary.normalized_symbols)
        joint_builder.append(
            boundary.fields, state.current, boundary.odd_symbols, boundary.endpoint
        )
    if width_spine.complete:
        width_spine.record(boundary.width_blank)
    normalized_f5, physical_f5 = _compose_f5_actions(state, boundary)
    ledger.bump(
        boundary_metric_key(plan.identity, _collatz_keys.BoundaryMacroMetric.ACTIONS)
    )
    ledger.bump(
        boundary_metric_key(
            plan.identity, _collatz_keys.BoundaryMacroMetric.REPETITIONS
        ),
        boundary.repetitions,
    )
    ledger.bump(
        boundary_metric_key(
            plan.identity, _collatz_keys.BoundaryMacroMetric.PHYSICAL_TICKS
        ),
        boundary.physical_ticks,
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        state.current.bit_length()
        + boundary.endpoint.bit_length()
        + boundary.fields.gain.bit_length()
        + boundary.fields.sum_gain.bit_length(),
    )
    lookup_enabled = prior_lookup_enabled
    if macros is not None:
        try:
            publish_boundary_macro_prefixes(
                boundary,
                macros,
                scratch,
                anchor=seed,
                normalized_offset=state.normalized,
                odd_offset=state.one_symbols,
            )
            lookup_enabled = True
        except BlockContextBudgetExceeded:
            macros.frontier.clear()
            lookup_enabled = False
            ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_PREFIX_BUDGET_BYPASSES)
    width_spine.reset_segment()
    return (
        MixedRunExecutorState(
            boundary.endpoint,
            state.remaining - boundary.physical_ticks,
            state.normalized + boundary.normalized_symbols,
            state.division_ticks + boundary.normalized_symbols,
            state.odd_ticks + boundary.odd_symbols,
            state.one_symbols + boundary.odd_symbols,
            state.zero_symbols + boundary.normalized_symbols - boundary.odd_symbols,
            state.run_actions + 1,
            normalized_f5,
            physical_f5,
        ),
        boundary,
        lookup_enabled,
    )


__all__ = [
    "admit_physical_boundary_plan",
    "consume_border_return",
    "consume_named_boundary",
    "minimum_useful_border_extent",
]
