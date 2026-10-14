"""Apply source-admitted 6305 return/exit actions to the Collatz run spine."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    select_border_return_macro,
)
from number_compiler.sequences.collatz.boundary_macro_prefixes import (
    _publish_boundary_macro_prefixes,
)
from number_compiler.sequences.collatz.boundary_macros import (
    AdmittedBoundaryMacroPlan,
    BoundaryActionTemplateMemo,
    CollatzBoundaryMacro,
    admit_routed_boundary_macro_plan,
    select_admitted_boundary_macro,
    validate_admitted_boundary_macro_plan,
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
    ledger.bump("collatz_physical_boundary_plan_checks")
    ledger.bump(
        "collatz_physical_boundary_plan_operand_bits",
        source.bit_length() + remaining.bit_length(),
    )
    return plan


def minimum_useful_border_extent(plan: AdmittedBoundaryMacroPlan | None) -> int:
    """Let border preflight defer only to an admitted edge-cycle alternative."""
    if plan is not None and (plan.family == "0563" or plan.family.startswith("26847")):
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
            ledger.bump("collatz_physical_border_return_admission_budget_refusals")
            if minimum_useful_physical_ticks:
                raise _OptionalBorderPreflightRefused from exc
            raise

    ledger.bump("collatz_physical_border_return_admission_checks")
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
            "collatz_physical_border_return_candidate_alternate_route_fallbacks"
        )
        return None, None
    if border is None:
        return None, None
    if parity_builder is not None:
        parity_builder.append_border_return_macro(border)
    if include_joint:
        joint_builder.require_steps(before, border.normalized_symbols)
        joint_builder.append(border.fields, before, border.odd_symbols, border.endpoint)
    if width_spine.complete:
        width_spine.record(border.width_blank)
    normalized_f5, physical_f5 = _compose_f5_actions(state, border)
    ledger.bump("collatz_physical_boundary_6305R_macro_actions")
    ledger.bump("collatz_physical_boundary_6305R_macro_repetitions", border.repetitions)
    ledger.bump("collatz_physical_border_return_3_reentries", border.returns)
    ledger.bump(
        "collatz_physical_border_return_zero_tail_symbols", sum(border.zero_tails)
    )
    ledger.bump(
        "collatz_physical_border_return_exit_8_to_4", int(border.exit_port == "8_to_4")
    )
    ledger.bump(
        "collatz_physical_border_return_exit_8_to_9",
        int(border.exit_port.startswith("8_to_9")),
    )
    ledger.bump(
        "collatz_physical_temporal_run_operand_bits",
        before.bit_length()
        + border.endpoint.bit_length()
        + border.fields.gain.bit_length()
        + border.fields.sum_gain.bit_length(),
    )
    if macros is not None:
        try:
            _publish_boundary_macro_prefixes(
                border,
                macros,
                scratch,
                anchor=seed,
                normalized_offset=state.normalized,
                odd_offset=state.one_symbols,
            )
        except BlockContextBudgetExceeded:
            macros.frontier.clear()
            ledger.bump("collatz_boundary_prefix_budget_bypasses")
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
    boundary = select_admitted_boundary_macro(plan, templates=templates)
    if (
        boundary is None
        or boundary.family != plan.family
        or boundary.repetitions != plan.repetitions
        or boundary.normalized_symbols != plan.normalized_symbols
    ):
        raise AssertionError("Collatz boundary changed after admission")
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
    family = plan.family
    ledger.bump(f"collatz_physical_boundary_{family}_macro_actions")
    ledger.bump(
        f"collatz_physical_boundary_{family}_macro_repetitions", boundary.repetitions
    )
    ledger.bump(
        f"collatz_physical_boundary_{family}_macro_physical_ticks",
        boundary.physical_ticks,
    )
    ledger.bump(
        "collatz_physical_temporal_run_operand_bits",
        state.current.bit_length()
        + boundary.endpoint.bit_length()
        + boundary.fields.gain.bit_length()
        + boundary.fields.sum_gain.bit_length(),
    )
    lookup_enabled = prior_lookup_enabled
    if macros is not None:
        try:
            _publish_boundary_macro_prefixes(
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
            ledger.bump("collatz_boundary_prefix_budget_bypasses")
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
