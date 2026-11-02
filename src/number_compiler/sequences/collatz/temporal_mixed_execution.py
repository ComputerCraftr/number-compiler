"""Select and consume exact mixed Collatz actions in the run executor."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, NamedTuple

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.mixed_action_cache import (
    MixedActionTailNotAdmitted,
    applied_mixed_action,
    lookup_mixed_action,
    remember_mixed_action,
)
from number_compiler.sequences.collatz.mixed_clock_macros import (
    MixedClockMacro,
    select_mixed_clock_macro,
    validate_mixed_clock_macro,
)
from number_compiler.sequences.collatz.source_cylinder_cache import CollatzDyadicMacros
from number_compiler.sequences.collatz.tape_width import CollatzWidthSpineAccumulator
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
    project_dyadic_fields_f5,
)
from number_compiler.sequences.collatz.terminal_run_execution import (
    consume_terminal_power_two,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointTemporalBuilder,
    )


@dataclass(frozen=True, slots=True)
class MixedMacroApplication:
    macro: MixedClockMacro
    normalized_f5: CollatzF5AffineAction | None
    physical_f5: CollatzF5AffineAction | None


@dataclass(frozen=True, slots=True)
class MixedRunProgress:
    application: MixedMacroApplication
    current: int
    remaining: int
    normalized: int
    division_ticks: int
    odd_ticks: int
    one_symbols: int
    zero_symbols: int
    run_actions: int

    def executor_state(self) -> MixedRunExecutorState:
        return MixedRunExecutorState(
            self.current,
            self.remaining,
            self.normalized,
            self.division_ticks,
            self.odd_ticks,
            self.one_symbols,
            self.zero_symbols,
            self.run_actions,
            self.application.normalized_f5,
            self.application.physical_f5,
        )


class MixedRunExecutorState(NamedTuple):
    current: int
    remaining: int
    normalized: int
    division_ticks: int
    odd_ticks: int
    one_symbols: int
    zero_symbols: int
    run_actions: int
    normalized_f5: CollatzF5AffineAction | None
    physical_f5: CollatzF5AffineAction | None


class MixedRouteNotAdmitted(Exception):
    """The bounded route probe found no exact mixed action for this source."""


class MixedMacroTailNotAdmitted(Exception):
    """A retained exact action leaves too much work for the root route."""


_MAX_ROOT_ROUTE_TAIL = DyadicReturnImageWorkspace.MAX_LEAF_STEPS


def consume_initial_mixed_route(
    source: int,
    remaining: int,
    *,
    control_bits: int,
    templates: BoundaryActionTemplateMemo,
    ledger: ResourceLedger,
    d8_table: D8TemporalTable | None,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
) -> tuple[MixedRunExecutorState | None, D8TemporalTable | None]:
    """Try the complete cache parent before one bounded exact cold selector."""
    oversized_mixed_parent = False
    try:
        cached = consume_cached_mixed_run(
            source,
            remaining,
            ledger=ledger,
            include_width=include_width,
            width_spine=width_spine,
            include_joint=include_joint,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
            scratch=scratch,
            normalized_f5=normalized_f5,
            physical_f5=physical_f5,
            normalized=0,
            division_ticks=0,
            odd_ticks=0,
            one_symbols=0,
            zero_symbols=0,
            run_actions=0,
            maximum_tail=_MAX_ROOT_ROUTE_TAIL,
        )
    except (MixedActionTailNotAdmitted, MixedMacroTailNotAdmitted):
        cached = None
        oversized_mixed_parent = True
    if cached is not None:
        return cached.executor_state(), d8_table

    # Give the existing exact-cylinder owner a chance before any new mixed
    # preview.  This preserves its larger-parent and consumer-specific hits on
    # the root route; the ordinary run loop remains the fallback owner.
    dyadic_state = _consume_cached_root_dyadic_action(
        source,
        remaining,
        ledger=ledger,
        macros=macros,
        scratch=scratch,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        include_innovation_tape=parity_builder is not None,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
    )
    if dyadic_state is not None:
        return dyadic_state, d8_table

    def try_complete_conditional_parent() -> MixedRunExecutorState | None:
        """Use a cold conditional motif only when its proved parent fits exactly.

        This helper is called early only without a shared cache.  When a shared
        cache exists, the ordinary cached/terminal/mixed route wins; the
        conditional power is reserved for a root that route cannot complete.
        """
        if include_width or parity_builder is not None:
            return None
        if source % 10 != 3 or source.bit_length() < 256 or remaining < 256:
            return None
        from number_compiler.sequences.collatz.conditional_scheduler_admission import (
            find_bounded_conditional_driver,
        )

        driver = find_bounded_conditional_driver(source, remaining)
        if driver is None:
            ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_FAST_REFUSALS)
            return None
        if macros is not None and remaining - driver[1] > 64:
            return None
        # Local import breaks the otherwise circular executor-state dependency.
        from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
            consume_conditional_scheduler_candidate,
            issue_conditional_scheduler_candidate,
        )

        candidate = issue_conditional_scheduler_candidate(
            source,
            remaining,
            scratch=scratch,
            ledger=ledger,
            macros=macros,
            include_f5=normalized_f5 is not None,
            include_joint=include_joint,
        )
        if candidate is None or candidate.physical_ticks > remaining:
            return None
        if 2 * candidate.physical_ticks < remaining:
            return None
        if macros is not None and remaining - candidate.physical_ticks > 64:
            return None
        try:
            return consume_conditional_scheduler_candidate(
                MixedRunExecutorState(
                    source,
                    remaining,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    normalized_f5,
                    physical_f5,
                ),
                candidate,
                scratch=scratch,
                control_bits=control_bits,
                include_joint=include_joint,
                joint_builder=joint_builder,
                ledger=ledger,
                macros=macros,
            )
        except BlockContextBudgetExceeded:
            # Budget preflight has no publisher side effects.
            return None

    terminal = None
    if source & 1:
        terminal = consume_terminal_power_two(
            source,
            remaining,
            ledger=ledger,
            scratch=scratch,
            control_bits=control_bits,
            include_joint=include_joint,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            normalized=0,
            division_ticks=0,
            odd_ticks=0,
            one_symbols=0,
            zero_symbols=0,
            run_actions=0,
            normalized_f5=normalized_f5,
            physical_f5=physical_f5,
            maximum_tail=_MAX_ROOT_ROUTE_TAIL,
        )
    if terminal is not None:
        return (
            MixedRunExecutorState(
                terminal.macro.endpoint,
                terminal.remaining,
                terminal.normalized,
                terminal.division_ticks,
                terminal.odd_ticks,
                terminal.one_symbols,
                terminal.zero_symbols,
                terminal.run_actions,
                terminal.normalized_f5,
                terminal.physical_f5,
            ),
            d8_table,
        )
    # Prefer the exact power-of-two endpoint before any cold conditional
    # discovery. A warm shared-cache parent already returned above.
    if macros is None or oversized_mixed_parent:
        root = try_complete_conditional_parent()
        if root is not None:
            return root, d8_table
        if oversized_mixed_parent:
            raise MixedRouteNotAdmitted
    macro, table = select_mixed_macro(
        source,
        remaining,
        templates=templates,
        ledger=ledger,
        d8_table=d8_table,
        max_preview_bits=32,
    )
    if macro is None:
        root = try_complete_conditional_parent() if macros is not None else None
        if root is not None:
            return root, table
        raise MixedRouteNotAdmitted
    if remaining - macro.physical_ticks > _MAX_ROOT_ROUTE_TAIL:
        if macros is not None:
            remember_mixed_action(macros, macro, scratch)
            root = try_complete_conditional_parent()
            if root is not None:
                return root, table
        raise MixedRouteNotAdmitted
    progress = consume_selected_mixed_run(
        macro,
        source,
        remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
        normalized=0,
        division_ticks=0,
        odd_ticks=0,
        one_symbols=0,
        zero_symbols=0,
        run_actions=0,
    )
    return progress.executor_state(), table


def _consume_cached_root_dyadic_action(
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    include_innovation_tape: bool,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
) -> MixedRunExecutorState | None:
    if macros is None:
        return None
    from number_compiler.sequences.collatz.temporal_dyadic_cache_execution import (
        try_consume_cached_dyadic_action,
    )

    try:
        state, _ = try_consume_cached_dyadic_action(
            MixedRunExecutorState(
                source,
                remaining,
                0,
                0,
                0,
                0,
                0,
                0,
                normalized_f5,
                physical_f5,
            ),
            True,
            ledger=ledger,
            macros=macros,
            scratch=scratch,
            include_innovation_tape=include_innovation_tape,
            include_width_spine=include_width,
            width_spine=width_spine,
            include_joint_cocycle=include_joint,
            joint_builder=joint_builder,
            maximum_tail=_MAX_ROOT_ROUTE_TAIL,
        )
    except MixedMacroTailNotAdmitted as exc:
        raise MixedRouteNotAdmitted from exc
    return state


def _progress_after_mixed_action(
    application: MixedMacroApplication,
    *,
    remaining: int,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
    run_actions: int,
    width_spine: CollatzWidthSpineAccumulator,
) -> MixedRunProgress:
    macro = application.macro
    (
        current,
        remaining,
        normalized,
        division_ticks,
        odd_ticks,
        one_symbols,
        zero_symbols,
    ) = advance_mixed_macro_counts(
        macro,
        remaining,
        normalized,
        division_ticks,
        odd_ticks,
        one_symbols,
        zero_symbols,
    )
    width_spine.reset_segment()
    return MixedRunProgress(
        application,
        current,
        remaining,
        normalized,
        division_ticks,
        odd_ticks,
        one_symbols,
        zero_symbols,
        run_actions + 1,
    )


def advance_mixed_macro_counts(
    macro: MixedClockMacro,
    remaining: int,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
) -> tuple[int, int, int, int, int, int, int]:
    """Apply one admitted macro's exact clocks to the executor counters."""
    return (
        macro.endpoint,
        remaining - macro.physical_ticks,
        normalized + macro.normalized_symbols,
        division_ticks + macro.normalized_symbols,
        odd_ticks + macro.odd_symbols,
        one_symbols + macro.odd_symbols,
        zero_symbols + macro.normalized_symbols - macro.odd_symbols,
    )


def _consume_mixed_macro(
    macro: MixedClockMacro,
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    from_cache: bool,
) -> MixedMacroApplication:
    validate_mixed_clock_macro(macro)
    if (
        macro.source != source
        or macro.physical_ticks > remaining
        or not macro.fields.certifies(source)
        or macro.fields.endpoint(source) != macro.endpoint
    ):
        raise ValueError("mixed Collatz action differs from its selected source")
    if parity_builder is not None:
        parity_builder.append_mixed_clock_macro(macro)
    if include_joint:
        joint_builder.require_steps(source, macro.normalized_symbols)
        joint_builder.append(
            macro.fields,
            source,
            macro.odd_symbols,
            macro.endpoint,
            cache=False,
        )
    if include_width:
        if not width_spine.complete or macro.width_blank is None:
            raise ValueError("mixed action lacks its demanded exact width summary")
        width_spine.record(macro.width_blank)
    if normalized_f5 is not None and physical_f5 is not None:
        f5 = project_dyadic_fields_f5(macro.fields)
        normalized_f5 = normalized_f5.then(f5)
        physical_f5 = physical_f5.then(f5)
    if macros is not None:
        if from_cache:
            applied_mixed_action(macros)
        else:
            remember_mixed_action(macros, macro, scratch)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_MIXED_CLOCK_MACRO_ACTIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_MIXED_CLOCK_MACRO_REPETITIONS,
        macro.repetitions,
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_MIXED_CLOCK_MACRO_PHYSICAL_TICKS,
        macro.physical_ticks,
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        source.bit_length()
        + macro.endpoint.bit_length()
        + macro.fields.gain.bit_length()
        + macro.fields.offset.bit_length(),
    )
    return MixedMacroApplication(macro, normalized_f5, physical_f5)


def consume_cached_mixed_macro(
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    maximum_tail: int | None = None,
) -> MixedMacroApplication | None:
    """Probe a complete source/action/program parent before any discovery."""
    if macros is None:
        return None
    macro = lookup_mixed_action(
        macros,
        source,
        remaining,
        scratch,
        include_width=include_width,
        minimum_physical_ticks=(
            max(0, remaining - maximum_tail) if maximum_tail is not None else None
        ),
    )
    if macro is None:
        return None
    if maximum_tail is not None and remaining - macro.physical_ticks > maximum_tail:
        raise MixedMacroTailNotAdmitted
    return _consume_mixed_macro(
        macro,
        source,
        remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
        from_cache=True,
    )


def select_mixed_macro(
    source: int,
    remaining: int,
    *,
    templates: BoundaryActionTemplateMemo,
    ledger: ResourceLedger,
    d8_table: D8TemporalTable | None,
    max_preview_bits: int | None = None,
) -> tuple[MixedClockMacro | None, D8TemporalTable | None]:
    """Run bounded D8-backed previews while preserving the query row owner."""
    table = d8_table
    if table is None:
        table = D8TemporalTable.for_ledger(ledger)
    if max_preview_bits is None:
        macro = select_mixed_clock_macro(
            source,
            remaining,
            templates=templates,
            d8_table=table,
        )
    else:
        macro = select_mixed_clock_macro(
            source,
            remaining,
            templates=templates,
            d8_table=table,
            max_preview_bits=max_preview_bits,
        )
    return macro, table


def consume_selected_mixed_macro(
    macro: MixedClockMacro,
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
) -> MixedMacroApplication:
    return _consume_mixed_macro(
        macro,
        source,
        remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
        from_cache=False,
    )


def consume_cached_mixed_run(
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
    run_actions: int,
    maximum_tail: int | None = None,
) -> MixedRunProgress | None:
    application = consume_cached_mixed_macro(
        source,
        remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
        maximum_tail=maximum_tail,
    )
    if application is None:
        return None
    return _progress_after_mixed_action(
        application,
        remaining=remaining,
        normalized=normalized,
        division_ticks=division_ticks,
        odd_ticks=odd_ticks,
        one_symbols=one_symbols,
        zero_symbols=zero_symbols,
        run_actions=run_actions,
        width_spine=width_spine,
    )


def consume_selected_mixed_run(
    macro: MixedClockMacro,
    source: int,
    remaining: int,
    *,
    ledger: ResourceLedger,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
    run_actions: int,
) -> MixedRunProgress:
    application = consume_selected_mixed_macro(
        macro,
        source,
        remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
    )
    return _progress_after_mixed_action(
        application,
        remaining=remaining,
        normalized=normalized,
        division_ticks=division_ticks,
        odd_ticks=odd_ticks,
        one_symbols=one_symbols,
        zero_symbols=zero_symbols,
        run_actions=run_actions,
        width_spine=width_spine,
    )


def select_and_consume_mixed_run(
    source: int,
    remaining: int,
    *,
    selected: MixedClockMacro | None,
    templates: BoundaryActionTemplateMemo,
    ledger: ResourceLedger,
    d8_table: D8TemporalTable | None,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
    run_actions: int,
) -> tuple[MixedRunProgress | None, D8TemporalTable | None]:
    macro = selected
    table = d8_table
    if macro is None:
        macro, table = select_mixed_macro(
            source, remaining, templates=templates, ledger=ledger, d8_table=table
        )
    if macro is None:
        return None, table
    progress = consume_selected_mixed_run(
        macro,
        source,
        remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
        normalized=normalized,
        division_ticks=division_ticks,
        odd_ticks=odd_ticks,
        one_symbols=one_symbols,
        zero_symbols=zero_symbols,
        run_actions=run_actions,
    )
    return progress, table


def consume_cached_mixed_state(
    state: MixedRunExecutorState,
    *,
    ledger: ResourceLedger,
    include_width: bool,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros,
    scratch: RunArithmeticWorkspace,
) -> MixedRunExecutorState | None:
    """Apply a cached complete action and return the updated run state."""
    progress = consume_cached_mixed_run(
        state.current,
        state.remaining,
        ledger=ledger,
        include_width=include_width,
        width_spine=width_spine,
        include_joint=include_joint,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        scratch=scratch,
        normalized_f5=state.normalized_f5,
        physical_f5=state.physical_f5,
        normalized=state.normalized,
        division_ticks=state.division_ticks,
        odd_ticks=state.odd_ticks,
        one_symbols=state.one_symbols,
        zero_symbols=state.zero_symbols,
        run_actions=state.run_actions,
    )
    return None if progress is None else progress.executor_state()
