"""Admit source-guarded Collatz matrix spans with lazy parity ownership."""

from __future__ import annotations

from collections.abc import Callable
from contextlib import ExitStack
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.boundary_macros import (
        AdmittedBoundaryMacroPlan,
    )
    from number_compiler.sequences.collatz.boundary_templates import (
        BoundaryActionTemplateMemo,
    )
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        AdjacentBorderCarryMatrix,
        NamedBorderCarryMatrix,
    )
    from number_compiler.sequences.collatz.parity_carry_tape_actions import (
        LedgeredParityTapeActions,
    )


def _checked_actions(
    actions: LedgeredParityTapeActions, ledger: ResourceLedger
) -> LedgeredParityTapeActions:
    """Authenticate a supplied owner only on paths that actually need one."""
    from number_compiler.sequences.collatz.parity_carry_tape_actions import (
        LedgeredParityTapeActions,
    )

    if type(actions) is not LedgeredParityTapeActions or actions.ledger is not ledger:
        raise ValueError(
            "powered Collatz parity actions require the exact source ledger"
        )
    return actions


def _admit_next_macro(
    endpoint: int,
    ledger: ResourceLedger,
    physical_steps: int,
    *,
    parity_actions: LedgeredParityTapeActions | None,
    templates: BoundaryActionTemplateMemo,
    admitted_plan: AdmittedBoundaryMacroPlan | None = None,
) -> NamedBorderCarryMatrix | None:
    """Select one issued macro, consuming an optional already-admitted plan."""
    from number_compiler.sequences.collatz.boundary_macros import (
        select_admitted_boundary_macro,
        validate_admitted_boundary_macro_plan,
    )
    from number_compiler.sequences.collatz.boundary_templates import (
        BoundaryActionTemplateMemo,
    )
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        certify_named_border_carry_matrix,
    )
    from number_compiler.sequences.collatz.temporal_border_return_execution import (
        admit_physical_matrix_boundary_plan,
    )

    if type(endpoint) is not int or endpoint < 1:
        raise ValueError("powered Collatz join requires a positive endpoint")
    if type(ledger) is not ResourceLedger:
        raise TypeError("powered Collatz join requires its owning resource ledger")
    if (
        type(templates) is not BoundaryActionTemplateMemo
        or templates.ledger is not ledger
    ):
        raise ValueError("powered Collatz templates require the exact source ledger")
    if type(physical_steps) is not int or physical_steps < 1:
        raise ValueError("powered Collatz macro needs a positive physical horizon")

    plan = admitted_plan
    if plan is None:
        plan = admit_physical_matrix_boundary_plan(endpoint, physical_steps, ledger)
    else:
        validate_admitted_boundary_macro_plan(plan)
        if plan.source != endpoint or plan.available_physical_ticks != physical_steps:
            raise ValueError("pre-admitted Collatz plan belongs to another source span")
    if plan is None:
        return None

    macro = select_admitted_boundary_macro(plan, templates=templates)
    if macro.source != endpoint or not 1 <= macro.physical_ticks <= physical_steps:
        return None
    result = certify_named_border_carry_matrix(
        macro,
        ledger=ledger,
        parity_actions=parity_actions,
    )
    return result


def _join_admitted_span(
    source: int,
    ledger: ResourceLedger,
    physical_steps: int,
    actions: LedgeredParityTapeActions,
    templates: BoundaryActionTemplateMemo,
    first_plan: AdmittedBoundaryMacroPlan,
) -> NamedBorderCarryMatrix | AdjacentBorderCarryMatrix | None:
    """Reuse adjacent issued child actions across exact source seams."""
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        AdjacentBorderCarryMatrix,
    )

    first = _admit_next_macro(
        source,
        ledger,
        physical_steps,
        parity_actions=actions,
        templates=templates,
        admitted_plan=first_plan,
    )
    if first is None:
        return None
    accumulated: NamedBorderCarryMatrix | AdjacentBorderCarryMatrix = first
    remaining = physical_steps - first.physical_ticks
    current = first.endpoint
    if remaining == 0:
        return first

    for _ in range(physical_steps):
        parent_tape = accumulated.joined.parity_tape_for_action(cache=actions)
        if parent_tape is None:
            return None
        # Keep the exact left action live while admitting its next source.
        with actions.temporary_root_pin(parent_tape) as lease:
            segment = _admit_next_macro(
                current,
                ledger,
                remaining,
                parity_actions=actions,
                templates=templates,
            )
            if segment is None or segment.physical_ticks > remaining:
                return None
            next_join: GuardedPortJoin | None = accumulated.joined.then(
                segment.joined,
                ledger=ledger,
                parity_cache=actions,
            )
            if next_join is None:
                return None
            next_accumulated = AdjacentBorderCarryMatrix.compose_admitted_children(
                accumulated, segment, next_join
            )
            lease.commit()
        accumulated = next_accumulated
        remaining -= segment.physical_ticks
        current = segment.endpoint
        if remaining == 0:
            return accumulated
    return None


def retain_single_macro_scratch(
    scope: ExitStack,
    ledger: ResourceLedger,
    source: int,
    plan: AdmittedBoundaryMacroPlan,
) -> None:
    """Hold the bounded tape, binding and prefix workspace through packet use."""
    from number_compiler.sequences.collatz.boundary_macros import (
        validate_admitted_boundary_macro_plan,
    )

    validate_admitted_boundary_macro_plan(plan)
    if type(source) is not int or source != plan.source:
        raise ValueError("single-macro scratch belongs to another source")
    owner = ledger.register(
        f"collatz-single-matrix-scratch-{ledger.owner_count}", "execution_stack"
    )
    try:
        reservation = LedgerReservation(ledger, owner)
    except BaseException as error:
        try:
            ledger.mark_disposed(owner)
        except BaseException as cleanup_error:
            raise cleanup_error from error
        raise
    try:
        scope.callback(
            _close_single_macro_scratch,
            ledger,
            owner,
            reservation,
        )
    except BaseException as error:
        try:
            reservation.close()
            ledger.mark_disposed(owner)
        except BaseException as cleanup_error:
            raise cleanup_error from error
        raise
    # Every normalized letter contributes at most one leaf, one repeat node
    # and one concat node; fixed binding and root metadata add eight records.
    # Each record can retain action coefficients bounded by source and horizon
    # bit lengths. Prefix traversal has its own shorter-lived reservation.
    entries = 3 * plan.normalized_symbols + 8
    coefficient_words = max(
        1,
        (2 * plan.normalized_symbols + source.bit_length() + 63) // 64,
    )
    nodes = 96 + entries * (24 + 8 * coefficient_words)
    try:
        reservation.reserve(entries=entries, nodes=nodes)
    except BlockContextBudgetExceeded as error:
        try:
            _close_single_macro_scratch(ledger, owner, reservation)
        except BaseException as cleanup_error:
            raise cleanup_error from error
        raise


def _close_single_macro_scratch(
    ledger: ResourceLedger,
    owner: int,
    reservation: LedgerReservation,
) -> None:
    """Retry one transient reservation-close fault before retiring its owner."""
    failure: BaseException | None = None
    try:
        reservation.close()
    except BaseException as error:
        failure = error
        try:
            reservation.close()
        except BaseException as retry_error:
            try:
                ledger.validate_reservation(reservation)
            except RuntimeError:
                # A fault after the atomic close can report failure even
                # though the reservation is already gone.
                pass
            else:
                raise retry_error from error
    if not ledger.account_status(owner).disposed:
        ledger.mark_disposed(owner)
    if failure is not None:
        raise failure


def _admit_with_templates(
    source: int,
    ledger: ResourceLedger,
    physical_steps: int,
    templates: BoundaryActionTemplateMemo,
    *,
    parity_actions: LedgeredParityTapeActions | None,
    parity_actions_factory: Callable[[], LedgeredParityTapeActions] | None,
    trace_required: bool,
    single_macro_scope: ExitStack | None,
) -> NamedBorderCarryMatrix | AdjacentBorderCarryMatrix | None:
    from number_compiler.sequences.collatz.temporal_border_return_execution import (
        admit_physical_matrix_boundary_plan,
    )

    first_plan = admit_physical_matrix_boundary_plan(source, physical_steps, ledger)
    if first_plan is None:
        return None
    actions = parity_actions
    if actions is None and parity_actions_factory is not None:
        if (
            not trace_required
            and first_plan.physical_ticks == physical_steps
            and single_macro_scope is not None
        ):
            try:
                retain_single_macro_scratch(
                    single_macro_scope, ledger, source, first_plan
                )
            except BlockContextBudgetExceeded:
                # A conservative scratch envelope may refuse under a tight
                # ledger even when the established owner route can fit. Reuse
                # this exact issued plan and preserve the old exact path.
                actions = _checked_actions(parity_actions_factory(), ledger)
            else:
                return _admit_next_macro(
                    source,
                    ledger,
                    physical_steps,
                    parity_actions=None,
                    templates=templates,
                    admitted_plan=first_plan,
                )
        if actions is None:
            actions = _checked_actions(parity_actions_factory(), ledger)
    if actions is None:
        raise RuntimeError("matrix span has no parity action owner")
    return _join_admitted_span(
        source,
        ledger,
        physical_steps,
        actions,
        templates,
        first_plan,
    )


def admit_matrix_span(
    source: int,
    ledger: ResourceLedger,
    physical_steps: int,
    *,
    parity_actions: LedgeredParityTapeActions | None = None,
    parity_actions_factory: Callable[[], LedgeredParityTapeActions] | None = None,
    trace_required: bool = False,
    single_macro_scope: ExitStack | None = None,
) -> NamedBorderCarryMatrix | AdjacentBorderCarryMatrix | None:
    """Admit a bounded span, creating the parity owner only when it will be used.

    A complete, single-macro summary without a trace needs no reusable parity
    cache. Every joined span and every trace still acquires the query-owned
    cache before the first macro is certified, so its first action is not
    refolded when later children are joined.
    """
    from number_compiler.sequences.collatz.boundary_templates import (
        BoundaryActionTemplateMemo,
    )
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        MAX_ENDPOINT_PHYSICAL_STEPS,
    )

    if type(source) is not int or source < 1:
        raise ValueError("powered Collatz matrix requires a positive source")
    if type(ledger) is not ResourceLedger:
        raise TypeError("powered Collatz matrix requires its source ledger")
    if (
        type(physical_steps) is not int
        or not 1 <= physical_steps <= MAX_ENDPOINT_PHYSICAL_STEPS
    ):
        raise ValueError("powered Collatz physical span exceeds its finite horizon")
    if type(trace_required) is not bool:
        raise TypeError("trace requirement must be a Boolean")

    if parity_actions is not None:
        actions = _checked_actions(parity_actions, ledger)
        with BoundaryActionTemplateMemo(ledger) as templates:
            return _admit_with_templates(
                source,
                ledger,
                physical_steps,
                templates,
                parity_actions=actions,
                parity_actions_factory=parity_actions_factory,
                trace_required=trace_required,
                single_macro_scope=single_macro_scope,
            )

    if parity_actions_factory is None:
        # Preserve direct-call ownership semantics. Public query paths pass a
        # lazy factory, while standalone callers own one bounded chain cache.
        from number_compiler.sequences.collatz.parity_carry_tape_actions import (
            LedgeredParityTapeActions,
        )

        with (
            LedgeredParityTapeActions(ledger) as actions,
            BoundaryActionTemplateMemo(ledger) as templates,
        ):
            return _admit_with_templates(
                source,
                ledger,
                physical_steps,
                templates,
                parity_actions=actions,
                parity_actions_factory=None,
                trace_required=trace_required,
                single_macro_scope=single_macro_scope,
            )

    # Query-owned lazy path: preflight before the parity owner or its module is
    # loaded. A complete one-macro summary can be certified with bounded
    # standalone prefix scratch; traces and joined spans need the owner.
    with BoundaryActionTemplateMemo(ledger) as templates:
        return _admit_with_templates(
            source,
            ledger,
            physical_steps,
            templates,
            parity_actions=None,
            parity_actions_factory=parity_actions_factory,
            trace_required=trace_required,
            single_macro_scope=single_macro_scope,
        )


__all__ = ["admit_matrix_span", "retain_single_macro_scratch"]
