"""Source-bound admission of one exact segment for a unified skew chain."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    CollatzSegmentIdentity,
    NonBorderSegment,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    select_border_return_macro,
    validate_border_return_macro,
)
from number_compiler.sequences.collatz.boundary_macros import (
    AdmittedBoundaryMacroPlan,
    admit_boundary_macro_plan,
    select_admitted_boundary_macro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.innovation_input_tape import (
    boundary_macro_specs,
)
from number_compiler.sequences.collatz.joint_radix_border import JointRadix6Source
from number_compiler.sequences.collatz.terminal_preimage import (
    select_terminal_power2_macro,
    validate_terminal_power2_macro,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    FactorSpecs,
    SeamWitness,
)


def _select_admitted_boundary_plan(
    plan: AdmittedBoundaryMacroPlan,
    templates: BoundaryActionTemplateMemo,
    preflight: Callable[[int], None] | None,
) -> tuple[
    CollatzSegmentIdentity,
    int,
    DyadicTerminalFieldAction,
    BlankLedger,
    FactorSpecs,
    SeamWitness | None,
]:
    if preflight is not None:
        preflight(plan.normalized_symbols)
    boundary = select_admitted_boundary_macro(plan, templates=templates)
    validate_boundary_macro(boundary)
    return (
        boundary.identity,
        boundary.odd_symbols,
        boundary.fields,
        boundary.width_blank,
        boundary_macro_specs(boundary),
        boundary,
    )


def admit_next_unified_segment(
    source: int,
    remaining: int,
    templates: BoundaryActionTemplateMemo,
    preflight: Callable[[int], None] | None = None,
    *,
    ledger: ResourceLedger | None = None,
    initial_plan: AdmittedBoundaryMacroPlan | None = None,
    initial_plan_checked: bool = False,
    radix_state: JointRadix6Source | None = None,
) -> (
    tuple[
        CollatzSegmentIdentity,
        int,
        DyadicTerminalFieldAction,
        BlankLedger,
        FactorSpecs,
        SeamWitness | None,
    ]
    | None
):
    """Select one exact bounded action without replaying parity bits."""
    state = (
        radix_state
        if radix_state is not None
        else JointRadix6Source.from_source(source)
    )
    if type(state) is not JointRadix6Source:
        raise TypeError("skew macro selector requires an exact radix-6 source state")
    state.require_source(source)
    if not state.even and source > 1:
        power = 3 * source + 1
        exponent = power.bit_length() - 1
        if power & (power - 1) == 0 and exponent + 1 <= remaining:
            if preflight is not None:
                preflight(exponent)
            terminal = select_terminal_power2_macro(source, remaining)
        else:
            terminal = None
        if terminal is not None:
            validate_terminal_power2_macro(terminal)
            return (
                NonBorderSegment.TERMINAL_POWER_OF_TWO,
                1,
                terminal.fields,
                terminal.width_blank,
                (((1,), 1), ((0,), terminal.exponent - 1)),
                terminal,
            )

    plan = (
        initial_plan
        if initial_plan_checked
        else admit_boundary_macro_plan(
            source,
            remaining,
            minimum_repetitions=1,
            radix_state=state,
            ledger=ledger,
        )
    )
    if plan is not None and plan.identity in (
        ENTRY_421,
        ENTRY_4721,
        ENTRY_0563,
        *ENTRY_26847_PHASES,
        ENTRY_89_AT_NINE,
    ):
        return _select_admitted_boundary_plan(plan, templates, preflight)

    if state.decimal_residue(10) in (0, 3, 5) or state.decimal_residue(20) == 6:
        border = select_border_return_macro(
            source,
            remaining,
            preflight=preflight,
            ledger=ledger,
            radix_state=state,
        )
        if border is not None:
            validate_border_return_macro(border)
            return (
                border.identity,
                border.odd_symbols,
                border.fields,
                border.width_blank,
                tuple(((bit,), count) for bit, count in border.parts),
                border,
            )

    if plan is not None:
        return _select_admitted_boundary_plan(plan, templates, preflight)

    if source > 1 and state.even:
        exponent = v2_positive(source)
        if exponent <= remaining:
            if preflight is not None:
                preflight(exponent)
            fields = DyadicTerminalFieldAction.zero_run(exponent)
            return (
                NonBorderSegment.ZERO_RUN,
                0,
                fields,
                BlankLedger(-exponent, -exponent, 0),
                (((0,), exponent),),
                None,
            )
    return None
