"""Production consumer for source-certified weighted unary future classes.

The represented alphabet is one repeated normalized parity word.  A border
plan, not this class, authorizes its decimal-family outputs; all optional
F5/joint/width/parity publishers remain the existing checked consumers.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import ENTRY_89_AT_NINE
from number_compiler.sequences.collatz.boundary_macros import (
    select_admitted_boundary_macro,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.temporal_border_return_execution import (
    admit_physical_boundary_plan,
    consume_named_boundary,
)
from number_compiler.sequences.collatz.weighted_right_congruence import (
    bind_weighted_right_class,
    transport_weighted_right_binding,
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
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )
    from number_compiler.sequences.collatz.tape_width import (
        CollatzWidthSpineAccumulator,
    )
    from number_compiler.sequences.collatz.temporal_run_state import CollatzRunControl


def consume_weighted_right_run(
    control: CollatzRunControl,
    *,
    seed: int,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    templates: BoundaryActionTemplateMemo,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
) -> bool:
    """Consume long, fully authenticated 89 odd-runs before speculative joins.

    All other macro families retain their independent certified producers.  A
    cheap dyadic necessary condition avoids eager compilation on short/unknown
    paths.  Accepted actions reuse the actual named publisher and its ports.
    """
    source = control.current
    remaining = control.remaining
    if remaining < 256 or source % 10 != 9 or (source + 1) % (1 << 16):
        return False
    # The named selector is authoritative about both its family and extent.
    plan = admit_physical_boundary_plan(source, remaining, ledger)
    if (
        plan is None
        or plan.identity != ENTRY_89_AT_NINE
        or plan.repetitions < 16
        or plan.physical_ticks < 32
        or plan.physical_ticks > remaining
        or remaining - plan.physical_ticks < 64
    ):
        return False
    word = DyadicTerminalFieldAction.one_run(1)
    binding = control.weighted_binding
    if (
        binding is None
        or control.weighted_cursor_source != source
        or binding.word != word
        or not binding.guard.admits(source)
        or binding.future.remaining is not None
        and binding.future.remaining < plan.repetitions
    ):
        binding = bind_weighted_right_class(
            word, source, preflight=scratch.require_bits
        )
    if (
        binding.future.remaining is not None
        and binding.future.remaining < plan.repetitions
    ):
        raise AssertionError("named 89 producer exceeded the weighted future lifetime")
    # The named issuer constructs the exact source-bound action once. The
    # weighted right-congruence transition consumes that same authenticated
    # field action, so it does not independently power the same word.
    issued_boundary = select_admitted_boundary_macro(plan, templates=templates)
    transition = binding.power(
        plan.repetitions,
        action_authority=issued_boundary,
        preflight=scratch.require_bits,
    )
    weight = transition.evaluate(source)
    if (
        issued_boundary.endpoint != weight.physical_endpoint
        or issued_boundary.endpoint != weight.normalized_endpoint
        or issued_boundary.physical_ticks != 2 * plan.repetitions
        or issued_boundary.odd_symbols != plan.repetitions
    ):
        raise AssertionError(
            "named border action differs from weighted future certificate"
        )
    state, boundary, lookup = consume_named_boundary(
        control.snapshot(),
        plan,
        seed=seed,
        ledger=ledger,
        scratch=scratch,
        control_bits=control_bits,
        templates=templates,
        include_joint=control.joint_requested,
        width_spine=width_spine,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        macros=macros,
        prior_lookup_enabled=control.lookup_enabled,
        issued_boundary=issued_boundary,
    )
    if state.current != weight.physical_endpoint:
        raise AssertionError("weighted future consumer lost the physical endpoint")
    control.lookup_enabled = lookup
    control.apply_boundary(state, boundary)
    if transition.target.remaining == 0:
        # The endpoint has reached the exact first-changed-bit seam; the old
        # repeated word no longer certifies even one next transition.
        control.weighted_binding = None
        control.weighted_cursor_source = None
    else:
        control.weighted_binding = transport_weighted_right_binding(
            transition, state.current
        )
        control.weighted_cursor_source = state.current
    return True


__all__ = ["bind_weighted_right_class", "consume_weighted_right_run"]
