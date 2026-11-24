"""Production issue/consume for source-guarded non-border Collatz cyclic rows.

The authenticated cyclic row supplies the scalar endpoint and demanded
field, width and parity projections without a physical parity history.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _keys
from number_compiler.sequences.collatz.cyclic_abc_grammar import (
    CyclicRowAdmission,
    issue_cyclic_row,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
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
    from number_compiler.sequences.collatz.tape_width import (
        CollatzWidthSpineAccumulator,
    )
    from number_compiler.sequences.collatz.temporal_run_state import CollatzRunControl


def issued_field_prefix(admitted: CyclicRowAdmission) -> DyadicTerminalFieldAction:
    """Project the issued Laurent endpoint, predecessor and geometric sum."""
    return DyadicTerminalFieldAction.from_cyclic_admission(admitted)


def exact_cyclic_width_ledger(admitted: CyclicRowAdmission) -> BlankLedger:
    """Exact physical width extrema from first/last motif phases, not history.

    Let P be the normalized affine motif. On authenticated complete copies,
    X_{m+1}=P(X_m) has positive slope. The sign of X_{m+1}-X_m is constant
    for all m, because differences are multiplied by that positive slope.
    Every phase prefix and the intermediate 3*x+1 in an odd shortcut is an
    increasing affine function of X_m. Hence each phase's minimum/maximum
    across whole copies occurs in the FIRST or LAST copy. The incomplete
    final copy is traversed once. Work: O(motif length + log copies), not
    O(physical ticks); no width occurrence tape is retained.
    """
    if type(admitted) is not CyclicRowAdmission:
        raise TypeError("width ledger requires an authenticated cyclic admission")
    admitted.require_issued()
    row, source, action = admitted.guard.action, admitted.source, admitted.action
    if action.steps < 1:
        raise ValueError("width ledger lacks the exact source/endpoint guard")
    source_width = source.bit_length()
    minimum = maximum = source_width

    def observe(word: str, inlet: int) -> int:
        nonlocal minimum, maximum
        value = inlet
        for bit in word:
            if (value & 1) != int(bit):
                raise AssertionError("width phase differs from the issued parity row")
            if bit == "1":
                value = 3 * value + 1
                width = value.bit_length()
                minimum = min(minimum, width)
                maximum = max(maximum, width)
            value >>= 1
            width = value.bit_length()
            minimum = min(minimum, width)
            maximum = max(maximum, width)
        return value

    copies, tail = divmod(action.steps, len(row.word))
    after_copies = source
    if copies:
        first_endpoint = observe(row.word, source)
        if copies > 1:
            last_steps = (copies - 1) * len(row.word)
            last_source, _ = admitted.guard.point(last_steps, 3 ** row.odds(last_steps))
            after_copies = observe(row.word, last_source)
        else:
            after_copies = first_endpoint
    final = observe(row.word[:tail], after_copies) if tail else after_copies
    if final != admitted.endpoint:
        raise AssertionError("width extrema lost the exact powered endpoint")
    return BlankLedger(
        final.bit_length() - source_width,
        minimum - source_width,
        maximum - source_width,
    )


def consume_source_cyclic_abc_row(
    control: CollatzRunControl,
    *,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros_present: bool,
    require_mixed_prefix: bool,
    require_boundary_witness: bool,
) -> bool:
    """Replace long mixed classifications with one certified row/phase action."""
    if (
        control.phase != 0
        or control.pending_normalized_source is not None
        or control.remaining < 16
        or not 10 <= control.current.bit_length() <= 4096
        or (control.include_innovation_tape and parity_builder is None)
        or macros_present
        or require_mixed_prefix
    ):
        return False

    if require_boundary_witness:
        # An innovation request may use the cyclic continuation only AFTER
        # its first physical boundary macro was stamped by the original
        # selector. Cyclic affine equality alone cannot issue that stamp.
        stamp = control.first_boundary_stamp
        macro = control.first_boundary_macro
        if (
            stamp is None
            or macro is None
            or not stamp.certifies(
                control.seed, control.physical_ticks, stamp.occurrence, macro
            )
        ):
            return False

    source = control.current
    ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_SOURCE_QUERIES)

    def preflight(steps: int) -> None:
        scratch.require_bits(
            8
            * (
                source.bit_length()
                + 4 * steps
                + 4 * control.remaining.bit_length()
                + 128
            )
        )

    try:
        admission = issue_cyclic_row(source, control.remaining, reserve_bits=preflight)
    except BlockContextBudgetExceeded:
        ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_BUDGET_REFUSALS)
        return False
    if admission is None:
        return False
    action = admission.action
    endpoint = admission.endpoint
    if endpoint <= 0:
        raise AssertionError("mixed row lacks its exact source guard")

    # Prepare optional projections before publishing any scalar state.
    if control.joint_requested:
        joint_builder.require_steps(source, action.steps)
    width_piece = exact_cyclic_width_ledger(admission) if width_spine.complete else None
    next_normalized_f5 = control.normalized_f5
    next_physical_f5 = control.physical_f5
    if next_normalized_f5 is not None or next_physical_f5 is not None:
        if next_normalized_f5 is None or next_physical_f5 is None:
            raise AssertionError("F5 demand lacks its source-issued paired action")
        inverse = pow(2, -action.steps, 5)
        f5 = CollatzF5AffineAction(
            action.gain * inverse % 5, action.offset * inverse % 5
        )
        next_normalized_f5 = next_normalized_f5.then(f5)
        next_physical_f5 = next_physical_f5.then(f5)
    if parity_builder is not None:
        parity_builder.append_cyclic_row(admission)
        ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_PARITY_PROJECTIONS)
    if control.joint_requested:
        joint_builder.append_cyclic(admission)
        ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_JOINT_PROJECTIONS)
    if width_piece is not None:
        width_spine.record(width_piece)
        copies, tail = divmod(action.steps, len(admission.guard.action.word))
        ledger.bump(
            _keys.COLLATZ_CYCLIC_GRAMMAR_WIDTH_PHASE_STEPS,
            min(copies, 2) * len(admission.guard.action.word) + tail,
        )
        ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_WIDTH_PROJECTIONS)
    control.current = endpoint
    control.remaining -= admission.physical_ticks
    control.normalized += action.steps
    control.division_ticks += action.steps
    control.one_symbols += action.odds
    control.zero_symbols += action.steps - action.odds
    control.odd_ticks += action.odds
    control.normalized_f5 = next_normalized_f5
    control.physical_f5 = next_physical_f5
    control.run_actions += 1
    control.unified_skew_retry = True
    control.weighted_binding = None
    control.weighted_cursor_source = None
    ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_ADMITTED_ACTIONS)
    ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_CLASSIFICATIONS_ELIDED, action.steps)
    ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_SHORTCUT_STEPS, action.steps)
    ledger.bump(_keys.COLLATZ_CYCLIC_GRAMMAR_PHYSICAL_TICKS, admission.physical_ticks)
    return True


__all__ = [
    "consume_source_cyclic_abc_row",
    "exact_cyclic_width_ledger",
    "issued_field_prefix",
]
