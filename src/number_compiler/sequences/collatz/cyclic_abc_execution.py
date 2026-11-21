"""Production issue/consume for source-guarded non-border Collatz cyclic rows.

The scalar route needs no physical parity history. An optional F5
projection uses the same row, while joint, width, innovation and root-checkpoint
consumers retain their prior authoritative publishers.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
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
    project_dyadic_fields_f5,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.sequences.collatz.tape_width import (
        CollatzWidthSpineAccumulator,
    )
    from number_compiler.sequences.collatz.temporal_run_state import CollatzRunControl


def issued_field_prefix(admitted: CyclicRowAdmission) -> DyadicTerminalFieldAction:
    """Reuse the pre-existing checked ordered field-action monoid.

    The producer first checks the full dyadic guard and exact affine
    coefficients; only the bounded motif is decoded into field letters.
    """
    row = admitted.row
    length = admitted.action.steps
    factor = DyadicTerminalFieldAction.identity()
    zero = DyadicTerminalFieldAction.zero_run(1)
    one = DyadicTerminalFieldAction.one_run(1)
    for word, count in zip(row.abc.words, row.abc.counts, strict=True):
        if not count:
            continue
        letter_action = DyadicTerminalFieldAction.identity()
        for bit in word:
            letter_action = letter_action.then(one if bit == "1" else zero)
        factor = factor.then(letter_action.power(count))
    copies, tail = divmod(length, len(row.word))
    result = factor.power(copies)
    for bit in row.word[:tail]:
        result = result.then(one if bit == "1" else zero)
    if (
        result.steps != length
        or result.gain != admitted.action.gain
        or result.offset != admitted.action.offset
        or not result.certifies(admitted.source)
        or result.endpoint(admitted.source) != admitted.endpoint
    ):
        raise AssertionError("periodic grammar lost the authenticated ordered action")
    return result


def consume_source_cyclic_abc_row(
    control: CollatzRunControl,
    *,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    width_spine: CollatzWidthSpineAccumulator,
    macros_present: bool,
    require_mixed_prefix: bool,
    parity_requested: bool,
) -> bool:
    """Replace long mixed classifications with one certified row/phase action."""
    if (
        control.phase != 0
        or control.pending_normalized_source is not None
        or control.remaining < 16
        or not 10 <= control.current.bit_length() <= 4096
        or control.joint_requested
        or width_spine.requested
        or control.include_innovation_tape
        or parity_requested
        or macros_present
        or require_mixed_prefix
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
    if endpoint <= 0 or not action.certifies(source):
        raise AssertionError("mixed row lacks its exact source guard")

    # Prepare optional projections before publishing any scalar state.
    fields = (
        issued_field_prefix(admission) if control.normalized_f5 is not None else None
    )
    next_normalized_f5 = control.normalized_f5
    next_physical_f5 = control.physical_f5
    if next_normalized_f5 is not None or next_physical_f5 is not None:
        if fields is None or next_normalized_f5 is None or next_physical_f5 is None:
            raise AssertionError("F5 demand lacks its source-issued paired action")
        f5 = project_dyadic_fields_f5(fields)
        next_normalized_f5 = next_normalized_f5.then(f5)
        next_physical_f5 = next_physical_f5.then(f5)
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


__all__ = ["consume_source_cyclic_abc_row", "issued_field_prefix"]
