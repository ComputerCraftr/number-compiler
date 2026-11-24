"""Source-bound powers of the certified 60/40 Mahler graph row.

The immutable row definition is shared across receiving sources.  Its
application separately checks the source cylinder, the fractional interval,
the full ordered port sequence, and every requested repeat.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING, Final

from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    HalfOpenInterval,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction,
)
from number_compiler.sequences.antihydra.runtime import ArithmeticResult

if TYPE_CHECKING:
    from collections.abc import Callable


_MAX_TICKS: Final[int] = 4096


@dataclass(frozen=True, slots=True)
class _GraphRow:
    entry: tuple[int, int]
    source_residue: int


# Port = (integer units and fractional tenths, integer tens parity).
# The 00 parity action visits 60 -> 40 -> 60 or its rotation.
_GRAPH_ROWS: Final[tuple[_GraphRow, ...]] = (
    _GraphRow((60, 1), 16),
    _GraphRow((40, 0), 64),
)


def _port(integer: int, tail: ExactRational) -> tuple[int, int]:
    digit = 10 * tail.numerator // tail.denominator
    return (10 * (integer % 10) + digit, integer // 10 % 2)


def _row_action() -> MahlerJointFutureAction:
    """The exact 00 action with every fractional tenth in the 0 port."""
    action = MahlerJointFutureAction.zero_run(2)
    return MahlerJointFutureAction.with_gain(
        action.extent,
        action.residue,
        action.innovation,
        action.guard.intersect(
            HalfOpenInterval(ExactRational(0), ExactRational(2, 45))
        ),
        action.safety,
        action.gain,
    )


_ROW_ACTION: Final[MahlerJointFutureAction] = _row_action()


def _require_row_action(action: MahlerJointFutureAction) -> None:
    """Verify the immutable catalogue operator before applying it."""
    if (
        type(action) is not MahlerJointFutureAction
        or type(action.guard) is not HalfOpenInterval
        or type(action.guard.lower) is not ExactRational
        or type(action.guard.upper) is not ExactRational
        or type(action.safety) is not MahlerSourceBoundSafetyAction
    ):
        raise ValueError("graph catalogue operator has changed")
    try:
        snapshot = (
            action.extent,
            action.residue,
            action.innovation,
            action.gain,
            action.guard.lower.numerator,
            action.guard.lower.denominator,
            action.guard.upper.numerator,
            action.guard.upper.denominator,
            action.safety.extent,
            action.safety.offset_hat,
            action.safety.cap_hat,
        )
    except AssertionError as error:
        raise ValueError("graph catalogue operator has changed") from error
    if any(type(value) is not int for value in snapshot) or snapshot != (
        2,
        0,
        0,
        9,
        0,
        1,
        2,
        45,
        2,
        0,
        36,
    ):
        raise ValueError("graph catalogue operator has changed")


def _selected_row(source: int, tail: ExactRational) -> _GraphRow | None:
    entry = _port(source, tail)
    for row in _GRAPH_ROWS:
        if row.entry == entry and source % 80 == row.source_residue:
            return row
    return None


def certify_graph_row(
    source: int,
    tail: ExactRational,
    copies: int,
    *,
    reserve_bits: Callable[[int], None],
) -> tuple[_GraphRow, MahlerJointFutureAction, int, ExactRational] | None:
    """Bind a closed operator to one source before powering its response."""
    if type(source) is not int or source <= 0 or type(tail) is not ExactRational:
        raise TypeError("graph row requires a positive integer and an exact rational")
    if type(copies) is not int or not 1 <= copies <= _MAX_TICKS // 2:
        raise ValueError("powered graph exceeds its physical tick limit")
    if not callable(reserve_bits):
        raise TypeError("graph row requires a scratch owner")
    inlet_bits = (
        source.bit_length()
        + abs(tail.numerator).bit_length()
        + tail.denominator.bit_length()
    )
    reserve_bits(8 * (inlet_bits + 256))
    row = _selected_row(source, tail)
    if row is None:
        return None
    action = _ROW_ACTION
    _require_row_action(action)
    if not action.admits(source, tail):
        return None
    duration = action.extent * copies
    reserve_bits(8 * (inlet_bits + 32 * duration + 512))
    if source % (1 << (duration + 2)):
        return None
    if copies == 1:
        powered = action
    else:
        # The admitted source has a zero parity word for the complete span.
        # The shared zero-run owner supplies its gain and ordered safety action;
        # the graph port additionally requires the final fractional digit zero.
        zero = MahlerJointFutureAction.zero_run(duration)
        graph_guard = HalfOpenInterval(
            ExactRational(0), ExactRational(1 << duration, 10 * zero.gain)
        )
        powered = MahlerJointFutureAction.with_gain(
            zero.extent,
            zero.residue,
            zero.innovation,
            graph_guard,
            zero.safety,
            zero.gain,
        )
    if not powered.admits(source, tail):
        return None
    endpoint, final = powered.apply(source, tail)
    if _port(endpoint, final) != row.entry:
        raise ArithmeticError("certified graph row changed its closed port")
    return row, powered, endpoint, final


def powered_graph(
    result: ArithmeticResult, tail: Fraction, copies: int
) -> dict[str, object]:
    """Apply an admitted 60/40 graph row at the authenticated source."""
    if type(result) is not ArithmeticResult:
        raise TypeError("powered graph requires an issued arithmetic result")
    result.require_source()
    if type(tail) is not Fraction:
        raise TypeError("powered graph requires an exact fractional tail")
    if type(copies) is not int or copies < 1:
        raise ValueError("powered graph requires a positive copy count")
    if copies > _MAX_TICKS // 2:
        raise ValueError("powered graph exceeds its physical tick limit")
    source = result.h - 1
    unavailable: dict[str, object] = {
        "status": "unavailable",
        "source": source,
        "requested_copies": copies,
        "coverage": "60-40-closed-row",
        "clock_unit": "physical-ticks",
    }
    if source <= 0 or not Fraction(0) <= tail < Fraction(1, 2):
        return unavailable
    exact = ExactRational(tail.numerator, tail.denominator)
    scratch = RunArithmeticWorkspace.for_ledger(result.ledger, "mahler_graph")
    with scratch.scope():
        applied = certify_graph_row(
            source, exact, copies, reserve_bits=scratch.require_bits
        )
        if applied is None:
            return unavailable
        row, action, endpoint, final = applied
        return {
            "status": "available",
            "source": source,
            "source_binding": result.source_binding,
            "initial_fraction": str(tail),
            "port": row.entry,
            "requested_copies": copies,
            "row_ticks": 2,
            "physical_ticks": action.extent,
            "endpoint": endpoint,
            "final_fraction": str(Fraction(final.numerator, final.denominator)),
            "weighted_carry": action.innovation,
            "guard": (
                str(
                    Fraction(
                        action.guard.lower.numerator, action.guard.lower.denominator
                    )
                ),
                str(
                    Fraction(
                        action.guard.upper.numerator, action.guard.upper.denominator
                    )
                ),
            ),
            "coverage": "60-40-closed-row",
            "clock_unit": "physical-ticks",
            "source_prefix_ledger_safe": result.first_failure_index is None,
            "source_first_failure_index": result.first_failure_index,
            "physical_continuation_authorized": False,
        }
