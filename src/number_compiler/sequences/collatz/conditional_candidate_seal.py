"""Exact immutable payload snapshots for retained conditional candidates."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceClosedPortAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
        CertifiedSchedulerCandidate,
    )


def _tag(value: object) -> tuple[object, object]:
    return (type(value), value)


def _cylinder(value: CollatzTwoSidedCylinder) -> tuple[object, ...]:
    return (
        id(value),
        _tag(value.lower),
        _tag(value.upper),
        _tag(value.residue),
        _tag(value.modulus),
    )


def _coverage(value: object) -> tuple[object, ...] | None:
    if value is None:
        return None
    from number_compiler.sequences.collatz.collatz_digit_coverage import (
        Radix6DigitCoverage,
    )

    if type(value) is not Radix6DigitCoverage:
        raise TypeError("conditional bridge coverage has malformed authority")
    return (
        id(value),
        _tag(value.width),
        _tag(value.high_digits),
        _tag(value.high_word),
        _tag(value.low_digits),
        _tag(value.low_word),
        _tag(value.forced_five_suffix),
        _tag(value.alternatives),
        _tag(value.proven_value),
    )


def _trace(
    trace: MacroTraceGrammar | tuple[int, ...] | None,
) -> tuple[object, ...] | None:
    if trace is None:
        return None
    if type(trace) is tuple:
        if any(type(value) is not int or not 0 <= value < 160 for value in trace):
            raise TypeError("conditional trace tuple has malformed authority")
        return (type(trace), tuple(_tag(value) for value in trace))
    if type(trace) is not MacroTraceGrammar:
        raise TypeError("conditional trace has malformed authority")
    pending = [(trace, False)]
    active: set[int] = set()
    seen: set[int] = set()
    nodes: list[tuple[object, ...]] = []
    while pending:
        node, leaving = pending.pop()
        if type(node) is not MacroTraceGrammar:
            raise TypeError("conditional trace node has malformed authority")
        identity = id(node)
        if leaving:
            active.remove(identity)
            seen.add(identity)
            continue
        if identity in active:
            raise TypeError("conditional trace grammar contains a cycle")
        if identity in seen:
            continue
        if (
            type(node.letters) is not tuple
            or type(node.length) is not int
            or any(
                type(value) is not int or not 0 <= value < 160 for value in node.letters
            )
        ):
            raise TypeError("conditional trace letters have malformed authority")
        left, right = node.left, node.right
        if (left is None) != (right is None):
            raise TypeError("conditional trace node has malformed children")
        if left is None:
            if node.length != len(node.letters):
                raise TypeError("conditional trace leaf length is malformed")
        elif (
            type(left) is not MacroTraceGrammar
            or type(right) is not MacroTraceGrammar
            or node.letters
            or node.length != left.length + right.length
        ):
            raise TypeError("conditional trace concatenation is malformed")
        nodes.append(
            (
                identity,
                _tag(node.length),
                type(node.letters),
                tuple(_tag(value) for value in node.letters),
                _tag(None if left is None else id(left)),
                _tag(None if right is None else id(right)),
            )
        )
        active.add(identity)
        pending.append((node, True))
        if left is not None and right is not None:
            pending.extend(((right, False), (left, False)))
    return tuple(nodes)


def _joined(joined: object) -> tuple[object, ...] | None:
    if joined is None:
        return None
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        GuardedRadix6Bridge,
    )

    if (
        type(joined) is not GuardedPortJoin
        or type(joined.bridge) is not GuardedRadix6Bridge
    ):
        raise TypeError("conditional joined port has malformed authority")
    bridge = joined.bridge

    from number_compiler.sequences.collatz.guarded_radix6_bridge import FiveBand

    def bands_snapshot(bands: object) -> tuple[object, ...]:
        if not is_exact_object_tuple(bands) or any(
            type(band) is not FiveBand for band in bands
        ):
            raise TypeError("conditional bridge bands have malformed authority")
        typed_bands = cast(tuple[FiveBand, ...], bands)
        return (
            id(bands),
            type(bands),
            tuple((_tag(band.lower), _tag(band.upper)) for band in typed_bands),
        )

    defects = bridge.centered_defect_range
    if (
        not is_exact_object_tuple(defects)
        or len(defects) != 2
        or any(type(value) is not int for value in defects)
    ):
        raise TypeError("conditional bridge defect range is malformed")
    typed_defects = defects

    return (
        id(joined),
        _cylinder(joined.source),
        id(joined.port),
        id(bridge),
        _cylinder(bridge.inlet),
        _cylinder(bridge.target),
        id(bridge.action),
        tuple(_tag(value) for value in bridge.action.coefficient_snapshot()),
        _tag(bridge.odd_events),
        _coverage(bridge.source_coverage),
        _coverage(bridge.target_coverage),
        bands_snapshot(bridge.source_fives),
        bands_snapshot(bridge.inherited_fives),
        bands_snapshot(bridge.born_fives),
        bands_snapshot(bridge.target_fives),
        _tag(bridge.centered_at_minus_one),
        (id(defects), type(defects), tuple(_tag(value) for value in typed_defects)),
    )


def snapshot_scheduler_candidate(
    candidate: CertifiedSchedulerCandidate,
) -> tuple[object, ...]:
    """Capture every value a verified retained candidate can later publish."""
    port = candidate.port
    if type(port) is not SourceClosedPortAction:
        raise TypeError("conditional candidate port has malformed authority")
    port_snapshot = port.audit_snapshot()
    phase = candidate.numerator_phase
    phase_value = None
    if phase is not None:
        from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
            UpperNumeratorF5Matrix,
        )

        if type(phase) is not UpperNumeratorF5Matrix:
            raise TypeError("conditional candidate F5 phase is malformed")
        phase_value = (
            id(phase),
            _tag(phase.scale),
            _tag(phase.offset),
            _tag(phase.returns),
        )
    pair_transfer = candidate.pair_transfer
    pair_value = None
    if pair_transfer is not None:
        from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
            GuardedDecimalPairTransfer,
        )

        if type(pair_transfer) is not GuardedDecimalPairTransfer:
            raise TypeError("conditional candidate pair transfer is malformed")
        pair_value = (id(pair_transfer), id(pair_transfer.port))
    carry_program = candidate.carry_program
    carry_value = None
    if carry_program is not None:
        from number_compiler.sequences.collatz.guarded_radix6_bridge import (
            GuardedTemporalCarryCounts,
        )

        if type(carry_program) is not GuardedTemporalCarryCounts:
            raise TypeError("conditional candidate carry program is malformed")
        carry_value = (id(carry_program), carry_program.audit_snapshot())
    upper = candidate.upper_sturmian
    upper_value = None
    if upper is not None:
        if (
            type(upper) is not tuple
            or len(upper) != 3
            or any(type(value) is not int for value in upper)
        ):
            raise TypeError("conditional candidate upper factor is malformed")
        upper_value = (type(upper), tuple(_tag(value) for value in upper))
    return (
        id(candidate),
        _tag(candidate.source),
        _tag(candidate.endpoint),
        _tag(candidate.physical_ticks),
        _tag(candidate.normalized_steps),
        _tag(candidate.odd_ticks),
        _tag(candidate.return_count),
        id(port),
        id(port.action),
        repr(port_snapshot),
        _trace(port.trace),
        _trace(candidate.tail_trace),
        phase_value,
        pair_value,
        _joined(candidate.joined_port),
        carry_value,
        upper_value,
    )
