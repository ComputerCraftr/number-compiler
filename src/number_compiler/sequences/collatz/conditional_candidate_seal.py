"""Exact immutable payload snapshots for retained conditional candidates."""

from __future__ import annotations

from dataclasses import dataclass
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
    from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape


@dataclass(frozen=True, slots=True, eq=False)
class _IdentityRef:
    """Retain an object and compare its authority by identity only."""

    value: object

    def __eq__(self, other: object) -> bool:
        return type(other) is _IdentityRef and self.value is other.value


@dataclass(frozen=True, slots=True)
class _ParityTapeNodeSeal:
    reference: _IdentityRef
    kind: str
    word: tuple[int, ...]
    children: tuple[ParityCarryTape, ...]
    count: int
    steps: int
    odds: int


@dataclass(frozen=True, slots=True)
class _ParityTapeSeal:
    root: _IdentityRef
    rows: tuple[_ParityTapeNodeSeal, ...]
    work: int


@dataclass(frozen=True, slots=True)
class CandidateSealSnapshot:
    """Memo payload plus pinned parity rows and their verification allowance."""

    payload: tuple[object, ...]
    parity_tape: _ParityTapeSeal | None
    parity_work: int


def _inspect_parity_tape(
    tape: object,
    *,
    retain: bool,
) -> tuple[_ParityTapeSeal | None, int]:
    from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape

    if type(tape) is not ParityCarryTape:
        raise TypeError("conditional parity tape has malformed authority")

    pending: list[tuple[ParityCarryTape, int]] = [(tape, 0)]
    active: set[int] = set()
    seen: set[int] = set()
    rows: list[_ParityTapeNodeSeal] = []
    root_reference = _IdentityRef(tape) if retain else None
    node: ParityCarryTape | None = None
    child: ParityCarryTape | None = None
    work = 0
    try:
        while pending:
            node, child_index = pending[-1]
            identity = id(node)
            if identity not in active and identity not in seen:
                if (
                    type(node.kind) is not str
                    or type(node.word) is not tuple
                    or len(node.word) > 64
                    or type(node.children) is not tuple
                    or type(node.repetitions) is not int
                    or type(node.steps) is not int
                    or type(node.odds) is not int
                    or any(
                        type(bit) is not int or bit not in (0, 1) for bit in node.word
                    )
                    or any(
                        type(child) is not ParityCarryTape for child in node.children
                    )
                ):
                    raise TypeError("conditional parity tape node has malformed fields")
                work += (
                    64 * (5 + len(node.children))
                    + len(node.word)
                    + node.repetitions.bit_length()
                    + node.steps.bit_length()
                    + node.odds.bit_length()
                )
                active.add(identity)
            if child_index < len(node.children):
                child = node.children[child_index]
                pending[-1] = (node, child_index + 1)
                child_identity = id(child)
                if child_identity in active:
                    raise TypeError("conditional parity tape grammar contains a cycle")
                if child_identity not in seen:
                    pending.append((child, 0))
                continue
            if node.kind == "word":
                valid = (
                    1 <= len(node.word) <= 64
                    and not node.children
                    and node.repetitions == 1
                    and node.steps == len(node.word)
                    and node.odds == sum(node.word)
                )
            elif node.kind == "concat":
                valid = (
                    not node.word
                    and node.repetitions == 1
                    and len(node.children) >= 1
                    and node.steps == sum(child.steps for child in node.children)
                    and node.odds == sum(child.odds for child in node.children)
                )
            elif node.kind == "repeat":
                valid = (
                    not node.word
                    and len(node.children) == 1
                    and node.repetitions >= 1
                    and node.steps == node.children[0].steps * node.repetitions
                    and node.odds == node.children[0].odds * node.repetitions
                )
            else:
                valid = False
            if not valid:
                raise TypeError("conditional parity tape node is not a valid SLP node")
            if retain:
                rows.append(
                    _ParityTapeNodeSeal(
                        _IdentityRef(node),
                        node.kind,
                        node.word,
                        node.children,
                        node.repetitions,
                        node.steps,
                        node.odds,
                    )
                )
            active.remove(identity)
            seen.add(identity)
            pending.pop()
        if not retain:
            return None, work
        if root_reference is None:
            raise ArithmeticError("conditional parity root identity was omitted")
        return _ParityTapeSeal(root_reference, tuple(rows), work), work
    finally:
        pending.clear()
        active.clear()
        seen.clear()
        rows.clear()
        node = None
        child = None


def parity_tape_verification_work(tape: object) -> int:
    """Return conservative bits for each pinned row, edge, word and scalar."""
    _snapshot, work = _inspect_parity_tape(tape, retain=False)
    return work


def _validate_parity_tape_seal(tape: object, seal: _ParityTapeSeal) -> None:
    from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape

    if type(tape) is not ParityCarryTape or tape is not seal.root.value:
        raise TypeError("conditional parity tape root changed after memo issuance")
    for row in seal.rows:
        node = row.reference.value
        if (
            type(node) is not ParityCarryTape
            or type(node.kind) is not str
            or node.kind != row.kind
            or type(node.word) is not tuple
            or node.word is not row.word
            or type(node.children) is not tuple
            or node.children is not row.children
            or type(node.repetitions) is not int
            or node.repetitions != row.count
            or type(node.steps) is not int
            or node.steps != row.steps
            or type(node.odds) is not int
            or node.odds != row.odds
        ):
            raise TypeError("conditional parity tape changed after memo issuance")


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


def _joined(
    joined: object,
    *,
    expected_tape: _ParityTapeSeal | None,
    capture_tape: bool,
    validate_tape_action: bool,
) -> tuple[tuple[object, ...] | None, _ParityTapeSeal | None, int]:
    if joined is None:
        if expected_tape is not None:
            raise TypeError("conditional joined port lost its sealed parity tape")
        return None, None, 0
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        GuardedRadix6Bridge,
    )

    if (
        type(joined) is not GuardedPortJoin
        or type(joined.bridge) is not GuardedRadix6Bridge
    ):
        raise TypeError("conditional joined port has malformed authority")
    if (
        joined.named_macro is not None
        or joined.factor_grammar is not None
        or type(joined.factor_repetitions) is not int
        or joined.factor_repetitions != 1
    ):
        raise TypeError("conditional candidate join has unsupported source grammar")
    bridge = joined.bridge
    parity_tape = joined.parity_tape
    if capture_tape:
        if parity_tape is None:
            parity_seal = None
            parity_work = 0
        else:
            parity_seal, parity_work = _inspect_parity_tape(parity_tape, retain=True)
            if parity_seal is None:
                raise ArithmeticError("conditional parity tape snapshot was omitted")
    else:
        if expected_tape is None:
            if parity_tape is not None:
                raise TypeError("conditional join acquired an unissued parity tape")
            parity_seal = None
            parity_work = 0
        else:
            _validate_parity_tape_seal(parity_tape, expected_tape)
            parity_seal = expected_tape
            parity_work = expected_tape.work
    if capture_tape and validate_tape_action:
        resolved_tape = joined.parity_tape_for_action()
        if resolved_tape is not None and (
            resolved_tape.steps != joined.port.action.steps
            or resolved_tape.odds != joined.port.odd_events
            or resolved_tape.action().coefficient_snapshot()
            != joined.port.action.coefficient_snapshot()
        ):
            raise ValueError("conditional parity tape differs from its issued port")

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
        (
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
            _tag(joined.named_macro),
            _tag(joined.factor_grammar),
            _tag(joined.factor_repetitions),
            parity_seal,
        ),
        parity_seal,
        parity_work,
    )


def snapshot_scheduler_candidate(
    candidate: CertifiedSchedulerCandidate,
    *,
    expected: CandidateSealSnapshot | None = None,
    validate_tape_action: bool = False,
) -> CandidateSealSnapshot:
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
    joined_value, parity_seal, parity_work = _joined(
        candidate.joined_port,
        expected_tape=None if expected is None else expected.parity_tape,
        capture_tape=expected is None,
        validate_tape_action=validate_tape_action,
    )
    payload = (
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
        joined_value,
        carry_value,
        upper_value,
    )
    return CandidateSealSnapshot(payload, parity_seal, parity_work)
