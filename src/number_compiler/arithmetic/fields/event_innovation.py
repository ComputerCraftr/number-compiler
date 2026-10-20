"""Finite-difference event normalization in the existing innovation arena.

This normalizes symbolic terms, not coefficients or temporal occurrences.
Intervals differentiate to endpoints; source atoms remain exact symbolic atoms.
Certified zero blocks may cancel different radial-growth packets without
expanding their radial powers. This is not a complete zero oracle across
arbitrary atoms, source admission, or temporal grammar closure.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationAdd,
    InnovationAtom,
    InnovationCharted,
    InnovationID,
    InnovationInterval,
    InnovationRadial,
    InnovationScale,
    InnovationZero,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)
from number_compiler.resources.stores import LedgerList


@dataclass(frozen=True, slots=True)
class EventContext:
    reference: InnovationID
    chart: CylinderChart = field(default_factory=CylinderChart)
    radial: RadialMultiplier = field(default_factory=RadialMultiplier)


def event_context_units(context: EventContext) -> int:
    bits = sum(
        max(1, abs(v).bit_length())
        for v in (context.chart.offset, context.radial.no_growth, context.radial.growth)
    )
    return (bits + 63) // 64


class EventWork:
    """One bounded arithmetic transaction; no source/action publication authority."""

    def __init__(self, arena: SymbolicInnovationArena) -> None:
        self.arena = arena
        self.ledger = arena.ledger
        prefix = f"event-normalization-{self.ledger.owner_count}"
        self.graph = OwnedMemo[EventContext, tuple[tuple[int, EventContext], ...]](
            self.ledger,
            self.ledger.register(prefix + "-graph", "query_memo"),
            nodes_per_entry=1,
        )
        self.weights = OwnedMemo[EventContext, int](
            self.ledger,
            self.ledger.register(prefix + "-weights", "query_memo"),
            nodes_per_entry=1,
        )
        self.terms = OwnedMemo[EventContext, int](
            self.ledger,
            self.ledger.register(prefix + "-terms", "query_memo"),
            nodes_per_entry=1,
        )
        self.basis = OwnedMemo[int, int](
            self.ledger,
            self.ledger.register(prefix + "-radial-basis", "query_memo"),
            nodes_per_entry=1,
        )
        self.stack_owner = self.ledger.register(prefix + "-stack", "query_memo")
        self.stack: LedgerList[EventContext] = self.ledger.make_list(
            self.stack_owner, append_only=False
        )
        self.scratch_owner = self.ledger.register(prefix + "-scratch", "query_memo")
        self.scratch_units = 0

    def reserve(self, units: int) -> None:
        self.ledger.reserve(self.scratch_owner, nodes=units)
        self.scratch_units += units

    def enqueue(self, context: EventContext) -> None:
        if context in self.graph:
            return
        self.reserve(event_context_units(context))
        self.graph[context] = ()
        self.ledger.reserve(self.stack_owner, entries=1, nodes=1)
        try:
            self.stack.append(context)
        except BaseException:
            self.ledger.release(self.stack_owner, entries=1, nodes=1)
            raise

    def add(
        self, table: OwnedMemo[EventContext, int], key: EventContext, value: int
    ) -> None:
        if key not in table:
            self.reserve(event_context_units(key))
        before = table.get(key, 0)
        bits = max(abs(before).bit_length(), abs(value).bit_length()) + 1
        self.reserve((bits + 63) // 64)
        table[key] = before + value
        self.ledger.bump(_fields_keys.EVENT_NORMALIZATION_INTEGER_BITS, bits)

    def close(self) -> None:
        count = len(self.stack)
        self.stack.clear()
        self.ledger.release(self.stack_owner, entries=count, nodes=count)
        self.ledger.mark_disposed(self.stack_owner)
        self.ledger.release(self.scratch_owner, nodes=self.scratch_units)
        self.ledger.mark_disposed(self.scratch_owner)
        self.graph.dispose()
        self.weights.dispose()
        self.terms.dispose()
        self.basis.dispose()


def event_children(
    arena: SymbolicInnovationArena, state: EventContext
) -> tuple[tuple[int, EventContext], ...]:
    node = arena.resolve(state.reference)
    chart, radial = state.chart, state.radial
    if isinstance(node, InnovationAdd):
        return (
            (1, EventContext(node.left, chart, radial)),
            (1, EventContext(node.right, chart, radial)),
        )
    if isinstance(node, InnovationScale):
        return ((node.coefficient, EventContext(node.child, chart, radial)),)
    if isinstance(node, InnovationCharted):
        return ((1, EventContext(node.child, chart.then(node.chart), radial)),)
    if isinstance(node, InnovationRadial):
        # R_d (1+z)^r = (1+z)^r R_(d-r); translation commutes.
        if chart.slope == -1:
            chart = CylinderChart(-1, chart.offset - node.multiplier.growth)
        return ((1, EventContext(node.child, chart, radial.then(node.multiplier))),)
    return ()


def emit_events(
    work: EventWork, state: EventContext, weight: int, difference: bool
) -> None:
    arena = work.arena
    node = arena.resolve(state.reference)
    if isinstance(node, InnovationZero):
        return
    if isinstance(node, InnovationInterval):
        chart, length = state.chart, node.length
        start = -chart.offset if chart.slope == 1 else chart.offset - length + 1
        if difference:
            one = arena.interval(1)
            work.add(
                work.terms,
                EventContext(one, CylinderChart(1, -start), state.radial),
                weight,
            )
            work.add(
                work.terms,
                EventContext(one, CylinderChart(1, -start - length), state.radial),
                -weight,
            )
        else:
            work.add(
                work.terms,
                EventContext(state.reference, CylinderChart(1, -start), state.radial),
                weight,
            )
        return
    if not isinstance(node, InnovationAtom):
        raise TypeError("event normalization encountered a nonterminal expression")
    work.add(work.terms, state, weight)
    if difference:
        shifted = CylinderChart(
            state.chart.slope, state.chart.offset - state.chart.slope
        )
        work.add(
            work.terms, EventContext(state.reference, shifted, state.radial), -weight
        )


def _shift(state: EventContext) -> int:
    return -state.chart.slope * state.chart.offset


def _packet_group(state: EventContext) -> tuple[int, int, int]:
    # Fixed atom/orientation and 2-power are common formal factors. Their
    # values and source predicates are never queried to prove cancellation.
    return state.reference.local_id, state.chart.slope, state.radial.no_growth


def _certificate_reserve(work: EventWork, bits: int) -> None:
    work.reserve(max(1, (bits + 63) // 64))
    work.ledger.bump(_fields_keys.EVENT_RADIAL_CERTIFICATE_INTEGER_BITS, bits)


def _zero_radial_block(
    work: EventWork, order: list[EventContext], start: int, stop: int
) -> bool:
    """Certify zero in t=1+z, expanding relative shifts, never radial powers.

    Strip the common source/chart/2-power and z^origin. For each remaining
    c*z^d*(1+z)^r, expand only (t-1)^d*t^r into a sparse dictionary. The gap
    partition bounds d by choose(K-1,2) for a block of K terms. An empty
    dictionary is an exact identity certificate; a surviving term causes no
    rewrite. No truncated jet or modulus can authorize this cancellation.
    """
    origin = _shift(order[start])
    try:
        for index in range(start, stop):
            state = order[index]
            weight = work.terms[state]
            degree = _shift(state) - origin
            # The partition's relative-shift bound is checked before looping.
            size = stop - start
            if not 0 <= degree <= (size - 1) * (size - 2) // 2:
                raise ArithmeticError("radial certificate escaped its gap block")
            choose = 1
            for k in range(degree + 1):
                # choose(d,k) <= 2^d. Reserve before coefficient multiplication
                # and before updating the sparse sum, including failed work.
                bits = abs(weight).bit_length() + degree + 2
                _certificate_reserve(work, bits)
                _certificate_reserve(
                    work, max(state.radial.growth.bit_length(), k.bit_length()) + 1
                )
                exponent = state.radial.growth + k
                coefficient = weight * choose
                if (degree - k) % 2:
                    coefficient = -coefficient
                previous = work.basis.get(exponent, 0)
                _certificate_reserve(work, max(abs(previous).bit_length(), bits) + 1)
                coefficient += previous
                if coefficient:
                    work.basis[exponent] = coefficient
                elif exponent in work.basis:
                    del work.basis[exponent]
                work.ledger.bump(_fields_keys.EVENT_RADIAL_CERTIFICATE_TERMS)
                if k < degree:
                    _certificate_reserve(work, degree + degree.bit_length() + 2)
                    choose = choose * (degree - k) // (k + 1)
        return not work.basis
    finally:
        work.basis.clear()


def _cancel_radial_identities(work: EventWork) -> None:
    """Remove only exact zero blocks; this never equates arbitrary source atoms."""
    if len(work.terms) < 2:
        return
    work.reserve(2 * len(work.terms))
    for state in work.terms:
        work.reserve(event_context_units(state))
    order = sorted(
        (state for state in work.terms if work.terms[state]),
        key=lambda state: (
            *_packet_group(state),
            _shift(state),
            state.radial.growth,
        ),
    )
    start = 0
    for stop in range(1, len(order) + 1):
        size = stop - start
        if stop < len(order) and _packet_group(order[stop]) == _packet_group(
            order[start]
        ):
            _certificate_reserve(
                work, abs(_shift(order[start])).bit_length() + size.bit_length() * 2 + 2
            )
            if _shift(order[stop]) <= _shift(order[start]) + size * (size - 1) // 2:
                continue
        if size > 1:
            work.ledger.bump(_fields_keys.EVENT_RADIAL_CERTIFICATE_BLOCKS)
            if _zero_radial_block(work, order, start, stop):
                for index in range(start, stop):
                    del work.terms[order[index]]
                work.ledger.bump(_fields_keys.EVENT_RADIAL_ZERO_BLOCKS)
                work.ledger.bump(_fields_keys.EVENT_RADIAL_CANCELLED_PACKETS, size)
        start = stop


def _normalize(
    arena: SymbolicInnovationArena, expression: InnovationID, *, difference: bool
) -> InnovationID:
    arena.resolve(expression)
    work = EventWork(arena)
    root = EventContext(expression)
    try:
        work.enqueue(root)
        while work.stack:
            state = work.stack.pop()
            work.ledger.release(work.stack_owner, entries=1, nodes=1)
            edges = event_children(arena, state)
            work.graph[state] = edges
            work.ledger.bump(_fields_keys.EVENT_NORMALIZATION_CONTEXTS)
            for _, child in edges:
                work.reserve(event_context_units(child))
                work.enqueue(child)
        # Input nodes are topologically interned. Every parent contributes
        # before any child is processed, including shared subexpressions.
        work.reserve(len(work.graph))
        order = sorted(work.graph, key=lambda s: s.reference.local_id, reverse=True)
        work.add(work.weights, root, 1)
        for state in order:
            weight = work.weights.get(state, 0)
            if not weight:
                continue
            edges = work.graph[state]
            if not edges:
                emit_events(work, state, weight, difference)
            for coefficient, child in edges:
                bits = abs(coefficient).bit_length() + abs(weight).bit_length()
                work.reserve(max(1, (bits + 63) // 64))
                work.add(work.weights, child, weight * coefficient)
        _cancel_radial_identities(work)
        work.reserve(2 * len(work.terms))
        terms: list[tuple[int, InnovationID]] = []
        for state in sorted(
            work.terms,
            key=lambda s: (
                s.reference.local_id,
                s.chart.slope,
                s.chart.offset,
                s.radial.no_growth,
                s.radial.growth,
            ),
        ):
            weight = work.terms[state]
            if not weight:
                continue
            atom = arena.radial(arena.chart(state.reference, state.chart), state.radial)
            terms.append((weight, atom))
        work.ledger.bump(_fields_keys.EVENT_NORMALIZATION_NONZERO_TERMS, len(terms))
        return arena.linear_combination(terms)
    finally:
        work.close()


def event_difference(
    arena: SymbolicInnovationArena, expression: InnovationID
) -> InnovationID:
    """Construct (1-z)expression with canonical equal-packet cancellation.

    Work depends on distinct transported DAG contexts, not polynomial width.
    Different radial-growth packets cancel only with exact sparse basis
    certificates. No bound on packet count over temporal composition follows.
    """
    return _normalize(arena, expression, difference=True)


def normalize_event_sum(
    arena: SymbolicInnovationArena, expression: InnovationID
) -> InnovationID:
    """Normalize packets and certified radial identities without future coefficients."""
    return _normalize(arena, expression, difference=False)
