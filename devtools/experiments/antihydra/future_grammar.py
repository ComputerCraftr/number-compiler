"""Exact finite source-family grammar and checked *candidate* repetitions.

Edges refine the original source congruence, not a freely chosen diamond word.
Prime/carry views are demanded from one concrete witness of that family. A
finite family, a cyclotomic cycle, or a fractional fixed point never certifies
an infinite positive source. This bounded research owner reuses source_safety;
it is not a production scheduler or a successful general pumping constructor.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.antihydra.source_observers import (
    EventObservations,
    observe_event,
)
from devtools.experiments.antihydra.source_safety import (
    PRIME_BANK,
    SourceBlockID,
    SourceEvent,
    SourceSafetyWorkspace,
    source_event,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.arithmetic.fields.consumer_pullback import (
    HalfOpenInterval as Interval,
)
from number_compiler.resources.stores import LedgerDict


@dataclass(frozen=True, slots=True)
class TelescopingAction:
    """D'=(P D+J)/Q; t'=(P t-J)/Q on the admitted source family."""

    gain: int
    denominator: int
    innovation: int


@dataclass(frozen=True, slots=True)
class CyclotomicLane:
    prime: int
    multiplier: int
    offset: int
    multiplier_order: int
    affine_order: int
    fractional_cycle_lane: int | None


@dataclass(frozen=True, slots=True)
class PeriodicObstruction:
    source: int
    source_obstruction: int
    source_repetition_limit: int
    fractional_fixed_point: Q
    fractional_cycle_admitted: bool


@dataclass(frozen=True, slots=True)
class FiberTransport:
    """Exact parameter change across one source-selected grammar edge.

    If ``j`` is natural, the parent high fiber is
    ``input_offset + input_stride*j``.  At the event boundary its high fiber is
    ``output_offset + output_stride*j``.  This is a relation on the complete
    source cylinder; it is not inferred from a prime or carry projection.
    """

    input_offset: int
    input_stride: int
    output_offset: int
    output_stride: int
    gain_inverse: int


@dataclass(frozen=True, slots=True)
class GrammarEdge:
    parent: SourceBlockID
    child: SourceBlockID
    exponent: int
    transport: FiberTransport


@dataclass(frozen=True, slots=True)
class FiniteRepeatedClauseTransport:
    """A finite parameter transport for a supplied repeated clause.

    ``transitions`` clause applications are followed by one further admitted
    occurrence.  For this fixed horizon, every natural ``j`` and every fraction
    in ``guard`` has the next clause available.  Changing ``transitions``
    generally changes the original source class.  This is therefore not an
    invariant pump, an all-time fixed source, or a discovered future language.
    """

    clause: SourceBlockID
    admitted: SourceBlockID
    transitions: int
    input_offset: int
    input_stride: int
    output_offset: int
    output_stride: int
    guard: Interval


@dataclass(frozen=True, slots=True)
class FailureBoundary:
    """First unsafe step and its ceiling-source residual, if any.

    At failure ``residual`` can be negative or at least one half; it is the
    centered residual relative to ``endpoint_source``, not a fractional part.
    """

    step: int | None
    endpoint_source: int
    residual: Q


@dataclass(frozen=True, slots=True)
class NormalizedSafeKernel:
    """Source-renamed safe-skip effect; never a successor identity."""

    width: int
    scale: Q
    guard_width: Q
    output_origin: Q
    ledger_delta: int
    ledger_minimum: int


@dataclass(frozen=True, slots=True)
class SafeOccurrenceChart:
    source_residue: int
    endpoint: int
    input_origin: Q


@dataclass(frozen=True, slots=True)
class JointObservation:
    """One finite witness, explicitly shared by every observer."""

    source: int
    fraction: Q
    deck: int
    high_fiber: int
    telescoping: TelescopingAction
    event: SourceEvent
    readouts: EventObservations
    cyclotomic: tuple[CyclotomicLane, ...]


class ReachableFutureGrammar:
    """Parameterized prefix grammar; k remains an arbitrary natural high fiber.

    An edge with label q imposes D_current = 2**(q-1) (mod 2**q).
    compose solves that constraint on the original source before publication.
    max_event is an exploration cutoff, never an assertion that larger events
    are impossible. D=0 has no first odd event and is outside these event edges.
    """

    def __init__(self, workspace: SourceSafetyWorkspace, *, max_event: int = 8) -> None:
        if type(max_event) is not int or not 1 <= max_event <= workspace.max_width:
            raise ValueError("event limit must fit the source workspace")
        self.workspace = workspace
        self.max_event = max_event
        ledger = workspace.ledger
        root = workspace.cylinder(0, 0)
        owner = ledger.register(
            f"mahler-grammar-{ledger.owner_count}", "reachable edges"
        )
        kernel_owner = ledger.register(
            f"mahler-grammar-kernels-{ledger.owner_count}", "finite proof blocks"
        )
        self._edges: LedgerDict[tuple[SourceBlockID, int], GrammarEdge] = (
            ledger.make_dict(owner)
        )
        self._kernels: LedgerDict[NormalizedSafeKernel, NormalizedSafeKernel] = (
            ledger.make_dict(kernel_owner)
        )
        self._edge_owner = owner
        self._kernel_owner = kernel_owner
        self._closed = False
        self.root = root

    def _require_open(self) -> None:
        if self._closed:
            raise ValueError("closed Mahler reachable-future grammar")

    def edge(self, parent: SourceBlockID, exponent: int) -> GrammarEdge:
        self._require_open()
        block = self.workspace.view(parent)  # Reject foreign handles before cache use.
        if type(exponent) is not int or not 1 <= exponent <= self.max_event:
            raise ValueError("event exponent outside the declared exploration bound")
        if block.width + exponent > self.workspace.max_width:
            self.workspace.ledger.bump("grammar_width_refusals")
            raise BlockContextBudgetExceeded("reachable grammar width budget exceeded")
        key = (parent, exponent)
        if key in self._edges:
            self.workspace.ledger.bump("grammar_edge_hits")
            return self._edges[key]
        event = self.workspace.cylinder(exponent, 1 << (exponent - 1))
        event_block = self.workspace.view(event)
        modulus, gain = event_block.skew.lower, block.skew.upper
        inverse = pow(gain, -1, modulus)
        if not 0 <= inverse < modulus or gain * inverse % modulus != 1 % modulus:
            raise ArithmeticError("event gain inverse failed its runtime check")
        lift = (
            (event_block.residue + modulus - block.endpoint % modulus) * inverse
        ) % modulus
        high = (block.endpoint + gain * lift - event_block.residue) // modulus
        if high < 0:
            raise ArithmeticError("event parameter transport left natural fibers")
        result = self.workspace.compose(parent, event)
        child = self.workspace.view(result)
        if child.residue != block.residue + (lift << block.width):
            raise ArithmeticError("edge lost its original-source parameter")
        if child.endpoint != event_block.endpoint + 3**exponent * high:
            raise ArithmeticError("edge lost its event-output parameter")
        edge = GrammarEdge(
            parent,
            result,
            exponent,
            FiberTransport(lift, modulus, high, gain, inverse),
        )
        self.workspace.ledger.reserve(self._edges.owner, entries=1)
        self._edges[key] = edge
        self.workspace.ledger.bump("grammar_edges_constructed")
        self.workspace.ledger.bump(
            "grammar_transport_integer_bits",
            sum(value.bit_length() for value in (lift, modulus, high, gain, inverse)),
        )
        return edge

    def extend(self, parent: SourceBlockID, exponent: int) -> SourceBlockID:
        return self.edge(parent, exponent).child

    def admits(self, handle: SourceBlockID, source: int, fraction: Q) -> bool:
        self._require_open()
        block = self.workspace.view(handle)
        fraction.validate()
        return (
            type(source) is int
            and source >= 0
            and (source > 0 or fraction > Q(0))
            and source % (1 << block.width) == block.residue
            and block.guard.contains(fraction)
        )

    def telescoping(self, handle: SourceBlockID) -> TelescopingAction:
        self._require_open()
        block = self.workspace.view(handle)
        transfer = block.skew
        p, q, innovation = transfer.upper, transfer.lower, transfer.offset
        if innovation < 0:
            raise ArithmeticError("ceiling-source innovation must be nonnegative")
        self.workspace.ledger.bump("grammar_telescoping_evaluations")
        self.workspace.ledger.bump(
            "grammar_telescoping_operand_bits",
            p.bit_length() + q.bit_length() + innovation.bit_length(),
        )
        return TelescopingAction(p, q, innovation)

    def witness(self, handle: SourceBlockID) -> tuple[int, Q]:
        self._require_open()
        block = self.workspace.view(handle)
        if block.guard.empty:
            raise ValueError("empty source family has no witness")
        lo, hi = block.guard.lower, block.guard.upper
        # This grid is finer than the distance between distinct rational bounds.
        bits = (lo.denominator * hi.denominator).bit_length() + 1
        denominator = 1 << bits
        numerator = (lo.numerator * denominator + lo.denominator - 1) // lo.denominator
        fraction = Q(numerator, denominator)
        source = block.residue or 1 << block.width
        if not self.admits(handle, source, fraction):
            raise ArithmeticError("dyadic witness escaped its original source family")
        self.workspace.ledger.bump("grammar_witness_bits", source.bit_length() + bits)
        return source, fraction

    def repeat(self, handle: SourceBlockID, count: int) -> SourceBlockID:
        """Binary composition of a supplied admitted clause, not pump discovery."""
        self._require_open()
        block = self.workspace.view(handle)
        if type(count) is not int or count < 0:
            raise ValueError("nonnegative repetition count required")
        if block.width * count > self.workspace.max_width:
            self.workspace.ledger.bump("grammar_width_refusals")
            raise BlockContextBudgetExceeded("repeated grammar width budget exceeded")
        result, power, remaining = self.root, handle, count
        while remaining:
            if remaining & 1:
                result = self.workspace.compose(result, power)
            remaining >>= 1
            if remaining:
                power = self.workspace.compose(power, power)
        return result

    def finite_repeated_clause_transport(
        self, handle: SourceBlockID, transitions: int
    ) -> FiniteRepeatedClauseTransport:
        """Construct a finite relation with logarithmically many compositions.

        The returned relation is extensional for every natural high fiber.  Its
        half-open guard is the guard of all ``transitions + 1`` occurrences, so
        strict endpoint admission is retained rather than sampled.  Exact
        residues, endpoints and rational guard bounds still have linear bit
        size in the requested width; this is not a sublinear-size constructor.
        """
        self._require_open()
        clause = self.workspace.view(handle)
        if clause.width == 0:
            raise ValueError("a repeated clause must have positive width")
        if type(transitions) is not int or transitions < 0:
            raise ValueError("nonnegative transition count required")
        total_width = clause.width * (transitions + 1)
        if total_width > self.workspace.max_width:
            self.workspace.ledger.bump("grammar_width_refusals")
            raise BlockContextBudgetExceeded("finite repeated-clause width exceeded")

        if transitions == 0:
            prefix, admitted = self.root, handle
        else:
            prefix = self.repeat(handle, transitions)
            admitted = self.workspace.compose(prefix, handle)
        prefix_block = self.workspace.view(prefix)
        admitted_block = self.workspace.view(admitted)
        scale = 1 << clause.width
        residue_difference = admitted_block.residue - clause.residue
        if residue_difference < 0 or residue_difference % scale:
            raise ArithmeticError("repeated input escaped the clause source chart")
        input_offset = residue_difference // scale
        input_stride = 1 << (clause.width * transitions)

        tail = admitted_block.residue >> prefix_block.width
        after_prefix = prefix_block.endpoint + 3**prefix_block.width * tail
        output_difference = after_prefix - clause.residue
        if output_difference < 0 or output_difference % scale:
            raise ArithmeticError("repeated output escaped the clause source chart")
        output_offset = output_difference // scale
        output_stride = 3 ** (clause.width * transitions)
        self.workspace.ledger.bump("grammar_finite_clause_transports")
        self.workspace.ledger.bump(
            "grammar_finite_transport_integer_bits",
            sum(
                value.bit_length()
                for value in (
                    input_offset,
                    input_stride,
                    output_offset,
                    output_stride,
                )
            ),
        )
        return FiniteRepeatedClauseTransport(
            handle,
            admitted,
            transitions,
            input_offset,
            input_stride,
            output_offset,
            output_stride,
            admitted_block.guard,
        )

    def first_failure(
        self, handle: SourceBlockID, source: int, fraction: Q
    ) -> FailureBoundary:
        """Descend composed guards to the exact first unsafe physical step.

        This is a total safe/fail consumer of an already admitted finite source
        action.  It does not enumerate all earlier scalar states: a safe child
        is skipped through its affine endpoint and the failing child is split.
        Missing child cylinders can still require linear-size exact certificate
        construction.  Their worklist visits and retained bits remain charged
        by the source workspace.
        """
        self._require_open()
        block = self.workspace.view(handle)
        fraction.validate()
        if (
            type(source) is not int
            or source < 0
            or source % (1 << block.width) != block.residue
        ):
            raise ValueError("source is outside the finite grammar clause")
        if not Interval().contains(fraction):
            return FailureBoundary(0, source, fraction)
        kernel, chart = self.normalized_safe_effect(handle)
        normalized = fraction - chart.input_origin
        if Q(0) <= normalized < kernel.guard_width:
            endpoint = block.endpoint + 3**block.width * (source >> block.width)
            safe_after = kernel.scale * normalized + kernel.output_origin
            return FailureBoundary(None, endpoint, safe_after)

        current_id, current_source, current_fraction, offset = (
            handle,
            source,
            fraction,
            0,
        )
        while True:
            current = self.workspace.view(current_id)
            self.workspace.ledger.bump("grammar_failure_descent_nodes")
            if current.width == 1:
                after = current.fractional.apply(current_fraction)
                assert after is not None
                endpoint = current.endpoint + 3 * (current_source >> 1)
                if Interval().contains(current_fraction) and not Interval().contains(
                    after
                ):
                    return FailureBoundary(offset + 1, endpoint, after)
                raise ArithmeticError("leaf guard disagrees with exact safe interval")

            left_width = current.width // 2
            left = self.workspace.cylinder(
                left_width, current_source % (1 << left_width)
            )
            left_block = self.workspace.view(left)
            if not left_block.guard.contains(current_fraction):
                current_id = left
                continue

            middle_source = left_block.endpoint + 3**left_width * (
                current_source >> left_width
            )
            middle_fraction = left_block.fractional.apply(current_fraction)
            assert middle_fraction is not None
            right_width = current.width - left_width
            right = self.workspace.cylinder(
                right_width, middle_source % (1 << right_width)
            )
            if self.workspace.view(right).guard.contains(middle_fraction):
                raise ArithmeticError("composed failure has no failing child")
            current_id = right
            current_source = middle_source
            current_fraction = middle_fraction
            offset += left_width

    def normalized_safe_effect(
        self, handle: SourceBlockID
    ) -> tuple[NormalizedSafeKernel, SafeOccurrenceChart]:
        """Factor a finite safe-skip effect from its source occurrence chart.

        Equal kernels share only the normalized safe action.  The returned
        chart and original handle retain source authority and first-failure
        descent; kernel equality never authorizes a successor merge.
        """
        self._require_open()
        block = self.workspace.view(handle)
        origin = block.guard.lower
        transformed = block.fractional.scale * origin + block.fractional.offset
        kernel = NormalizedSafeKernel(
            block.width,
            block.fractional.scale,
            block.guard.upper - origin,
            transformed,
            block.ledger_delta,
            block.ledger_minimum,
        )
        if kernel not in self._kernels:
            self.workspace.ledger.reserve(self._kernel_owner, entries=1)
            self._kernels[kernel] = kernel
            self.workspace.ledger.bump("grammar_safe_kernels_constructed")
            self.workspace.ledger.bump(
                "grammar_safe_kernel_integer_bits",
                sum(
                    abs(value).bit_length()
                    for value in (
                        kernel.width,
                        kernel.scale.numerator,
                        kernel.scale.denominator,
                        kernel.guard_width.numerator,
                        kernel.guard_width.denominator,
                        kernel.output_origin.numerator,
                        kernel.output_origin.denominator,
                        kernel.ledger_delta,
                        kernel.ledger_minimum,
                    )
                ),
            )
        else:
            self.workspace.ledger.bump("grammar_safe_kernel_hits")
        return self._kernels[kernel], SafeOccurrenceChart(
            block.residue, block.endpoint, origin
        )

    def periodic_obstruction(
        self, handle: SourceBlockID, source: int
    ) -> PeriodicObstruction:
        """Exact integer-source cap for repeating this complete parity block.

        H=(3**L-2**L)*D+J is positive. n repeats require 2**(n*L)|H.
        The cap concerns source-word admission, independent of fractional safety.
        An admitted fractional fixed point does not remove this obstruction.
        """
        self._require_open()
        block = self.workspace.view(handle)
        if (
            type(source) is not int
            or source <= 0
            or block.width == 0
            or source % (1 << block.width) != block.residue
        ):
            raise ValueError("positive source must admit a nonempty-width block")
        action = self.telescoping(handle)
        gap = action.gain - action.denominator
        obstruction = gap * source + action.innovation
        valuation = (obstruction & -obstruction).bit_length() - 1
        fixed = Q(action.innovation, gap)
        self.workspace.ledger.bump("grammar_periodic_checks")
        self.workspace.ledger.bump("grammar_obstruction_bits", obstruction.bit_length())
        return PeriodicObstruction(
            source,
            obstruction,
            valuation // block.width,
            fixed,
            block.guard.contains(fixed),
        )

    def cyclotomic(self, handle: SourceBlockID) -> tuple[CyclotomicLane, ...]:
        """Conditional rational lanes for u=2t, not residues of arbitrary reals.

        A None fixed-point lane means its reduced denominator is noninvertible.
        Orders are observed finite-bank facts, never independent phase choices.
        """
        self._require_open()
        block = self.workspace.view(handle)
        if block.width == 0:
            raise ValueError("cyclotomic repetition requires positive width")
        action = self.telescoping(handle)
        fixed_u = Q(2 * action.innovation, action.gain - action.denominator)
        rows = []
        for p in PRIME_BANK:
            inverse = pow(action.denominator, -1, p)
            multiplier = action.gain * inverse % p
            offset = -2 * action.innovation * inverse % p
            phase, order = multiplier, 1
            while phase != 1:
                phase = phase * multiplier % p
                order += 1
                self.workspace.ledger.bump("grammar_cyclotomic_phase_steps")
            lane = None
            if fixed_u.denominator % p:
                lane = fixed_u.numerator * pow(fixed_u.denominator, -1, p) % p
                if (multiplier * lane + offset) % p != lane:
                    raise ArithmeticError(
                        "cyclotomic fixed point lost telescoping binding"
                    )
            affine_order = p if multiplier == 1 and offset != 0 else order
            self.workspace.ledger.bump("grammar_cyclotomic_lanes")
            rows.append(
                CyclotomicLane(p, multiplier, offset, order, affine_order, lane)
            )
        return tuple(rows)

    def observe_edge(
        self, parent: SourceBlockID, exponent: int, *, max_columns: int = 4096
    ) -> JointObservation:
        """Demand the final event on one witness of the *complete prefix*."""
        self._require_open()
        child = self.extend(parent, exponent)
        source, fraction = self.witness(child)
        prefix = self.workspace.view(parent)
        middle = prefix.endpoint + 3**prefix.width * (source >> prefix.width)
        residual = prefix.fractional.apply(fraction)
        assert residual is not None
        event = source_event(self.workspace, middle, residual)
        if event.exponent != exponent:
            raise ArithmeticError("grammar edge is not source-selected")
        return JointObservation(
            source,
            fraction,
            source % 64,
            source // 64,
            self.telescoping(child),
            event,
            observe_event(event, self.workspace.ledger, max_columns=max_columns),
            self.cyclotomic(child),
        )

    def close(self) -> None:
        """Release retained edges; the caller-owned source workspace stays live."""
        if self._closed:
            return
        count = len(self._edges)
        kernel_count = len(self._kernels)
        self._edges.clear()
        self._kernels.clear()
        if count:
            self.workspace.ledger.release(self._edge_owner, entries=count)
        if kernel_count:
            self.workspace.ledger.release(self._kernel_owner, entries=kernel_count)
        self.workspace.ledger.mark_disposed(self._edge_owner)
        self.workspace.ledger.mark_disposed(self._kernel_owner)
        self._closed = True
