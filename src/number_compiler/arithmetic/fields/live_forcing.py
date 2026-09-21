"""Bounded modular forcing over the existing innovation DAG.

Five later doublings kill a decimal forcing contribution modulo 32. Pruning
precedes dependency traversal and residue demands. Live packets stay symbolic;
only a demanded residue view evaluates their bounded radial stencils.

This is a query projection, not an exact innovation ID or successor authority.
The three-growth-run law guarantees the live growth bound on admitted decimal
trajectories; arbitrary formal expressions exceeding it are refused, not
truncated. No source admission is inferred from a matching numeric bound.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from types import TracebackType
from typing import Self

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.event_innovation import (
    _children,
    _Context,
    _context_units,
    _emit,
    _EventWork,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    RadialMultiplier,
    SymbolicInnovationArena,
    _Atom,
    _Interval,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class LiveForcingPacket:
    """A modular arithmetic packet; atom/source authority stays with its owner."""

    atom: InnovationID
    chart: CylinderChart
    growth: int
    coefficient: int


@dataclass(frozen=True, slots=True)
class ResidueRun:
    start: int
    stop: int
    residue: int


class LiveForcingProjection:
    """Ledger-owned query view with explicit close/reset lifetime.

    Coefficients are residues in Z/2**bits. A caller needs a separately proved
    source coefficient bound before converting them to exact digits or signs.
    """

    def __init__(
        self,
        arena: SymbolicInnovationArena,
        expression: InnovationID,
        *,
        bits: int = 5,
    ) -> None:
        if type(arena) is not SymbolicInnovationArena:
            raise TypeError("live forcing requires the shared innovation arena")
        if type(bits) is not int or not 1 <= bits <= 64:
            raise ValueError("live forcing precision must be between 1 and 64 bits")
        arena.resolve(expression)
        self._bits = bits
        self._modulus = 1 << bits
        # Query work limit, not a source certificate. On a separately admitted
        # decimal trajectory the three-growth-run law proves this is sufficient.
        self._maximum_growth = 3 * bits
        self._work = _EventWork(arena)
        self._closed = False
        try:
            self._construct(expression)
        except BaseException:
            self.close()
            raise

    @property
    def ledger(self) -> ResourceLedger:
        """Resource owner shared with demanded arithmetic consumers."""
        self._check_open()
        return self._work.ledger

    @property
    def bits(self) -> int:
        return self._bits

    @property
    def modulus(self) -> int:
        return self._modulus

    @property
    def maximum_growth(self) -> int:
        return self._maximum_growth

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("closed live-forcing projection")
        self._work.arena.resolve(self._work.arena.zero)

    def _add_weight(self, state: _Context, value: int) -> None:
        work = self._work
        work.reserve(_context_units(state) + 2)
        work.ledger.bump("live_forcing_modular_integer_bits", self.bits * 2 + 1)
        work.weights[state] = (work.weights.get(state, 0) + value) % self.modulus

    def _construct(self, expression: InnovationID) -> None:
        work, arena = self._work, self._work.arena
        root = _Context(expression)
        work.enqueue(root)
        while work.stack:
            state = work.stack.pop()
            work.ledger.release(work.stack_owner, entries=1, nodes=1)
            work.ledger.bump("live_forcing_contexts")
            # Do not resolve the child, its atom, its chart or its coefficients.
            if state.radial.no_growth >= self.bits:
                work.ledger.bump("live_forcing_dead_contexts")
                continue
            children = _children(arena, state)
            edges = []
            work.reserve(2 * len(children))
            for coefficient, child in children:
                work.reserve(max(1, (abs(coefficient).bit_length() + 63) // 64))
                work.ledger.bump(
                    "live_forcing_input_coefficient_bits",
                    max(1, abs(coefficient).bit_length()),
                )
                reduced = coefficient % self.modulus
                if not reduced:
                    work.ledger.bump("live_forcing_zero_scale_edges")
                    continue
                edges.append((reduced, child))
                work.enqueue(child)
            work.graph[state] = tuple(edges)
        work.reserve(len(work.graph))
        order = sorted(work.graph, key=lambda s: s.reference.local_id, reverse=True)
        self._add_weight(root, 1)
        for state in order:
            weight = work.weights.get(state, 0)
            if not weight or state.radial.no_growth >= self.bits:
                continue
            admitted_edges = work.graph[state]
            if admitted_edges:
                for coefficient, child in admitted_edges:
                    work.reserve((2 * self.bits + 63) // 64)
                    self._add_weight(child, weight * coefficient)
                continue
            # An empty edge set can also be a killed Scale node. Only actual
            # leaves emit. The exact node kind is inspected, never atom values.
            node = arena.resolve(state.reference)
            if not isinstance(node, (_Interval, _Atom)):
                continue
            q = state.radial.no_growth
            work.ledger.bump("live_forcing_modular_integer_bits", self.bits * 2 + 1)
            scale = (weight << q) % self.modulus
            live = _Context(
                state.reference, state.chart, RadialMultiplier(0, state.radial.growth)
            )
            _emit(work, live, scale, False)
        # Cancellation is modulo the requested precision and precedes the live
        # degree check. No discarded modular term is rewritten in the exact DAG.
        work.reserve(len(work.terms))
        for state in tuple(work.terms):
            value = work.terms[state] % self.modulus
            if not value:
                del work.terms[state]
            elif state.radial.growth > self.maximum_growth:
                raise ValueError("live forcing exceeds the query growth bound")
            else:
                work.terms[state] = value
        work.ledger.bump("live_forcing_packets", len(work.terms))
        work.graph.clear()
        work.weights.clear()
        retained_units = sum(
            _context_units(state) + (self.bits + 63) // 64 for state in work.terms
        )
        if retained_units > work.scratch_units:
            work.reserve(retained_units - work.scratch_units)
        else:
            work.ledger.release(
                work.scratch_owner, nodes=work.scratch_units - retained_units
            )
            work.scratch_units = retained_units

    def packets(self) -> Iterator[LiveForcingPacket]:
        """Expose live arithmetic structure, never future coefficient queries."""
        self._check_open()
        for state in self._work.terms:
            self._check_open()
            yield LiveForcingPacket(
                state.reference,
                state.chart,
                state.radial.growth,
                self._work.terms[state],
            )

    def residue_runs(self, start: int, stop: int) -> tuple[ResidueRun, ...]:
        """Demand scalar/interval residues without walking the spatial span.

        Source atoms remain opaque and require their own admitted consumer.
        A bounded radial interval creates at most 2*(growth+1) boundary events,
        regardless of its length. These are modular observation events, not a
        stored carry history or temporal successor.
        """
        self._check_open()
        if type(start) is not int or type(stop) is not int or stop < start:
            raise ValueError("residue interval requires ordered exact integers")
        if start == stop:
            return ()
        work, arena = self._work, self._work.arena
        if work.basis:
            raise RuntimeError("live forcing demand workspace is in use")
        scratch_before = work.scratch_units
        try:
            work.reserve(
                max(1, (max(start.bit_length(), stop.bit_length()) + 63) // 64)
            )
            initial = 0
            for packet in self.packets():
                node = arena.resolve(packet.atom)
                if not isinstance(node, _Interval):
                    raise TypeError(
                        "live forcing residue demand has an unresolved atom"
                    )
                if packet.chart.slope != 1:
                    raise ArithmeticError("interval reflection was not normalized")
                left = -packet.chart.offset
                choose = 1
                for j in range(packet.growth + 1):
                    work.reserve(4)
                    work.ledger.bump("live_forcing_stencil_terms")
                    work.ledger.bump(
                        "live_forcing_modular_integer_bits",
                        self.bits + packet.growth + 2,
                    )
                    value = packet.coefficient * choose % self.modulus
                    work.reserve(
                        2
                        * max(
                            1,
                            (max(abs(left).bit_length(), node.length.bit_length()) + 66)
                            // 64,
                        )
                    )
                    for position, change in (
                        (left + j, value),
                        (left + node.length + j, -value),
                    ):
                        work.reserve(max(1, (abs(position).bit_length() + 63) // 64))
                        if position <= start:
                            initial = (initial + change) % self.modulus
                        elif position < stop:
                            work.basis[position] = (
                                work.basis.get(position, 0) + change
                            ) % self.modulus
                    if j < packet.growth:
                        choose = choose * (packet.growth - j) // (j + 1)
            work.reserve(3 * len(work.basis) + 1)
            result: list[ResidueRun] = []
            previous, residue = start, initial
            for position in sorted(work.basis):
                change = work.basis[position]
                if not change:
                    continue
                result.append(ResidueRun(previous, position, residue))
                previous = position
                residue = (residue + change) % self.modulus
            result.append(ResidueRun(previous, stop, residue))
            return tuple(result)
        finally:
            work.basis.clear()
            work.ledger.release(
                work.scratch_owner, nodes=work.scratch_units - scratch_before
            )
            work.scratch_units = scratch_before

    def close(self) -> None:
        if not self._closed:
            self._work.close()
            self._closed = True

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        self.close()
