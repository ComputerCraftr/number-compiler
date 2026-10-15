"""Carry-event recovery and compressed observations of live forcing residues.

Pair-view inputs are P modulo 32; centered entry points explicitly uncenter
Delta first. A caller must separately establish P in [0,18] on the admitted
source before interpreting these arithmetic projections as exact carries.
Neither returned event handles nor SLPs authorize a temporal successor.
"""

from dataclasses import dataclass

from number_compiler.arithmetic.automata.residue_carry_slp import (
    ResidueCarrySLPProjector,
    ResidueCarrySLPResult,
)
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.centered_carry import (
    carry_coboundary,
    uncenter_pair_field,
)
from number_compiler.arithmetic.fields.live_forcing import LiveForcingProjection
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    SymbolicInnovationArena,
)
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


@dataclass(frozen=True, slots=True)
class RecoveredCarryEvents:
    """Exact arithmetic views under the caller's pair-range admission.

    ``reset_jumps[i] = c[i+1]-c[i]``; ``correction = (z-10)Q``.
    These scoped arithmetic handles carry no successor/source authority.
    With physical incoming zero, ``terminal_carry`` is the leading-one birth.
    """

    extent: int
    incoming: int
    terminal_carry: int
    reset_jumps: InnovationID
    correction: InnovationID


def recover_centered_carry_events(
    arena: SymbolicInnovationArena,
    residual: InnovationID,
    *,
    extent: int,
    incoming: int = 0,
) -> RecoveredCarryEvents:
    """Recover signed resets and forcing correction from modular boundaries.

    Each constant residue interval applies one element of the existing carry
    monoid. Its length never enters an iteration: a non-neutral interval resets
    at its first coordinate and is constant thereafter; a neutral one wires
    its input through. Adjacent carry-one intervals merge even when their pair
    residues differ. No pair/carry SLP or represented coefficient is created.

    Work is proportional to the demanded residue boundaries and emitted reset
    events, plus the existing live-projection cost, not the spatial extent.
    This is not a bound on boundary growth across temporal composition. The
    source owner must establish exact P in [0,18]; modulo 32 alone cannot do so.
    """
    if type(arena) is not SymbolicInnovationArena:
        raise TypeError("carry events require the shared innovation arena")
    arena.resolve(residual)
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be zero or one")
    pair = uncenter_pair_field(arena, residual, extent=extent)
    ledger = arena.ledger
    owner = ledger.register(f"carry-event-demand-{ledger.owner_count}", "query_memo")
    units = 0
    try:
        # Cursors are owned before allocating the projection; its separate
        # boundary lease remains live through all arithmetic consumption.
        required = 6 + 2 * max(1, (extent.bit_length() + 63) // 64)
        ledger.reserve(owner, nodes=required)
        units = required
        with (
            LiveForcingProjection(arena, pair) as view,
            view.leased_residue_runs(0, extent) as runs,
        ):
            for run in runs:
                ledger.bump(_fields_keys.CARRY_EVENT_BOUNDARY_CHECKS)
                if not 0 <= run.residue <= 18:
                    raise ValueError("pair residue is outside the decimal pair range")

            carry = incoming
            opened = 0 if incoming else None
            outgoing = arena.zero
            resets = arena.zero

            def append_occupied(start: int, stop: int) -> None:
                nonlocal outgoing
                if stop > start:
                    interval = arena.chart(
                        arena.interval(stop - start), CylinderChart(1, -start)
                    )
                    outgoing = arena.add(outgoing, interval)
                    ledger.bump(_fields_keys.CARRY_EVENT_OCCUPIED_INTERVALS)

            for run in runs:
                ledger.bump(_fields_keys.CARRY_EVENT_DOMAIN_ACTIONS)
                after = apply_carry_fn(value_carry_fn(run.residue, 10), carry)
                if after == carry:
                    continue
                point = arena.chart(arena.interval(1), CylinderChart(1, -run.start))
                resets = arena.linear_combination(((1, resets), (after - carry, point)))
                ledger.bump(_fields_keys.CARRY_EVENT_RESET_EVENTS)
                if after:
                    opened = run.start
                else:
                    assert opened is not None
                    append_occupied(opened, run.start)
                    opened = None
                carry = after
            if opened is not None:
                append_occupied(opened, extent)
            correction = carry_coboundary(arena, outgoing, base=10)
            return RecoveredCarryEvents(extent, incoming, carry, resets, correction)
    finally:
        ledger.release(owner, nodes=units)
        ledger.mark_disposed(owner)


def project_live_pair_carries(
    view: LiveForcingProjection, *, start: int, stop: int, incoming: int = 0
) -> ResidueCarrySLPResult:
    """Feed compressed modular intervals to the existing grammar transducer.

    No integer positions or represented carry words are visited. Input grammar
    construction is charged before allocation and discarded after projection.
    The caller owns the returned result and must close it after observation.
    """
    if type(view) is not LiveForcingProjection:
        raise TypeError("carry projection requires the bounded forcing view")
    if view.bits != 5:
        raise ValueError("decimal pair carry projection requires modulo 32")
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be zero or one")
    ledger = view.ledger
    owner = ledger.register(f"live-carry-input-{ledger.owner_count}", "query_memo")
    units = 0
    grammar: SLPArena | None = None
    projector: ResidueCarrySLPProjector | None = None
    try:
        # Admit the initial empty grammar node before constructing the arena.
        ledger.reserve(owner, nodes=1)
        units = 1
        grammar = SLPArena()
        root = grammar.empty()
        runs = view.residue_runs(start, stop)
        ledger.reserve(owner, nodes=3 * len(runs))
        units += 3 * len(runs)
        for run in runs:
            if not 0 <= run.residue <= 18:
                raise ValueError("pair residue is outside the decimal pair range")
            # At most terminal, repeat and concat; intern hits are conservatively
            # admitted too. Length arithmetic uses binary metadata, not a scan.
            size = run.stop - run.start
            required = 3 + 3 * max(1, (size.bit_length() + 63) // 64)
            ledger.reserve(owner, nodes=required)
            units += required
            leaf = grammar.terminal(run.residue)
            repeated = grammar.repeat(leaf, size)
            root = grammar.concat(root, repeated)
            ledger.bump(_fields_keys.LIVE_CARRY_INPUT_RUNS)
        projector = ResidueCarrySLPProjector(ledger)
        result = projector.project(grammar, grammar.nodes[root], incoming=incoming)
        ledger.bump(_fields_keys.LIVE_CARRY_INPUT_NODES, len(grammar.nodes))
        return result
    finally:
        if projector is not None:
            projector.close()
        if grammar is not None:
            grammar.nodes.clear()
            grammar._cat.clear()
            grammar._rep.clear()
            grammar._term.clear()
        ledger.release(owner, nodes=units)
        ledger.mark_disposed(owner)


def project_centered_residue_carries(
    arena: SymbolicInnovationArena,
    residual: InnovationID,
    *,
    extent: int,
    incoming: int = 0,
) -> ResidueCarrySLPResult:
    """Observe Delta through P=Delta+9E_m, preserving the polynomial basis.

    This uses the existing symbolic uncentering law and bounded modulo-32
    projection. It does not infer that supplied Delta is source-reachable.
    """
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("incoming carry must be zero or one")
    pair = uncenter_pair_field(arena, residual, extent=extent)
    with LiveForcingProjection(arena, pair) as view:
        return project_live_pair_carries(view, start=0, stop=extent, incoming=incoming)
