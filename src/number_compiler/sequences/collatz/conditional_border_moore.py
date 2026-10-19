"""Finite-horizon, source-wide *conditional* Collatz border transducer.

States represent whole upper-interval/lower-CRT cylinders. Every exact
6305-tail/3-return/8-exit inlet is represented; unknown tails and partial
returns are typed refusals.

Finite Moore classes describe only this bounded output contract. They do not
replace source guards or certify a global infinite-period quotient.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceClosedPortAction,
    SourceCongruence,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock


class ConditionalBorderBudgetExceeded(BlockContextBudgetExceeded):
    """The demanded finite inlet partition exceeds the declared budget."""


@dataclass(frozen=True, slots=True)
class ConditionalBorderEdge:
    """One guarded next-tail letter, or an explicit refused inlet."""

    tail: int | None
    endpoint_border: int | None
    inlet: CollatzTwoSidedCylinder
    action: DyadicTerminalFieldAction | None
    target: CollatzTwoSidedCylinder | None
    physical_ticks: int | None
    successor: int | None
    refusal: str | None = None
    odd_events: int = 0

    @property
    def letter(self) -> tuple[int | None, int | None, str | None]:
        return self.tail, self.endpoint_border, self.refusal


@dataclass(frozen=True, slots=True)
class ConditionalBorderState:
    cylinder: CollatzTwoSidedCylinder
    remaining_ticks: int
    edges: tuple[ConditionalBorderEdge, ...]
    status: str


@dataclass(frozen=True, slots=True)
class PointedBorderPath:
    """Certified pointed branch retaining its exact ORIGINAL-source guard."""

    action: SourceClosedPortAction
    target: CollatzTwoSidedCylinder
    tails: tuple[int, ...]
    physical_ticks: int
    state_path: tuple[int, ...]
    skew_clock: SkewQuadraticClock


@dataclass(frozen=True, slots=True)
class ConditionalBorderMoore:
    source: CollatzTwoSidedCylinder
    physical_ticks: int
    states: tuple[ConditionalBorderState, ...]
    classes: tuple[int, ...]
    class_count: int
    max_tail: int

    def select(self, pointed_source: int) -> PointedBorderPath | None:
        """Follow already-issued disjoint guards; never pick a speculative inlet.

        The selected source's remaining original-source class is pulled back
        through every preceding affine action.  This is a *pointed* program,
        not an assertion that other alternatives followed the same route.
        """
        if not self.source.contains(pointed_source):
            raise ValueError("pointed source does not belong to the ring")
        source = pointed_source
        node_id = 0
        tails: list[int] = []
        odd_events = 0
        state_path = [0]
        full = DyadicTerminalFieldAction.identity()
        clock = SkewQuadraticClock.identity(32)
        guard = SourceCongruence(self.source.residue, self.source.modulus)
        while True:
            node = self.states[node_id]
            if node.status == "complete":
                if full.steps == 0:
                    return None
                port = SourceClosedPortAction(full, guard, odd_events, None)
                if (
                    not port.admits(pointed_source)
                    or port.endpoint(pointed_source) != source
                ):
                    raise ArithmeticError(
                        "conditional border action lost the pointed root"
                    )
                clock.verify(full, pointed_source, source)
                return PointedBorderPath(
                    port,
                    node.cylinder,
                    tuple(tails),
                    self.physical_ticks,
                    tuple(state_path),
                    clock,
                )
            if node.status != "active":
                return None
            edges = [e for e in node.edges if e.inlet.contains(source)]
            if len(edges) != 1:
                raise ArithmeticError(
                    "conditional successor guards overlap or omit the source"
                )
            edge = edges[0]
            if edge.action is None or edge.successor is None or edge.target is None:
                return None
            pulled = SourceCongruence(edge.inlet.residue, edge.inlet.modulus).pullback(
                full
            )
            if pulled is None:
                raise ArithmeticError("certified inlet has no root preimage")
            joined = guard.meet(pulled)
            if joined is None or not joined.admits(pointed_source):
                raise ArithmeticError("certified inlet conflicts with original root")
            guard = joined
            source = edge.action.endpoint(source)
            if not edge.target.contains(source):
                raise ArithmeticError("conditional inlet failed exact affine transport")
            full = full.then(edge.action)
            odd_events += edge.odd_events
            if edge.tail is not None:
                clock = clock.then(_return_clock(edge.tail))
            else:
                clock = clock.then(SkewQuadraticClock.atom(edge.odd_events, 32))
            # An 8-border contributes one even physical step but no 6305
            # return/odd symbol. Keep its guard in the same affine action.
            if edge.tail is not None:
                tails.append(edge.tail)
            node_id = edge.successor
            state_path.append(node_id)

    def demanded_pointed_ports(
        self,
        pointed_source: int,
        *,
        binary_bits: int = 32,
        radix_places: dict[int, int] | None = None,
        walsh64: bool = False,
        include_width_coverage: bool = False,
    ) -> dict[str, object]:
        """Emit demanded ports for one selected, already-proved source path."""
        from number_compiler.sequences.collatz.conditional_border_observation import (
            demanded_conditional_pointed_ports,
        )

        return demanded_conditional_pointed_ports(
            self,
            pointed_source,
            binary_bits=binary_bits,
            radix_places=radix_places,
            walsh64=walsh64,
            include_width_coverage=include_width_coverage,
        )

    def observation(self) -> dict[str, object]:
        """Finite future-closed border classes, with refused letters visible."""
        return {
            "source_alternatives": self.source.count,
            "physical_ticks": self.physical_ticks,
            "raw_states": len(self.states),
            "conditional_moore_classes": self.class_count,
            "all_inlet_partitions_conserved": True,
            "states_with_unresolved_inlets": sum(
                any(e.refusal is not None for e in state.edges) for state in self.states
            ),
            "future_language": "bounded 6305 tail/exit/clock with guarded refusals",
            "unrestricted_global_moore_claim": False,
        }


def _return_clock(tail: int, precision: int = 32) -> SkewQuadraticClock:
    one = SkewQuadraticClock.atom(1, precision)
    zero = SkewQuadraticClock.atom(0, precision)
    return one.then(zero.power(tail)).then(one)


def _trace_clock(
    trace: MacroTraceGrammar,
    precision: int = 32,
) -> SkewQuadraticClock:
    """Fold a shared SLP's quadratic clock once per unique DAG node."""
    memo: dict[int, SkewQuadraticClock] = {}
    pending: list[tuple[MacroTraceGrammar, bool]] = [(trace, False)]
    while pending:
        node, children_ready = pending.pop()
        key = id(node)
        if key in memo:
            continue
        if node.left is None:
            result = SkewQuadraticClock.identity(precision)
            for tail in node.letters:
                result = result.then(_return_clock(tail, precision))
            memo[key] = result
        elif children_ready:
            assert node.right is not None
            memo[key] = memo[id(node.left)].then(memo[id(node.right)])
        else:
            assert node.right is not None
            pending.append((node, True))
            pending.append((node.right, False))
            pending.append((node.left, False))
    return memo[id(trace)]


def _return_action(tail: int) -> DyadicTerminalFieldAction:
    one = DyadicTerminalFieldAction.one_run(1)
    return one.then(DyadicTerminalFieldAction.zero_run(tail)).then(one)


def _landing_parts(
    inlet: CollatzTwoSidedCylinder,
    action: DyadicTerminalFieldAction,
) -> tuple[tuple[int, CollatzTwoSidedCylinder, CollatzTwoSidedCylinder], ...]:
    """Partition the WHOLE inlet by the first outgoing endpoint parity bit.

    The completed 6305 return preserves residue 3 modulo 5.  Its parity
    therefore distinguishes the next 3-border from the 8-exit.  This is an
    affine preimage, not an interior decimal digit scan.
    """
    base = inlet.admitted_by(action)
    if base is None or base.count != inlet.count:
        raise ArithmeticError("the declared tail fails its parity-word guard")
    target = base.transport(action)
    if target.forced_residue(5) != 3:
        raise ArithmeticError("6305 carry broke the authenticated F5 border")
    forced = target.forced_residue(10)
    if forced in (3, 8):
        return ((forced, base, target),)
    d = action.steps
    modulus = 1 << (d + 1)
    result: list[tuple[int, CollatzTwoSidedCylinder, CollatzTwoSidedCylinder]] = []
    for parity, border in ((0, 8), (1, 3)):
        residue = ((parity << d) - action.offset) * pow(action.gain, -1, modulus)
        child = base.intersect_congruence(residue % modulus, modulus)
        if child is None:
            continue
        image = child.transport(action)
        if image.forced_residue(10) != border:
            raise ArithmeticError("outgoing border parity was not forced")
        result.append((border, child, image))
    if sum(part.count for _, part, _ in result) != inlet.count:
        raise ArithmeticError("outgoing 6305 carry partition lost sources")
    return tuple(result)


def compile_conditional_border_moore(
    cylinder: CollatzTwoSidedCylinder,
    physical_ticks: int,
    *,
    max_tail: int = 12,
    max_states: int = 256,
    max_returns: int = 32,
) -> ConditionalBorderMoore:
    """Build and minimize an exact, finite conditional 6305 successor graph.

    Every finite inlet is represented, including overlong tails and partial
    horizons. No guessed tail, parity, exit, carry or Sturmian period is ever
    published. State budgets refuse before publishing a truncated graph.
    """
    if type(cylinder) is not CollatzTwoSidedCylinder:
        raise TypeError("conditional Moore compiler requires an exact cylinder")
    if type(physical_ticks) is not int or physical_ticks < 1:
        raise ValueError("physical Collatz horizon must be positive")
    if type(max_tail) is not int or not 1 <= max_tail <= 64:
        raise ValueError("conditional Moore tail precision is outside 1..64")
    if type(max_states) is not int or not 2 <= max_states <= 16384:
        raise ValueError("conditional Moore state budget is outside 2..16384")
    if type(max_returns) is not int or not 1 <= max_returns <= 64:
        raise ValueError("conditional Moore return budget is outside 1..64")
    if cylinder.forced_residue(10) != 3:
        raise ValueError(
            "conditional border language requires an authenticated 3-border"
        )

    # Mutable builder records are replaced by immutable state objects at exit.
    queue: list[tuple[CollatzTwoSidedCylinder, int, int]] = [
        (cylinder, physical_ticks, 0)
    ]
    index = {(cylinder, physical_ticks, 0): 0}
    states: list[ConditionalBorderState] = []
    while len(states) < len(queue):
        current, remaining, depth = queue[len(states)]
        if remaining == 0:
            states.append(ConditionalBorderState(current, remaining, (), "complete"))
            continue
        if current.forced_residue(10) == 8:
            # 8->4/9 is one even step; retain both exact 20-residue exits.
            # No later 9->8 or 4->2 word is guessed.
            even_edges: list[ConditionalBorderEdge] = []
            even_action = DyadicTerminalFieldAction.zero_run(1)
            for residue, terminal in ((8, 4), (18, 9)):
                part = current.intersect_congruence(residue, 20)
                if part is None:
                    continue
                target = part.transport(even_action)
                if target.forced_residue(10) != terminal:
                    raise ArithmeticError("even border exit was not source-wide")
                key = (target, remaining - 1, depth)
                if key not in index:
                    if len(queue) >= max_states:
                        raise ConditionalBorderBudgetExceeded(
                            "conditional Moore state budget reached on an 8-border"
                        )
                    index[key] = len(queue)
                    queue.append(key)
                even_edges.append(
                    ConditionalBorderEdge(
                        None,
                        terminal,
                        part,
                        even_action,
                        target,
                        1,
                        index[key],
                    )
                )
            if sum(e.inlet.count for e in even_edges) != current.count:
                raise ArithmeticError(
                    "conditional 8-border partition lost source fibers"
                )
            states.append(
                ConditionalBorderState(current, remaining, tuple(even_edges), "active")
            )
            continue
        if current.forced_residue(10) == 9:
            # The certified 9->8->(4 or 9) physical pair is the normalized
            # odd action (3*x+1)/2, costing TWO physical ticks. Its next
            # border is chosen by the exact 20-residue, not a period guess.
            # This also covers an authentic 8->9 predecessor without storing
            # an unnecessary interior 8 digit.
            if remaining < 2:
                states.append(
                    ConditionalBorderState(
                        current,
                        remaining,
                        (
                            ConditionalBorderEdge(
                                None,
                                None,
                                current,
                                None,
                                None,
                                2,
                                None,
                                "partial_physical_odd_step",
                            ),
                        ),
                        "active",
                    )
                )
                continue
            if depth >= max_returns:
                states.append(ConditionalBorderState(current, remaining, (), "budget"))
                continue
            odd_edges: list[ConditionalBorderEdge] = []
            odd_action = DyadicTerminalFieldAction.one_run(1)
            for source_residue, terminal in ((9, 4), (19, 9)):
                part = current.intersect_congruence(source_residue, 20)
                if part is None:
                    continue
                target = part.transport(odd_action)
                if target.forced_residue(10) != terminal:
                    raise ArithmeticError("9-cycle exit is not source-wide")
                key = (target, remaining - 2, depth + 1)
                if key not in index:
                    if len(queue) >= max_states:
                        raise ConditionalBorderBudgetExceeded(
                            "conditional Moore state budget reached on a 9-cycle"
                        )
                    index[key] = len(queue)
                    queue.append(key)
                odd_edges.append(
                    ConditionalBorderEdge(
                        None,
                        terminal,
                        part,
                        odd_action,
                        target,
                        2,
                        index[key],
                        odd_events=1,
                    )
                )
            if sum(e.inlet.count for e in odd_edges) != current.count:
                raise ArithmeticError(
                    "conditional 9-cycle partition lost source fibers"
                )
            states.append(
                ConditionalBorderState(current, remaining, tuple(odd_edges), "active")
            )
            continue
        if current.forced_residue(10) != 3:
            states.append(ConditionalBorderState(current, remaining, (), "exit"))
            continue
        if depth >= max_returns:
            states.append(ConditionalBorderState(current, remaining, (), "budget"))
            continue
        return_edges: list[ConditionalBorderEdge] = []
        for tail, source_part in current.conditional_next_tails(max_tail=max_tail):
            if tail is None:
                return_edges.append(
                    ConditionalBorderEdge(
                        None,
                        None,
                        source_part,
                        None,
                        None,
                        None,
                        None,
                        "unresolved_long_tail",
                    )
                )
                continue
            cost = tail + 4
            if cost > remaining:
                return_edges.append(
                    ConditionalBorderEdge(
                        tail,
                        None,
                        source_part,
                        None,
                        None,
                        cost,
                        None,
                        "partial_physical_return",
                    )
                )
                continue
            action = _return_action(tail)
            for border, part, target in _landing_parts(source_part, action):
                new_remaining = remaining - cost
                key = (target, new_remaining, depth + 1)
                if key not in index:
                    if len(queue) >= max_states:
                        raise ConditionalBorderBudgetExceeded(
                            "conditional Moore state budget reached before closing all inlets"
                        )
                    index[key] = len(queue)
                    queue.append(key)
                return_edges.append(
                    ConditionalBorderEdge(
                        tail,
                        border,
                        part,
                        action,
                        target,
                        cost,
                        index[key],
                        odd_events=2,
                    )
                )
        if sum(edge.inlet.count for edge in return_edges) != current.count:
            raise ArithmeticError("conditional Collatz graph lost an inlet fiber")
        states.append(
            ConditionalBorderState(current, remaining, tuple(return_edges), "active")
        )

    # Finite-horizon Moore: right congruence for ALL declared inlet letters,
    # physical clocks and typed refusals. Concrete source guards live on the
    # edges and must always be checked independently of the class identifier.
    # Decreasing horizons form a DAG, so exact future signatures can be folded
    # bottom-up without assuming any periodic inlet word.
    classes = [-1] * len(states)
    signatures: dict[tuple[object, ...], int] = {}
    for i in sorted(range(len(states)), key=lambda n: states[n].remaining_ticks):
        state = states[i]
        transitions = tuple(
            sorted(
                (
                    (-1 if e.tail is None else e.tail),
                    (-1 if e.endpoint_border is None else e.endpoint_border),
                    e.physical_ticks,
                    e.odd_events,
                    e.refusal,
                    None if e.successor is None else classes[e.successor],
                )
                for e in state.edges
            )
        )
        signature = (state.status, state.remaining_ticks, transitions)
        if signature not in signatures:
            signatures[signature] = len(signatures)
        classes[i] = signatures[signature]
    return ConditionalBorderMoore(
        cylinder,
        physical_ticks,
        tuple(states),
        tuple(classes),
        len(signatures),
        max_tail,
    )


@dataclass(frozen=True, slots=True)
class ConditionalPoweredBranch:
    """An exact source slice, powered action, or conservatively refused inlet."""

    inlet: CollatzTwoSidedCylinder
    target: CollatzTwoSidedCylinder | None
    port: SourceClosedPortAction | None
    physical_ticks: int
    tails: MacroTraceGrammar
    refusal: str | None = None


@dataclass(frozen=True, slots=True)
class ConditionalReturnPower:
    """One binary-powered *conditional* return relation, including refusals.

    The return count is fixed. Physical duration may differ among inlet
    branches; no mismatched tick counts are treated as an equal-time square.
    """

    source: CollatzTwoSidedCylinder
    return_count: int
    branches: tuple[ConditionalPoweredBranch, ...]

    def __post_init__(self) -> None:
        if sum(b.inlet.count for b in self.branches) != self.source.count:
            raise ArithmeticError("powered conditional return lost source alternatives")

    def select(self, pointed_source: int) -> ConditionalPoweredBranch:
        if not self.source.contains(pointed_source):
            raise ValueError("pointed source is outside the powered inlet class")
        selected = tuple(b for b in self.branches if b.inlet.contains(pointed_source))
        if len(selected) != 1:
            raise ArithmeticError("conditional powered inlet is not a partition")
        return selected[0]

    def demanded_pointed_clock(
        self,
        source: int,
        *,
        precision: int = 32,
    ) -> SkewQuadraticClock | None:
        """Clock and radial scale of the same certified powered SLP action."""
        branch = self.select(source)
        if branch.port is None:
            return None
        clock = _trace_clock(branch.tails, precision)
        clock.verify(branch.port.action, source, branch.port.endpoint(source))
        return clock

    @property
    def class_count(self) -> int:
        """Future output classes for the declared return-count observation.

        The *guards* remain on branches even if output signatures coincide.
        They are never discarded when choosing the next source transition.
        """
        return len(
            {
                (
                    b.refusal,
                    b.physical_ticks,
                    None if b.target is None else b.target.forced_residue(10),
                    None if b.port is None else b.port.odd_events,
                    None if b.port is None else b.port.action.steps,
                )
                for b in self.branches
            }
        )


def _covers_entire_cylinder(
    cylinder: CollatzTwoSidedCylinder,
    guard: SourceCongruence,
) -> bool:
    return guard.admits(cylinder.first) and (
        cylinder.count == 1
        or (
            cylinder.modulus % guard.modulus == 0
            and cylinder.residue % guard.modulus == guard.residue
        )
    )


def _one_return_relation(
    cylinder: CollatzTwoSidedCylinder,
    *,
    max_tail: int,
) -> ConditionalReturnPower:
    if cylinder.forced_residue(10) != 3:
        return ConditionalReturnPower(
            cylinder,
            1,
            (
                ConditionalPoweredBranch(
                    cylinder,
                    None,
                    None,
                    0,
                    MacroTraceGrammar.leaf(()),
                    "not_a_three_border",
                ),
            ),
        )
    branches = []
    for j, part in cylinder.conditional_next_tails(max_tail=max_tail):
        if j is None:
            branches.append(
                ConditionalPoweredBranch(
                    part,
                    None,
                    None,
                    0,
                    MacroTraceGrammar.leaf(()),
                    "unresolved_long_tail",
                )
            )
            continue
        action = _return_action(j)
        for _, admitted, target in _landing_parts(part, action):
            guard = SourceCongruence(admitted.residue, admitted.modulus)
            port = SourceClosedPortAction(action, guard, 2, None)
            branches.append(
                ConditionalPoweredBranch(
                    admitted,
                    target,
                    port,
                    j + 4,
                    MacroTraceGrammar.leaf((j,)),
                )
            )
    return ConditionalReturnPower(cylinder, 1, tuple(branches))


def _validate_power_request(
    source: CollatzTwoSidedCylinder,
    exponent: int,
    max_tail: int,
    max_coefficient_bits: int,
    ledger: ResourceLedger | None,
) -> None:
    if type(source) is not CollatzTwoSidedCylinder:
        raise TypeError("power source must be an exact Collatz cylinder")
    if type(exponent) is not int or not 0 <= exponent <= 12:
        raise ValueError("conditional return power exponent must be in 0..12")
    if type(max_tail) is not int or not 1 <= max_tail <= 64:
        raise ValueError("conditional return max tail must be in 1..64")
    if type(max_coefficient_bits) is not int or max_coefficient_bits < 32:
        raise ValueError("conditional coefficient budget is too small")
    if ledger is not None and type(ledger) is not ResourceLedger:
        raise TypeError("conditional powering accounting needs a query ledger")
    if (1 << exponent) * 8 > max_coefficient_bits:
        raise ConditionalBorderBudgetExceeded(
            "requested conditional temporal power exceeds its coefficient budget"
        )


def try_compile_conditional_repeated_motif(
    source: CollatzTwoSidedCylinder,
    exponent: int,
    *,
    max_tail: int = 12,
    max_coefficient_bits: int = 8192,
    ledger: ResourceLedger | None = None,
) -> ConditionalReturnPower | None:
    """Power a small *whole-fiber* driver, never a guessed seed period.

    The forced prefix is independently issued from both source ends.
    SourceClosedPortAction.power then proves ALL repetitions by source
    guard preimages. This avoids expanding 2**k copies or their Moore
    inlet nodes when the existing 6305 cylinder is already closed.
    """
    _validate_power_request(source, exponent, max_tail, max_coefficient_bits, ledger)
    copies = 1 << exponent
    if copies < 4 or source.forced_residue(10) != 3:
        return None
    for motif_length in (1, 2, 4, 8):
        if motif_length > copies:
            break
        prefix, _, tails = source.forced_future(
            max_returns=motif_length, max_tail=max_tail, ledger=ledger
        )
        if len(tails) != motif_length:
            continue
        # An exact 2-adic centered-defect precheck.  If a whole fiber
        # does not satisfy it, the much more expensive binary action
        # need not be constructed. The subsequent port.power() remains
        # the independent authoritative parity-word certificate.
        needed = prefix.steps * (copies // motif_length)
        if source.count > 1 and source.binary_precision < needed:
            continue
        defect = (1 << prefix.steps) - prefix.gain
        residual = (defect * source.first - prefix.offset) % (1 << needed)
        if residual:
            continue
        guard = SourceCongruence(prefix.source_residue, prefix.source_modulus).meet(
            SourceCongruence(3, 5)
        )
        if guard is None:
            raise ArithmeticError("source-forced driver lost its F5 guard")
        port = SourceClosedPortAction(prefix, guard, 2 * motif_length, None)
        try:
            powered = port.power(
                copies // motif_length,
                max_coefficient_bits=max_coefficient_bits,
                ledger=ledger,
            )
        except (BlockContextBudgetExceeded, OverflowError):
            powered = None
        if powered is None or not _covers_entire_cylinder(source, powered.guard):
            continue
        certified = source.intersect_congruence(
            powered.guard.residue, powered.guard.modulus, ledger=ledger
        )
        if certified is None or certified.count != source.count:
            raise ArithmeticError("powered source cylinder lost alternatives")
        target = certified.transport(powered.action, ledger=ledger)
        # The motif was supplied by *all* sources in this cylinder, and
        # the powered guard independently authenticates every later copy.
        trace = MacroTraceGrammar.leaf(tails)
        trace_power = trace
        for _ in range(exponent - (motif_length.bit_length() - 1)):
            trace_power = trace_power.then(trace_power)
        if trace_power.length != copies:
            raise ArithmeticError("binary power trace has wrong return count")
        return ConditionalReturnPower(
            source,
            copies,
            (
                ConditionalPoweredBranch(
                    certified,
                    target,
                    powered,
                    (copies // motif_length) * sum(j + 4 for j in tails),
                    trace_power,
                ),
            ),
        )
    return None


def compile_conditional_return_power(
    cylinder: CollatzTwoSidedCylinder,
    exponent: int,
    *,
    max_tail: int = 12,
    max_branches: int = 256,
    max_coefficient_bits: int = 8192,
) -> ConditionalReturnPower:
    """Square a conditional 6305 return relation for ``2**exponent`` returns.

    Every second-half inlet is computed on the ENTIRE transported first-half
    source cylinder. The two affine source guards are joined by pullback.
    When the full fiber certifies a repeated word, use existing binary power
    instead of traversing its individual return events. Open inlets remain
    typed refusals. Never equate source-independent harmonic observations with
    a certified future driver.
    """
    _validate_power_request(cylinder, exponent, max_tail, max_coefficient_bits, None)
    if type(max_branches) is not int or not 1 <= max_branches <= 16384:
        raise ValueError("conditional branch budget must be in 1..16384")
    cache: dict[tuple[CollatzTwoSidedCylinder, int], ConditionalReturnPower] = {}

    pending: list[tuple[CollatzTwoSidedCylinder, int, bool]] = [
        (cylinder, exponent, False)
    ]
    while pending:
        source, k, combine_halves = pending.pop()
        key = source, k
        if key in cache:
            continue
        if not combine_halves:
            repeated = try_compile_conditional_repeated_motif(
                source,
                k,
                max_tail=max_tail,
                max_coefficient_bits=max_coefficient_bits,
            )
            if repeated is not None:
                cache[key] = repeated
                continue
            if k == 0:
                cache[key] = _one_return_relation(source, max_tail=max_tail)
                continue
            pending.append((source, k, True))
            half_key = source, k - 1
            if half_key not in cache:
                pending.append((source, k - 1, False))
            continue

        # All dependencies have a smaller exponent, so this explicit
        # postorder worklist replaces recursion without changing the binary
        # source-guard composition.
        half = cache[(source, k - 1)]
        if len(half.branches) == 1:
            only = half.branches[0]
            if (
                only.port is not None
                and only.target is not None
                and only.target.forced_residue(10) == 3
            ):
                try:
                    squared = only.port.power(
                        2, max_coefficient_bits=max_coefficient_bits
                    )
                except (BlockContextBudgetExceeded, OverflowError):
                    squared = None
                if squared is not None and _covers_entire_cylinder(
                    source, squared.guard
                ):
                    certified_source = source.intersect_congruence(
                        squared.guard.residue, squared.guard.modulus
                    )
                    if (
                        certified_source is None
                        or certified_source.count != source.count
                    ):
                        raise ArithmeticError(
                            "powered guard lost its complete source class"
                        )
                    target = certified_source.transport(squared.action)
                    result = ConditionalReturnPower(
                        source,
                        1 << k,
                        (
                            ConditionalPoweredBranch(
                                certified_source,
                                target,
                                squared,
                                only.physical_ticks * 2,
                                only.tails.then(only.tails),
                            ),
                        ),
                    )
                    cache[key] = result
                    continue

        needed: dict[tuple[CollatzTwoSidedCylinder, int], None] = {}
        for before in half.branches:
            if (
                before.port is not None
                and before.target is not None
                and before.target.forced_residue(10) == 3
            ):
                needed[(before.target, k - 1)] = None
        missing = [dependency for dependency in needed if dependency not in cache]
        if missing:
            pending.append((source, k, True))
            pending.extend(
                (dependency[0], dependency[1], False)
                for dependency in reversed(missing)
            )
            continue

        out: list[ConditionalPoweredBranch] = []
        for before in half.branches:
            if before.port is None or before.target is None:
                out.append(before)
                continue
            if before.target.forced_residue(10) != 3:
                out.append(
                    ConditionalPoweredBranch(
                        before.inlet,
                        None,
                        None,
                        before.physical_ticks,
                        before.tails,
                        "exit_before_requested_return_count",
                    )
                )
                continue
            after_rel = cache[(before.target, k - 1)]
            for after in after_rel.branches:
                # The after inlet is an exact subcoset of before.target;
                # pull it all the way back through the first-half map.
                pulled = SourceCongruence(
                    after.inlet.residue, after.inlet.modulus
                ).pullback(before.port.action)
                if pulled is None:
                    continue
                input_part = before.inlet.intersect_congruence(
                    pulled.residue, pulled.modulus
                )
                if input_part is None:
                    continue
                if after.port is None:
                    out.append(
                        ConditionalPoweredBranch(
                            input_part,
                            None,
                            None,
                            before.physical_ticks,
                            before.tails,
                            after.refusal,
                        )
                    )
                    continue
                if after.target is None:
                    raise ArithmeticError("powered action has no exact target cylinder")
                combined = before.port.then(after.port)
                if combined is None or not _covers_entire_cylinder(
                    input_part, combined.guard
                ):
                    raise ArithmeticError("source-closed guard failed a binary square")
                certified_input = input_part.intersect_congruence(
                    combined.guard.residue, combined.guard.modulus
                )
                if certified_input is None or certified_input.count != input_part.count:
                    raise ArithmeticError(
                        "joint guard lost the original source alternative"
                    )
                target = certified_input.transport(combined.action)
                if (
                    target.count != input_part.count
                    or target.first != after.target.first
                    or target.last != after.target.last
                ):
                    raise ArithmeticError(
                        "powered conditional image changed its full CRT fiber"
                    )
                out.append(
                    ConditionalPoweredBranch(
                        certified_input,
                        target,
                        combined,
                        before.physical_ticks + after.physical_ticks,
                        before.tails.then(after.tails),
                    )
                )
                if len(out) > max_branches:
                    raise ConditionalBorderBudgetExceeded(
                        "conditional temporal square exceeds its branch budget"
                    )
        result = ConditionalReturnPower(source, 1 << k, tuple(out))
        if len(result.branches) > max_branches:
            raise ConditionalBorderBudgetExceeded(
                "conditional temporal square exceeds its branch budget"
            )
        cache[key] = result

    return cache[(cylinder, exponent)]


__all__ = (
    "ConditionalBorderBudgetExceeded",
    "ConditionalBorderEdge",
    "ConditionalBorderMoore",
    "ConditionalBorderState",
    "ConditionalPoweredBranch",
    "ConditionalReturnPower",
    "PointedBorderPath",
    "compile_conditional_border_moore",
    "compile_conditional_return_power",
    "try_compile_conditional_repeated_motif",
)
