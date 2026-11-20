"""Source-authorized carry-in programs for *all* named Collatz border macros.

There are two complementary transfers:

* A five-state deterministic weighted mod-5 transducer. A proved parity
  letter plus the current value mod 5 fixes the units digit, hence the
  incoming carry to the tens position for each multiplication by three.
  Repeated named motifs are binary-powered: no temporal leaf loop is needed.
* The existing source-guarded 100x100 pair transfer, fed exact admitted macro
  prefixes. This keeps higher decimal carries, upper-parity inlets, forced
  base-6 resets, and later digit ports on the same root cylinder.  Unknown
  upper inlets remain guarded alternatives; they are not inferred from mod 5.

An incomplete digit word such as 2684 is an authenticated prefix of an issued
26847 action, not a new infinitely repeatable macro identity.
"""

from __future__ import annotations

from collections.abc import Callable
from contextlib import ExitStack
from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    CollatzSegmentIdentity,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    validate_border_return_macro,
)
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_port_join import (
    GuardedPortCut,
    GuardedPortJoin,
    PortPuncture,
    certify_pointed_port_join,
)
from number_compiler.sequences.collatz.source_closed_port_action import SourceCongruence

MAX_NAMED_MATRIX_TRACE_PREFIX = 64

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        GuardedTemporalCarryCounts,
    )
    from number_compiler.sequences.collatz.parity_carry_tape_actions import (
        LedgeredParityTapeActions,
    )
    from number_compiler.sequences.collatz.temporal_source_morphism import (
        CertifiedCollatzRootMorphism,
    )


@dataclass(frozen=True, slots=True)
class UnitsCarryMatrix:
    """Five-state weighted transfer (x mod 5 -> x' mod 5, sum of c_tens).

    The parity letter comes from an independently issued Collatz macro.
    Every input residue represents a complete class of *decimal units*
    satisfying that exact parity. Output tens carries are forced, while
    hundreds carry remains a guarded port in the 100x100 relation.
    """

    target: tuple[int, int, int, int, int] = (0, 1, 2, 3, 4)
    tens: tuple[int, int, int, int, int] = (0, 0, 0, 0, 0)
    odds: int = 0
    steps: int = 0

    def __post_init__(self) -> None:
        if (
            len(self.target) != 5
            or len(self.tens) != 5
            or any(type(n) is not int or n < 0 or n >= 5 for n in self.target)
            or any(type(n) is not int or n < 0 for n in self.tens)
            or type(self.odds) is not int
            or type(self.steps) is not int
            or not 0 <= self.odds <= self.steps
        ):
            raise ValueError("malformed mod-5 forced-carry transfer")

    @classmethod
    def letter(cls, odd: int) -> UnitsCarryMatrix:
        if type(odd) is not int or odd not in (0, 1):
            raise ValueError("forced tens carry requires an authenticated parity bit")
        if not odd:
            return cls(
                cast(
                    tuple[int, int, int, int, int], tuple(3 * r % 5 for r in range(5))
                ),
                (0, 0, 0, 0, 0),
                0,
                1,
            )
        return cls(
            cast(
                tuple[int, int, int, int, int], tuple((4 * r + 3) % 5 for r in range(5))
            ),
            cast(
                tuple[int, int, int, int, int],
                tuple((3 * (r if r & 1 else r + 5) + 1) // 10 for r in range(5)),
            ),
            1,
            1,
        )

    def then(self, after: UnitsCarryMatrix) -> UnitsCarryMatrix:
        if type(after) is not UnitsCarryMatrix:
            raise TypeError("units carry needs another certified transfer")
        return UnitsCarryMatrix(
            cast(
                tuple[int, int, int, int, int],
                tuple(after.target[self.target[r]] for r in range(5)),
            ),
            cast(
                tuple[int, int, int, int, int],
                tuple(self.tens[r] + after.tens[self.target[r]] for r in range(5)),
            ),
            self.odds + after.odds,
            self.steps + after.steps,
        )

    def power(self, repetitions: int) -> UnitsCarryMatrix:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("forced-carry repetition requires nonnegative exponent")
        return binary_power(
            self,
            repetitions,
            identity=UnitsCarryMatrix(),
            compose=lambda first, after: first.then(after),
        ).value

    @classmethod
    def factors(
        cls, grammar: tuple[tuple[tuple[int, ...], int], ...]
    ) -> UnitsCarryMatrix:
        """Fold exact mixed-border, zero-run and 89/421/4721 factor SLPs."""
        if type(grammar) is not tuple:
            raise TypeError("weighted factors require an authenticated tuple")
        result = cls()
        for motif, count in grammar:
            if (
                type(motif) is not tuple
                or not 1 <= len(motif) <= 64
                or any(type(bit) is not int or bit not in (0, 1) for bit in motif)
                or type(count) is not int
                or count < 1
            ):
                raise ValueError("malformed Collatz weighted factor")
            result = result.then(cls.word(motif).power(count))
        return result

    @classmethod
    def word(cls, letters: tuple[int, ...]) -> UnitsCarryMatrix:
        acc = cls()
        for bit in letters:
            acc = acc.then(cls.letter(bit))
        return acc

    def apply(self, source_mod5: int) -> tuple[int, int]:
        if type(source_mod5) is not int or not 0 <= source_mod5 < 5:
            raise ValueError("source's exact mod-5 residue is required")
        return self.target[source_mod5], self.tens[source_mod5]


def _joined_trace_packet(
    joined: GuardedPortJoin,
    units: UnitsCarryMatrix,
    source: int,
    physical_ticks: int,
    normalized_steps: int,
    *,
    action_identity: str | None,
    skew_clock: dict[str, object] | None,
    parity_actions: LedgeredParityTapeActions | None,
) -> dict[str, object]:
    """Render one bounded authenticated parity prefix for either result kind."""
    if type(normalized_steps) is not int or not 0 <= normalized_steps <= min(
        units.steps, MAX_NAMED_MATRIX_TRACE_PREFIX
    ):
        raise ValueError("Collatz matrix trace prefix exceeds 64 normalized steps")
    joined.port.verify_issued()
    tape = joined.parity_tape_for_action(cache=parity_actions)
    if tape is None:
        raise ValueError("matrix result has no retained authenticated parity tape")
    parity = tape.prefix_letters(normalized_steps)
    prefix_units = (
        parity_actions.prefix_units(tape, normalized_steps)
        if parity_actions is not None
        else tape.prefix_units(normalized_steps)
    )
    prefix_action = tape.prefix_action(normalized_steps)
    target_mod5, tens_carries = prefix_units.apply(source % 5)
    if (
        not prefix_action.certifies(source)
        or prefix_action.endpoint(source) % 5 != target_mod5
        or prefix_units.odds != sum(parity)
    ):
        raise ArithmeticError("bounded trace differs from retained carry action")
    odd_events = sum(parity)
    return {
        "action_identity": action_identity,
        "clocks": {
            "normalized_steps": {
                "value": units.steps,
                "unit": "normalized-halving-events",
            },
            "odd_events": {"value": units.odds, "unit": "odd-events"},
            "physical_ticks": {
                "value": physical_ticks,
                "unit": "physical-ticks",
            },
            "skew_clock": skew_clock,
        },
        "trace": {
            "unit": "normalized-halving-events",
            "normalized_steps": normalized_steps,
            "parity": parity,
            "odd_events": odd_events,
            "physical_ticks": {
                "value": normalized_steps + odd_events,
                "unit": "physical-ticks",
            },
            "source_mod5": source % 5,
            "endpoint_mod5": target_mod5,
            "forced_tens_carries": tens_carries,
            "physical_prefix_status": (
                "complete" if normalized_steps == units.steps else "partial"
            ),
        },
    }


@dataclass(frozen=True, slots=True, init=False)
class NamedBorderCarryMatrix:
    """A proved named macro's tens-inlet program and guarded 100x100 relation."""

    macro: CollatzBoundaryMacro | BorderReturnMacro
    joined: GuardedPortJoin
    units: UnitsCarryMatrix

    @classmethod
    def issue_from_admitted_macro(
        cls,
        macro: CollatzBoundaryMacro | BorderReturnMacro,
        joined: GuardedPortJoin,
        units: UnitsCarryMatrix,
    ) -> NamedBorderCarryMatrix:
        """Create the result only from the producer's exact word summary."""
        result = object.__new__(cls)
        object.__setattr__(result, "macro", macro)
        object.__setattr__(result, "joined", joined)
        object.__setattr__(result, "units", units)
        result.validate()
        return result

    def validate(self) -> None:
        """Recheck producer authority before using retained macro metadata."""
        if type(self.macro) is CollatzBoundaryMacro:
            validate_boundary_macro(self.macro)
        elif type(self.macro) is BorderReturnMacro:
            validate_border_return_macro(self.macro)
        else:
            raise TypeError("only producer-issued border macros can fill the matrix")
        if (
            self.joined.port.action.coefficient_snapshot()
            != self.macro.fields.coefficient_snapshot()
            or self.joined.port.odd_events != self.macro.odd_symbols
            or self.joined.source.forced_residue(5) != self.macro.source % 5
            or self.units.steps != self.macro.normalized_symbols
            or self.units.odds != self.macro.odd_symbols
            or self.joined.named_macro is not self.macro
        ):
            raise ValueError(
                "named carry/decimal matrices lost their common issued source"
            )
        endpoint5, _ = self.units.apply(self.macro.source % 5)
        if endpoint5 != self.macro.endpoint % 5:
            raise ArithmeticError("powered low-digit carry matrix lost macro endpoint")

    @property
    def source(self) -> int:
        return self.macro.source

    @property
    def endpoint(self) -> int:
        return self.macro.endpoint

    @property
    def physical_ticks(self) -> int:
        return self.macro.physical_ticks

    @property
    def forced_tens_carries(self) -> int:
        return self.units.apply(self.macro.source % 5)[1]

    def puncture(
        self,
        time: int,
        request: PortPuncture | None = None,
        *,
        pointed_source: int | None = None,
        max_rows: int = 200,
        parity_actions: LedgeredParityTapeActions | None = None,
    ) -> GuardedPortCut:
        """Demand an interior time cut without scalar replaying the macro."""
        cut = self.joined.puncture(
            time,
            request,
            pointed_source=pointed_source,
            max_rows=max_rows,
            parity_cache=parity_actions,
        )
        if time < self.units.steps:
            prefix = cut.prefix
            prefix5 = self._prefix_units(time, parity_actions=parity_actions)
            target5, _ = prefix5.apply(self.macro.source % 5)
            if cut.rows and any(row.input_pair % 5 != target5 for row in cut.rows):
                raise ArithmeticError(
                    "hundreds-carry matrix contradicts forced units digit"
                )
            if prefix.endpoint(self.macro.source) % 5 != target5:
                raise ArithmeticError(
                    "named macro carry inlet and source prefix disagree"
                )
            forced_digit = (
                target5
                if target5 % 2 == (prefix.endpoint(self.macro.source) % 2)
                else target5 + 5
            )
            if cut.rows:
                expected_tens = (3 * forced_digit + 1) // 10 if forced_digit & 1 else 0
                if any(row.tens != expected_tens for row in cut.rows):
                    raise ArithmeticError(
                        "named macro forced tens carry was not propagated to matrix"
                    )
        return cut

    def _prefix_units(
        self,
        time: int,
        *,
        parity_actions: LedgeredParityTapeActions | None = None,
    ) -> UnitsCarryMatrix:
        """Demand a single small port from the compressed parity grammar."""
        if not 0 <= time <= self.units.steps:
            raise ValueError("requested interior time outside named action")
        tape = self.joined.parity_tape_for_action(cache=parity_actions)
        if tape is None:
            raise ValueError("named matrix lost its retained source parity grammar")
        if parity_actions is None:
            return tape.prefix_units(time)
        return parity_actions.prefix_units(tape, time)

    def trace_packet(
        self,
        *,
        normalized_steps: int = MAX_NAMED_MATRIX_TRACE_PREFIX,
        parity_actions: LedgeredParityTapeActions | None = None,
    ) -> dict[str, object]:
        """Read a bounded parity prefix from the retained authenticated SLP.

        The packet keeps the three clocks distinct: normalized halvings,
        odd events, and physical Collatz ticks.  It never reconstructs an
        itinerary from the source integer or creates a scheduler occurrence.
        """
        if type(self.macro) is CollatzBoundaryMacro:
            validate_boundary_macro(self.macro)
            physical_ticks = self.macro.physical_ticks
        elif type(self.macro) is BorderReturnMacro:
            validate_border_return_macro(self.macro)
            physical_ticks = self.macro.physical_ticks
        else:
            raise TypeError("trace requires a producer-issued Collatz macro")
        clock = self.joined.port.clock
        skew_clock: dict[str, object] | None = None
        if clock is not None:
            skew_clock = {
                "steps": clock.steps,
                "unit": "normalized-halving-events",
                "precision_bits": clock.precision,
                "value": clock.value,
            }
        return _joined_trace_packet(
            self.joined,
            self.units,
            self.macro.source,
            physical_ticks,
            normalized_steps,
            action_identity=self.macro.identity.display_label,
            skew_clock=skew_clock,
            parity_actions=parity_actions,
        )

    def weighted_carry_counts(
        self, pointed_source: int, *, max_steps: int = 512
    ) -> GuardedTemporalCarryCounts:
        """Return the *entire* weighted port only where its inlet is certified.

        The mod-5 tens component is fully binary-powered for named motifs.
        Higher decimal carry counts still require a proved 100-state inlet
        program; the existing bounded evaluator refuses unproved long ones.
        """
        if not self.joined.source.contains(pointed_source):
            raise ValueError(
                "pointed weighted carry source outside the issued cylinder"
            )
        result = self.joined.authenticate_weighted_ports(
            pointed_source,
            max_steps=max_steps,
        )
        if result.carry_tens != self.forced_tens_carries:
            raise ArithmeticError(
                "named powered tens-carry count differs from weighted 100-state path"
            )
        if result.last_pair != self.macro.fields.endpoint(pointed_source) % 100:
            raise ArithmeticError(
                "named weighted matrix interior lost its endpoint pair"
            )
        return result

    def successor_candidate_partition(
        self,
    ) -> tuple[tuple[CollatzSegmentIdentity | None, CollatzTwoSidedCylinder], ...]:
        """Exact root partitions by *every* named next-border candidate.

        These are source-pulled modulo-160 entry guards. An entry family is
        not yet permission to power a particular repetition count: its
        valuation/width/horizon guard must still be issued by the canonical
        successor selector. Unknown odd entrances are retained as None.
        """
        return self.joined.future_family_partition()

    def successor_partition(self) -> tuple[tuple[int, GuardedPortJoin], ...]:
        """Partition possible next decimal borders on original-source guards.

        A digit does not yet certify a future macro length/valuation; the next
        admission must still pass its own exact parity and width guards.
        """
        return self.joined.future_border_partition()


@dataclass(frozen=True, slots=True, init=False)
class AdjacentBorderCarryMatrix:
    """Exact finite join of adjacent issued border actions.

    The constituent macros remain separate certificates. This result carries
    their composed port and low digit transfer without inventing a synthetic
    macro identity for the whole chain.
    """

    joined: GuardedPortJoin
    units: UnitsCarryMatrix

    @classmethod
    def compose_admitted_children(
        cls,
        left: NamedBorderCarryMatrix | AdjacentBorderCarryMatrix,
        right: NamedBorderCarryMatrix,
        joined: GuardedPortJoin,
    ) -> AdjacentBorderCarryMatrix:
        """Transport exact parent summaries through their issued parity join."""
        if type(left) is NamedBorderCarryMatrix:
            left.validate()
        elif type(left) is AdjacentBorderCarryMatrix:
            left.validate()
        else:
            raise TypeError("adjacent composition requires an issued left summary")
        if type(right) is not NamedBorderCarryMatrix:
            raise TypeError("adjacent composition requires an issued right macro")
        right.validate()
        if type(joined) is not GuardedPortJoin:
            raise TypeError("adjacent composition requires its exact joined port")
        if left.endpoint != right.source:
            raise ValueError("adjacent carry segments have an open source seam")
        left_tape = left.joined.parity_tape_for_action()
        right_tape = right.joined.parity_tape_for_action()
        parents = joined.parity_composition_parents()
        if (
            left_tape is None
            or right_tape is None
            or parents is None
            or parents[0] is not left_tape
            or parents[1] is not right_tape
        ):
            raise ValueError("joined carry action has different certified parents")
        result = object.__new__(cls)
        object.__setattr__(result, "joined", joined)
        object.__setattr__(result, "units", left.units.then(right.units))
        result.validate()
        return result

    def validate(self) -> None:
        """Check the joined issuer witness and its transported carry clocks."""
        if (
            type(self.joined) is not GuardedPortJoin
            or type(self.units) is not UnitsCarryMatrix
        ):
            raise TypeError("adjacent carry transfer requires an exact joined action")
        if self.joined.source.count != 1:
            raise ValueError("adjacent carry transfer requires a pointed source")
        source = self.joined.source.first
        endpoint = self.joined.port.endpoint(source)
        parents = self.joined.parity_composition_parents()
        if (
            parents is None
            or self.joined.port.action.steps != self.units.steps
            or self.joined.port.odd_events != self.units.odds
            or not self.joined.bridge.target.contains(endpoint)
            or self.units.steps + self.units.odds <= 0
            or self.units.apply(source % 5)[0] != endpoint % 5
        ):
            raise ArithmeticError(
                "adjacent carry transfer lost its exact joined action"
            )
        self.joined.port.verify_issued()

    @property
    def source(self) -> int:
        return self.joined.source.first

    @property
    def endpoint(self) -> int:
        return self.joined.port.endpoint(self.source)

    @property
    def physical_ticks(self) -> int:
        return self.units.steps + self.units.odds

    @property
    def forced_tens_carries(self) -> int:
        return self.units.apply(self.source % 5)[1]

    def trace_packet(
        self,
        *,
        normalized_steps: int = MAX_NAMED_MATRIX_TRACE_PREFIX,
        parity_actions: LedgeredParityTapeActions | None = None,
    ) -> dict[str, object]:
        return _joined_trace_packet(
            self.joined,
            self.units,
            self.source,
            self.physical_ticks,
            normalized_steps,
            action_identity=None,
            skew_clock=None,
            parity_actions=parity_actions,
        )


def certify_named_border_carry_matrix(
    macro: CollatzBoundaryMacro | BorderReturnMacro,
    *,
    source: CollatzTwoSidedCylinder | None = None,
    ledger: ResourceLedger | None = None,
    parity_actions: LedgeredParityTapeActions | None = None,
) -> NamedBorderCarryMatrix:
    """Issue a reusable guarded carry operator from an *already admitted* macro."""
    if type(macro) is CollatzBoundaryMacro:
        validate_boundary_macro(macro)
    elif type(macro) is BorderReturnMacro:
        validate_border_return_macro(macro)
    else:
        raise TypeError("named carry matrix requires an issued macro")
    if source is None:
        source = CollatzTwoSidedCylinder(macro.source, macro.source, 0, 1)
    if type(source) is not CollatzTwoSidedCylinder or not source.contains(macro.source):
        raise ValueError("named carry matrix requires an original-source cylinder")
    if parity_actions is not None:
        from number_compiler.sequences.collatz.parity_carry_tape_actions import (
            LedgeredParityTapeActions,
        )

        if (
            type(parity_actions) is not LedgeredParityTapeActions
            or ledger is None
            or parity_actions.ledger is not ledger
        ):
            raise ValueError("named parity actions must use the source query ledger")
    # Exact parity authority plus the initial 5-adic phase makes every units
    # digit, hence every tens carry, identical across this admitted fiber.
    guard = SourceCongruence(macro.fields.source_residue, macro.fields.source_modulus)
    restricted_guard = guard.meet(SourceCongruence(macro.source % 5, 5))
    if restricted_guard is None:
        raise ArithmeticError("named carry source contradicts its border phase")
    guard = restricted_guard
    restricted = source.intersect_congruence(guard.residue, guard.modulus)
    if (
        restricted is None
        or not restricted.contains(macro.source)
        or restricted.count != source.count
    ):
        raise ValueError("source cylinder includes unproved named carry alternatives")
    joined = certify_pointed_port_join(
        macro.source,
        macro.fields,
        macro.odd_symbols,
        ledger=ledger,
        macro=macro,
        source_cylinder=source,
        parity_cache=parity_actions,
    )
    tape = joined.parity_tape_for_action(cache=parity_actions)
    if tape is None:
        raise ArithmeticError("named source join did not retain its parity grammar")
    if parity_actions is not None:
        units = parity_actions.prefix_units(tape, tape.steps)
    elif ledger is None:
        units = tape.prefix_units(tape.steps)
    else:
        # Standalone ledgered certification has no persistent tape owner to
        # provide a DAG-size bound, so reserve against the expanded finite
        # matrix horizon before allocating prefix chunks or effect rows.
        from number_compiler.resources.ledger import LedgerReservation

        scratch_owner = ledger.register(
            f"collatz-named-matrix-prefix-scratch-{ledger.owner_count}",
            "execution_stack",
        )
        scratch_entries = 2 * tape.steps + 16
        scratch_nodes = 64 + 24 * scratch_entries
        try:
            with LedgerReservation(ledger, scratch_owner) as reservation:
                reservation.reserve(entries=scratch_entries, nodes=scratch_nodes)
                units = tape.prefix_units(tape.steps)
        finally:
            if not ledger.account_status(scratch_owner).disposed:
                ledger.mark_disposed(scratch_owner)
    if units.steps != macro.fields.steps or units.odds != macro.odd_symbols:
        raise ArithmeticError("forced-carry matrix differs from issued macro clocks")
    program = NamedBorderCarryMatrix.issue_from_admitted_macro(macro, joined, units)
    # Source-wide guard already determines the count, not just this witness.
    program.joined.require_pointed(macro.source, parity_cache=parity_actions)
    return program


MAX_ENDPOINT_PHYSICAL_STEPS = 128


def _matrix_span_with_owner(
    source: int,
    ledger: ResourceLedger,
    physical_steps: int,
    parity_actions: LedgeredParityTapeActions | None,
    *,
    parity_actions_factory: Callable[[], LedgeredParityTapeActions] | None = None,
    trace_required: bool = False,
    single_macro_scope: ExitStack | None = None,
) -> NamedBorderCarryMatrix | AdjacentBorderCarryMatrix | None:
    from number_compiler.sequences.collatz.matrix_span_admission import (
        admit_matrix_span,
    )

    return admit_matrix_span(
        source,
        ledger,
        physical_steps,
        parity_actions=parity_actions,
        parity_actions_factory=parity_actions_factory,
        trace_required=trace_required,
        single_macro_scope=single_macro_scope,
    )


def powered_from_endpoint(
    root: CertifiedCollatzRootMorphism,
    physical_steps: int,
    *,
    parity_actions: LedgeredParityTapeActions | None = None,
    parity_actions_factory: Callable[[], LedgeredParityTapeActions] | None = None,
    trace_required: bool = False,
    single_macro_scope: ExitStack | None = None,
) -> NamedBorderCarryMatrix | AdjacentBorderCarryMatrix | None:
    """Join exact next macros from an actual Collatz root occurrence.

    The selected macro starts at ``root.last.value``. A past source/endpoint
    action is never reused as if it started at this new root. Each following
    segment is admitted independently from the exact prior endpoint, and a
    request is unavailable if any seam or remaining tail is unrepresented.
    """
    from number_compiler.sequences.collatz.temporal_source_morphism import (
        CertifiedCollatzRootMorphism,
    )

    if type(root) is not CertifiedCollatzRootMorphism:
        raise TypeError("powered Collatz join requires an issued root occurrence")
    root.validate()
    return _matrix_span_with_owner(
        root.last.value,
        root.owner.ledger,
        physical_steps,
        parity_actions,
        parity_actions_factory=parity_actions_factory,
        trace_required=trace_required,
        single_macro_scope=single_macro_scope,
    )


def powered_from_term(
    term: PoweredCollatzTerm,
    physical_steps: int,
    *,
    parity_actions: LedgeredParityTapeActions | None = None,
    parity_actions_factory: Callable[[], LedgeredParityTapeActions] | None = None,
    trace_required: bool = False,
    single_macro_scope: ExitStack | None = None,
) -> NamedBorderCarryMatrix | AdjacentBorderCarryMatrix | None:
    """Select the next physical border from an actual projected Collatz term.

    A zero-step query is anchored at the term's authenticated initial seed and
    its existing ledger. Positive queries require the term's producer-issued
    true-root morphism, so this entry point never guesses a center or replays
    the scalar orbit to manufacture an endpoint.
    """
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    if type(term) is not PoweredCollatzTerm:
        raise TypeError("powered Collatz join requires the actual powered term")
    if (
        type(physical_steps) is not int
        or not 1 <= physical_steps <= MAX_ENDPOINT_PHYSICAL_STEPS
    ):
        raise ValueError("powered Collatz physical span exceeds its finite horizon")
    if parity_actions is not None:
        from number_compiler.sequences.collatz.parity_carry_tape_actions import (
            LedgeredParityTapeActions,
        )

        if (
            type(parity_actions) is not LedgeredParityTapeActions
            or parity_actions.ledger is not term.resource_ledger
        ):
            raise ValueError(
                "powered Collatz parity actions require the term's exact ledger"
            )
    if term.steps == 0:
        return _matrix_span_with_owner(
            term.seed,
            term.resource_ledger,
            physical_steps,
            parity_actions,
            parity_actions_factory=parity_actions_factory,
            trace_required=trace_required,
            single_macro_scope=single_macro_scope,
        )
    try:
        root = term.true_root_morphism()
    except ValueError:
        return None
    from number_compiler.sequences.collatz.temporal_source_morphism import (
        CertifiedCollatzRootMorphism,
    )

    if (
        type(root) is not CertifiedCollatzRootMorphism
        or root.owner.seed != term.seed
        or root.owner.horizon != term.steps
        or root.start_tick != 0
        or root.ticks != term.steps
        or root.first.value != term.seed
    ):
        raise ValueError("Collatz root occurrence is detached from the requested term")
    return powered_from_endpoint(
        root,
        physical_steps,
        parity_actions=parity_actions,
        parity_actions_factory=parity_actions_factory,
        trace_required=trace_required,
        single_macro_scope=single_macro_scope,
    )


@dataclass(frozen=True, slots=True)
class ComposedBorderCarryMatrix:
    """One source-bound mixed 0/89/142/1472/0563/26847 powered action."""

    joined: GuardedPortJoin
    units: UnitsCarryMatrix

    def __post_init__(self) -> None:
        if self.joined.factor_grammar is None or self.joined.named_macro is not None:
            raise ValueError("composed port requires the issued factor SLP")
        if (
            self.units.steps != self.joined.port.action.steps
            or self.units.odds != self.joined.port.odd_events
        ):
            raise ValueError("composed weighted carry action lost its event clocks")

    def pointed_tens(self, source: int) -> int:
        if not self.joined.source.contains(source):
            raise ValueError("composed weighted carry source is outside its guard")
        endpoint5, tens = self.units.apply(source % 5)
        if endpoint5 != self.joined.port.endpoint(source) % 5:
            raise ArithmeticError(
                "composed digit carry matrix disagrees with affine action"
            )
        return tens

    def puncture(
        self,
        time: int,
        request: PortPuncture | None = None,
        *,
        pointed_source: int | None = None,
        max_rows: int = 200,
        parity_actions: LedgeredParityTapeActions | None = None,
    ) -> GuardedPortCut:
        return self.joined.puncture(
            time,
            request,
            pointed_source=pointed_source,
            max_rows=max_rows,
            parity_cache=parity_actions,
        )


def certify_composed_border_carry_matrix(
    source: int,
    action: DyadicTerminalFieldAction,
    odd_events: int,
    factors: tuple[tuple[tuple[int, ...], int], ...],
    *,
    repetitions: int = 1,
) -> ComposedBorderCarryMatrix:
    """Use an already proved mixed macro SLP, including even 0-runs."""
    joined = certify_pointed_port_join(
        source,
        action,
        odd_events,
        factor_grammar=factors,
        factor_repetitions=repetitions,
    )
    tape = joined.parity_tape_for_action()
    if tape is None:
        raise ArithmeticError("composed source join did not retain its factor grammar")
    units = tape.prefix_units(tape.steps)
    if units.steps != action.steps or units.odds != odd_events:
        raise ValueError("composed carry matrix does not match temporal action")
    result = ComposedBorderCarryMatrix(joined, units)
    result.pointed_tens(source)
    return result


__all__ = [
    "MAX_ENDPOINT_PHYSICAL_STEPS",
    "AdjacentBorderCarryMatrix",
    "ComposedBorderCarryMatrix",
    "NamedBorderCarryMatrix",
    "UnitsCarryMatrix",
    "certify_composed_border_carry_matrix",
    "certify_named_border_carry_matrix",
    "powered_from_endpoint",
    "powered_from_term",
]
