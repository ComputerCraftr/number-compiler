"""Source-closed composition and powering of admitted Collatz seam actions.

The finite congruence records exact source guards at the original seams. It
can transport those guards through an already issued affine action, but it
does not prove that a named border family's maximal valuation repeats on a
foreign source.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.homogeneous_growth import HomogeneousGrowthScale
from number_compiler.arithmetic.fields.integer_congruence import (
    affine_preimage,
    join_congruences,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.arithmetic.fields.radix import radix_width
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    CycleEntryPhase,
    GuardedBorderPath,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_radix_border import (
    JointRadix6Source,
    candidate_family_guard,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.unified_skew_chain import UnifiedSkewChain
    from number_compiler.sequences.collatz.weighted_right_congruence import (
        CollatzDoubleWeight,
    )

_SOURCE_CLOSED_PORT_ISSUER = object()


def bounded_three_power_matches(exponent: int, target: int) -> bool:
    """Compare 3**exponent to target without allocating beyond target size."""
    if type(exponent) is not int or exponent < 0 or type(target) is not int:
        return False
    if target < 1:
        return False
    if exponent == 0:
        return target == 1
    if exponent >= target.bit_length():
        return False

    result = 1
    base = 3
    remaining = exponent
    while remaining:
        if remaining & 1:
            if result > target // base:
                return False
            result *= base
        remaining >>= 1
        if remaining:
            if base > target // base:
                base = target + 1
            else:
                base *= base
    return result == target


@dataclass(frozen=True, slots=True)
class MacroTraceGrammar:
    """Shared concatenation DAG for the finite seam source residues."""

    letters: tuple[int, ...] = ()
    left: MacroTraceGrammar | None = None
    right: MacroTraceGrammar | None = None
    length: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.letters) is not tuple
            or any(
                type(value) is not int or not 0 <= value < 160 for value in self.letters
            )
            or type(self.length) is not int
            or self.length < 0
        ):
            raise ValueError("invalid compact macro-seam trace")
        if self.left is None and self.right is None:
            if self.length != len(self.letters):
                raise ValueError("trace leaf length is inconsistent")
        elif (
            self.left is None
            or self.right is None
            or self.letters
            or self.length != self.left.length + self.right.length
        ):
            raise ValueError("trace concatenation is malformed")

    @classmethod
    def leaf(cls, source_residues: tuple[int, ...]) -> MacroTraceGrammar:
        return cls(source_residues, None, None, len(source_residues))

    def then(self, other: MacroTraceGrammar) -> MacroTraceGrammar:
        if type(other) is not MacroTraceGrammar:
            raise TypeError("trace composition requires another grammar")
        if not self.length:
            return other
        if not other.length:
            return self
        return MacroTraceGrammar((), self, other, self.length + other.length)

    def materialize(self, *, max_labels: int = 1024) -> tuple[int, ...]:
        if type(max_labels) is not int or max_labels < 0:
            raise ValueError("trace materialization budget must be nonnegative")
        if self.length > max_labels:
            raise BlockContextBudgetExceeded(
                "powered macro trace exceeds its label budget"
            )
        result: list[int] = []
        stack: list[MacroTraceGrammar] = [self]
        while stack:
            node = stack.pop()
            if node.left is None:
                result.extend(node.letters)
            else:
                assert node.right is not None
                stack.append(node.right)
                stack.append(node.left)
        return tuple(result)


def _as_trace_grammar(
    trace: MacroTraceGrammar | tuple[int, ...],
) -> MacroTraceGrammar:
    if type(trace) is MacroTraceGrammar:
        return trace
    if type(trace) is tuple:
        return MacroTraceGrammar.leaf(trace)
    raise TypeError("macro trace lost its concatenation grammar")


@dataclass(frozen=True, slots=True)
class SourceCongruence:
    """One exact source class with a CRT residue and positive lower bound."""

    residue: int = 0
    modulus: int = 1
    minimum_source: int = 1

    def __post_init__(self) -> None:
        if (
            type(self.modulus) is not int
            or self.modulus < 1
            or type(self.residue) is not int
            or not 0 <= self.residue < self.modulus
            or type(self.minimum_source) is not int
            or self.minimum_source < 1
        ):
            raise ValueError("invalid exact source congruence or lower bound")

    def admits(self, source: int) -> bool:
        return (
            type(source) is int
            and source >= self.minimum_source
            and source % self.modulus == self.residue
        )

    def meet(self, other: SourceCongruence) -> SourceCongruence | None:
        if type(other) is not SourceCongruence:
            raise TypeError("source guard intersection needs another congruence")
        joined = join_congruences(
            (self.residue, self.modulus), (other.residue, other.modulus)
        )
        return (
            None
            if joined is None
            else SourceCongruence(
                *joined,
                minimum_source=max(self.minimum_source, other.minimum_source),
            )
        )

    def pullback(self, before: DyadicTerminalFieldAction) -> SourceCongruence | None:
        """Preimage through the full affine map, including its denominator."""
        if type(before) is not DyadicTerminalFieldAction or not before.producer_issued:
            raise TypeError("guard pullback requires a producer-issued action")
        pulled = affine_preimage(
            (self.residue, self.modulus),
            gain=before.gain,
            offset=before.offset,
            denominator=1 << before.steps,
        )
        if pulled is None:
            return None
        if before.gain <= 0:
            raise ValueError("issued source actions must have positive affine gain")
        numerator = self.minimum_source * (1 << before.steps) - before.offset
        minimum_source = max(1, -((-numerator) // before.gain))
        return SourceCongruence(*pulled, minimum_source=minimum_source)


def _join(
    before: SourceCongruence,
    after: SourceCongruence,
    action: DyadicTerminalFieldAction,
) -> SourceCongruence | None:
    pulled = after.pullback(action)
    return None if pulled is None else before.meet(pulled)


def _action_operand_bits(action: SourceClosedPortAction) -> int:
    """Bound arithmetic inputs touched by one exact source-closed join."""
    values = (
        *action.action.coefficient_snapshot(),
        action.guard.residue,
        action.guard.modulus,
        action.guard.minimum_source,
        action.odd_events,
        _as_trace_grammar(action.trace).length,
    )
    bits = sum(abs(value).bit_length() for value in values)
    clock = action.clock
    if clock is not None:
        clock_values = (
            clock.precision,
            clock.steps,
            clock.odds,
            clock.value,
            clock.linear,
            clock.quadratic,
            clock.position_sum,
        )
        bits += sum(abs(value).bit_length() for value in clock_values)
        if clock.first_odd is not None:
            bits += clock.first_odd.bit_length()
        if clock.last_odd is not None:
            bits += clock.last_odd.bit_length()
    return bits


def _charge_composition(
    ledger: ResourceLedger | None,
    before: SourceClosedPortAction,
    after: SourceClosedPortAction,
) -> None:
    if ledger is None:
        return
    from number_compiler.resources.ledger import ResourceLedger

    if type(ledger) is not ResourceLedger:
        raise TypeError("source-closed composition accounting needs a query ledger")
    ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_COMPOSITION_ATTEMPTS)
    ledger.bump(
        _collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_COMPOSITION_OPERAND_BITS,
        _action_operand_bits(before) + _action_operand_bits(after),
    )


@dataclass(frozen=True, slots=True, init=False)
class SourceClosedPortAction:
    """One exact source guard and already issued normalized parity action."""

    action: DyadicTerminalFieldAction
    guard: SourceCongruence
    odd_events: int
    _clock: SkewQuadraticClock | None
    trace: MacroTraceGrammar | tuple[int, ...] = ()
    _issuer: object = field(init=False, repr=False, compare=False)
    _issued_snapshot: tuple[object, ...] = field(init=False, repr=False, compare=False)

    def __init__(
        self,
        action: DyadicTerminalFieldAction,
        guard: SourceCongruence,
        odd_events: int,
        _clock: SkewQuadraticClock | None,
        trace: MacroTraceGrammar | tuple[int, ...] = (),
        *,
        _issuer: object | None = None,
    ) -> None:
        if _issuer is not None and _issuer is not _SOURCE_CLOSED_PORT_ISSUER:
            raise TypeError("invalid source-closed action issuer")
        if _clock is not None and _issuer is not _SOURCE_CLOSED_PORT_ISSUER:
            raise TypeError("quadratic clocks require a checked internal producer")
        object.__setattr__(self, "action", action)
        object.__setattr__(self, "guard", guard)
        object.__setattr__(self, "odd_events", odd_events)
        object.__setattr__(self, "_clock", _clock)
        object.__setattr__(self, "trace", trace)
        self.validate_components()
        object.__setattr__(self, "_issuer", _SOURCE_CLOSED_PORT_ISSUER)
        object.__setattr__(self, "_issued_snapshot", self._snapshot())

    @classmethod
    def create_checked(
        cls,
        action: DyadicTerminalFieldAction,
        guard: SourceCongruence,
        odd_events: int,
        clock: SkewQuadraticClock | None,
        trace: MacroTraceGrammar | tuple[int, ...] = (),
    ) -> SourceClosedPortAction:
        """Issue only records derived from a verified chain or composition."""
        return cls(
            action,
            guard,
            odd_events,
            clock,
            trace,
            _issuer=_SOURCE_CLOSED_PORT_ISSUER,
        )

    def validate_components(self) -> None:
        clock = object.__getattribute__(self, "_clock")
        if (
            type(self.action) is not DyadicTerminalFieldAction
            or not self.action.producer_issued
            or type(self.guard) is not SourceCongruence
            or type(self.odd_events) is not int
            or not 0 <= self.odd_events <= self.action.steps
            or (clock is not None and type(clock) is not SkewQuadraticClock)
            or (
                clock is not None
                and (
                    clock.steps != self.action.steps
                    or clock.odds != self.odd_events
                    or clock.value != self.action.offset % (1 << clock.precision)
                )
            )
            or type(self.trace) not in (tuple, MacroTraceGrammar)
        ):
            raise ValueError("joint port action lost an authenticated component")
        if type(self.trace) is tuple:
            object.__setattr__(self, "trace", MacroTraceGrammar.leaf(self.trace))
        if not bounded_three_power_matches(self.odd_events, self.action.gain):
            raise ValueError("odd event count disagrees with the issued action gain")
        parity_guard = SourceCongruence(
            self.action.source_residue, self.action.source_modulus
        )
        if self.guard.meet(parity_guard) != self.guard:
            raise ValueError("joint guard does not imply the admitted parity cylinder")

    def _snapshot(self) -> tuple[object, ...]:
        action = object.__getattribute__(self, "action")
        guard = object.__getattribute__(self, "guard")
        clock = object.__getattribute__(self, "_clock")
        trace = object.__getattribute__(self, "trace")
        return (
            id(action),
            action.coefficient_snapshot(),
            action.producer_issued,
            id(guard),
            (guard.residue, guard.modulus, guard.minimum_source),
            object.__getattribute__(self, "odd_events"),
            None
            if clock is None
            else (
                id(clock),
                clock.precision,
                clock.steps,
                clock.odds,
                clock.value,
                clock.linear,
                clock.quadratic,
                clock.position_sum,
                clock.first_odd,
                clock.last_odd,
            ),
            (
                id(trace),
                trace.length,
                len(trace.letters),
                None if trace.left is None else id(trace.left),
                None if trace.right is None else id(trace.right),
            ),
        )

    @property
    def producer_issued(self) -> bool:
        try:
            return (
                self._issuer is _SOURCE_CLOSED_PORT_ISSUER
                and self._issued_snapshot == self._snapshot()
                and self.action.producer_issued
            )
        except (AttributeError, TypeError, ValueError):
            return False

    def verify_issued(self) -> None:
        if not self.producer_issued:
            raise ValueError("source-closed action issuance seal is invalid")

    def audit_snapshot(self) -> tuple[object, ...]:
        """Return immutable validated binding facts to audit collaborators."""
        self.verify_issued()
        return self._snapshot()

    @property
    def clock(self) -> SkewQuadraticClock | None:
        self.verify_issued()
        return self._clock

    @property
    def source_trace(self) -> tuple[int, ...]:
        self.verify_issued()
        assert type(self.trace) is MacroTraceGrammar
        return self.trace.materialize()

    @classmethod
    def identity(cls, *, precision: int | None = None) -> SourceClosedPortAction:
        return cls.create_checked(
            DyadicTerminalFieldAction.identity(),
            SourceCongruence(),
            0,
            None if precision is None else SkewQuadraticClock.identity(precision),
        )

    @classmethod
    def from_chain(
        cls, chain: UnifiedSkewChain, *, ledger: ResourceLedger | None = None
    ) -> SourceClosedPortAction:
        from number_compiler.sequences.collatz.unified_skew_chain import (
            UnifiedSkewChain,
        )

        if type(chain) is not UnifiedSkewChain:
            raise TypeError("source-closed port construction requires an issued chain")
        chain.verify()
        guard = SourceCongruence()
        prefix = DyadicTerminalFieldAction.identity()
        trace: list[int] = []
        for seam in chain.seams:
            if seam.action.steps < 1:
                raise ValueError("zero-step source-closed seam is not useful")
            trace.append(seam.source % 160)
            if type(seam.identity) in (CycleEntryPhase, GuardedBorderPath):
                try:
                    family_residue, family_modulus, family_minimum = (
                        candidate_family_guard(seam.identity)
                    )
                except ValueError:
                    # Some typed cycle/path identities are not outputs of the
                    # radix-160 candidate observer. Preserve their exact
                    # source witness instead of inventing a quotient class.
                    family_guard = SourceCongruence(seam.source % 160, 160)
                else:
                    family_guard = SourceCongruence(
                        family_residue, family_modulus, family_minimum
                    )
            else:
                # Non-border actions have no finite candidate label to quotient.
                # Keep their original exact radix-160 source witness.
                family_guard = SourceCongruence(seam.source % 160, 160)
            local = family_guard.meet(
                SourceCongruence(seam.action.source_residue, seam.action.source_modulus)
            )
            if local is None:
                raise AssertionError("issued seam parity and CRT guards conflict")
            joined_guard = _join(guard, local, prefix)
            if joined_guard is None:
                raise AssertionError("issued source-closed seam preimages conflict")
            guard = joined_guard
            prefix = prefix.then(seam.action)
        if prefix != chain.fields or not guard.admits(chain.source):
            raise AssertionError("compiled guard disagrees with its certified chain")
        action = cls.create_checked(
            chain.fields, guard, chain.odd_symbols, chain.clock, tuple(trace)
        )
        if ledger is not None:
            from number_compiler.resources.ledger import ResourceLedger

            if type(ledger) is not ResourceLedger:
                raise TypeError("source-closed guard metrics require a query ledger")
            ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_GUARD_COMPILATIONS)
        return action

    def then(
        self,
        after: SourceClosedPortAction,
        *,
        ledger: ResourceLedger | None = None,
    ) -> SourceClosedPortAction | None:
        if type(after) is not SourceClosedPortAction:
            raise TypeError("joint temporal composition requires another port action")
        self.verify_issued()
        after.verify_issued()
        if (self.clock is None) != (after.clock is None) or (
            self.clock is not None
            and after.clock is not None
            and self.clock.precision != after.clock.precision
        ):
            raise ValueError("quadratic clock precision differs across macros")
        _charge_composition(ledger, self, after)
        joint_guard = _join(self.guard, after.guard, self.action)
        if joint_guard is None:
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_COMPOSITION_REFUSALS
                )
            return None
        joint_action = self.action.then(after.action)
        if type(joint_action) is not DyadicTerminalFieldAction:
            raise AssertionError("issued affine composition lost its action type")
        joined_clock = (
            self.clock.then(after.clock)
            if self.clock is not None and after.clock is not None
            else None
        )
        return SourceClosedPortAction.create_checked(
            joint_action,
            joint_guard,
            self.odd_events + after.odd_events,
            joined_clock,
            _as_trace_grammar(self.trace).then(_as_trace_grammar(after.trace)),
        )

    def power(
        self,
        repetitions: int,
        *,
        max_coefficient_bits: int = 8192,
        ledger: ResourceLedger | None = None,
    ) -> SourceClosedPortAction | None:
        self.verify_issued()
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("power repetitions must be a natural integer")
        if type(max_coefficient_bits) is not int or max_coefficient_bits < 1:
            raise ValueError("powered coefficient budget must be positive")
        if ledger is not None:
            from number_compiler.resources.ledger import ResourceLedger

            if type(ledger) is not ResourceLedger:
                raise TypeError("source-closed power accounting needs a query ledger")

        def refused() -> None:
            if ledger is not None:
                ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_POWER_REFUSALS)

        result = self.identity(precision=self.clock.precision if self.clock else None)
        factor = self
        remaining = repetitions
        while remaining:
            if remaining & 1:
                if (
                    result.action.steps + factor.action.steps
                ) * 4 > max_coefficient_bits:
                    refused()
                    raise BlockContextBudgetExceeded(
                        "joint temporal power exceeds its bit budget"
                    )
                joined = result.then(factor, ledger=ledger)
                if joined is None:
                    refused()
                    return None
                result = joined
            remaining >>= 1
            if remaining:
                if factor.action.steps * 8 > max_coefficient_bits:
                    refused()
                    raise BlockContextBudgetExceeded(
                        "joint temporal square exceeds its bit budget"
                    )
                doubled = factor.then(factor, ledger=ledger)
                if doubled is None:
                    refused()
                    return None
                factor = doubled
        return result

    def admits(self, source: int) -> bool:
        self.verify_issued()
        return self.guard.admits(source) and self.action.certifies(source)

    def endpoint(self, source: int) -> int:
        if not self.admits(source):
            raise ValueError("source is outside the source-closed parity cylinder")
        return self.action.endpoint(source)

    def double_accumulators(self, source: int) -> CollatzDoubleWeight:
        """Demand both exact weighted outputs from this *guarded* action.

        The method does not construct an independent carry/accumulator tape.
        It preserves source-to-class transport: foreign source values are
        refused even when their endpoint arithmetic happens to be integral.
        """
        if not self.admits(source):
            raise ValueError("source lies outside the authenticated carry ports")
        from number_compiler.sequences.collatz.weighted_right_congruence import (
            exact_double_weight,
        )

        return exact_double_weight(self.action, source)

    def demanded_outer_inner_future(
        self,
        source: int,
        *,
        binary_bits: int = 128,
        five_places: int = 1,
        leading_bits: int = 8,
        max_returns: int = 8,
        max_tail: int = 128,
        conditional_tail_horizon: int = 6,
        radix_places: dict[int, int] | None = None,
        walsh64: bool = False,
        include_width_coverage: bool = False,
    ) -> dict[str, object]:
        """Bind the outer interval, inner CRT cone and next 6305 driver.

        The *entire* finite cylinder is intersected with the already-issued
        source-closed source guard before transporting the full affine stride.
        Only a next return that is common to every surviving source is
        published. The symbolic radial/helix fields share this very action;
        a leading multiplier prefix is never substituted for endpoint bits.
        This remains an explicit-demand path, not eager macro selection.
        """
        from number_compiler.sequences.collatz.collatz_two_sided_ring import (
            CollatzTwoSidedCylinder,
        )

        if not self.admits(source):
            raise ValueError("outer/inner ring requires an authenticated root source")
        if (
            type(conditional_tail_horizon) is not int
            or not 0 <= conditional_tail_horizon <= 64
        ):
            raise ValueError("conditional border horizon must be in 0..64")
        initial = CollatzTwoSidedCylinder.from_pointed_source(
            source,
            binary_bits=binary_bits,
            five_places=five_places,
            leading_bits=leading_bits,
        )
        # Named-family guards can constrain a source further than the finite
        # parity word. Track that refinement rather than claiming that all
        # original upper/lower alternatives admit a published border family.
        if self.guard.minimum_source > initial.upper:
            raise ValueError("source-closed lower source bound excludes the interval")
        restricted = CollatzTwoSidedCylinder(
            max(initial.lower, self.guard.minimum_source),
            initial.upper,
            initial.residue,
            initial.modulus,
        )
        guarded = restricted.intersect_congruence(
            self.guard.residue, self.guard.modulus
        )
        if guarded is None or not guarded.contains(source):
            raise ArithmeticError("source-closed guard excludes its original witness")
        restricted = guarded
        parity_admitted = restricted.admitted_by(self.action)
        if parity_admitted is None or parity_admitted.count != restricted.count:
            raise ArithmeticError("certified parity word is not forced by its guard")
        endpoint = parity_admitted.transport(self.action)
        if not endpoint.contains(self.action.endpoint(source)):
            raise AssertionError("two-sided action lost its authenticated endpoint")
        suffix, future, tails = endpoint.forced_future(
            max_returns=max_returns, max_tail=max_tail
        )
        if not future.contains(suffix.endpoint(self.action.endpoint(source))):
            raise AssertionError("forced future lost its exact Collatz source")
        requested_ports = None
        if radix_places is not None or walsh64:
            requested = radix_places if radix_places is not None else {64: 64}
            requested_ports = self.demanded_ports(
                source,
                base=64 if walsh64 else next(iter(requested)),
                places=64 if walsh64 else next(iter(requested.values())),
                radix_places=requested,
                walsh=walsh64,
            )
            if requested_ports["endpoint"] != self.action.endpoint(source):
                raise AssertionError("joint carry ports lost their affine source")
        conditional_inlets = (
            future.conditional_next_tails(max_tail=conditional_tail_horizon)
            if conditional_tail_horizon and future.forced_residue(10) == 3
            else ()
        )
        if type(include_width_coverage) is not bool:
            raise TypeError("width coverage request must be Boolean")
        coverage_packet: dict[str, object] | None = None
        if include_width_coverage:
            width_coverage: dict[str, object] = {}
            for name, ring in (
                ("source", restricted),
                ("endpoint", endpoint),
                ("future", future),
            ):
                coverage = ring.radix6_coverage(
                    max_leading_digits=leading_bits,
                    max_trailing_digits=min(binary_bits, 256),
                )
                width_coverage[name] = (
                    None if coverage is None else coverage.observation()
                )
                width_coverage[name + "_width_range"] = (
                    radix_width(ring.first, 6),
                    radix_width(ring.last, 6),
                )
            coverage_packet = width_coverage
        packet: dict[str, object] = {
            "conditional_next_tail_branches": tuple(
                (j, child.residue, child.modulus, child.count)
                for j, child in conditional_inlets
            ),
            "conditional_tail_branch_count": sum(
                child.count for _, child in conditional_inlets
            ),
            "source_alternatives": initial.count,
            "guarded_alternatives": restricted.count,
            "guard_restricts_initial_fiber": restricted.count != initial.count,
            "source_ring": restricted.summary(high_bits=min(leading_bits, 8)),
            "endpoint_ring": endpoint.summary(high_bits=min(leading_bits, 8)),
            "future_ring": future.summary(high_bits=min(leading_bits, 8)),
            "certified_future_three_tails": tails,
            "certified_future_normalized_steps": suffix.steps,
            "certified_future_odd_events": 2 * len(tails),
            "radial_scale": (self.odd_events, self.action.steps),
            "quadratic_clock": None
            if self.clock is None
            else (self.clock.value, self.clock.linear, self.clock.quadratic),
            "demanded_radix_walsh_ports": requested_ports,
            "candidate_authority": (
                "exact source coset and issued parity/finite candidate guard; "
                "not maximal named-family authority"
            ),
            "unforced_inlets_refused": True,
            "scope": "finite source-wide future, not global Collatz Moore closure",
        }
        if include_width_coverage:
            packet["radix6_digit_coverage"] = coverage_packet
        return packet

    def demanded_odd_position_moore(
        self,
        source: int,
        radix: int,
        position: int,
        *,
        max_states: int = 4096,
        include_walsh64: bool = False,
    ) -> dict[str, object]:
        """Minimize one digit observer for this already-issued parity word.

        The complete finite orbit is conditional on reapplying the same
        word. It is not evidence that a future Collatz selector chooses that
        word again.
        """
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            minimize_fixed_word_odd_position,
        )

        if type(include_walsh64) is not bool:
            raise TypeError("position Walsh64 demand must be Boolean")
        if not self.admits(source):
            raise ValueError("position Moore observer requires an admitted source")
        quotient = minimize_fixed_word_odd_position(
            self.action, radix, position, max_states=max_states
        )
        packet = quotient.observation(source)
        if include_walsh64:
            packet["conditional_digit_change_walsh64_mod5"] = (
                quotient.walsh64_future_digit_changes(source)
            )
        return packet

    @property
    def radial_clock(self) -> RadialSturmianClock:
        self.verify_issued()
        return RadialSturmianClock(
            HomogeneousGrowthScale(self.odd_events, self.action.steps)
        )

    def demanded_ports(
        self,
        source: int,
        *,
        base: int,
        places: int,
        walsh: bool = False,
        block_gap: int | None = None,
        radix_places: dict[int, int] | None = None,
        ledger: ResourceLedger | None = None,
    ) -> dict[str, object]:
        endpoint = self.endpoint(source)
        source_state = JointRadix6Source.from_source(source)
        endpoint_state = source_state.after_action(
            self.action, endpoint, self.odd_events
        )
        if ledger is not None:
            from number_compiler.resources.ledger import ResourceLedger

            if type(ledger) is not ResourceLedger:
                raise TypeError("source-closed port metrics require a query ledger")
            ledger.bump(_collatz_keys.COLLATZ_CROSS_FAMILY_PORT_DEMANDS)
        packet: dict[str, object] = {
            "source": source,
            "endpoint": endpoint,
            "steps": self.action.steps,
            "odd_events": self.odd_events,
            "source_f5": source_state.residue5,
            "endpoint_f5": endpoint_state.residue5,
            "source_crt160": source_state.decimal_residue(160),
            "endpoint_crt160": endpoint_state.decimal_residue(160),
            "radix6_source_cells": source_state.low_radix6,
            "radix6_endpoint_cells": endpoint_state.low_radix6,
            "source_guard_modulus": self.guard.modulus,
            "source_guard_residue": self.guard.residue,
            "source_guard_minimum": self.guard.minimum_source,
            "quadratic_clock": None
            if self.clock is None
            else (self.clock.value, self.clock.linear, self.clock.quadratic),
            "radial_scale": (self.odd_events, self.action.steps),
        }
        if self.odd_events:
            if radix_places is None:
                packet["difference_fields"] = endpoint_state.demanded_difference_ports(
                    base, places, walsh=walsh
                )
                if block_gap is not None:
                    packet["dyadic_block_difference"] = (
                        endpoint_state.demanded_power_block(block_gap, base**places)
                    )
            else:
                if type(radix_places) is not dict or not radix_places:
                    raise ValueError("multiradix demand must be a nonempty radix map")
                if any(
                    type(radix) is not int or type(depth) is not int or depth < 1
                    for radix, depth in radix_places.items()
                ):
                    raise ValueError("multiradix demand needs positive integer depths")
                if walsh and radix_places.get(64) != 64:
                    raise ValueError("Walsh64 requires 64 radix-64 boundaries")
                packet["difference_fields"] = {
                    str(radix): endpoint_state.demanded_difference_ports(
                        radix, depth, walsh=walsh and radix == 64
                    )
                    for radix, depth in radix_places.items()
                }
                if block_gap is not None:
                    packet["dyadic_block_difference"] = {
                        str(radix): endpoint_state.demanded_power_block(
                            block_gap, radix**depth
                        )
                        for radix, depth in radix_places.items()
                    }
        elif walsh:
            raise ValueError("Walsh tripling requires a positive odd-event count")
        return packet


__all__ = ["SourceClosedPortAction", "MacroTraceGrammar", "SourceCongruence"]
