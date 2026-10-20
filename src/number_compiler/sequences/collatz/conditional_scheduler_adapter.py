"""Fail-closed production bridge from guarded conditional returns to run actions.

Only a complete, producer-issued parity-cylinder action can enter the run
scheduler. Future Moore classes and Walsh/radial observations are never branch
authority. More demanding publishers retain their existing scheduler route.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.conditional_scheduler_admission import (
    find_bounded_conditional_driver,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceClosedPortAction,
    SourceCongruence,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    project_dyadic_fields_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
        GuardedDecimalPairTransfer,
        UpperNumeratorF5Matrix,
    )
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        GuardedTemporalCarryCounts,
    )
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointTemporalBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

_MIN_TICKS = 256
_MIN_SOURCE_BITS = 256
_MAX_COEFFICIENT_BITS = 8192
_MAX_CONDITIONAL_TAIL = 12
_CANDIDATE_MEMO_ISSUER = object()


def _conditional_motif_scratch_bits(
    source_bits: int, precision: int, coefficient_bits: int
) -> int:
    """Bound the fixed four-motif probe and one powered affine action.

    The production path tests only motif lengths 1, 2, 4 and 8, then powers a
    single source-closed action. It never builds the recursive branch graph.
    Each live arithmetic operand is bounded by the source, cylinder and
    coefficient limits; the fixed workspace factor covers the bounded
    prefix, CRT and binary-composition temporaries.
    """
    return 64 * (source_bits + precision + coefficient_bits + 256)


def _retain_discovery_workspace(
    scratch: RunArithmeticWorkspace,
    reservation: LedgerReservation,
    bits: int,
) -> None:
    """Transfer a successful candidate's live arithmetic bound to run scratch."""
    nodes = 16 + (bits + 63) // 64
    if nodes > scratch.nodes:
        reservation.transfer_to(scratch.owner, nodes=nodes - scratch.nodes)
        scratch.nodes = nodes
    scratch.require_bits(bits)


def _record_discovery_miss(ledger: ResourceLedger) -> None:
    ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_DISCOVERY_MISSES)


@dataclass(frozen=True, slots=True)
class CertifiedSchedulerCandidate:
    """One checked action and exact pointed physical clock.

    A candidate does not confer authority on an unobserved successor word; it
    retains the action's original guarded source class and full affine fields.
    """

    source: int
    endpoint: int
    physical_ticks: int
    normalized_steps: int
    odd_ticks: int
    return_count: int
    port: SourceClosedPortAction
    tail_trace: MacroTraceGrammar | None = None
    numerator_phase: UpperNumeratorF5Matrix | None = None
    pair_transfer: GuardedDecimalPairTransfer | None = None
    joined_port: GuardedPortJoin | None = None
    carry_program: GuardedTemporalCarryCounts | None = None
    upper_sturmian: tuple[int, int, int] | None = None
    _memo_issuer: object = field(init=False, repr=False, compare=False)
    _memo_snapshot: tuple[object, ...] | None = field(
        init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        object.__setattr__(self, "_memo_issuer", None)
        object.__setattr__(self, "_memo_snapshot", None)

    def seal_for_memo(self) -> None:
        """Memo-seal only after every observer has passed full verification."""
        if self._memo_issuer is _CANDIDATE_MEMO_ISSUER:
            self.verify_memo_issued()
            return
        self.verify()
        from number_compiler.sequences.collatz.conditional_candidate_seal import (
            snapshot_scheduler_candidate,
        )

        snapshot = snapshot_scheduler_candidate(self)
        object.__setattr__(self, "_memo_snapshot", snapshot)
        object.__setattr__(self, "_memo_issuer", _CANDIDATE_MEMO_ISSUER)

    def verify_memo_issued(self) -> None:
        from number_compiler.sequences.collatz.conditional_candidate_seal import (
            snapshot_scheduler_candidate,
        )

        try:
            valid = object.__getattribute__(
                self, "_memo_issuer"
            ) is _CANDIDATE_MEMO_ISSUER and object.__getattribute__(
                self, "_memo_snapshot"
            ) == snapshot_scheduler_candidate(self)
        except (AttributeError, TypeError, ValueError):
            valid = False
        if not valid:
            raise ValueError("conditional candidate memo issuance seal is invalid")

    def verify_memo_hit(self, source: int) -> None:
        self.verify_memo_issued()
        self._verify_scheduler_core()
        if type(source) is not int or source != self.source:
            raise ValueError("conditional memo hit does not match its exact source")

    def _verify_scheduler_core(self) -> None:
        if (
            type(self.port) is not SourceClosedPortAction
            or type(self.source) is not int
            or type(self.endpoint) is not int
            or type(self.physical_ticks) is not int
            or type(self.normalized_steps) is not int
            or type(self.odd_ticks) is not int
            or type(self.return_count) is not int
        ):
            raise TypeError("conditional scheduler action has malformed authority")
        self.port.verify_issued()
        if (
            self.source <= 0
            or self.endpoint <= 0
            or self.physical_ticks <= 0
            or self.normalized_steps <= 0
            or self.odd_ticks != 2 * self.return_count
            or self.physical_ticks != self.normalized_steps + self.odd_ticks
            or self.port.odd_events != self.odd_ticks
            or self.port.action.steps != self.normalized_steps
            or not self.port.admits(self.source)
            or self.port.endpoint(self.source) != self.endpoint
        ):
            raise ValueError(
                "conditional scheduler clocks/guards differ from issued source"
            )
        clock = self.port.clock
        if clock is not None:
            clock.verify(self.port.action, self.source, self.endpoint)

    def verification_operand_bits(
        self, control_bits: int, *, source_override: int | None = None
    ) -> int:
        """Bound the authority and guard checks before they run at consumption."""
        if type(self) is not CertifiedSchedulerCandidate:
            raise TypeError("conditional scheduler candidate has an invalid type")
        if (
            type(self.port) is not SourceClosedPortAction
            or type(self.port.action) is not DyadicTerminalFieldAction
            or type(self.port.guard) is not SourceCongruence
            or type(self.port.trace) is not MacroTraceGrammar
        ):
            raise TypeError("conditional scheduler action has malformed authority")
        if self.tail_trace is not None:
            if type(self.tail_trace) is not MacroTraceGrammar:
                raise TypeError("conditional scheduler trace has malformed authority")
            from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
                GuardedDecimalPairTransfer,
                UpperNumeratorF5Matrix,
            )

            if (
                self.pair_transfer is not None
                and type(self.pair_transfer) is not GuardedDecimalPairTransfer
            ):
                raise TypeError(
                    "conditional scheduler pair transfer has malformed authority"
                )
            if (
                self.numerator_phase is not None
                and type(self.numerator_phase) is not UpperNumeratorF5Matrix
            ):
                raise TypeError("conditional scheduler phase has malformed authority")
        elif self.pair_transfer is not None or self.numerator_phase is not None:
            raise TypeError("conditional scheduler matrices lost their trace")
        joined_values: tuple[int, ...] = ()
        if self.joined_port is not None or self.carry_program is not None:
            from number_compiler.sequences.collatz.guarded_port_join import (
                GuardedPortJoin,
            )
            from number_compiler.sequences.collatz.guarded_radix6_bridge import (
                GuardedTemporalCarryCounts,
            )

            if self.joined_port is not None:
                if type(self.joined_port) is not GuardedPortJoin:
                    raise TypeError("conditional joined port has malformed authority")
                source = self.joined_port.source
                target = self.joined_port.bridge.target
                joined_values = (
                    source.lower,
                    source.upper,
                    source.residue,
                    source.modulus,
                    target.lower,
                    target.upper,
                    target.residue,
                    target.modulus,
                    *self.joined_port.bridge.centered_defect_range,
                    *(
                        endpoint
                        for band in (
                            self.joined_port.bridge.source_fives
                            + self.joined_port.bridge.inherited_fives
                            + self.joined_port.bridge.born_fives
                            + self.joined_port.bridge.target_fives
                        )
                        for endpoint in (band.lower, band.upper)
                    ),
                )
            if (
                self.carry_program is not None
                and type(self.carry_program) is not GuardedTemporalCarryCounts
            ):
                raise TypeError("conditional carry program has malformed authority")
        if self.upper_sturmian is not None and (
            type(self.upper_sturmian) is not tuple
            or len(self.upper_sturmian) != 3
            or any(type(value) is not int for value in self.upper_sturmian)
        ):
            raise TypeError("conditional upper phase has malformed authority")
        operand_source = self.source if source_override is None else source_override
        if type(operand_source) is not int or operand_source <= 0:
            raise ValueError("conditional scheduler source bound must be positive")
        values = (
            self.endpoint,
            self.physical_ticks,
            self.normalized_steps,
            self.odd_ticks,
            self.return_count,
            *self.port.action.coefficient_snapshot(),
            self.port.guard.residue,
            self.port.guard.modulus,
            self.port.guard.minimum_source,
            self.port.trace.length,
            len(self.port.trace.letters),
            0 if self.tail_trace is None else self.tail_trace.length,
            0 if self.numerator_phase is None else self.numerator_phase.returns,
            0 if self.numerator_phase is None else self.numerator_phase.scale,
            0 if self.numerator_phase is None else self.numerator_phase.offset,
            *joined_values,
            0 if self.carry_program is None else self.carry_program.guard.residue,
            0 if self.carry_program is None else self.carry_program.guard.modulus,
            0
            if self.carry_program is None
            else self.carry_program.guard.minimum_source,
            0 if self.carry_program is None else self.carry_program.carry_tens,
            0 if self.carry_program is None else self.carry_program.carry_hundreds,
            0
            if self.carry_program is None
            or self.carry_program.matrix_power_period is None
            else self.carry_program.matrix_power_period,
            0
            if self.carry_program is None
            else self.carry_program.forced_six_reset_events,
            0
            if self.carry_program is None
            else self.carry_program.forced_six_div_remainders,
            0 if self.carry_program is None else self.carry_program.port_punctures,
            0 if self.carry_program is None else self.carry_program.matrix_compositions,
            0 if self.carry_program is None else self.carry_program.matrix_squarings,
            0 if self.carry_program is None else self.carry_program.scalar_steps,
            *(self.upper_sturmian if self.upper_sturmian is not None else (0, 0, 0)),
            control_bits,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("conditional scheduler action has malformed integer fields")
        if control_bits < 0:
            raise ValueError("conditional scheduler control bound must be nonnegative")
        clock = self.port.clock
        if clock is not None and type(clock) is not SkewQuadraticClock:
            raise TypeError("conditional scheduler clock has malformed authority")
        if clock is not None:
            values += (
                clock.precision,
                clock.steps,
                clock.odds,
                clock.value,
                clock.linear,
                clock.quadratic,
                clock.position_sum,
                *(
                    value
                    for value in (clock.first_odd, clock.last_odd)
                    if value is not None
                ),
            )
        trace = self.port.trace
        if (
            type(trace.letters) is not tuple
            or type(trace.length) is not int
            or (trace.left is not None and type(trace.left) is not MacroTraceGrammar)
            or (trace.right is not None and type(trace.right) is not MacroTraceGrammar)
        ):
            raise TypeError("conditional scheduler trace has malformed authority")
        source_bits = operand_source.bit_length()
        endpoint_bits = max(
            self.endpoint.bit_length(),
            max(
                source_bits + self.port.action.gain.bit_length(),
                self.port.action.offset.bit_length(),
            )
            + 1,
        )
        return 8 * (
            sum(abs(value).bit_length() for value in values)
            + source_bits
            + endpoint_bits
            + 32
        )

    def verify(self) -> None:
        self._verify_scheduler_core()
        if self._memo_issuer is _CANDIDATE_MEMO_ISSUER:
            self.verify_memo_issued()
            return
        if (
            self.tail_trace is not None
            or self.numerator_phase is not None
            or self.pair_transfer is not None
        ):
            from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
                GuardedDecimalPairTransfer,
                UpperNumeratorF5Matrix,
                upper_numerator_f5,
            )

            if (
                type(self.tail_trace) is not MacroTraceGrammar
                or type(self.pair_transfer) is not GuardedDecimalPairTransfer
                or self.pair_transfer.port is not self.port
                or self.port.trace != self.tail_trace
                or self.tail_trace.length != self.return_count
            ):
                raise ValueError("conditional pair matrix lost its issued trace")
            if self.joined_port is None:
                entry = self.pair_transfer.pointed_entry(self.source)
                if entry.output_pair != self.endpoint % 100:
                    raise ValueError("conditional pair matrix disagrees with endpoint")
            if self.numerator_phase is not None and (
                type(self.numerator_phase) is not UpperNumeratorF5Matrix
                or self.endpoint % 10 != 3
                or self.numerator_phase.returns != self.return_count
                or self.numerator_phase
                != UpperNumeratorF5Matrix.from_trace(self.tail_trace)
                or self.numerator_phase.apply(upper_numerator_f5(self.source))
                != upper_numerator_f5(self.endpoint)
            ):
                raise ValueError("conditional F5 phase disagrees with endpoint")
        if self.joined_port is not None:
            from number_compiler.sequences.collatz.guarded_port_join import (
                GuardedPortJoin,
            )

            joined = self.joined_port
            if (
                type(joined) is not GuardedPortJoin
                or joined.port is not self.port
                or joined.bridge.action.coefficient_snapshot()
                != self.port.action.coefficient_snapshot()
                or joined.bridge.odd_events != self.odd_ticks
                or not joined.source.contains(self.source)
            ):
                raise ValueError("conditional joined ports lost their issued source")
            first, last = joined.require_pointed(self.source)
            if last is None or last.output_pair != self.endpoint % 100:
                raise ArithmeticError("conditional joined matrix lost its endpoint")
            expected = (
                (3 * self.source + 1) // 2 if self.source & 1 else self.source // 2
            ) % 100
            if first.output_pair != expected:
                raise ArithmeticError("conditional joined matrix lost its first inlet")
        if self.carry_program is not None:
            from number_compiler.sequences.collatz.guarded_radix6_bridge import (
                GuardedTemporalCarryCounts,
            )

            program = self.carry_program
            if (
                type(program) is not GuardedTemporalCarryCounts
                or self.joined_port is None
                or program.steps != self.normalized_steps
                or program.odds != self.odd_ticks
                or program.last_pair != self.endpoint % 100
                or not program.guard.admits(self.source)
                or program.guard.modulus % (200 << program.steps) != 0
            ):
                raise ValueError("conditional carry program lost its source guard")
            program.verify_issued()
        if self.upper_sturmian is not None and (
            type(self.upper_sturmian) is not tuple
            or len(self.upper_sturmian) != 3
            or any(type(value) is not int for value in self.upper_sturmian)
            or self.joined_port is None
            or self.tail_trace is None
            or self.upper_sturmian
            != self.joined_port.bridge.demanded_zero_tail_sturmian_factor(
                self.source, self.tail_trace
            )
        ):
            raise ValueError("conditional source-bound upper phase changed")


def issue_conditional_scheduler_candidate(
    source: int,
    remaining: int,
    *,
    scratch: RunArithmeticWorkspace,
    ledger: ResourceLedger,
    max_coefficient_bits: int = _MAX_COEFFICIENT_BITS,
    macros: CollatzDyadicMacros | None = None,
    include_f5: bool = False,
    include_joint: bool = False,
) -> CertifiedSchedulerCandidate | None:
    """Demand a bounded whole-cylinder repeated-motif action on long borders."""
    if (
        type(source) is not int
        or source <= 0
        or type(remaining) is not int
        or remaining < 0
    ):
        raise ValueError(
            "scheduler candidate requires a positive source and natural horizon"
        )
    if (
        type(ledger) is not ResourceLedger
        or type(scratch) is not RunArithmeticWorkspace
    ):
        raise TypeError("conditional discovery requires its query ledger and workspace")
    if scratch.ledger is not ledger or not scratch.active:
        raise ValueError("conditional discovery workspace is not active for this query")
    if macros is not None and getattr(macros, "ledger", None) is not ledger:
        raise ValueError("conditional memo must belong to the query ledger")
    if type(max_coefficient_bits) is not int or max_coefficient_bits < 32:
        raise ValueError("scheduler coefficient budget must be positive")
    if type(include_f5) is not bool or type(include_joint) is not bool:
        raise TypeError("conditional matrix demands must be Boolean")
    if (
        source % 10 != 3
        or source.bit_length() < _MIN_SOURCE_BITS
        or remaining < _MIN_TICKS
    ):
        return None

    driver = find_bounded_conditional_driver(source, remaining, _MAX_CONDITIONAL_TAIL)
    if driver is None:
        ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_FAST_REFUSALS)
        return None
    exponent, hinted_ticks = driver
    if macros is not None and remaining - hinted_ticks > 64:
        return None
    repeats = 1 << exponent
    precision = min(8192, max(128, 8 * repeats), source.bit_length())
    port_demand = int(include_f5) | (int(include_joint) << 1)
    miss_key = (source, remaining, exponent, port_demand, max_coefficient_bits)
    if macros is not None:
        cached = macros.lookup_conditional_port(
            source,
            repeats,
            port_demand,
            max_coefficient_bits,
            remaining.bit_length(),
        )
        if cached is not None:
            if type(cached) is not CertifiedSchedulerCandidate:
                raise ValueError("conditional port memo lost certified type")
            if cached.source == source:
                cached.verify_memo_hit(source)
                if cached.physical_ticks <= remaining:
                    scratch.require_bits(
                        cached.verification_operand_bits(remaining.bit_length())
                    )
                    cached.verify_memo_hit(source)
                    ledger.bump(
                        _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_GUARDED_CACHE_HITS
                    )
                    return cached
            reused = replace(cached, source=source)
            if reused.physical_ticks <= remaining:
                scratch.require_bits(
                    reused.verification_operand_bits(remaining.bit_length())
                )
                reused = replace(reused, endpoint=reused.port.endpoint(source))
                if cached.joined_port is not None:
                    from number_compiler.sequences.collatz.guarded_port_join import (
                        GuardedPortJoin,
                    )
                    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
                        certify_guarded_radix6_bridge,
                    )

                    # Re-certify only the translated point under the cached
                    # affine guard. Do not replay discovery or the SLP trace.
                    singleton = CollatzTwoSidedCylinder(source, source, 0, 1)
                    bridge = certify_guarded_radix6_bridge(
                        singleton,
                        cached.port.action,
                        cached.odd_ticks,
                        max_upper_digits=0,
                        max_lower_digits=0,
                        ledger=ledger,
                    )
                    rebuilt_join = GuardedPortJoin(singleton, cached.port, bridge)
                    carried = (
                        rebuilt_join.authenticate_weighted_ports(source)
                        if cached.carry_program is not None
                        else None
                    )
                    upper = (
                        bridge.demanded_zero_tail_sturmian_factor(
                            source, cached.tail_trace
                        )
                        if cached.upper_sturmian is not None
                        and cached.tail_trace is not None
                        else None
                    )
                    reused = replace(
                        reused,
                        joined_port=rebuilt_join,
                        carry_program=carried,
                        upper_sturmian=upper,
                    )
                reused.verify()
                ledger.bump(
                    _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_GUARDED_CACHE_HITS
                )
                return reused
        if macros.was_conditional_miss(miss_key):
            ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_NEGATIVE_CACHE_HITS)
            return None
    ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_DISCOVERY_ATTEMPTS)
    workspace_owner = ledger.register(
        "collatz-conditional-discovery", "conditional_scheduler_workspace"
    )
    workspace_bits = _conditional_motif_scratch_bits(
        source.bit_length(), precision, max_coefficient_bits
    )
    try:
        # Discovery is a bounded four-motif probe, not recursive graph
        # compilation. A selected action transfers its reservation into the
        # run workspace; misses release all temporary credit.
        reservation = LedgerReservation(ledger, workspace_owner)
        with reservation:
            reservation.reserve(nodes=16 + (workspace_bits + 63) // 64)
            from number_compiler.sequences.collatz.conditional_border_moore import (
                try_compile_conditional_repeated_motif,
            )

            cylinder = CollatzTwoSidedCylinder.from_pointed_source(
                source,
                binary_bits=precision,
                five_places=1,
                leading_bits=min(12, source.bit_length()),
                ledger=ledger,
            )
            if cylinder.forced_residue(10) != 3:
                _record_discovery_miss(ledger)
                if macros is not None:
                    macros.remember_conditional_miss(miss_key)
                return None
            relation = try_compile_conditional_repeated_motif(
                cylinder,
                exponent,
                max_tail=_MAX_CONDITIONAL_TAIL,
                max_coefficient_bits=max_coefficient_bits,
                ledger=ledger,
            )
            if relation is None:
                _record_discovery_miss(ledger)
                if macros is not None:
                    macros.remember_conditional_miss(miss_key)
                return None
            selected = relation.select(source)
            if selected.port is None or selected.target is None:
                _record_discovery_miss(ledger)
                if macros is not None:
                    macros.remember_conditional_miss(miss_key)
                return None
            raw_port = selected.port
            # Preserve the decimal pair at every normalized prefix. A
            # temporal joint observer also needs the upper parity bit, so it
            # requests the complete 200-state inlet modulo 200*2**d.
            guard_modulus = (
                200 << raw_port.action.steps
                if include_joint
                else 5 << (raw_port.action.steps + 1)
            )
            guard_cost = raw_port.action.steps + (8 if include_joint else 4)
            if guard_cost > max_coefficient_bits:
                raise BlockContextBudgetExceeded(
                    "decimal border guard exceeds the coefficient budget"
                )
            border_guard = raw_port.guard.meet(
                SourceCongruence(source % guard_modulus, guard_modulus)
            )
            if border_guard is None or not border_guard.admits(source):
                raise ArithmeticError("source-certified decimal guard lost its root")
            port = SourceClosedPortAction(
                raw_port.action,
                border_guard,
                raw_port.odd_events,
                raw_port.clock,
                selected.tails,
            )
            if (
                selected.physical_ticks > remaining
                or selected.physical_ticks != hinted_ticks
                or selected.tails.length != repeats
                or not selected.inlet.contains(source)
                or not selected.target.contains(port.endpoint(source))
            ):
                _record_discovery_miss(ledger)
                if macros is not None:
                    macros.remember_conditional_miss(miss_key)
                return None
            tail_trace: MacroTraceGrammar | None = None
            numerator_phase = None
            pair_transfer = None
            joined: GuardedPortJoin | None = None
            carry_program = None
            upper_sturmian = None
            if include_f5 or include_joint:
                from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
                    GuardedDecimalPairTransfer,
                    UpperNumeratorF5Matrix,
                )
                from number_compiler.sequences.collatz.guarded_port_join import (
                    GuardedPortJoin,
                )
                from number_compiler.sequences.collatz.guarded_radix6_bridge import (
                    certify_return_trace_radix6_bridge,
                )

                tail_trace = selected.tails
                pair_transfer = GuardedDecimalPairTransfer(port)
                if source % 10 == 3 and port.endpoint(source) % 10 == 3:
                    numerator_phase = UpperNumeratorF5Matrix.from_trace(tail_trace)
                witnessed = selected.inlet.intersect_congruence(
                    port.guard.residue, port.guard.modulus
                )
                if witnessed is None:
                    raise ArithmeticError("joined radix-6 guard has no source fiber")
                if witnessed.first < port.guard.minimum_source:
                    witnessed = witnessed.intersect_interval(
                        port.guard.minimum_source, witnessed.upper
                    )
                if witnessed is None or not witnessed.contains(source):
                    raise ArithmeticError(
                        "joined source cylinder lost its pointed root"
                    )
                bridge = certify_return_trace_radix6_bridge(
                    witnessed, selected.tails, port.action, ledger=ledger
                )
                joined = GuardedPortJoin(witnessed, port, bridge)
                if include_joint:
                    try:
                        carry_program = joined.authenticate_weighted_ports(source)
                    except BlockContextBudgetExceeded:
                        # Other authenticated ports stay available when a
                        # mixed, nonperiodic inlet has no bounded count proof.
                        carry_program = None
                if include_f5:
                    upper_sturmian = bridge.demanded_zero_tail_sturmian_factor(
                        source, selected.tails
                    )
            candidate = CertifiedSchedulerCandidate(
                source,
                port.endpoint(source),
                selected.physical_ticks,
                port.action.steps,
                port.odd_events,
                repeats,
                port,
                tail_trace,
                numerator_phase,
                pair_transfer,
                joined,
                carry_program,
                upper_sturmian,
            )
            candidate.verify()
            # The candidate survives this scope until the caller either
            # consumes it or the query ends. Move the charge into the existing
            # run workspace before releasing any unneeded temporary credit.
            _retain_discovery_workspace(
                scratch,
                reservation,
                candidate.verification_operand_bits(remaining.bit_length()),
            )
            if macros is not None:
                macros.remember_conditional_port(
                    candidate, port_demand, max_coefficient_bits
                )
            return candidate
    except (BlockContextBudgetExceeded, OverflowError):
        ledger.bump(
            _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_DISCOVERY_BUDGET_REFUSALS
        )
        return None


def consume_conditional_scheduler_candidate(
    state: MixedRunExecutorState,
    candidate: CertifiedSchedulerCandidate,
    *,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    ledger: ResourceLedger,
    macros: CollatzDyadicMacros | None = None,
) -> MixedRunExecutorState:
    """Commit a validated action to the existing clocks/F5/joint publishers.

    Resource preflight and guard verification precede mutations. Width extrema,
    intermediate root checkpoints and parity publication must opt out upstream.
    """
    if state.current != candidate.source or state.remaining < candidate.physical_ticks:
        raise ValueError("conditional scheduler candidate is stale or exceeds horizon")
    scratch.require_bits(candidate.verification_operand_bits(control_bits))
    candidate.verify()
    if candidate.pair_transfer is not None:
        ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_POWER_PAIR_MATRIX_CHECKS)
        if candidate.numerator_phase is not None:
            ledger.bump(_collatz_keys.COLLATZ_LOW_BORDER_NUMERATOR_PHASE_CHECKS)
    fields = candidate.port.action
    scratch.require_bits(
        8
        * (
            candidate.source.bit_length()
            + candidate.endpoint.bit_length()
            + fields.gain.bit_length()
            + fields.offset.bit_length()
            + fields.sum_gain.bit_length()
            + 4 * control_bits
            + 32
        )
    )
    if include_joint:
        joint_builder.require_steps(candidate.source, fields.steps)

    next_normalized_f5 = state.normalized_f5
    next_physical_f5 = state.physical_f5
    if next_normalized_f5 is not None and next_physical_f5 is not None:
        f5 = project_dyadic_fields_f5(fields)
        next_normalized_f5 = next_normalized_f5.then(f5)
        next_physical_f5 = next_physical_f5.then(f5)
        if f5.apply(state.current) != candidate.endpoint % 5:
            raise ArithmeticError(
                "conditional scheduler F5 action disagrees with endpoint"
            )

    # The shared endpoint parent is optional, just as in the established
    # unified-skew publisher. Never retain an unmatched intermediate frontier.
    paired_parent_ready = False
    if macros is not None:
        macros.frontier.clear()
        if fields.steps >= 16 and fields.steps & (fields.steps - 1) == 0:
            try:
                macros.remember(
                    state.current,
                    fields.steps,
                    candidate.odd_ticks,
                    candidate.endpoint,
                )
                paired_parent_ready = True
            except BlockContextBudgetExceeded:
                ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_CACHE_BYPASSES)
    if include_joint:
        joint_builder.append(
            fields,
            state.current,
            candidate.odd_ticks,
            candidate.endpoint,
            cache=paired_parent_ready,
        )
    ledger.bump(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_CERTIFIED_ACTIONS)
    ledger.bump(
        _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_POWERED_RETURNS,
        candidate.return_count,
    )
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        state.current.bit_length()
        + fields.gain.bit_length()
        + fields.sum_gain.bit_length(),
    )
    ledger.bump(
        _collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_PHYSICAL_TICKS,
        candidate.physical_ticks,
    )
    return MixedRunExecutorState(
        candidate.endpoint,
        state.remaining - candidate.physical_ticks,
        state.normalized + candidate.normalized_steps,
        state.division_ticks + candidate.normalized_steps,
        state.odd_ticks + candidate.odd_ticks,
        state.one_symbols + candidate.odd_ticks,
        state.zero_symbols + candidate.normalized_steps - candidate.odd_ticks,
        state.run_actions + 1,
        next_normalized_f5,
        next_physical_f5,
    )


def try_consume_conditional_scheduler_candidate(
    state: MixedRunExecutorState,
    *,
    eligible: bool = True,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    ledger: ResourceLedger,
    macros: CollatzDyadicMacros | None = None,
) -> MixedRunExecutorState | None:
    """Select and consume one exact candidate, leaving fallback to the caller."""
    if type(eligible) is not bool:
        raise TypeError("conditional fallback eligibility must be boolean")
    if not eligible:
        return None
    candidate = issue_conditional_scheduler_candidate(
        state.current,
        state.remaining,
        scratch=scratch,
        ledger=ledger,
        macros=macros,
        include_f5=state.normalized_f5 is not None,
        include_joint=include_joint,
    )
    if candidate is None:
        return None
    try:
        return consume_conditional_scheduler_candidate(
            state,
            candidate,
            scratch=scratch,
            control_bits=control_bits,
            include_joint=include_joint,
            joint_builder=joint_builder,
            ledger=ledger,
            macros=macros,
        )
    except BlockContextBudgetExceeded:
        # Preflight failures leave scheduler state and publishers untouched.
        return None


__all__ = (
    "CertifiedSchedulerCandidate",
    "consume_conditional_scheduler_candidate",
    "issue_conditional_scheduler_candidate",
    "try_consume_conditional_scheduler_candidate",
)
