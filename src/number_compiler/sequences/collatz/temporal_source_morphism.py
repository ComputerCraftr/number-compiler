"""Pointed true-successor-root temporal squares for physical Collatz time.

Adapt NC17's 2rev10 root-morphism contract, not its decimal-reversal stencil.
A guarded parity-word certificate may be squared without selecting more leaves;
otherwise the next half is compiled from the *actual intermediate integer*.
The latter is exact, but may still invoke the original D8 fallback.  Neither a
Sturmian multiplier phase nor a Walsh output is used as a branch oracle.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, cast
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.homogeneous_growth import HomogeneousGrowthScale
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointRunAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
)
from number_compiler.sequences.collatz.temporal_f5_observer import CollatzF5AffineAction

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.collatz_two_sided_ring import (
        CollatzTwoSidedCylinder,
    )
    from number_compiler.sequences.collatz.temporal_run_result import (
        CollatzTemporalRunQuotient,
    )

_ISSUER = object()
_MAX_RADIX6_SOURCE_BITS = 8192
_MAX_RADIX6_TRANSPORT_BITS = 16384


@dataclass(frozen=True, slots=True)
class _SourceCertificate:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]
    ledger: ReferenceType[ResourceLedger]


@dataclass(frozen=True, slots=True)
class _MorphismCertificate:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]
    owner: ReferenceType[PointedCollatzSource]
    port_action: SourceClosedPortAction | None


@dataclass(frozen=True, slots=True, init=False, weakref_slot=True)
class PointedCollatzSource:
    """An exact positive source with a user-specified physical horizon."""

    seed: int
    horizon: int
    ledger: ResourceLedger = field(repr=False, compare=False)
    _issuer: _SourceCertificate = field(repr=False, compare=False)

    def __init__(
        self,
        seed: int,
        horizon: int,
        ledger: ResourceLedger,
        *,
        _issuer: object | None = None,
    ) -> None:
        if _issuer is not _ISSUER:
            raise TypeError("pointed source must come from the checked issuer")
        if type(seed) is not int or seed < 1 or type(horizon) is not int or horizon < 0:
            raise ValueError(
                "pointed source needs a positive integer and physical horizon"
            )
        if type(ledger) is not ResourceLedger:
            raise TypeError("pointed source requires a resource ledger")
        object.__setattr__(self, "seed", seed)
        object.__setattr__(self, "horizon", horizon)
        object.__setattr__(self, "ledger", ledger)
        object.__setattr__(
            self,
            "_issuer",
            _SourceCertificate(_ISSUER, ref(self), self._snapshot(), ref(ledger)),
        )

    def _snapshot(self) -> tuple[object, ...]:
        return (
            type(self.seed),
            self.seed,
            type(self.horizon),
            self.horizon,
        )

    def verify_issued(self) -> None:
        certificate = self._issuer
        if (
            type(certificate) is not _SourceCertificate
            or certificate.issuer is not _ISSUER
            or certificate.record() is not self
            or certificate.snapshot != self._snapshot()
            or certificate.ledger() is not self.ledger
        ):
            raise ValueError(
                "pointed Collatz source is not an unchanged factory result"
            )

    @classmethod
    def issue(
        cls, seed: int, horizon: int, *, ledger: ResourceLedger
    ) -> PointedCollatzSource:
        return cls(seed, horizon, ledger, _issuer=_ISSUER)


@dataclass(frozen=True, slots=True)
class CollatzRootFiber:
    """Exact source/target digits, not multiplier-only digit predictions."""

    value: int
    width: int
    high_prefix: int
    residue99: int
    radix_remainders: tuple[tuple[int, int], ...]

    @classmethod
    def of(cls, value: int) -> CollatzRootFiber:
        if type(value) is not int or value <= 0:
            raise ValueError("Collatz root fiber requires a positive integer")
        width = value.bit_length()
        return cls(
            value,
            width,
            value >> max(0, width - 8),
            value % 99,
            tuple((radix, value % (radix**2)) for radix in (3, 6, 10, 64)),
        )

    def digit_at(self, radix: int, position: int) -> int:
        if (
            type(radix) is not int
            or radix < 2
            or type(position) is not int
            or position < 0
        ):
            raise ValueError("invalid demanded radix digit")
        if position and position * (radix.bit_length() - 1) >= self.value.bit_length():
            return 0
        radix_power = cast(int, radix**position)
        return (self.value // radix_power) % radix


def _resolve_true_root(
    owner: PointedCollatzSource,
    start_tick: int,
    known_previous: CertifiedCollatzRootMorphism | None,
) -> int:
    """Authenticate one temporal boundary and return its exact integer root."""
    if type(owner) is not PointedCollatzSource:
        raise TypeError("Collatz root publisher requires a checked pointed owner")
    owner.verify_issued()
    if type(start_tick) is not int or start_tick < 0:
        raise ValueError("physical root start must be a natural tick")
    if known_previous is None:
        if start_tick != 0:
            raise ValueError("noninitial root needs an issued predecessor")
        return owner.seed
    known_previous.validate()
    if (
        known_previous.owner is not owner
        or known_previous.start_tick + known_previous.ticks != start_tick
    ):
        raise ValueError("previous morphism has foreign or nonadjacent lineage")
    return known_previous.last.value


def _physical_f5(action: SourceClosedPortAction) -> CollatzF5AffineAction:
    """Reduce an issued normalized affine map at its *physical* endpoint."""
    action.verify_issued()
    return _physical_f5_fields(action.action)


def _physical_f5_fields(action: DyadicTerminalFieldAction) -> CollatzF5AffineAction:
    if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
        raise ValueError("physical F5 projection requires an issued field action")
    inv = pow(2, -action.steps, 5)
    return CollatzF5AffineAction(
        (action.gain * inv) % 5,
        (action.offset * inv) % 5,
    )


def root_from_admitted_joint_action(
    owner: PointedCollatzSource,
    joint: CollatzJointRunAction,
    *,
    start_tick: int = 0,
    known_previous: CertifiedCollatzRootMorphism | None = None,
) -> CertifiedCollatzRootMorphism:
    """Rehydrate a demanded carrier from the admitted joint-action port."""
    from number_compiler.sequences.collatz.source_closed_port_action import (
        SourceCongruence,
    )

    if type(joint) is not CollatzJointRunAction:
        raise TypeError("true-root carrier requires the admitted joint action")
    source = _resolve_true_root(owner, start_tick, known_previous)
    if (
        joint.source != source
        or joint.physical_ticks <= 0
        or start_tick + joint.physical_ticks > owner.horizon
        or joint.fields.steps != joint.normalized_steps
    ):
        raise ValueError("admitted joint action belongs to another pointed source")
    port_action = None
    if joint.phase == 0:
        port_action = SourceClosedPortAction(
            joint.fields,
            SourceCongruence(
                joint.fields.source_residue,
                joint.fields.source_modulus,
            ),
            joint.odd_symbols,
            None,
        )
    physical_f5 = _physical_f5_fields(joint.fields)
    if joint.phase:
        physical_f5 = CollatzF5AffineAction(
            (3 * physical_f5.scale) % 5,
            (3 * physical_f5.offset + 1) % 5,
        )
    return CertifiedCollatzRootMorphism(
        owner,
        start_tick,
        joint.physical_ticks,
        CollatzRootFiber.of(source),
        CollatzRootFiber.of(joint.endpoint),
        joint.odd_symbols + joint.phase,
        joint.normalized_steps,
        physical_f5,
        port_action,
        1,
        _issuer=_ISSUER,
    )


@dataclass(frozen=True, slots=True, init=False, weakref_slot=True)
class CertifiedCollatzRootMorphism:
    """One or more adjacent true-root source-certified physical blocks.

    A block's ``port_action`` is present only if the entire normalized parity
    program is authenticated under one source guard.  It is never inferred
    from equal homogeneous exponents or projected prime-radix observations.
    """

    owner: PointedCollatzSource
    start_tick: int
    ticks: int
    first: CollatzRootFiber
    last: CollatzRootFiber
    odd_ticks: int
    division_ticks: int
    physical_f5: CollatzF5AffineAction
    port_action: SourceClosedPortAction | None
    run_actions: int
    second_half_selected_from_true_root: bool
    _issuer: _MorphismCertificate = field(repr=False, compare=False)

    def __init__(
        self,
        owner: PointedCollatzSource,
        start_tick: int,
        ticks: int,
        first: CollatzRootFiber,
        last: CollatzRootFiber,
        odd_ticks: int,
        division_ticks: int,
        physical_f5: CollatzF5AffineAction,
        port_action: SourceClosedPortAction | None,
        run_actions: int,
        second_half_selected_from_true_root: bool = False,
        *,
        _issuer: object | None = None,
    ) -> None:
        if _issuer is not _ISSUER:
            raise TypeError("temporal root morphism requires a checked producer")
        for name, value in (
            ("owner", owner),
            ("start_tick", start_tick),
            ("ticks", ticks),
            ("first", first),
            ("last", last),
            ("odd_ticks", odd_ticks),
            ("division_ticks", division_ticks),
            ("physical_f5", physical_f5),
            ("port_action", port_action),
            ("run_actions", run_actions),
            (
                "second_half_selected_from_true_root",
                second_half_selected_from_true_root,
            ),
        ):
            object.__setattr__(self, name, value)
        object.__setattr__(
            self,
            "_issuer",
            _MorphismCertificate(
                _ISSUER, ref(self), self._state(), ref(owner), port_action
            ),
        )
        self.validate()

    def _state(self) -> tuple[object, ...]:
        return (
            self.start_tick,
            self.ticks,
            self.first,
            self.last,
            self.odd_ticks,
            self.division_ticks,
            self.physical_f5,
            self.run_actions,
            self.second_half_selected_from_true_root,
        )

    def validate(self) -> None:
        certificate = self._issuer
        if (
            type(certificate) is not _MorphismCertificate
            or certificate.issuer is not _ISSUER
            or certificate.record() is not self
            or certificate.snapshot != self._state()
            or certificate.owner() is not self.owner
            or certificate.port_action is not self.port_action
        ):
            raise ValueError("pointed Collatz morphism lost issued authority")
        self.owner.verify_issued()
        if (
            any(
                type(v) is not int
                for v in (
                    self.start_tick,
                    self.ticks,
                    self.odd_ticks,
                    self.division_ticks,
                    self.run_actions,
                )
            )
            or self.start_tick < 0
            or self.ticks <= 0
            or self.start_tick + self.ticks > self.owner.horizon
            or min(self.odd_ticks, self.division_ticks, self.run_actions) < 0
            or self.odd_ticks + self.division_ticks != self.ticks
            or self.first != CollatzRootFiber.of(self.first.value)
            or self.last != CollatzRootFiber.of(self.last.value)
            or type(self.physical_f5) is not CollatzF5AffineAction
            or self.physical_f5.apply(self.first.value) != self.last.value % 5
            or type(self.second_half_selected_from_true_root) is not bool
        ):
            raise ValueError(
                "pointed physical Collatz action violates exact clocks or ports"
            )
        if self.port_action is not None:
            self.port_action.verify_issued()
            if (
                self.port_action.action.steps != self.division_ticks
                or self.port_action.odd_events != self.odd_ticks
                or not self.port_action.admits(self.first.value)
                or self.port_action.endpoint(self.first.value) != self.last.value
                or _physical_f5(self.port_action) != self.physical_f5
            ):
                raise ValueError(
                    "source guard disagrees with pointed physical endpoint"
                )

    @property
    def physical_interval(self) -> tuple[int, int]:
        self.validate()
        return (self.start_tick, self.start_tick + self.ticks)

    @property
    def source_scope(self) -> str:
        self.validate()
        return (
            "certified guarded full parity word"
            if self.port_action is not None
            else "pointed exact successor root; future inlet not proved"
        )

    def demanded_outer_inner_ports(
        self,
        *,
        base: int = 10,
        places: int = 8,
        walsh: bool = False,
        block_gap: int | None = None,
        radix_places: dict[int, int] | None = None,
        include_width_coverage: bool = False,
        max_leading_digits: int = 12,
        max_trailing_digits: int = 32,
    ) -> dict[str, object]:
        """Demand actual source/endpoint and optional carry/XOR/Walsh ports.

        Refuse when only the pointed source/target pair is known: a projected
        residue or a homogeneous radial clock is not a parity certificate.
        """
        self.validate()
        if type(include_width_coverage) is not bool:
            raise TypeError("width coverage demand must be Boolean")
        if include_width_coverage and (
            type(max_leading_digits) is not int
            or not 1 <= max_leading_digits <= 256
            or type(max_trailing_digits) is not int
            or not 0 <= max_trailing_digits <= 256
        ):
            raise ValueError("base-6 coverage precision is outside 0..256")
        source_bits: int | None = None
        if include_width_coverage:
            if self.port_action is None:
                raise ValueError("no source-wide parity cylinder for outer/inner ports")
            source_bits = max(1, self.port_action.action.steps)
            if (
                source_bits > _MAX_RADIX6_SOURCE_BITS
                or self.first.value.bit_length() > _MAX_RADIX6_SOURCE_BITS
            ):
                raise BlockContextBudgetExceeded(
                    "base-6 source coverage exceeds the binary cylinder budget"
                )
        if self.port_action is None:
            raise ValueError("no source-wide parity cylinder for outer/inner ports")
        packet = self.port_action.demanded_ports(
            self.first.value,
            base=base,
            places=places,
            walsh=walsh,
            block_gap=block_gap,
            radix_places=radix_places,
            ledger=self.owner.ledger,
        )
        if include_width_coverage:
            from number_compiler.sequences.collatz.collatz_two_sided_ring import (
                CollatzTwoSidedCylinder,
            )

            assert source_bits is not None
            source = self.first.value
            source_cylinder = CollatzTwoSidedCylinder.from_pointed_source(
                source,
                binary_bits=source_bits,
                five_places=1,
                leading_bits=min(12, source.bit_length()),
                ledger=self.owner.ledger,
            )
            guard = self.port_action.guard
            interval_cylinder = source_cylinder.intersect_interval(
                max(source_cylinder.lower, guard.minimum_source),
                source_cylinder.upper,
                ledger=self.owner.ledger,
            )
            if interval_cylinder is None:
                raise ArithmeticError("source guard removed its pointed root")
            crt_cylinder = interval_cylinder.intersect_congruence(
                guard.residue, guard.modulus, ledger=self.owner.ledger
            )
            if crt_cylinder is None:
                raise ArithmeticError("source CRT guard removed its pointed root")
            cylinder = crt_cylinder.admitted_by(
                self.port_action.action, ledger=self.owner.ledger
            )
            if cylinder is None or not cylinder.contains(source):
                raise ArithmeticError("parity cylinder lost the pointed source")
            projected_endpoint_bits = (
                cylinder.upper.bit_length() + self.port_action.action.gain.bit_length()
            )
            if projected_endpoint_bits > _MAX_RADIX6_TRANSPORT_BITS:
                raise BlockContextBudgetExceeded(
                    "base-6 endpoint coverage exceeds its transport bit budget"
                )
            endpoint = cylinder.transport(
                self.port_action.action, ledger=self.owner.ledger
            )
            projected_future_bits = endpoint.upper.bit_length() + 2 * (8 * (128 + 4))
            if projected_future_bits > _MAX_RADIX6_TRANSPORT_BITS:
                raise BlockContextBudgetExceeded(
                    "base-6 future coverage exceeds its transport bit budget"
                )
            future_action, future, tails = endpoint.forced_future(
                max_returns=8, max_tail=128, ledger=self.owner.ledger
            )
            coverage_rows: dict[str, object] = {}
            for name, region in (
                ("source", cylinder),
                ("endpoint", endpoint),
                ("future", future),
            ):
                coverage = region.radix6_coverage(
                    max_leading_digits=max_leading_digits,
                    max_trailing_digits=max_trailing_digits,
                    ledger=self.owner.ledger,
                )
                coverage_rows[name] = (
                    None if coverage is None else coverage.observation()
                )
                width_range = (
                    (coverage.width, coverage.width) if coverage is not None else None
                )
                coverage_rows[name + "_width_range"] = width_range
            packet["radix6_digit_coverage"] = {
                "regions": coverage_rows,
                "future_forced_tails": tails,
                "future_normalized_steps": future_action.steps,
                "scope": "exact finite source cylinder; uncovered positions remain unknown",
            }
        return packet

    def _conditional_source_cylinder(
        self, binary_bits: int, leading_bits: int
    ) -> CollatzTwoSidedCylinder:
        """Admit the shared pointed source for conditional-return observations."""
        self.validate()
        from number_compiler.sequences.collatz.collatz_two_sided_ring import (
            CollatzTwoSidedCylinder,
        )

        if self.last.value % 10 != 3:
            raise ValueError("conditional return request needs a 3-ending true root")
        return CollatzTwoSidedCylinder.from_pointed_source(
            self.last.value,
            binary_bits=binary_bits,
            five_places=1,
            leading_bits=min(leading_bits, self.last.value.bit_length()),
        )

    def demanded_conditional_border_moore(
        self,
        physical_ticks: int,
        *,
        binary_bits: int = 32,
        leading_bits: int = 8,
        max_tail: int = 12,
        max_states: int = 256,
    ) -> dict[str, object]:
        """Demand a future-closed finite 6305 inlet partition from this true root.

        The pointed choice retains its original-source guard; no open branch
        is silently folded into an assumed periodic macro.
        """
        from number_compiler.sequences.collatz.conditional_border_moore import (
            compile_conditional_border_moore,
        )

        cylinder = self._conditional_source_cylinder(binary_bits, leading_bits)
        graph = compile_conditional_border_moore(
            cylinder,
            physical_ticks,
            max_tail=max_tail,
            max_states=max_states,
            max_returns=min(64, max(1, physical_ticks // 4)),
        )
        pointed = graph.select(self.last.value)
        return {
            **graph.observation(),
            "pointed_tails": None if pointed is None else pointed.tails,
            "pointed_source_guard": None
            if pointed is None
            else (pointed.action.guard.residue, pointed.action.guard.modulus),
            "pointed_endpoint": None
            if pointed is None
            else (pointed.action.endpoint(self.last.value)),
            "source_issued": True,
        }

    def demanded_conditional_return_power(
        self,
        exponent: int,
        *,
        binary_bits: int = 64,
        leading_bits: int = 8,
        max_tail: int = 12,
        max_branches: int = 256,
    ) -> dict[str, object]:
        """Binary-square guarded alternative paths for 2**exponent returns.

        Return-count powering is *not* equal physical-time powering when
        alternative tails have different zero-run lengths.
        """
        from number_compiler.sequences.collatz.conditional_border_moore import (
            compile_conditional_return_power,
        )

        cylinder = self._conditional_source_cylinder(binary_bits, leading_bits)
        relation = compile_conditional_return_power(
            cylinder,
            exponent,
            max_tail=max_tail,
            max_branches=max_branches,
        )
        pointed = relation.select(self.last.value)
        return {
            "return_count": relation.return_count,
            "conditional_branches": len(relation.branches),
            "future_output_classes": relation.class_count,
            "source_alternatives_conserved": True,
            "pointed_refusal": pointed.refusal,
            "pointed_tails": None
            if pointed.port is None
            else (pointed.tails.materialize(max_labels=4096)),
            "pointed_physical_ticks": pointed.physical_ticks,
            "pointed_endpoint": None
            if pointed.port is None
            else (pointed.port.endpoint(self.last.value)),
            "source_issued": True,
            "globally_closed": False,
        }

    @property
    def radial_clock(self) -> RadialSturmianClock:
        self.validate()
        return RadialSturmianClock(
            HomogeneousGrowthScale(self.odd_ticks, self.division_ticks)
        )

    def digit_at(self, radix: int, position: int, *, after: bool = True) -> int:
        self.validate()
        if type(after) is not bool:
            raise TypeError("endpoint selection must be Boolean")
        return (self.last if after else self.first).digit_at(radix, position)

    def then(self, later: CertifiedCollatzRootMorphism) -> CertifiedCollatzRootMorphism:
        self.validate()
        later.validate()
        if (
            type(later) is not CertifiedCollatzRootMorphism
            or self.owner is not later.owner
            or self.start_tick + self.ticks != later.start_tick
            or self.last != later.first
        ):
            raise ValueError("physical Collatz morphisms lack true-root adjacency")
        action = None
        if self.port_action is not None and later.port_action is not None:
            action = self.port_action.then(later.port_action, ledger=self.owner.ledger)
            if action is None or not action.admits(self.first.value):
                raise ArithmeticError("certified joint parity guard lost true root")
        return CertifiedCollatzRootMorphism(
            self.owner,
            self.start_tick,
            self.ticks + later.ticks,
            self.first,
            later.last,
            self.odd_ticks + later.odd_ticks,
            self.division_ticks + later.division_ticks,
            self.physical_f5.then(later.physical_f5),
            action,
            self.run_actions + later.run_actions,
            True,
            _issuer=_ISSUER,
        )

    def _guarded_repetition(
        self,
        copies: int,
        *,
        max_coefficient_bits: int,
    ) -> CertifiedCollatzRootMorphism | None:
        """Single binary-powered proof of the whole repeated physical cylinder.

        Do not rebuild each temporal square or digit observer.  In contrast to
        a temporal driver guess, ``power`` intersects every guard preimage.
        """
        if self.port_action is None:
            return None
        try:
            powered = self.port_action.power(
                copies,
                max_coefficient_bits=max_coefficient_bits,
                ledger=self.owner.ledger,
            )
        except (BlockContextBudgetExceeded, OverflowError):
            return None
        if powered is None or not powered.admits(self.first.value):
            return None
        # The true first-half endpoint was independently producer-issued.
        # Check it remains the first exact copy of the proposed repetition.
        if not self.port_action.admits(self.first.value) or (
            self.port_action.endpoint(self.first.value) != self.last.value
        ):
            raise AssertionError(
                "guarded repeated word lost its actual source midpoint"
            )
        return CertifiedCollatzRootMorphism(
            self.owner,
            self.start_tick,
            self.ticks * copies,
            self.first,
            CollatzRootFiber.of(powered.endpoint(self.first.value)),
            self.odd_ticks * copies,
            self.division_ticks * copies,
            _physical_f5(powered),
            powered,
            1,
            True,
            _issuer=_ISSUER,
        )

    def _certified_border_continuation(
        self, *, max_coefficient_bits: int
    ) -> CertifiedCollatzRootMorphism | None:
        """Select a changing 6305 word from the exact current source cylinder."""
        current = self.last.value
        self.owner.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_CHECKS
        )
        self.owner.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_OPERAND_BITS,
            current.bit_length() + (10).bit_length() + self.ticks.bit_length() + 3,
        )
        if current % 10 != 3 or self.ticks < 4:
            self.owner.ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS
            )
            return None
        from number_compiler.sequences.collatz.collatz_two_sided_ring import (
            CollatzTwoSidedCylinder,
        )
        from number_compiler.sequences.collatz.source_closed_port_action import (
            SourceCongruence,
        )

        precision = min(8192, max(128, self.ticks + 32))
        cylinder = CollatzTwoSidedCylinder.from_pointed_source(
            current,
            binary_bits=precision,
            five_places=1,
            leading_bits=min(12, current.bit_length()),
            ledger=self.owner.ledger,
        )
        forced = cylinder.forced_border_word_for_ticks(
            self.ticks,
            max_returns=min(32, self.ticks // 4),
            max_tail=128,
            ledger=self.owner.ledger,
        )
        if forced is None:
            # Preserve all exact competing inlet classes. Do not infer a
            # continuation from a common Walsh or Sturmian output alone.
            # Bound the graph before allocating its source-cylinder branches.
            if self.ticks < 8 or current.bit_length() < 128:
                return None
            from number_compiler.sequences.collatz.conditional_border_moore import (
                ConditionalBorderBudgetExceeded,
                compile_conditional_border_moore,
            )

            try:
                conditional = compile_conditional_border_moore(
                    cylinder,
                    self.ticks,
                    max_tail=min(64, max(12, self.ticks // 4 + 4)),
                    max_returns=min(32, self.ticks // 4),
                    max_states=256,
                )
                selected = conditional.select(current)
            except ConditionalBorderBudgetExceeded:
                return None
            if selected is None:
                return None
            port = selected.action
            if port.action.steps * 4 > max_coefficient_bits:
                return None
            if not port.admits(current) or not selected.target.contains(
                port.endpoint(current)
            ):
                raise ArithmeticError("conditional border cone lost its true endpoint")
            return certified_collatz_root_from_port(
                self.owner, port, known_previous=self
            )
        action, target, tails = forced
        if action.steps * 4 > max_coefficient_bits:
            self.owner.ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS
            )
            return None
        guard = SourceCongruence(action.source_residue, action.source_modulus).meet(
            SourceCongruence(current % 5, 5)
        )
        if guard is None or not guard.admits(current):
            raise ArithmeticError("source-selected border word lost its exact guard")
        port = SourceClosedPortAction(action, guard, 2 * len(tails), None)
        if not port.admits(current) or not target.contains(port.endpoint(current)):
            raise ArithmeticError("source-selected border word lost its endpoint")
        return certified_collatz_root_from_port(self.owner, port, known_previous=self)

    def square(
        self, *, max_coefficient_bits: int = 8192
    ) -> CertifiedCollatzRootMorphism:
        """True-root square, with a non-eager guarded fast path where proved."""
        self.validate()
        if self.start_tick + 2 * self.ticks > self.owner.horizon:
            raise ValueError(
                "source-issued physical horizon does not admit this square"
            )
        if type(max_coefficient_bits) is not int or max_coefficient_bits < 1:
            raise ValueError("coefficient budget must be positive")
        proved = self._guarded_repetition(2, max_coefficient_bits=max_coefficient_bits)
        if proved is not None:
            return proved
        second = self._certified_border_continuation(
            max_coefficient_bits=max_coefficient_bits
        )
        if second is None:
            second = _compile_true_root_morphism(
                self.owner,
                self.ticks,
                start_tick=self.start_tick + self.ticks,
                known_previous=self,
            )
        return self.then(second)

    def power_of_two(
        self, exponent: int, *, max_coefficient_bits: int = 8192
    ) -> CertifiedCollatzRootMorphism:
        if type(exponent) is not int or not 0 <= exponent <= 30:
            raise ValueError("physical temporal power exponent is outside 0..30")
        self.validate()
        repetitions = 1 << exponent
        if self.start_tick + repetitions * self.ticks > self.owner.horizon:
            raise ValueError("source-issued physical horizon does not admit this power")
        if exponent == 0:
            return self
        if type(max_coefficient_bits) is not int or max_coefficient_bits < 1:
            raise ValueError("coefficient budget must be positive")
        proved = self._guarded_repetition(
            repetitions, max_coefficient_bits=max_coefficient_bits
        )
        if proved is not None:
            return proved
        # No certified repeated driver: continue with independently issued
        # true-successor roots.  This can still invoke the ordinary D8 route.
        result = self
        for _ in range(exponent):
            result = result.square(max_coefficient_bits=max_coefficient_bits)
        return result


def certified_collatz_root_from_port(
    owner: PointedCollatzSource,
    action: SourceClosedPortAction,
    *,
    known_previous: CertifiedCollatzRootMorphism | None = None,
) -> CertifiedCollatzRootMorphism:
    """Lift a previously producer-issued complete parity word, with its guard."""
    if type(action) is not SourceClosedPortAction:
        raise TypeError("root action requires an issued source-closed parity word")
    action.verify_issued()
    start_tick = (
        0
        if known_previous is None
        else known_previous.start_tick + known_previous.ticks
    )
    current = _resolve_true_root(owner, start_tick, known_previous)
    if type(current) is not int or current <= 0 or not action.admits(current):
        raise ValueError("true-root source is not admitted by the guarded action")
    ticks = action.action.steps + action.odd_events
    if start_tick + ticks > owner.horizon:
        raise ValueError("guarded action exceeds its pointed physical horizon")
    return CertifiedCollatzRootMorphism(
        owner,
        start_tick,
        ticks,
        CollatzRootFiber.of(current),
        CollatzRootFiber.of(action.endpoint(current)),
        action.odd_events,
        action.action.steps,
        _physical_f5(action),
        action,
        1,
        _issuer=_ISSUER,
    )


def certified_collatz_root_from_border(
    owner: PointedCollatzSource,
    macro: object,
    *,
    known_previous: CertifiedCollatzRootMorphism | None = None,
) -> CertifiedCollatzRootMorphism:
    """Lift an *issued* 6305 border action into true-root temporal squaring.

    The finite guard guarantees its normalized parity program and mod-5
    source class. It is NOT a promise that its named maximal border label
    will recur when the same word is accepted on a different source.
    """
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
        validate_border_return_macro,
    )
    from number_compiler.sequences.collatz.source_closed_port_action import (
        SourceCongruence,
    )

    if type(macro) is not BorderReturnMacro:
        raise TypeError("root border bridge requires an issued return macro")
    validate_border_return_macro(macro)
    start_tick = (
        0
        if known_previous is None
        else known_previous.start_tick + known_previous.ticks
    )
    current = _resolve_true_root(owner, start_tick, known_previous)
    if (
        macro.source != current
        or macro.physical_ticks != macro.fields.steps + macro.odd_symbols
    ):
        raise ValueError(
            "border word is not the actual pointed source/physical program"
        )
    initial_guard = SourceCongruence(
        macro.fields.source_residue, macro.fields.source_modulus
    )
    joined = initial_guard.meet(SourceCongruence(macro.source % 5, 5))
    if joined is None:
        raise ArithmeticError("source border's parity and F5 classes conflict")
    port = SourceClosedPortAction(
        macro.fields,
        joined,
        macro.odd_symbols,
        None,
        trace=(macro.source % 160,),
    )
    issued = certified_collatz_root_from_port(
        owner,
        port,
        known_previous=known_previous,
    )
    if issued.last.value != macro.endpoint:
        raise AssertionError("producer border endpoint is not the true root")
    return issued


def _compile_true_root_morphism(
    owner: PointedCollatzSource,
    ticks: int,
    *,
    start_tick: int = 0,
    known_previous: CertifiedCollatzRootMorphism | None = None,
) -> CertifiedCollatzRootMorphism:
    """Compile the next exact physical block from its authenticated true root.

    The compiler can use its current border rings and D8 fallback; no global
    Collatz driver or arbitrary-seed repeated parity word is presumed.
    """
    initial = _resolve_true_root(owner, start_tick, known_previous)
    if (
        type(ticks) is not int
        or ticks <= 0
        or type(start_tick) is not int
        or start_tick < 0
        or start_tick + ticks > owner.horizon
    ):
        raise ValueError("temporal request exceeds the physical source horizon")
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        compile_collatz_temporal_run_quotient,
    )

    result: CollatzTemporalRunQuotient = compile_collatz_temporal_run_quotient(
        initial,
        ticks,
        ledger=owner.ledger,
        include_f5=True,
    )
    joint_action = result.joint_action
    if joint_action is None:
        raise ValueError("source compiler did not publish a joint run action")
    return root_from_admitted_joint_action(
        owner,
        joint_action,
        start_tick=start_tick,
        known_previous=known_previous,
    )


__all__ = [
    "CertifiedCollatzRootMorphism",
    "CollatzRootFiber",
    "PointedCollatzSource",
    "certified_collatz_root_from_border",
    "certified_collatz_root_from_port",
]
