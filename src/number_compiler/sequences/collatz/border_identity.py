"""Typed identities for guarded Collatz border actions.

Cycle identity and entry phase are semantic. Their display labels are derived
metadata and are never parsed back into an action selector.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Final, Protocol, TypeAlias, TypeGuard
from weakref import ReferenceType, ref

from number_compiler.hashlife.interfaces.border_macros import (
    BorderWireValue,
    canonical_cycle_rotation,
    cycle_phase_for_unique_label,
    render_cycle_label,
)

CollatzPortWire: TypeAlias = tuple[str, int, int, bool, int, int, int]
CollatzGuardWire: TypeAlias = tuple[int, int, int] | None

CLOSED_BORDER_CYCLE_TAG: Final[str] = "collatz-closed-border-cycle-v3"
GUARDED_BORDER_PATH_TAG: Final[str] = "collatz-guarded-border-path-v2"
COLLATZ_DIGIT_PORT_TAG: Final[str] = "collatz-digit-port-v1"


@dataclass(frozen=True, slots=True)
class MixedParityMotif:
    """An ordered parity program, distinct from a guarded digit cycle."""

    bits: tuple[int, ...]
    _admitted_bits: tuple[int, ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if (
            type(self.bits) is not tuple
            or not 2 <= len(self.bits) <= 64
            or any(type(bit) is not int or bit not in (0, 1) for bit in self.bits)
            or not 0 < sum(self.bits) < len(self.bits)
        ):
            raise ValueError("mixed boundary motif requires 2..64 Boolean symbols")
        object.__setattr__(self, "_admitted_bits", self.bits)

    def require_valid(self) -> None:
        bits = getattr(self, "bits", None)
        if type(bits) is not tuple or bits is not getattr(self, "_admitted_bits", None):
            raise ValueError("mixed boundary motif changed after admission")


def _guard_matches_snapshot(
    guard: BoundarySelectorGuard | None,
    has_guard: object,
    residue: object,
    modulus: object,
    minimum_source: object,
) -> bool:
    if type(has_guard) is not bool:
        return False
    if not has_guard:
        return (
            guard is None
            and type(residue) is int
            and type(modulus) is int
            and type(minimum_source) is int
            and residue == modulus == minimum_source == 0
        )
    return (
        type(guard) is BoundarySelectorGuard
        and type(residue) is int
        and type(modulus) is int
        and type(minimum_source) is int
        and type(guard.residue) is int
        and type(guard.modulus) is int
        and type(guard.minimum_source) is int
        and guard.residue == residue
        and guard.modulus == modulus
        and guard.minimum_source == minimum_source
    )


@dataclass(frozen=True, slots=True)
class BoundarySelectorGuard:
    """Finite source-residue selector guard attached to an admitted port."""

    residue: int
    modulus: int
    minimum_source: int

    def __post_init__(self) -> None:
        if (
            type(self.residue) is not int
            or type(self.modulus) is not int
            or type(self.minimum_source) is not int
            or self.modulus < 1
            or not 0 <= self.residue < self.modulus
            or self.minimum_source < 1
        ):
            raise ValueError("invalid finite boundary selector guard")

    def matches_residue(self, residue: int) -> bool:
        return type(residue) is int and residue % self.modulus == self.residue

    def admits_source(self, source: int) -> bool:
        return (
            type(source) is int
            and source >= self.minimum_source
            and self.matches_residue(source)
        )

    def wire_value(self) -> tuple[int, int, int]:
        return (self.residue, self.modulus, self.minimum_source)


@dataclass(frozen=True, slots=True)
class CollatzBorderPort:
    """One directed digit edge and its complete source-selection guard."""

    source_digit: int
    target_digit: int
    selector_guard: BoundarySelectorGuard | None = None

    def __post_init__(self) -> None:
        if (
            type(self.source_digit) is not int
            or not 0 <= self.source_digit <= 9
            or type(self.target_digit) is not int
            or not 0 <= self.target_digit <= 9
            or (
                self.selector_guard is not None
                and type(self.selector_guard) is not BoundarySelectorGuard
            )
        ):
            raise ValueError("invalid guarded Collatz border port")
        if self.selector_guard is not None:
            self.selector_guard.__post_init__()

    def wire_value(self) -> CollatzPortWire:
        guard = self.selector_guard
        return (
            COLLATZ_DIGIT_PORT_TAG,
            self.source_digit,
            self.target_digit,
            guard is not None,
            0 if guard is None else guard.residue,
            0 if guard is None else guard.modulus,
            0 if guard is None else guard.minimum_source,
        )


@dataclass(frozen=True, slots=True, eq=False)
class ClosedBorderCycle:
    """Canonical rotation of the full directed, guarded port word."""

    digits: tuple[int, ...]
    selector_guards: tuple[BoundarySelectorGuard | None, ...] = ()
    _ports: tuple[CollatzBorderPort, ...] = field(init=False, repr=False, compare=False)
    _port_wire_values: tuple[CollatzPortWire, ...] = field(
        init=False, repr=False, compare=False
    )
    _selector_guard_wire_values: tuple[CollatzGuardWire, ...] = field(
        init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if (
            type(self.digits) is not tuple
            or len(self.digits) < 2
            or any(
                type(digit) is not int or not 0 <= digit <= 9 for digit in self.digits
            )
        ):
            raise ValueError("border cycle must contain at least two decimal digits")
        if self.selector_guards == ():
            object.__setattr__(self, "selector_guards", (None,) * len(self.digits))
        if (
            type(self.selector_guards) is not tuple
            or len(self.selector_guards) != len(self.digits)
            or any(
                guard is not None and type(guard) is not BoundarySelectorGuard
                for guard in self.selector_guards
            )
        ):
            raise ValueError("cycle ports need one valid guard per source digit")
        ports = tuple(
            CollatzBorderPort(
                self.digits[index],
                self.digits[(index + 1) % len(self.digits)],
                self.selector_guards[index],
            )
            for index in range(len(self.digits))
        )
        object.__setattr__(self, "_ports", ports)
        port_wire_values = tuple(port.wire_value() for port in ports)
        object.__setattr__(self, "_port_wire_values", port_wire_values)
        selector_guard_wire_values = tuple(
            None if guard is None else guard.wire_value()
            for guard in self.selector_guards
        )
        object.__setattr__(
            self, "_selector_guard_wire_values", selector_guard_wire_values
        )
        canonical, _offset = canonical_cycle_rotation(
            ports, guard_key=lambda port: port.wire_value()
        )
        if ports != canonical:
            raise ValueError("border cycle must use its least guarded rotation")

    def __eq__(self, other: object) -> bool:
        if type(other) is not ClosedBorderCycle:
            return False
        self.require_valid()
        other.require_valid()
        return self._port_wire_values == other._port_wire_values

    def __hash__(self) -> int:
        self.require_valid()
        return hash((ClosedBorderCycle, self._port_wire_values))

    def require_valid(self) -> None:
        """Reject a mutated cycle before exposing its ports or using its key."""
        digits = self.digits
        guards = self.selector_guards
        ports = self._ports
        snapshots = self._port_wire_values
        guard_wire_values = self._selector_guard_wire_values
        if (
            type(digits) is not tuple
            or len(digits) < 2
            or any(type(digit) is not int or not 0 <= digit <= 9 for digit in digits)
            or type(guards) is not tuple
            or len(guards) != len(digits)
            or any(
                guard is not None and type(guard) is not BoundarySelectorGuard
                for guard in guards
            )
            or type(ports) is not tuple
            or len(ports) != len(digits)
            or type(snapshots) is not tuple
            or len(snapshots) != len(digits)
            or type(guard_wire_values) is not tuple
            or len(guard_wire_values) != len(digits)
        ):
            raise ValueError("closed border cycle fields changed after admission")
        for index, (port, snapshot) in enumerate(zip(ports, snapshots, strict=True)):
            if (
                type(port) is not CollatzBorderPort
                or type(snapshot) is not tuple
                or len(snapshot) != 7
            ):
                raise ValueError("closed border cycle fields changed after admission")
            tag, source, target, has_guard, residue, modulus, minimum_source = snapshot
            guard_wire = guard_wire_values[index]
            guard_wire_matches = (
                guard_wire is None
                and not has_guard
                or type(guard_wire) is tuple
                and len(guard_wire) == 3
                and all(type(value) is int for value in guard_wire)
                and has_guard
                and guard_wire == (residue, modulus, minimum_source)
            )
            if (
                tag != COLLATZ_DIGIT_PORT_TAG
                or type(source) is not int
                or type(target) is not int
                or type(tag) is not str
                or type(digits[index]) is not int
                or type(digits[(index + 1) % len(digits)]) is not int
                or type(port.source_digit) is not int
                or type(port.target_digit) is not int
                or port.source_digit != source
                or port.target_digit != target
                or digits[index] != source
                or digits[(index + 1) % len(digits)] != target
                or not _guard_matches_snapshot(
                    guards[index], has_guard, residue, modulus, minimum_source
                )
                or not _guard_matches_snapshot(
                    port.selector_guard, has_guard, residue, modulus, minimum_source
                )
                or not guard_wire_matches
            ):
                raise ValueError("closed border cycle changed after admission")

    @property
    def ports(self) -> tuple[CollatzBorderPort, ...]:
        self.require_valid()
        return self._ports

    @classmethod
    def from_rotation(
        cls,
        digits: tuple[int, ...],
        selector_guards: tuple[BoundarySelectorGuard | None, ...] = (),
        *,
        entry_position: int = 0,
    ) -> tuple[ClosedBorderCycle, int]:
        """Return the canonical cycle and input entry's canonical phase."""
        if type(digits) is not tuple or len(digits) < 2:
            raise ValueError("border cycle requires a digit tuple")
        if type(entry_position) is not int or not 0 <= entry_position < len(digits):
            raise ValueError("cycle input entry position is outside the cycle")
        if type(selector_guards) is not tuple:
            raise TypeError("cycle construction requires an immutable guard tuple")
        guards = (None,) * len(digits) if selector_guards == () else selector_guards
        if (
            type(guards) is not tuple
            or len(guards) != len(digits)
            or any(
                guard is not None and type(guard) is not BoundarySelectorGuard
                for guard in guards
            )
        ):
            raise ValueError("cycle construction requires one guard per port")
        ports = tuple(
            CollatzBorderPort(
                digits[index],
                digits[(index + 1) % len(digits)],
                guards[index],
            )
            for index in range(len(digits))
        )
        canonical, offset = canonical_cycle_rotation(
            ports, guard_key=lambda port: port.wire_value()
        )
        cycle = cls(
            tuple(port.source_digit for port in canonical),
            tuple(port.selector_guard for port in canonical),
        )
        return cycle, (entry_position - offset) % len(digits)

    def phase_for_entry(self, entry_digit: int) -> int:
        self.require_valid()
        return cycle_phase_for_unique_label(self.digits, entry_digit)

    def structural_key(self, phase: int) -> BorderWireValue:
        """Encode the complete guarded cycle compactly and retain its phase.

        The cyclic digit tuple determines every directed edge's source and
        target. Keeping those digits once beside each port's optional guard
        avoids repeating edge tags and adjacent digits in bounded source-image
        descriptors while preserving the complete guarded word.
        """
        self.require_valid()
        if type(phase) is not int or not 0 <= phase < len(self.digits):
            raise ValueError("cycle structural key has an invalid entry phase")
        return (
            CLOSED_BORDER_CYCLE_TAG,
            self.digits,
            self._selector_guard_wire_values,
            phase,
        )


@dataclass(frozen=True, slots=True, eq=False)
class CycleEntryPhase:
    """One explicit phase of a closed cycle, optionally source-guarded."""

    cycle: ClosedBorderCycle
    phase: int
    _identity_snapshot: BorderWireValue = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if type(self.cycle) is not ClosedBorderCycle:
            raise TypeError("cycle occurrence requires a canonical closed cycle")
        self.cycle.require_valid()
        if type(self.phase) is not int or not 0 <= self.phase < len(self.cycle.digits):
            raise ValueError("cycle entry phase is outside the cycle")
        object.__setattr__(
            self,
            "_identity_snapshot",
            self.cycle.structural_key(self.phase),
        )

    def __eq__(self, other: object) -> bool:
        if type(other) is not CycleEntryPhase:
            return False
        self.require_valid()
        other.require_valid()
        return self._identity_snapshot == other._identity_snapshot

    def __hash__(self) -> int:
        self.require_valid()
        return hash((CycleEntryPhase, self._identity_snapshot))

    def require_valid(self) -> None:
        """Reject forged field changes before exposing admitted occurrence data."""
        if type(self.cycle) is not ClosedBorderCycle:
            raise ValueError("cycle occurrence fields changed after admission")
        self.cycle.require_valid()
        if type(self.phase) is not int or not 0 <= self.phase < len(self.cycle.digits):
            raise ValueError("cycle occurrence fields changed after admission")
        if self.cycle.structural_key(self.phase) != self._identity_snapshot:
            raise ValueError("cycle occurrence changed after admission")

    @property
    def entry_digit(self) -> int:
        self.require_valid()
        return self.cycle.digits[self.phase]

    @property
    def selector_guard(self) -> BoundarySelectorGuard | None:
        self.require_valid()
        return self.cycle.ports[self.phase].selector_guard

    @property
    def display_label(self) -> str:
        self.require_valid()
        return render_cycle_label(self.cycle.digits, self.phase)

    def observation(self, *, run_parameters: tuple[int, ...] = ()) -> dict[str, object]:
        return {
            "kind": "closed-cycle",
            "cycle": self.cycle.digits,
            "entry_phase": self.phase,
            "entry_digit": self.entry_digit,
            "selector_guard": (
                None
                if self.selector_guard is None
                else self.selector_guard.wire_value()
            ),
            "run_parameters": run_parameters,
            "display_label": self.display_label,
        }

    def structural_key(self) -> BorderWireValue:
        """Encode typed phase without relying on enum or display objects."""
        self.require_valid()
        return self._identity_snapshot


class BoundaryPathKind(Enum):
    """Guarded open or variable-tail border programs."""

    SIX_THREE_ZERO = "six-three-zero"
    THREE_ZERO_FIVE = "three-zero-five"
    THREE_BORDER_RETURN = "three-border-return"


class BorderEntryPort(Enum):
    DIGIT_ZERO = 0
    DIGIT_THREE = 3
    DIGIT_FIVE = 5
    DIGIT_SIX = 6


class BorderExitPort(Enum):
    UNRESOLVED = "unresolved"
    RETURN_TO_THREE = "return_to_3"
    RETURN_AT_HORIZON = "return_at_horizon"
    EIGHT_TO_FOUR = "8_to_4"
    EIGHT_TO_NINE = "8_to_9"
    EIGHT_TO_NINE_TO_EIGHT = "8_to_9_to_8"
    EIGHT_TO_NINE_OPEN = "8_to_9_open"
    EIGHT_TO_NINE_PENDING = "8_to_9_pending"


class NonBorderSegment(Enum):
    ZERO_RUN = "zero_run"
    TERMINAL_POWER_OF_TWO = "terminal"


@dataclass(frozen=True, slots=True)
class GuardedBorderPath:
    """A guarded path with explicit ports; run data stays on its occurrence."""

    kind: BoundaryPathKind
    entry_digit: int
    exit_digit: int | None
    selector_guard: BoundarySelectorGuard | None = None

    def __post_init__(self) -> None:
        if type(self.kind) is not BoundaryPathKind:
            raise TypeError("guarded path requires a declared path kind")
        if type(self.entry_digit) is not int or not 0 <= self.entry_digit <= 9:
            raise ValueError("guarded path entry must be a decimal digit")
        if self.exit_digit is not None and (
            type(self.exit_digit) is not int or not 0 <= self.exit_digit <= 9
        ):
            raise ValueError("guarded path exit must be a decimal digit or absent")
        if (
            self.selector_guard is not None
            and type(self.selector_guard) is not BoundarySelectorGuard
        ):
            raise TypeError("guarded path selector must use its typed source guard")
        if self.selector_guard is not None:
            self.selector_guard.__post_init__()
        if self.kind is BoundaryPathKind.SIX_THREE_ZERO and (
            self.entry_digit != 6 or self.exit_digit != 0
        ):
            raise ValueError("6→3→0 path requires its exact entry and exit digits")
        if self.kind is BoundaryPathKind.THREE_ZERO_FIVE and (
            self.entry_digit != 3 or self.exit_digit != 5
        ):
            raise ValueError("3→0*→5 path requires its exact entry and exit digits")
        if self.kind is BoundaryPathKind.THREE_BORDER_RETURN and (
            self.entry_digit not in (0, 3, 5, 6) or self.exit_digit not in (3, 4, 8, 9)
        ):
            raise ValueError("border-return path has an unsupported entry or exit")

    @property
    def display_label(self) -> str:
        if self.kind is BoundaryPathKind.SIX_THREE_ZERO:
            return "6→3→0"
        if self.kind is BoundaryPathKind.THREE_ZERO_FIVE:
            return "3→0*→5"

        entry_prefix = {
            0: "0*→(3|5→6→3)→",
            3: "3→",
            5: "5→6→3→",
            6: "6→3→",
        }.get(self.entry_digit)
        if entry_prefix is None or self.exit_digit not in (3, 4, 8, 9):
            raise ValueError("border-return path has an unsupported entry or exit")
        exit_suffix = {
            3: "3",
            4: "8→4",
            8: "8",
            9: "8→9",
        }[self.exit_digit]
        return f"{entry_prefix}0*→5→6→{exit_suffix}"

    def observation(self, *, run_parameters: tuple[int, ...] = ()) -> dict[str, object]:
        return {
            "kind": "guarded-path",
            "path_kind": self.kind.value,
            "entry_digit": self.entry_digit,
            "exit_digit": self.exit_digit,
            "selector_guard": (
                None
                if self.selector_guard is None
                else self.selector_guard.wire_value()
            ),
            "run_parameters": run_parameters,
            "display_label": self.display_label,
        }

    def structural_key(self) -> BorderWireValue:
        """Encode guarded path control and ports for immutable image ports."""
        return (
            GUARDED_BORDER_PATH_TAG,
            self.kind.value,
            self.entry_digit,
            self.exit_digit,
            None if self.selector_guard is None else self.selector_guard.wire_value(),
        )


BoundaryActionIdentity: TypeAlias = CycleEntryPhase | GuardedBorderPath
CollatzSegmentIdentity: TypeAlias = BoundaryActionIdentity | NonBorderSegment
BoundaryOccurrence: TypeAlias = tuple[int, int, int, BoundaryActionIdentity]

_BOUNDARY_OCCURRENCE_ISSUER = object()


class _SelectedBoundaryMacro(Protocol):
    """Exact fields shared by the two producer-issued boundary macro types."""

    @property
    def source(self) -> int: ...

    @property
    def physical_ticks(self) -> int: ...

    @property
    def identity(self) -> BoundaryActionIdentity: ...


@dataclass(frozen=True, slots=True, init=False, weakref_slot=True)
class BoundaryOccurrenceProducerStamp:
    """Bind a selected macro to its actual source-relative temporal position."""

    source: int
    horizon: int
    occurrence: BoundaryOccurrence
    macro: object
    _issuer: object
    _snapshot: tuple[object, ...]
    _issued_self: ReferenceType[BoundaryOccurrenceProducerStamp]

    @classmethod
    def _issue(
        cls,
        source: int,
        horizon: int,
        occurrence: BoundaryOccurrence,
        macro: _SelectedBoundaryMacro,
    ) -> BoundaryOccurrenceProducerStamp:
        _require_selected_macro(macro)
        if (
            type(source) is not int
            or source <= 0
            or type(horizon) is not int
            or horizon < 0
            or not is_boundary_occurrence(occurrence)
            or occurrence[0] + occurrence[2] > horizon
        ):
            raise ValueError("cannot stamp a malformed boundary occurrence")
        stamp = object.__new__(cls)
        for name, value in (
            ("source", source),
            ("horizon", horizon),
            ("occurrence", occurrence),
            ("macro", macro),
            ("_issuer", _BOUNDARY_OCCURRENCE_ISSUER),
            ("_snapshot", (source, horizon, occurrence, macro)),
        ):
            object.__setattr__(stamp, name, value)
        object.__setattr__(stamp, "_issued_self", ref(stamp))
        return stamp

    @classmethod
    def from_selected_macro(
        cls,
        source: int,
        horizon: int,
        remaining: int,
        macro: _SelectedBoundaryMacro,
        *,
        boundary_offset: int | None = None,
    ) -> BoundaryOccurrenceProducerStamp:
        """Stamp the actual selected macro source, including reentry seams."""
        if (
            type(horizon) is not int
            or horizon < 0
            or type(remaining) is not int
            or not 0 <= remaining <= horizon
        ):
            raise ValueError("selected boundary run has an invalid horizon")
        _require_selected_macro(macro)
        start_tick = horizon - remaining if boundary_offset is None else boundary_offset
        boundary_source = macro.source
        physical_ticks = macro.physical_ticks
        identity = macro.identity
        if (
            type(start_tick) is not int
            or start_tick < 0
            or type(boundary_source) is not int
            or type(physical_ticks) is not int
            or type(identity) not in (CycleEntryPhase, GuardedBorderPath)
        ):
            raise ValueError("selected boundary macro has malformed occurrence data")
        occurrence = (start_tick, boundary_source, physical_ticks, identity)
        return cls._issue(source, horizon, occurrence, macro)

    def certifies(
        self,
        source: int,
        horizon: int,
        occurrence: BoundaryOccurrence,
        macro: object,
    ) -> bool:
        return (
            self._issuer is _BOUNDARY_OCCURRENCE_ISSUER
            and self._issued_self() is self
            and type(self.source) is int
            and self.source > 0
            and type(self.horizon) is int
            and self.horizon >= 0
            and is_boundary_occurrence(self.occurrence)
            and type(self._snapshot) is tuple
            and len(self._snapshot) == 4
            and type(self._snapshot[0]) is int
            and type(self._snapshot[1]) is int
            and self._snapshot[0] == self.source
            and self._snapshot[1] == self.horizon
            and self._snapshot[2] is self.occurrence
            and self._snapshot[3] is self.macro
            and type(source) is int
            and source == self.source
            and type(horizon) is int
            and horizon == self.horizon
            and is_boundary_occurrence(occurrence)
            and occurrence == self.occurrence
            and macro is self.macro
        )


def _require_selected_macro(macro: object) -> None:
    """Reject structural lookalikes; stamps bind only issued family macros."""
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )

    if type(macro) not in (CollatzBoundaryMacro, BorderReturnMacro):
        raise TypeError("boundary occurrence stamp requires an issued macro")


def _is_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    """Narrow an exact tuple before validating an external occurrence value."""
    return type(value) is tuple


def is_boundary_occurrence(value: object) -> TypeGuard[BoundaryOccurrence]:
    """Validate the typed identity carried by one admitted border occurrence."""
    return (
        _is_object_tuple(value)
        and len(value) == 4
        and type(value[0]) is int
        and value[0] >= 0
        and type(value[1]) is int
        and type(value[2]) is int
        and type(value[3]) in (CycleEntryPhase, GuardedBorderPath)
    )


def _guard(
    residue: int, modulus: int, minimum_source: int = 1
) -> BoundarySelectorGuard:
    return BoundarySelectorGuard(residue, modulus, minimum_source)


CYCLE_421, _CYCLE_421_ENTRY_PHASE = ClosedBorderCycle.from_rotation(
    (4, 2, 1), (_guard(4, 40, 5), None, None)
)
CYCLE_4721, _CYCLE_4721_ENTRY_PHASE = ClosedBorderCycle.from_rotation(
    (4, 7, 2, 1), (_guard(14, 40), None, None, None)
)
CYCLE_0563, _CYCLE_0563_ENTRY_PHASE = ClosedBorderCycle.from_rotation(
    (0, 5, 6, 3), (_guard(30, 40), None, None, None)
)
CYCLE_26847, _ = ClosedBorderCycle.from_rotation(
    (2, 6, 8, 4, 7),
    (
        _guard(112, 160),
        _guard(56, 80),
        _guard(28, 40),
        _guard(34, 40),
        _guard(7, 10),
    ),
)
CYCLE_89, _ = ClosedBorderCycle.from_rotation((8, 9), (None, _guard(9, 10)))

ENTRY_421 = CycleEntryPhase(CYCLE_421, _CYCLE_421_ENTRY_PHASE)
ENTRY_4721 = CycleEntryPhase(CYCLE_4721, _CYCLE_4721_ENTRY_PHASE)
ENTRY_0563 = CycleEntryPhase(CYCLE_0563, _CYCLE_0563_ENTRY_PHASE)
ENTRY_26847_PHASES = tuple(
    CycleEntryPhase(CYCLE_26847, phase) for phase in range(len(CYCLE_26847.digits))
)
ENTRY_89_AT_NINE = CycleEntryPhase(CYCLE_89, CYCLE_89.phase_for_entry(9))

PATH_630 = GuardedBorderPath(BoundaryPathKind.SIX_THREE_ZERO, 6, 0, _guard(6, 20))
PATH_305 = GuardedBorderPath(BoundaryPathKind.THREE_ZERO_FIVE, 3, 5, _guard(3, 10))

BOUNDARY_SELECTOR_IDENTITIES: tuple[BoundaryActionIdentity, ...] = (
    ENTRY_421,
    ENTRY_4721,
    ENTRY_0563,
    *ENTRY_26847_PHASES,
    PATH_630,
    PATH_305,
    ENTRY_89_AT_NINE,
)


def selector_guard_for(
    identity: BoundaryActionIdentity,
) -> BoundarySelectorGuard:
    """Return a declared finite candidate guard, not runtime admission proof."""
    if type(identity) is CycleEntryPhase:
        guard = identity.selector_guard
    elif type(identity) is GuardedBorderPath:
        guard = identity.selector_guard
    else:
        raise TypeError("unsupported Collatz border identity")
    if guard is None:
        raise ValueError("border identity has no finite selector guard")
    return guard


def cycle_phase(
    identity: BoundaryActionIdentity, cycle: ClosedBorderCycle
) -> int | None:
    if type(identity) is not CycleEntryPhase:
        return None
    identity.require_valid()
    cycle.require_valid()
    if identity.cycle == cycle:
        return identity.phase
    return None


def border_return_path(entry_digit: int, exit_digit: int) -> GuardedBorderPath:
    return GuardedBorderPath(
        BoundaryPathKind.THREE_BORDER_RETURN,
        entry_digit,
        exit_digit,
    )


__all__ = [
    "BOUNDARY_SELECTOR_IDENTITIES",
    "CYCLE_0563",
    "CYCLE_89",
    "CYCLE_421",
    "CYCLE_4721",
    "CYCLE_26847",
    "ENTRY_0563",
    "ENTRY_89_AT_NINE",
    "ENTRY_421",
    "ENTRY_4721",
    "ENTRY_26847_PHASES",
    "PATH_305",
    "PATH_630",
    "BorderEntryPort",
    "BorderExitPort",
    "BoundaryActionIdentity",
    "BoundaryOccurrence",
    "BoundaryOccurrenceProducerStamp",
    "BoundaryPathKind",
    "BoundarySelectorGuard",
    "CollatzBorderPort",
    "ClosedBorderCycle",
    "CollatzSegmentIdentity",
    "CycleEntryPhase",
    "GuardedBorderPath",
    "NonBorderSegment",
    "border_return_path",
    "cycle_phase",
    "is_boundary_occurrence",
    "selector_guard_for",
]
