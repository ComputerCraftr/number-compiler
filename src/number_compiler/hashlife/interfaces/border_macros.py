"""Typed metadata for finite, source-anchored border programs.

These records describe catalogue motifs and concrete phases.  They carry no
authority on their own: family owners must validate each cursor against their
already-issued source record before constructing them.  In particular, a
macro identity names a structural word, while ``phase`` and the two cursors
identify one observed use of that word.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field, fields, is_dataclass
from enum import Enum
from typing import (
    Protocol,
    TypeAlias,
    TypeGuard,
    TypeVar,
    runtime_checkable,
)

from number_compiler.arithmetic.contracts.family_identity import (
    FamilyId as _FamilyId,
)


def _require_border_family(family: _FamilyId) -> None:
    """Validate metadata ownership; CLI capabilities belong to the registry."""
    if type(family) is not _FamilyId:
        raise TypeError("border family must use a typed owner-law identifier")


class BorderMacroKind(Enum):
    """Generic structural shapes; family laws stay in each identity signature."""

    EDGE = "edge"
    CYCLE = "cycle"
    BURST = "burst"
    PATH = "path"


class BorderTemporalUnit(Enum):
    """Distinct clocks accepted by the shared finite-action seam contract."""

    PHYSICAL_TICKS = "physical-ticks"
    TRACE_SQUARING_STEPS = "trace-squaring-steps"


@dataclass(frozen=True, slots=True)
class BorderTemporalSpan:
    """One verified finite action span, before family-specific composition.

    ``owner`` is the exact already-issued family macro. This record does not
    issue or authenticate it; producers must validate their action first.
    Radix and position identify the pointed residue domain, and ``unit``
    prevents numerically equal offsets from mixing unrelated clocks. The
    already-verified family producer owns coordinate bounds and proves that
    both residues inhabit the resulting radix/position domain; this shared
    record compares the domain without recomputing its modulus.
    """

    family: _FamilyId
    owner: object = field(repr=False, compare=False)
    unit: BorderTemporalUnit
    radix: int
    position: int
    offset: int
    steps: int
    duration_limit: int
    clock_horizon: int
    source_residue: int
    endpoint_residue: int

    def __post_init__(self) -> None:
        _require_border_family(self.family)
        if type(self.unit) is not BorderTemporalUnit:
            raise TypeError("border temporal span requires a typed clock unit")
        if self.owner is None:
            raise ValueError("border temporal span needs its existing macro owner")
        if (
            type(self.radix) is not int
            or self.radix < 2
            or type(self.position) is not int
            or self.position < 0
        ):
            raise ValueError("border temporal radix/position is outside its domain")
        if (
            type(self.offset) is not int
            or self.offset < 0
            or type(self.steps) is not int
            or self.steps < 1
            or type(self.duration_limit) is not int
            or self.duration_limit < 1
            or self.steps > self.duration_limit
            or type(self.clock_horizon) is not int
            or self.clock_horizon < 1
            or self.offset + self.steps > self.clock_horizon
        ):
            raise ValueError("border temporal span exceeds its exact duration bound")
        if (
            type(self.source_residue) is not int
            or self.source_residue < 0
            or type(self.endpoint_residue) is not int
            or self.endpoint_residue < 0
        ):
            raise ValueError(
                "border temporal residues must be exact nonnegative integers"
            )


def require_exact_temporal_port_join(
    earlier: BorderTemporalSpan, later: BorderTemporalSpan
) -> None:
    """Check the shared clock/domain/source seam before a family joins ports.

    The family producer still composes its complete conditional action and
    validates its own carry, puncture and issuer evidence after this check.
    """
    if type(earlier) is not BorderTemporalSpan or type(later) is not BorderTemporalSpan:
        raise TypeError("temporal port join requires typed action spans")
    if (
        earlier.family is not later.family
        or earlier.owner is not later.owner
        or earlier.unit is not later.unit
        or earlier.radix != later.radix
        or earlier.position != later.position
        or earlier.duration_limit != later.duration_limit
        or earlier.clock_horizon != later.clock_horizon
    ):
        raise ValueError("temporal port spans have incompatible owner or domain")
    if earlier.offset + earlier.steps != later.offset:
        raise ValueError("temporal port spans are not chronologically adjacent")
    combined_steps = earlier.steps + later.steps
    if combined_steps > earlier.duration_limit:
        raise ValueError("joined temporal action exceeds its duration limit")
    if later.offset + later.steps > earlier.clock_horizon:
        raise ValueError("joined temporal port span exceeds its duration bound")
    if earlier.endpoint_residue != later.source_residue:
        raise ValueError("temporal port spans have an incompatible endpoint seam")


BorderWireValue: TypeAlias = str | int | bool | None | tuple["BorderWireValue", ...]
"""Immutable value tree used only when a typed identity is serialized."""


@runtime_checkable
class BorderMacroSignature(Protocol):
    """Family-owned named semantic signature for a border action."""

    @property
    def family(self) -> _FamilyId: ...

    def wire_value(self) -> BorderWireValue: ...


_CycleItem = TypeVar("_CycleItem")
_WireOrderToken: TypeAlias = tuple[int, tuple[int, ...]]


def _wire_order_key(value: BorderWireValue) -> tuple[_WireOrderToken, ...]:
    """Return a total, iterative ordering key for mixed immutable wire values."""
    pending: list[object] = [value]
    tokens: list[_WireOrderToken] = []
    while pending:
        item = pending.pop()
        if item is None:
            tokens.append((0, ()))
        elif type(item) is bool:
            tokens.append((1, (int(item),)))
        elif type(item) is int:
            tokens.append((2, (item,)))
        elif type(item) is str:
            tokens.append((3, tuple(ord(character) for character in item)))
        elif _is_object_tuple(item):
            tokens.append((4, (len(item),)))
            pending.extend(reversed(item))
        else:
            raise TypeError("border guard key must use immutable wire values")
    return tuple(tokens)


def canonical_cycle_rotation(
    ports: tuple[_CycleItem, ...],
    *,
    guard_key: Callable[[_CycleItem], BorderWireValue],
) -> tuple[tuple[_CycleItem, ...], int]:
    """Choose the least rotation of complete guarded ports, never reflection.

    The offset is the left rotation that produced the canonical sequence.
    Consumers retain its inverse as occurrence phase. Family port types and
    guards remain in their owner; only ordered canonicalization is shared.
    """
    if type(ports) is not tuple or not ports:
        raise ValueError("a guarded border cycle cannot be empty")
    keys = tuple(_wire_order_key(guard_key(port)) for port in ports)
    offset = min(
        range(len(ports)),
        key=lambda start: keys[start:] + keys[:start],
    )
    return ports[offset:] + ports[:offset], offset


def cycle_phase_for_unique_label(labels: tuple[int, ...], label: int) -> int:
    """Resolve a displayed entry only when it identifies exactly one phase."""
    if (
        type(labels) is not tuple
        or not labels
        or any(type(value) is not int for value in labels)
        or type(label) is not int
    ):
        raise TypeError("cycle labels and entry label must be exact integers")
    matches = tuple(index for index, value in enumerate(labels) if value == label)
    if len(matches) != 1:
        raise ValueError("cycle entry label must identify exactly one phase")
    return matches[0]


def render_cycle_label(labels: tuple[int, ...], phase: int) -> str:
    """Render a cycle occurrence without parsing its display back into an ID."""
    if (
        type(labels) is not tuple
        or not labels
        or any(type(value) is not int or not 0 <= value <= 9 for value in labels)
        or type(phase) is not int
        or not 0 <= phase < len(labels)
    ):
        raise ValueError("invalid decimal cycle display coordinates")
    rotated = labels[phase:] + labels[:phase]
    return "".join(map(str, (*rotated, rotated[0])))


def _is_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    """Narrow an exact runtime tuple at a dynamic value boundary."""
    return type(value) is tuple


def _is_border_macro_signature(value: object) -> TypeGuard[BorderMacroSignature]:
    """Validate a runtime implementation of the typed signature protocol."""
    return isinstance(value, BorderMacroSignature)


def _is_wire_value(value: object) -> bool:
    pending = [value]
    while pending:
        item = pending.pop()
        if type(item) in (int, str, bool, type(None)):
            continue
        if _is_object_tuple(item):
            pending.extend(item)
            continue
        return False
    return True


def _is_immutable_signature_value(value: object) -> bool:
    """Check that a signature is a tree of immutable typed values.

    The wire packet alone is not enough: a mutable object can implement the
    runtime protocol and change its packet after an identity has been interned.
    Family signatures are frozen dataclasses whose fields recursively contain
    frozen records, enums, or immutable tuples. An explicit worklist keeps this
    check within the repository's no-recursion source policy.
    """
    pending: list[tuple[object, bool]] = [(value, False)]
    active: set[int] = set()
    complete: set[int] = set()
    while pending:
        item, leaving = pending.pop()
        identity = id(item)
        if leaving:
            active.remove(identity)
            complete.add(identity)
            continue
        if type(item) in (str, int, bool, type(None)):
            continue
        if identity in active:
            return False
        if identity in complete:
            continue
        if isinstance(item, Enum):
            active.add(identity)
            pending.append((item, True))
            pending.append((item.value, False))
            continue
        if _is_object_tuple(item):
            active.add(identity)
            pending.append((item, True))
            pending.extend((child, False) for child in item)
            continue
        if not is_dataclass(item) or isinstance(item, type):
            return False
        parameters = getattr(type(item), "__dataclass_params__", None)
        if parameters is None or not parameters.frozen:
            return False
        active.add(identity)
        pending.append((item, True))
        pending.extend(
            (getattr(item, descriptor.name), False) for descriptor in fields(item)
        )
    return True


@dataclass(frozen=True, slots=True)
class BorderMacroIdentity:
    """Structural identity of a border word, with no numeric catalogue id."""

    family: _FamilyId
    kind: BorderMacroKind
    signature: BorderMacroSignature = field(compare=False, hash=False)
    _signature_type: type[BorderMacroSignature] = field(init=False, repr=False)
    _signature_wire: BorderWireValue = field(init=False, repr=False)

    def __post_init__(self) -> None:
        _require_border_family(self.family)
        has_type_snapshot = hasattr(self, "_signature_type")
        has_wire_snapshot = hasattr(self, "_signature_wire")
        if has_type_snapshot or has_wire_snapshot:
            if not has_type_snapshot or not has_wire_snapshot:
                raise ValueError(
                    "border macro identity has a partial signature snapshot"
                )
            self.checked_signature()
            return
        if type(self.kind) is not BorderMacroKind:
            raise TypeError("border macro kind must use the closed typed vocabulary")
        if not _is_border_macro_signature(self.signature):
            raise TypeError("border macro identity requires a typed family signature")
        if not _is_immutable_signature_value(self.signature):
            raise TypeError("border macro signature must be an immutable typed record")
        if self.signature.family is not self.family:
            raise ValueError("border macro signature belongs to another family")
        signature_wire = self.signature.wire_value()
        if not _is_wire_value(signature_wire):
            raise TypeError("border macro signature has an invalid immutable packet")
        object.__setattr__(self, "_signature_type", type(self.signature))
        object.__setattr__(self, "_signature_wire", signature_wire)

    def checked_signature(self) -> BorderMacroSignature:
        """Return the typed record only while it still matches its identity."""
        signature = self.signature
        if (
            type(signature) is not self._signature_type
            or not _is_immutable_signature_value(signature)
            or signature.family is not self.family
            or signature.wire_value() != self._signature_wire
        ):
            raise ValueError("border macro signature changed after identity creation")
        return signature

    def packet(self) -> dict[str, object]:
        """Render identity metadata without granting occurrence authority."""
        return {
            "family": self.family.value,
            "kind": self.kind.value,
            "signature": self._signature_wire,
        }


@dataclass(frozen=True, slots=True, eq=False)
class BorderSourceCursor:
    """One candidate owner/root coordinate used by a finite border phase.

    ``owner`` and ``root`` are references to existing family-owned state.  The
    cursor does not issue, retain, or extend either one. Family owners must
    validate each coordinate before consuming metadata; cursor equality alone
    is not source authority.
    """

    family: _FamilyId
    owner: object = field(repr=False, compare=False)
    root: object = field(repr=False, compare=False)
    physical_tick: int
    pair_depth: int
    clock_phase: int

    def __post_init__(self) -> None:
        _require_border_family(self.family)
        if self.owner is None or self.root is None:
            raise ValueError("border cursor needs an existing owner and root")
        if type(self.physical_tick) is not int or self.physical_tick < 0:
            raise ValueError("border cursor tick must be nonnegative")
        if type(self.pair_depth) is not int or self.pair_depth < 1:
            raise ValueError("border cursor depth must be positive")
        if type(self.clock_phase) is not int or self.clock_phase < 0:
            raise ValueError("border cursor clock phase must be nonnegative")

    def same_child(self, other: BorderSourceCursor) -> bool:
        """Whether both cursor coordinates refer to the same candidate root."""
        if type(other) is not BorderSourceCursor:
            return False
        same_root = self.root is other.root
        if type(self.root) in (int, str, bytes) and type(other.root) is type(self.root):
            same_root = self.root == other.root
        return (
            self.family == other.family
            and self.owner is other.owner
            and same_root
            and self.physical_tick == other.physical_tick
            and self.pair_depth == other.pair_depth
            and self.clock_phase == other.clock_phase
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, BorderSourceCursor):
            return False
        return self.same_child(other)

    def __hash__(self) -> int:
        if type(self.root) in (int, str, bytes):
            root_key: object = (type(self.root), self.root)
        else:
            root_key = (type(self.root), id(self.root))
        return hash(
            (
                self.family,
                id(self.owner),
                root_key,
                self.physical_tick,
                self.pair_depth,
                self.clock_phase,
            )
        )


@dataclass(frozen=True, slots=True)
class BorderMacroPhase:
    """A structural macro phase attached to exact adjacent source cursors."""

    identity: BorderMacroIdentity
    phase: int
    source: BorderSourceCursor
    target: BorderSourceCursor
    source_state: tuple[BorderWireValue, ...]
    target_state: tuple[BorderWireValue, ...]
    width_in: int
    width_out: int
    clock_in: tuple[int, ...] = ()
    clock_out: tuple[int, ...] = ()
    physical_span: int = 1

    def __post_init__(self) -> None:
        if type(self.identity) is not BorderMacroIdentity:
            raise TypeError("border phase requires a typed structural identity")
        if type(self.phase) is not int or self.phase < 0:
            raise ValueError("border phase index must be nonnegative")
        if (
            type(self.source) is not BorderSourceCursor
            or type(self.target) is not BorderSourceCursor
        ):
            raise TypeError("border phase requires typed source and target cursors")
        if (
            self.source.family != self.identity.family
            or self.target.family != self.identity.family
            or self.source.owner is not self.target.owner
            or self.source.pair_depth != self.target.pair_depth
            or type(self.physical_span) is not int
            or self.physical_span not in (1, 2)
            or self.target.physical_tick
            != self.source.physical_tick + self.physical_span
        ):
            raise ValueError(
                "border phase cursors do not describe one exact child step"
            )
        if (
            type(self.source_state) is not tuple
            or type(self.target_state) is not tuple
            or any(not _is_wire_value(value) for value in self.source_state)
            or any(not _is_wire_value(value) for value in self.target_state)
        ):
            raise TypeError("border states must be immutable tuples")
        if (
            type(self.width_in) is not int
            or type(self.width_out) is not int
            or self.width_in < 1
            or self.width_out < self.width_in
            or self.width_out - self.width_in > self.physical_span
        ):
            raise ValueError("invalid border width transition")
        if (
            type(self.clock_in) is not tuple
            or type(self.clock_out) is not tuple
            or any(
                type(value) is not int for value in (*self.clock_in, *self.clock_out)
            )
            or len(self.clock_in) != len(self.clock_out)
        ):
            raise ValueError("invalid typed border clock coordinates")


def require_exact_border_join(
    earlier: BorderMacroPhase, later: BorderMacroPhase
) -> None:
    """Require two observed phases to meet at the same completed child root."""
    if type(earlier) is not BorderMacroPhase or type(later) is not BorderMacroPhase:
        raise TypeError("border join requires typed phases")
    if (
        earlier.identity.family != later.identity.family
        or earlier.target.pair_depth != later.source.pair_depth
        or not earlier.target.same_child(later.source)
    ):
        raise ValueError("border phases do not join at the exact completed child")


__all__ = [
    "BorderMacroIdentity",
    "BorderMacroKind",
    "BorderMacroSignature",
    "BorderMacroPhase",
    "BorderTemporalSpan",
    "BorderTemporalUnit",
    "BorderWireValue",
    "BorderSourceCursor",
    "canonical_cycle_rotation",
    "cycle_phase_for_unique_label",
    "render_cycle_label",
    "require_exact_border_join",
    "require_exact_temporal_port_join",
]
