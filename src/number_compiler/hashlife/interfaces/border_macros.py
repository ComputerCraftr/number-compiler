"""Typed metadata for finite, source-anchored border programs.

These records describe catalogue motifs and concrete phases.  They carry no
authority on their own: family owners must validate each cursor against their
already-issued source record before constructing them.  In particular, a
macro identity names a structural word, while ``phase`` and the two cursors
identify one observed use of that word.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum


class BorderFamilyId(Enum):
    """Owner-law families used by the shared border metadata layer."""

    REVERSE_ADD = "reverse-add"
    TWO_REVERSE_TEN = "2rev10"


class BorderMacroKind(Enum):
    """Generic structural shapes; family laws stay in each identity signature."""

    EDGE = "edge"
    CYCLE = "cycle"
    BURST = "burst"
    PATH = "path"


def _is_structural(value: object) -> bool:
    pending = [value]
    while pending:
        item = pending.pop()
        if type(item) in (int, str, bool, type(None)):
            continue
        if type(item) is tuple:
            pending.extend(item)
            continue
        return False
    return True


@dataclass(frozen=True, slots=True)
class BorderMacroIdentity:
    """Structural identity of a border word, with no numeric catalogue id."""

    family: BorderFamilyId
    kind: BorderMacroKind
    signature: tuple[object, ...]

    def __post_init__(self) -> None:
        if type(self.family) is not BorderFamilyId:
            raise TypeError("border macro family must use a typed owner-law identifier")
        if type(self.kind) is not BorderMacroKind:
            raise TypeError("border macro kind must use the closed typed vocabulary")
        if type(self.signature) is not tuple or not self.signature:
            raise ValueError("border macro identity requires a structural signature")
        if any(not _is_structural(value) for value in self.signature):
            raise TypeError(
                "border macro signatures must contain immutable typed values"
            )


@dataclass(frozen=True, slots=True, eq=False)
class BorderSourceCursor:
    """One candidate owner/root coordinate used by a finite border phase.

    ``owner`` and ``root`` are references to existing family-owned state.  The
    cursor does not issue, retain, or extend either one. Family owners must
    validate each coordinate before consuming metadata; cursor equality alone
    is not source authority.
    """

    family: BorderFamilyId
    owner: object = field(repr=False, compare=False)
    root: object = field(repr=False, compare=False)
    physical_tick: int
    pair_depth: int
    clock_phase: int

    def __post_init__(self) -> None:
        if type(self.family) is not BorderFamilyId:
            raise TypeError(
                "border cursor family must use a typed owner-law identifier"
            )
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
    source_state: tuple[object, ...]
    target_state: tuple[object, ...]
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
            or any(not _is_structural(value) for value in self.source_state)
            or any(not _is_structural(value) for value in self.target_state)
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
    "BorderFamilyId",
    "BorderMacroIdentity",
    "BorderMacroKind",
    "BorderMacroPhase",
    "BorderSourceCursor",
    "require_exact_border_join",
]
