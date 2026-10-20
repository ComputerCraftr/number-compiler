"""Typed source roots and temporal observations for 2rev10 Hashlife."""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle


@dataclass(frozen=True, slots=True)
class DoubleReverseSLPID(ArenaHandle):
    """Typed root handle for one double-reverse SLP arena generation."""

    def __post_init__(self) -> None:
        ArenaHandle.__post_init__(self)
        if self.kind != "double_reverse_slp":
            raise ValueError("invalid double-reverse SLP handle kind")


@dataclass(frozen=True, slots=True)
class DoubleReversePortAction:
    """A powered output grammar and its exact source and boundary seams."""

    source: DoubleReverseSLPID
    target: DoubleReverseSLPID
    steps: int
    phase_in: int
    phase_out: int
    left_births: int
    right_births: int

    def then(self, other: DoubleReversePortAction) -> DoubleReversePortAction:
        """Compose only actions whose exact output root feeds the next input."""
        if type(other) is not DoubleReversePortAction:
            raise TypeError("temporal composition requires a guarded port action")
        if self.target != other.source:
            raise ValueError("temporal action source-root seam mismatch")
        if self.phase_out != other.phase_in:
            raise ValueError("temporal action border-phase seam mismatch")
        return DoubleReversePortAction(
            self.source,
            other.target,
            self.steps + other.steps,
            self.phase_in,
            other.phase_out,
            self.left_births + other.left_births,
            self.right_births + other.right_births,
        )


@dataclass(frozen=True, slots=True)
class IssuedDoubleReversePortAction:
    """One action and its immutable issue-time handle/scalar snapshot."""

    action: DoubleReversePortAction
    binding: tuple[object, ...]


def temporal_action_binding(action: DoubleReversePortAction) -> tuple[object, ...]:
    """Snapshot each nested handle field and scalar at action issuance."""
    if (
        type(action) is not DoubleReversePortAction
        or type(action.source) is not DoubleReverseSLPID
        or type(action.target) is not DoubleReverseSLPID
    ):
        raise ValueError("malformed double-reverse action binding")
    return (
        action.source.owner,
        action.source.kind,
        action.source.local_id,
        action.target.owner,
        action.target.kind,
        action.target.local_id,
        action.steps,
        action.phase_in,
        action.phase_out,
        action.left_births,
        action.right_births,
    )


@dataclass(frozen=True, slots=True)
class PointedDigitStencil:
    """Exact selected digit and local output ports on one source-bound cone."""

    source: DoubleReverseSLPID
    f_steps: int
    phase_in: int
    phase_out: int
    width: int
    msd_index: int
    digit: int
    ltgt: int
    f5: int
    moore_state: int
    prefix_steps: int = 0


@dataclass(frozen=True, slots=True)
class DoubleReverseSourcePrefix:
    """An exact transient cursor; phase=None grants no temporal power."""

    source: DoubleReverseSLPID
    target: DoubleReverseSLPID
    physical_steps: int
    certified_phase: int | None


class UncertifiedPointedStencilError(ValueError):
    """No admitted short prefix reaches the required 2rev10 border law."""


@dataclass(frozen=True, slots=True)
class IssuedDoubleReverseSourcePrefix:
    """Owner-published prefix cursor with a primitive-field mutation seal."""

    entry: DoubleReverseSourcePrefix
    binding: tuple[int | str | None, ...]


def source_prefix_binding(
    entry: DoubleReverseSourcePrefix,
) -> tuple[int | str | None, ...]:
    """Snapshot source and target handle fields without using portable IDs."""
    return (
        id(entry.source.owner),
        entry.source.kind,
        entry.source.local_id,
        id(entry.target.owner),
        entry.target.kind,
        entry.target.local_id,
        entry.physical_steps,
        entry.certified_phase,
    )


def source_prefix_node_cost(key: object, value: object) -> int:
    """Account the single retained transient prefix cursor and its key."""
    if type(key) is not int or key < 0:
        raise ValueError("malformed 2rev10 source-prefix memo key")
    if type(value) is not IssuedDoubleReverseSourcePrefix:
        raise ValueError("malformed 2rev10 source-prefix memo payload")
    entry = value.entry
    if type(entry) is not DoubleReverseSourcePrefix:
        raise ValueError("malformed 2rev10 source-prefix cursor")
    integers: tuple[int, ...] = (
        key,
        entry.source.local_id,
        entry.target.local_id,
        entry.physical_steps,
        0 if entry.certified_phase is None else entry.certified_phase,
        *(component for component in value.binding if type(component) is int),
    )
    if any(type(component) is not int or component < 0 for component in integers):
        raise ValueError("malformed 2rev10 source-prefix coordinates")
    return 8 + sum(max(1, (item.bit_length() + 63) // 64) for item in integers)


def temporal_action_node_cost(key: object, action: object) -> int:
    """Charge exact integer limbs for the retained action and its scoped key."""
    if not is_exact_object_tuple(key) or len(key) != 3:
        raise ValueError("malformed temporal action memo entry")
    coordinates = key
    if any(type(value) is not int or value < 0 for value in coordinates):
        raise ValueError("malformed temporal action memo key")
    exact_coordinates = cast(tuple[int, int, int], coordinates)
    if type(action) is not IssuedDoubleReversePortAction:
        raise ValueError("malformed temporal action memo payload")
    if (
        type(action.action) is not DoubleReversePortAction
        or type(action.binding) is not tuple
        or action.binding != temporal_action_binding(action.action)
    ):
        raise ValueError("malformed temporal action issue binding")
    exact_action = action.action
    integers: tuple[int, ...] = (
        *exact_coordinates,
        exact_action.source.local_id,
        exact_action.target.local_id,
        exact_action.steps,
        exact_action.phase_in,
        exact_action.phase_out,
        exact_action.left_births,
        exact_action.right_births,
    )
    if any(type(value) is not int or value < 0 for value in integers):
        raise ValueError("malformed temporal action coordinates")
    return (
        12
        + len(action.binding)
        + sum(max(1, (value.bit_length() + 63) // 64) for value in integers)
    )
