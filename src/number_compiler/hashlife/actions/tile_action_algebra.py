"""Canonical homogeneous powers and fixed-size heterogeneous temporal DAGs."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.polynomials.frobenius_sector import ReverseFrobeniusPlan
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_actions as _actions_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerDict

_DEFAULT_TEMPORAL_COCYCLE_1 = TemporalCocycle()


@dataclass(frozen=True, slots=True)
class PrimitiveTileAction:
    kernel: ActionProgramID
    signature: PortSignatureID
    children: tuple[FieldCellActionID, FieldCellActionID] | None = None
    cocycle: TemporalCocycle = _DEFAULT_TEMPORAL_COCYCLE_1
    repetitions: int = 1
    homogeneous: bool = True
    spatial_events_add: bool = False
    blank_left_tail: int = 0
    blank_right_tail: int = 0
    stable_blank_output: bool = False
    reverse_frobenius: ReverseFrobeniusPlan | None = None


def retained_reverse_plan_nodes(maximum_classes: int) -> int:
    """Count one plan and its fixed sector records.

    The plan references an immutable kernel declaration shared by every action;
    it does not copy or own that declaration's finite proof graph.
    """
    if type(maximum_classes) is not int or maximum_classes < 1:
        raise ValueError("reverse Frobenius node count requires positive geometry")
    return 1 + maximum_classes.bit_length()


def retained_action_nodes(reverse_frobenius: ReverseFrobeniusPlan | None) -> int:
    """Count the action record and every retained inline algebraic record."""
    if reverse_frobenius is None:
        return 1
    if type(reverse_frobenius) is not ReverseFrobeniusPlan:
        raise TypeError("tile action has another Frobenius plan sort")
    return 1 + retained_reverse_plan_nodes(reverse_frobenius.maximum_classes)


ActionSemanticKey = (
    tuple[str, ActionProgramID, int, TemporalCocycle]
    | tuple[str, FieldCellActionID, FieldCellActionID]
)


def blank_context_metadata(
    first: PrimitiveTileAction,
    second: PrimitiveTileAction | None = None,
) -> tuple[int, int, bool]:
    """Return the certified blank tails for one primitive or composition."""
    for record in (first,) if second is None else (first, second):
        if (
            type(record.blank_left_tail) is not int
            or type(record.blank_right_tail) is not int
            or type(record.stable_blank_output) is not bool
        ):
            raise TypeError("tile action has invalid blank-tail metadata sorts")
        if record.blank_left_tail < 0 or record.blank_right_tail < 0:
            raise ValueError("tile action has negative blank-tail metadata")
    if second is None:
        return first.blank_left_tail, first.blank_right_tail, first.stable_blank_output
    stable = first.stable_blank_output and second.stable_blank_output
    ready = max(first.blank_left_tail, first.blank_right_tail)
    return (
        ready + second.blank_left_tail if stable else 0,
        ready + second.blank_right_tail if stable else 0,
        stable,
    )


class _Host(Protocol):
    ledger: ResourceLedger
    _actions: LedgerDict[int, PrimitiveTileAction]
    _action_keys: LedgerDict[ActionSemanticKey, int]
    _compositions: LedgerDict[tuple[FieldCellActionID, FieldCellActionID], int]
    _next_action: int
    _action_owner: int
    _action_key_owner: int
    _compose_owner: int

    def _action(self, action: FieldCellActionID) -> PrimitiveTileAction: ...
    def _handle(self, local_id: int) -> FieldCellActionID: ...
    def kernels_compatible(
        self,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> bool: ...


def compose_actions(
    self: _Host,
    before: FieldCellActionID,
    after: FieldCellActionID,
) -> FieldCellActionID:
    """Intern a power or ordered child composition without flattening its DAG."""
    first, second = self._action(before), self._action(after)
    homogeneous = (
        first.homogeneous
        and second.homogeneous
        and first.kernel == second.kernel
        and first.signature == second.signature
    )
    if not homogeneous and not self.kernels_compatible(first.kernel, second.kernel):
        raise ValueError("mixed temporal actions require compatible cell alphabets")
    result_kernel = first.kernel if homogeneous else second.kernel
    result_signature = first.signature if homogeneous else second.signature
    key = before, after
    repetitions = first.repetitions + second.repetitions
    expected = TemporalCocycle(
        first.cocycle.physical_ticks + second.cocycle.physical_ticks,
        first.cocycle.event_weight + second.cocycle.event_weight,
        first.cocycle.frame_shift + second.cocycle.frame_shift,
    )
    spatial_events_add = first.spatial_events_add or second.spatial_events_add
    blank_left_tail, blank_right_tail, stable_blank_output = blank_context_metadata(
        first,
        second,
    )
    found = self._compositions.get(key)
    if found is not None:
        if type(found) is not int:
            raise TypeError("temporal action interner contains an integer alias")
        result = self._handle(found)
        record = self._action(result)
        if (
            record.kernel != result_kernel
            or record.signature != result_signature
            or record.cocycle != expected
            or record.repetitions != repetitions
            or record.homogeneous != homogeneous
            or (not homogeneous and record.children != key)
            or record.spatial_events_add != spatial_events_add
            or record.stable_blank_output != stable_blank_output
            or record.blank_left_tail != blank_left_tail
            or record.blank_right_tail != blank_right_tail
        ):
            raise ValueError("temporal action interner points to another record")
        self.ledger.bump(_actions_keys.TILE_TEMPORAL_ACTION_HITS)
        return result
    semantic_key: ActionSemanticKey = (
        ("power", result_kernel, repetitions, expected)
        if homogeneous
        else ("compose", before, after)
    )
    canonical = self._action_keys.get(semantic_key)
    if canonical is not None:
        if type(canonical) is not int:
            raise TypeError("temporal semantic interner contains an integer alias")
        result = self._handle(canonical)
        record = self._action(result)
        if (
            record.kernel != result_kernel
            or record.signature != result_signature
            or record.repetitions != repetitions
            or record.cocycle != expected
            or record.homogeneous != homogeneous
            or (not homogeneous and record.children != key)
            or record.spatial_events_add != spatial_events_add
            or record.stable_blank_output != stable_blank_output
            or record.blank_left_tail != blank_left_tail
            or record.blank_right_tail != blank_right_tail
        ):
            raise ValueError("temporal semantic interner points to another record")
        self.ledger.reserve(self._compose_owner, entries=1)
        try:
            self._compositions[key] = canonical
        except BaseException:
            self.ledger.release(self._compose_owner, entries=1)
            raise
        self.ledger.bump(_actions_keys.TILE_TEMPORAL_ACTION_SEMANTIC_ALIAS_HITS)
        return result
    has_reverse_frobenius = (
        homogeneous
        and first.reverse_frobenius is not None
        and second.reverse_frobenius is not None
    )
    reservations = (
        (
            self._action_owner,
            1,
            retained_action_nodes(first.reverse_frobenius)
            if has_reverse_frobenius
            else 1,
        ),
        (self._action_key_owner, 1, 0),
        (self._compose_owner, 1, 0),
    )
    self.ledger.reserve_many(reservations)
    local_id = self._next_action
    self._next_action += 1
    try:
        reverse_frobenius = None
        if has_reverse_frobenius:
            assert first.reverse_frobenius is not None
            assert second.reverse_frobenius is not None
            reverse_frobenius = first.reverse_frobenius.then(second.reverse_frobenius)
        self._actions[local_id] = PrimitiveTileAction(
            result_kernel,
            result_signature,
            key,
            expected,
            repetitions,
            homogeneous,
            spatial_events_add,
            blank_left_tail,
            blank_right_tail,
            stable_blank_output,
            reverse_frobenius,
        )
        self._action_keys[semantic_key] = local_id
        self._compositions[key] = local_id
    except BaseException:
        self._actions.pop(local_id, None)
        self._action_keys.pop(semantic_key, None)
        self._compositions.pop(key, None)
        for owner, entries, nodes in reservations:
            self.ledger.release(owner, entries, nodes)
        raise
    self.ledger.bump(_shared_keys.TILE_TEMPORAL_ACTION_PUBLICATIONS)
    if self._actions[local_id].reverse_frobenius is not None:
        self.ledger.bump(_actions_keys.REVERSE_FROBENIUS_PLAN_COMPOSITIONS)
    return self._handle(local_id)


__all__ = [
    "ActionSemanticKey",
    "PrimitiveTileAction",
    "blank_context_metadata",
    "compose_actions",
    "retained_action_nodes",
    "retained_reverse_plan_nodes",
]
