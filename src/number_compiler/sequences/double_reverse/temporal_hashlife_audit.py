"""Payload audits for source-bound 2rev10 Hashlife memo owners."""

from __future__ import annotations

from typing import TYPE_CHECKING, TypeVar, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell
from number_compiler.sequences.double_reverse.temporal_hashlife_slp import (
    existing_concat,
    existing_part,
    existingsymbol_at,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReversePortAction,
    DoubleReverseSLPID,
    IssuedDoubleReversePortAction,
    IssuedDoubleReverseSourcePrefix,
    source_prefix_binding,
    source_prefix_node_cost,
    temporal_action_binding,
    temporal_action_node_cost,
)

if TYPE_CHECKING:
    from number_compiler.sequences.double_reverse.temporal_hashlife import (
        DoubleReverseTemporalHashlife,
    )

_Key = TypeVar("_Key")
_Value = TypeVar("_Value")


def _memo_account_is_exact(
    ledger: ResourceLedger,
    memo: OwnedMemo[_Key, _Value],
    owner: int,
    container: object,
    *,
    role: str,
) -> bool:
    account = ledger.account_status(owner)
    return (
        memo.ledger is ledger
        and memo.owner == owner
        and memo.audit_snapshot().container is container
        and account.container_identity == id(container)
        and account.role == role
        and not account.disposed
        and memo.nodes_per_entry == 1
        and memo.node_cost is None
        and memo.audit_snapshot().dynamic_nodes == 0
        and account.entries == len(memo)
        and account.nodes == len(memo)
    )


class TemporalHashlifeAuditBase:
    """Owner algorithms for independent retained temporal-cache inspection."""

    __slots__ = ()
    ledger: ResourceLedger
    arena: LedgerSLPArena
    source_root: int
    max_steps: int
    _slices: OwnedMemo[tuple[int, int, int], int]
    _cone: OwnedMemo[tuple[int, int], int]
    _actions: OwnedMemo[tuple[int, int, int], IssuedDoubleReversePortAction]
    _prefixes: OwnedMemo[int, IssuedDoubleReverseSourcePrefix]
    _audit_slices: object
    _audit_cones: object
    _audit_actions: object
    _audit_prefixes: object
    _prefix_issued: IssuedDoubleReverseSourcePrefix | None
    _prefix_binding_snapshot: tuple[int | str | None, ...] | None

    def _root(self, handle: DoubleReverseSLPID) -> int:
        raise NotImplementedError

    def _certify(self, root: int, *, audit: bool) -> int | None:
        raise NotImplementedError

    def _validate_issued_action(
        self, action: DoubleReversePortAction, issued: object, *, audit: bool = False
    ) -> None:
        raise NotImplementedError

    def _payload_audit_boundary_visit(self) -> None:
        raise NotImplementedError

    def audit_temporal_slice_store(
        self,
    ) -> tuple[list[PayloadAuditEntry], list[PayloadAuditEntry]]:
        memo = self._slices
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []
        container = self._audit_slices
        if not _memo_account_is_exact(
            self.ledger,
            memo,
            memo.owner,
            container,
            role="double_reverse_temporal_memo",
        ):
            raise ValueError("2rev10 temporal slice owner is invalid")
        for key, value in memo.items():
            valid = (
                type(key) is tuple
                and len(key) == 3
                and all(type(item) is int for item in key)
                and type(value) is int
            )
            if valid:
                source, begin, end = key
                valid = (
                    0 <= source < len(self.arena.nodes)
                    and 0 <= begin < end <= self.arena.nodes[source].length
                    and not (begin == 0 and end == self.arena.nodes[source].length)
                    and 0 <= value < len(self.arena.nodes)
                )
                if valid:
                    expected = existing_part(self.arena, source, begin, end)
                    valid = (
                        expected == value
                        and self.arena.nodes[value].length == end - begin
                    )
            destination = approved if valid else invalid
            destination.extend(
                (
                    PayloadAuditEntry(memo.owner, key),
                    PayloadAuditEntry(memo.owner, value),
                )
            )
        return approved, invalid

    def audit_temporal_cone_store(
        self,
    ) -> tuple[list[PayloadAuditEntry], list[PayloadAuditEntry]]:
        memo = self._cone
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []
        if not _memo_account_is_exact(
            self.ledger,
            memo,
            memo.owner,
            self._audit_cones,
            role="double_reverse_temporal_memo",
        ):
            raise ValueError("2rev10 temporal cone owner is invalid")

        rows = list(memo.items())
        rows.sort(
            key=lambda row: (
                row[0][1]
                if type(row[0]) is tuple and len(row[0]) == 2 and type(row[0][1]) is int
                else -1,
                row[0][0]
                if type(row[0]) is tuple and len(row[0]) == 2 and type(row[0][0]) is int
                else -1,
            )
        )
        verified: dict[tuple[int, int], int] = {}
        for key, value in rows:
            valid = (
                type(key) is tuple
                and len(key) == 2
                and all(type(item) is int for item in key)
                and type(value) is int
            )
            if valid:
                block, steps = key
                valid = (
                    0 <= block < len(self.arena.nodes)
                    and type(steps) is int
                    and steps > 0
                    and steps <= self.max_steps
                    and steps & (steps - 1) == 0
                    and self.arena.nodes[block].length == 4 * steps
                    and 0 <= value < len(self.arena.nodes)
                    and self.arena.nodes[value].length == 2 * steps
                )
                if valid and steps == 1:
                    read_digits = tuple(
                        existingsymbol_at(
                            self.arena,
                            block,
                            index,
                            on_visit=self._payload_audit_boundary_visit,
                        )
                        for index in range(4)
                    )
                    valid = all(
                        type(digit) is int and 0 <= digit <= 9 for digit in read_digits
                    )
                    digits = cast(tuple[int, int, int, int], read_digits)
                    left = (
                        self.arena.existing_terminal(
                            stencil_cell(digits[0], digits[1], digits[2])
                        )
                        if valid
                        else None
                    )
                    right = (
                        self.arena.existing_terminal(
                            stencil_cell(digits[1], digits[2], digits[3])
                        )
                        if valid
                        else None
                    )
                    expected = (
                        None
                        if left is None or right is None
                        else existing_concat(self.arena, left, right)
                    )
                    valid = expected == value
                elif valid:
                    half = steps // 2
                    child_blocks = (
                        existing_part(self.arena, block, 0, 2 * steps),
                        existing_part(self.arena, block, steps, 3 * steps),
                        existing_part(self.arena, block, 2 * steps, 4 * steps),
                    )
                    child_outputs: list[int] = []
                    for child_block in child_blocks:
                        if child_block is None:
                            valid = False
                            break
                        child_key = (child_block, half)
                        child_output = verified.get(child_key)
                        if child_output is None:
                            valid = False
                            break
                        child_outputs.append(child_output)
                    if valid:
                        left_middle = existing_concat(
                            self.arena, child_outputs[0], child_outputs[1]
                        )
                        middle_right = existing_concat(
                            self.arena, child_outputs[1], child_outputs[2]
                        )
                        if left_middle is None or middle_right is None:
                            valid = False
                        else:
                            left_result = verified.get((left_middle, half))
                            right_result = verified.get((middle_right, half))
                            expected = (
                                None
                                if left_result is None or right_result is None
                                else existing_concat(
                                    self.arena, left_result, right_result
                                )
                            )
                            valid = expected == value
            if valid:
                verified[key] = value
            destination = approved if valid else invalid
            destination.extend(
                (
                    PayloadAuditEntry(memo.owner, key),
                    PayloadAuditEntry(memo.owner, value),
                )
            )
        return approved, invalid

    def audit_source_prefix_store(
        self,
    ) -> tuple[list[PayloadAuditEntry], list[PayloadAuditEntry]]:
        """Validate the one ledger-owned continuation cursor without replaying it."""
        memo = self._prefixes
        owner = memo.owner
        account = self.ledger.account_status(owner)
        if (
            self._audit_prefixes is not memo.audit_snapshot().container
            or account.container_identity != id(self._audit_prefixes)
            or account.role != "double_reverse_temporal_memo"
            or account.disposed
            or memo.ledger is not self.ledger
            or memo.node_cost is not source_prefix_node_cost
            or memo.nodes_per_entry != 0
            or memo.audit_snapshot().dynamic_nodes != account.nodes
            or account.entries != len(memo)
        ):
            raise ValueError("2rev10 source-prefix owner is invalid")
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []
        cost_nodes = 0
        for key, issued in memo.items():
            valid = (
                type(key) is int
                and key == self.source_root
                and type(issued) is IssuedDoubleReverseSourcePrefix
                and issued is self._prefix_issued
            )
            if valid:
                entry = issued.entry
                valid = (
                    type(entry.physical_steps) is int
                    and 0 <= entry.physical_steps <= min(32, self.max_steps)
                    and self._root(entry.source) == self.source_root
                    and 0 <= self._root(entry.target) < len(self.arena.nodes)
                    and (
                        entry.certified_phase is None
                        or type(entry.certified_phase) is int
                        and entry.certified_phase in (0, 1, 2, 3)
                    )
                    and issued.binding == source_prefix_binding(entry)
                    and issued.binding == self._prefix_binding_snapshot
                    and self._certify(self._root(entry.target), audit=True)
                    == entry.certified_phase
                )
            if valid:
                cost_nodes += memo.entry_nodes(key, issued)
            destination = approved if valid else invalid
            destination.extend(
                (
                    PayloadAuditEntry(owner, key),
                    PayloadAuditEntry(owner, issued),
                )
            )
        if cost_nodes != account.nodes:
            raise ValueError("2rev10 source-prefix accounting is inconsistent")
        return approved, invalid

    def audit_temporal_actions(
        self, ledger: ResourceLedger
    ) -> PayloadAuditContribution:
        memo = self._actions
        account = ledger.account_status(memo.owner)
        cost_nodes = 0
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []
        valid_owner = (
            self.ledger is ledger
            and memo.ledger is ledger
            and memo.audit_snapshot().container is self._audit_actions
            and account.container_identity == id(self._audit_actions)
            and account.role == "double_reverse_temporal_memo"
            and not account.disposed
            and memo.node_cost is temporal_action_node_cost
            and memo.nodes_per_entry == 0
            and memo.audit_snapshot().dynamic_nodes == account.nodes
            and account.entries == len(memo)
        )
        if not valid_owner:
            raise ValueError("2rev10 temporal action owner is invalid")

        for key, issued in memo.items():
            action = (
                issued.action if type(issued) is IssuedDoubleReversePortAction else None
            )
            valid = (
                type(key) is tuple
                and len(key) == 3
                and all(type(value) is int and value >= 0 for value in key)
                and type(issued) is IssuedDoubleReversePortAction
                and type(action) is DoubleReversePortAction
                and type(issued.binding) is tuple
                and issued.binding == temporal_action_binding(action)
                and key == (action.source.local_id, action.steps, action.phase_in)
            )
            if valid:
                exact_action = cast(DoubleReversePortAction, action)
                exact_issued = issued
                try:
                    self._validate_issued_action(exact_action, exact_issued, audit=True)
                    cost_nodes += memo.entry_nodes(key, exact_issued)
                except (
                    ArithmeticError,
                    AttributeError,
                    IndexError,
                    KeyError,
                    TypeError,
                    ValueError,
                ):
                    valid = False
            destination = approved if valid else invalid
            destination.extend(
                (
                    PayloadAuditEntry(memo.owner, key),
                    PayloadAuditEntry(memo.owner, issued),
                )
            )
        if cost_nodes != account.nodes:
            raise ValueError("2rev10 temporal action accounting is inconsistent")
        slice_approved, slice_invalid = self.audit_temporal_slice_store()
        cone_approved, cone_invalid = self.audit_temporal_cone_store()
        prefix_approved, prefix_invalid = self.audit_source_prefix_store()
        approved.extend(slice_approved)
        approved.extend(cone_approved)
        approved.extend(prefix_approved)
        invalid.extend(slice_invalid)
        invalid.extend(cone_invalid)
        invalid.extend(prefix_invalid)
        return PayloadAuditContribution(tuple(approved), tuple(invalid))


def audit_double_reverse_temporal_actions(
    ledger_value: object, root_value: object, expected_root_type: type[object]
) -> PayloadAuditContribution:
    """Validate exact public dispatch before invoking the owner's audit."""
    if type(ledger_value) is not ResourceLedger:
        raise TypeError("2rev10 temporal auditor received a foreign ledger")
    if type(root_value) is not expected_root_type:
        raise TypeError("2rev10 temporal auditor received a foreign owner")
    return cast("DoubleReverseTemporalHashlife", root_value).audit_temporal_actions(
        ledger_value
    )
