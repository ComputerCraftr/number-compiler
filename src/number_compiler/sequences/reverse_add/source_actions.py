"""Canonical original sources and chronological reverse/add action descriptors."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerList


@dataclass(frozen=True, slots=True)
class ReverseSource(ArenaHandle):
    """Authenticated handle for the original input digits."""


@dataclass(frozen=True, slots=True)
class _ReverseSourceRecord:
    exact: ExactSource


@dataclass(frozen=True, slots=True)
class ReverseActionID(ArenaHandle):
    """Ledger-owned identity of one canonical reverse/add temporal action."""


@dataclass(frozen=True, slots=True)
class ReverseActionNode:
    steps: int
    before: ReverseActionID | None
    after: ReverseActionID | None
    depth: int


class ReverseActionArena:
    """Canonical, authenticated binary descriptors for powers of one step."""

    _KIND = "reverse-source-action"
    _SOURCE_KIND = "reverse-source"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("reverse action arena requires a resource ledger")
        self.ledger = ledger
        self.owner = ArenaToken("reverse-source-actions")
        prefix = f"reverse-source-actions-{ledger.owner_count}"
        self._nodes = OwnedMemo[int, ReverseActionNode](
            ledger,
            ledger.register(prefix + "-nodes", "reverse_source_action"),
            nodes_per_entry=1,
        )
        self._normal = OwnedMemo[int, ReverseActionID](
            ledger,
            ledger.register(prefix + "-normal", "reverse_source_action_normal_form"),
            composition_entries=True,
        )
        self._sources = OwnedMemo[int, _ReverseSourceRecord](
            ledger,
            ledger.register(prefix + "-sources", "reverse_original_source"),
            nodes_per_entry=1,
        )
        self._workspace_owner = ledger.register(
            prefix + "-workspace", "reverse_source_action_workspace"
        )
        self._workspace: LedgerList[tuple[int, bool]] = ledger.make_list(
            self._workspace_owner, append_only=False
        )
        ledger.register_container(
            self._workspace_owner,
            self._workspace,
            node_count=lambda: len(self._workspace),
            payloads=lambda: self._workspace,
        )
        self._source_authority: (
            tuple[_ReverseSourceRecord, ExactSource, tuple[int, ...], int] | None
        ) = None
        self._closed = False
        try:
            identity = self._append(ReverseActionNode(0, None, None, 0))
            primitive = self._append(ReverseActionNode(1, None, None, 1))
        except BaseException:
            self._normal.dispose()
            self._nodes.dispose()
            self._sources.dispose()
            self.ledger.mark_disposed(self._workspace_owner)
            self.owner = ArenaToken("failed-reverse-source-actions")
            self._closed = True
            raise
        self.identity, self.primitive = identity, primitive

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed reverse action arena")

    def _append(self, node: ReverseActionNode) -> ReverseActionID:
        local_id = len(self._nodes)
        handle = ReverseActionID(self.owner, self._KIND, local_id)
        self._nodes[local_id] = node
        try:
            self._normal[node.steps] = handle
        except BaseException:
            del self._nodes[local_id]
            raise
        return handle

    def node(self, action: ReverseActionID) -> ReverseActionNode:
        self._check_open()
        if type(action) is not ReverseActionID:
            raise TypeError("reverse/add image requires a scoped action ID")
        action.validate(self.owner, self._KIND, size=len(self._nodes))
        node = self._nodes[action.local_id]
        if self._normal.get(node.steps) != action:
            raise ValueError("reverse action normal form was altered")
        if action.local_id == 0:
            if node != ReverseActionNode(0, None, None, 0):
                raise ValueError("reverse identity action was altered")
        elif action.local_id == 1:
            if node != ReverseActionNode(1, None, None, 1):
                raise ValueError("reverse primitive action was altered")
        else:
            if (
                type(node.steps) is not int
                or node.steps < 2
                or type(node.before) is not ReverseActionID
                or type(node.after) is not ReverseActionID
                or node.before.local_id >= action.local_id
                or node.after.local_id >= action.local_id
            ):
                raise ValueError("reverse composite action was altered")
            node.before.validate(self.owner, self._KIND, size=action.local_id)
            node.after.validate(self.owner, self._KIND, size=action.local_id)
            before = self._nodes[node.before.local_id]
            after = self._nodes[node.after.local_id]
            if (
                self._normal.get(before.steps) != node.before
                or self._normal.get(after.steps) != node.after
                or before.steps + after.steps != node.steps
                or node.depth != 1 + max(before.depth, after.depth)
            ):
                raise ValueError("reverse composite action geometry was altered")
        return node

    def admit_source(self, seed: int, base: int) -> ReverseSource:
        self._check_open()
        seed = require_integer(seed, "seed", 0)
        base = require_integer(base, "base", 2)
        if self._source_authority is not None:
            raise ValueError("reverse action arena already owns an original source")
        digits: list[int] = []
        value = seed
        while True:
            digits.append(value % base)
            value //= base
            if not value:
                break
        self.ledger.bump("reverse_source_original_digit_decodes", len(digits))
        exact = ExactSource(tuple(digits), base, orbit="reverse-add")
        record = _ReverseSourceRecord(exact)
        handle = ReverseSource(self.owner, self._SOURCE_KIND, 0)
        self._sources[0] = record
        self._source_authority = record, exact, exact.digits, exact.base
        return handle

    def source(self, source: ReverseSource) -> ExactSource:
        self._check_open()
        if type(source) is not ReverseSource:
            raise TypeError("reverse/add image requires a scoped source ID")
        source.validate(self.owner, self._SOURCE_KIND, size=len(self._sources))
        record = self._sources[source.local_id]
        authority = self._source_authority
        if (
            authority is None
            or record is not authority[0]
            or record.exact is not authority[1]
            or record.exact.digits is not authority[2]
            or record.exact.base != authority[3]
            or record.exact.orbit != "reverse-add"
            or record.exact.blank != 0
            or record.exact.extent is not None
            or record.exact.alphabet_size is not None
        ):
            raise ValueError("reverse original source authority was altered")
        return record.exact

    def action(self, steps: int) -> ReverseActionID:
        self._check_open()
        steps = require_integer(steps, "reverse/add steps", 0)
        found = self._normal.get(steps)
        if found is not None:
            self.node(found)
            return found
        if self._workspace:
            raise RuntimeError("reverse action construction workspace is active")
        credit = 0
        starting_nodes = len(self._nodes)

        def push(item: tuple[int, bool]) -> None:
            nonlocal credit
            self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
            credit += 1
            self._workspace.append(item)

        try:
            push((steps, False))
            while self._workspace:
                current, expanded = self._workspace.pop()
                self.ledger.release(self._workspace_owner, entries=1, nodes=1)
                credit -= 1
                if self._normal.get(current) is not None:
                    continue
                left_steps = current // 2
                right_steps = current - left_steps
                if not expanded:
                    push((current, True))
                    if self._normal.get(right_steps) is None:
                        push((right_steps, False))
                    if self._normal.get(left_steps) is None:
                        push((left_steps, False))
                    continue
                before = self._normal[left_steps]
                after = self._normal[right_steps]
                depth = 1 + max(self.node(before).depth, self.node(after).depth)
                self._append(ReverseActionNode(current, before, after, depth))
            return self._normal[steps]
        except BaseException:
            while self._workspace:
                self._workspace.pop()
            if credit:
                self.ledger.release(self._workspace_owner, entries=credit, nodes=credit)
            while len(self._nodes) > starting_nodes:
                local_id = len(self._nodes) - 1
                node = self._nodes[local_id]
                del self._normal[node.steps]
                del self._nodes[local_id]
            raise

    def compose(
        self, before: ReverseActionID, after: ReverseActionID
    ) -> ReverseActionID:
        return self.action(self.node(before).steps + self.node(after).steps)

    @property
    def operator_nodes(self) -> int:
        return max(0, len(self._nodes) - 1)

    @property
    def compose_operations(self) -> int:
        return sum(node.steps >= 2 for node in self._nodes.values())

    def dispose(self) -> None:
        if self._closed:
            return
        self._normal.dispose()
        self._nodes.dispose()
        self._sources.dispose()
        self.ledger.mark_disposed(self._workspace_owner)
        self._source_authority = None
        self.owner = ArenaToken("disposed-reverse-source-actions")
        self._closed = True
