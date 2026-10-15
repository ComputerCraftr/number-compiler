"""Carry transduction of a compressed modulo-32 pair-residue view.

Residues 0..18 are unambiguous representatives ``P mod 32`` for decimal pair
values.  The input is the pair-value view itself, never a difference such as
``H=(1-z)Delta``.  Recovering pair values from differences would require a
separate modulo-32 prefix state in addition to the two carry states.

Checking the numeric residue range does not authenticate an actual source
word.  This module is only an exact arithmetic projection of a supplied SLP.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Self

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
    centered_carry_fn,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    arithmetic_automata as _automata_keys,
)
from number_compiler.resources.stores import LedgerList

PAIR_RESIDUE_MODULUS = 32
MAX_DECIMAL_PAIR_RESIDUE = 18


def _integer_limb_units(*values: int) -> int:
    bits = sum(max(1, abs(value).bit_length()) for value in values)
    return max(1, (bits + 63) // 64)


def _slp_node_units(node: SLPNode) -> int:
    return _integer_limb_units(
        node.id,
        node.length,
        node.symbol,
        node.left,
        node.right,
        node.child,
        node.count,
    )


@dataclass(frozen=True, slots=True)
class _Outcome:
    final_carry: int
    outgoing: int
    jumps: int


@dataclass(frozen=True, slots=True)
class _Summary:
    low: _Outcome
    high: _Outcome
    node: SLPNode

    def at(self, carry: int) -> _Outcome:
        return self.high if carry else self.low


class ResidueCarrySLPResult:
    """Query-owned compressed carry words; call :meth:`close` when finished."""

    __slots__ = (
        "_closed",
        "_closed_jump_root",
        "_incoming_root",
        "_jump_root",
        "_outgoing_root",
        "_owner",
        "arena",
        "final_carry",
        "input_length",
        "ledger",
    )

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self._owner = ledger.register(
            f"residue-carry-slp-output-{ledger.owner_count}", "query_memo"
        )
        empty_units = _slp_node_units(SLPNode(0, "EMPTY", 0))
        reserved = False
        try:
            ledger.reserve(self._owner, entries=1, nodes=empty_units)
            reserved = True
            self.arena = SLPArena()
        except BaseException:
            if reserved:
                ledger.release(self._owner, entries=1, nodes=empty_units)
            ledger.mark_disposed(self._owner)
            raise
        ledger.register_container(
            self._owner,
            self.arena.nodes,
            node_count=lambda: sum(_slp_node_units(node) for node in self.arena.nodes),
            payloads=lambda: self.arena.nodes,
        )
        self._closed = False
        self._incoming_root = -1
        self._outgoing_root = self.arena.empty()
        self._jump_root = self.arena.empty()
        self._closed_jump_root = self.arena.empty()
        self.final_carry = 0
        self.input_length = 0

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed residue carry SLP result")

    @property
    def outgoing_root(self) -> int:
        self._check_open()
        return self._outgoing_root

    @property
    def jump_root(self) -> int:
        """Interior coefficients ``c_(i+1)-c_i``, of input length ``m``."""
        self._check_open()
        return self._jump_root

    @property
    def closed_jump_root(self) -> int:
        """Interior jumps followed by ``-c_m``, retaining the full boundary."""
        self._check_open()
        return self._closed_jump_root

    @property
    def derived_nodes(self) -> int:
        self._check_open()
        return len(self.arena.nodes)

    def _reserve_node(self, units: int) -> None:
        self._check_open()
        self.ledger.reserve(self._owner, entries=1, nodes=units)

    def _metadata_workspace(self, *values: int, result_bits: int) -> int:
        operand_bits = sum(max(1, abs(value).bit_length()) for value in values)
        units = max(1, (operand_bits + max(1, result_bits) + 63) // 64)
        self.ledger.reserve(self._owner, nodes=units)
        self.ledger.bump(
            _automata_keys.RESIDUE_CARRY_SLP_METADATA_OPERAND_BITS,
            operand_bits,
        )
        return units

    def terminal(self, symbol: int) -> int:
        existing = self.arena._term.get(symbol)
        if existing is not None:
            return existing
        predicted = SLPNode(len(self.arena.nodes), "TERM", 1, symbol=symbol)
        units = _slp_node_units(predicted)
        self._reserve_node(units)
        before = len(self.arena.nodes)
        try:
            result = self.arena.terminal(symbol)
        except BaseException:
            self.ledger.release(self._owner, entries=1, nodes=units)
            raise
        if len(self.arena.nodes) != before + 1:
            self.ledger.release(self._owner, entries=1, nodes=units)
            raise AssertionError("SLP terminal allocation escaped its preflight")
        return result

    def concat(self, left: int, right: int) -> int:
        if left == self.arena.empty_id:
            return right
        if right == self.arena.empty_id:
            return left
        existing = self.arena._cat.get((left, right))
        if existing is not None:
            return existing
        left_length = self.arena.nodes[left].length
        right_length = self.arena.nodes[right].length
        result_bits = (
            max(max(1, left_length.bit_length()), max(1, right_length.bit_length())) + 1
        )
        workspace = self._metadata_workspace(
            left_length, right_length, result_bits=result_bits
        )
        try:
            length = left_length + right_length
        except BaseException:
            self.ledger.release(self._owner, nodes=workspace)
            raise
        predicted = SLPNode(
            len(self.arena.nodes), "CONCAT", length, left=left, right=right
        )
        units = _slp_node_units(predicted)
        try:
            self._reserve_node(units)
        except BaseException:
            self.ledger.release(self._owner, nodes=workspace)
            raise
        before = len(self.arena.nodes)
        try:
            result = self.arena.concat(left, right)
        except BaseException:
            self.ledger.release(self._owner, entries=1, nodes=units)
            self.ledger.release(self._owner, nodes=workspace)
            raise
        self.ledger.release(self._owner, nodes=workspace)
        if len(self.arena.nodes) != before + 1:
            self.ledger.release(self._owner, entries=1, nodes=units)
            raise AssertionError("SLP concatenation allocation escaped its preflight")
        return result

    def close(self) -> None:
        if self._closed:
            return
        count = len(self.arena.nodes)
        units = sum(_slp_node_units(node) for node in self.arena.nodes)
        self.arena._term.clear()
        self.arena._cat.clear()
        self.arena._rep.clear()
        self.arena.nodes.clear()
        self.ledger.release(self._owner, entries=count, nodes=units)
        self.ledger.mark_disposed(self._owner)
        self._closed = True

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, *_error: object) -> None:
        self.close()


class ResidueCarrySLPProjector:
    """Reusable, ledger-owned transducer workspace for supplied residue SLPs."""

    __slots__ = ("_closed", "_memo", "_stack", "_stack_owner", "ledger")

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("residue carry projection requires a resource ledger")
        self.ledger = ledger
        prefix = f"residue-carry-slp-{ledger.owner_count}"
        self._memo = OwnedMemo[int, _Summary](
            ledger,
            ledger.register(prefix + "-summaries", "query_memo"),
            nodes_per_entry=3,
        )
        self._stack_owner = ledger.register(prefix + "-stack", "query_memo")
        self._stack: LedgerList[tuple[int, bool]] = ledger.make_list(
            self._stack_owner, nodes_per_entry=1, append_only=False
        )
        self._closed = False

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed residue carry SLP projector")
        if len(self._memo) or len(self._stack):
            raise RuntimeError("residue carry SLP workspace is already active")

    def _push(self, node_id: int, expanded: bool) -> None:
        self.ledger.reserve(self._stack_owner, entries=1, nodes=1)
        try:
            self._stack.append((node_id, expanded))
        except BaseException:
            self.ledger.release(self._stack_owner, entries=1, nodes=1)
            raise
        self.ledger.bump(_automata_keys.RESIDUE_CARRY_SLP_WORKSPACE_FRAMES)

    def _pop(self) -> tuple[int, bool]:
        frame = self._stack.pop()
        self.ledger.release(self._stack_owner, entries=1, nodes=1)
        return frame

    @staticmethod
    def _validate_root(arena: SLPArena, root: SLPNode) -> int:
        if type(arena) is not SLPArena:
            raise TypeError("residue carry input requires an SLPArena")
        if type(root) is not SLPNode:
            raise TypeError("residue carry SLP root requires an arena node")
        if not 0 <= root.id < len(arena.nodes) or arena.nodes[root.id] is not root:
            raise ValueError("residue carry SLP root is foreign or out of range")
        return root.id

    def _metadata_binary(self, left: int, right: int, *, multiply: bool) -> int:
        left_bits = max(1, abs(left).bit_length())
        right_bits = max(1, abs(right).bit_length())
        result_bits = (
            left_bits + right_bits if multiply else max(left_bits, right_bits) + 1
        )
        units = max(1, (left_bits + right_bits + result_bits + 63) // 64)
        self.ledger.reserve(self._stack_owner, nodes=units)
        try:
            result = left * right if multiply else left + right
        finally:
            self.ledger.release(self._stack_owner, nodes=units)
        self.ledger.bump(
            _automata_keys.RESIDUE_CARRY_SLP_METADATA_OPERAND_BITS,
            max(1, left.bit_length()) + max(1, right.bit_length()),
        )
        return result

    def _validated_node(self, arena: SLPArena, node_id: int) -> SLPNode:
        if not 0 <= node_id < len(arena.nodes):
            raise ValueError("residue carry SLP child is foreign or out of range")
        node = arena.nodes[node_id]
        if type(node) is not SLPNode or type(node.id) is not int or node.id != node_id:
            raise ValueError("residue carry SLP node identity was mutated")
        fields = (
            node.length,
            node.symbol,
            node.left,
            node.right,
            node.child,
            node.count,
        )
        if any(type(value) is not int for value in fields):
            raise ValueError("residue carry SLP metadata was mutated")
        if node.kind == "EMPTY":
            valid = node_id == arena.empty_id and node == SLPNode(node_id, "EMPTY", 0)
        elif node.kind == "TERM":
            valid = (
                node.length == 1
                and 0 <= node.symbol <= MAX_DECIMAL_PAIR_RESIDUE
                and node.left == node.right == node.child == -1
                and node.count == 0
                and arena._term.get(node.symbol) == node_id
            )
        elif node.kind == "CONCAT":
            basic = (
                0 <= node.left < node_id
                and 0 <= node.right < node_id
                and node.symbol == node.child == -1
                and node.count == 0
                and arena._cat.get((node.left, node.right)) == node_id
                and type(arena.nodes[node.left]) is SLPNode
                and type(arena.nodes[node.right]) is SLPNode
            )
            expected = (
                self._metadata_binary(
                    arena.nodes[node.left].length,
                    arena.nodes[node.right].length,
                    multiply=False,
                )
                if basic
                else -1
            )
            valid = basic and node.length == expected
        elif node.kind == "REPEAT":
            basic = (
                0 <= node.child < node_id
                and node.count >= 2
                and node.symbol == node.left == node.right == -1
                and arena._rep.get((node.child, node.count)) == node_id
                and type(arena.nodes[node.child]) is SLPNode
                and arena.nodes[node.child].kind != "REPEAT"
            )
            expected = (
                self._metadata_binary(
                    arena.nodes[node.child].length, node.count, multiply=True
                )
                if basic
                else -1
            )
            valid = basic and node.length == expected
        else:
            valid = False
        if not valid:
            raise ValueError("residue carry SLP node definition was mutated")
        return node

    @staticmethod
    def _identity(output: ResidueCarrySLPResult) -> _Summary:
        empty = output.arena.empty()
        node = SLPNode(-1, "EMPTY", 0)
        return _Summary(_Outcome(0, empty, empty), _Outcome(1, empty, empty), node)

    def _compose(
        self,
        before: _Summary,
        after: _Summary,
        output: ResidueCarrySLPResult,
    ) -> _Summary:
        def outcome(incoming: int) -> _Outcome:
            first = before.at(incoming)
            second = after.at(first.final_carry)
            return _Outcome(
                second.final_carry,
                output.concat(first.outgoing, second.outgoing),
                output.concat(first.jumps, second.jumps),
            )

        low = outcome(0)
        high = outcome(1)
        self.ledger.bump(_automata_keys.RESIDUE_CARRY_SLP_COMPOSITIONS)
        return _Summary(low, high, before.node)

    def _power(
        self, summary: _Summary, count: int, output: ResidueCarrySLPResult
    ) -> _Summary:
        result = self._identity(output)
        base = summary
        exponent = count
        while exponent:
            self.ledger.bump(_automata_keys.RESIDUE_CARRY_SLP_REPEAT_BITS)
            if exponent & 1:
                result = self._compose(result, base, output)
            exponent_bits = max(1, exponent.bit_length())
            shifted_bits = max(1, exponent_bits - 1)
            units = max(1, (exponent_bits + shifted_bits + 63) // 64)
            self.ledger.reserve(self._stack_owner, nodes=units)
            try:
                exponent = exponent >> 1
            finally:
                self.ledger.release(self._stack_owner, nodes=units)
            self.ledger.bump(
                _automata_keys.RESIDUE_CARRY_SLP_REPEAT_SHIFT_OPERAND_BITS,
                max(1, exponent.bit_length() + 1),
            )
            if exponent:
                base = self._compose(base, base, output)
        return result

    def project(
        self, arena: SLPArena, root: SLPNode, *, incoming: int = 0
    ) -> ResidueCarrySLPResult:
        """Project supplied ``P mod 32`` pair values; grant no source admission."""
        self._check_open()
        if type(incoming) is not int or incoming not in (0, 1):
            raise ValueError("incoming carry must be zero or one")
        root_id = self._validate_root(arena, root)
        output = ResidueCarrySLPResult(self.ledger)
        try:
            self._push(root_id, False)
            while self._stack:
                node_id, expanded = self._pop()
                if self._memo.get(node_id) is not None:
                    continue
                node = self._validated_node(arena, node_id)
                if node.kind in ("EMPTY", "TERM"):
                    expanded = True
                if not expanded:
                    self._push(node_id, True)
                    children = (
                        (node.left, node.right)
                        if node.kind == "CONCAT"
                        else (node.child,)
                    )
                    for child in reversed(children):
                        if self._memo.get(child) is None:
                            self._push(child, False)
                    continue
                if node.kind == "EMPTY":
                    identity = self._identity(output)
                    summary = _Summary(identity.low, identity.high, node)
                elif node.kind == "TERM":
                    carry_fn = centered_carry_fn(node.symbol - 9)
                    low = apply_carry_fn(carry_fn, 0)
                    high = apply_carry_fn(carry_fn, 1)
                    summary = _Summary(
                        _Outcome(
                            low,
                            output.terminal(low),
                            output.terminal(low),
                        ),
                        _Outcome(
                            high,
                            output.terminal(high),
                            output.terminal(high - 1),
                        ),
                        node,
                    )
                elif node.kind == "CONCAT":
                    summary = self._compose(
                        self._memo[node.left], self._memo[node.right], output
                    )
                    summary = _Summary(summary.low, summary.high, node)
                elif node.kind == "REPEAT":
                    summary = self._power(self._memo[node.child], node.count, output)
                    summary = _Summary(summary.low, summary.high, node)
                else:
                    raise AssertionError(node.kind)
                self._memo[node_id] = summary
                self.ledger.bump(_automata_keys.RESIDUE_CARRY_SLP_UNIQUE_NODES)

            for node_id, summary in self._memo.items():
                if self._validated_node(arena, node_id) != summary.node:
                    raise ValueError("residue carry SLP changed during projection")
            selected = self._memo[root_id].at(incoming)
            closed_jumps = output.concat(
                selected.jumps, output.terminal(-selected.final_carry)
            )
            output._incoming_root = root_id
            output._outgoing_root = selected.outgoing
            output._jump_root = selected.jumps
            output._closed_jump_root = closed_jumps
            output.final_carry = selected.final_carry
            output.input_length = root.length
            return output
        except BaseException:
            output.close()
            raise
        finally:
            if self._stack:
                count = len(self._stack)
                self._stack.clear()
                self.ledger.release(self._stack_owner, entries=count, nodes=count)
            self._memo.clear()

    def close(self) -> None:
        if self._closed:
            return
        if self._stack:
            count = len(self._stack)
            self._stack.clear()
            self.ledger.release(self._stack_owner, entries=count, nodes=count)
        self._memo.dispose()
        self.ledger.mark_disposed(self._stack_owner)
        self._closed = True

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, *_error: object) -> None:
        self.close()


__all__ = [
    "MAX_DECIMAL_PAIR_RESIDUE",
    "PAIR_RESIDUE_MODULUS",
    "ResidueCarrySLPProjector",
    "ResidueCarrySLPResult",
]
