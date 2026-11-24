"""Source-owned causal decimal words for the ordered powers-of-five stream."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from types import TracebackType
from typing import Self

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error

_MAX_EXPONENT = 4096


def _matrix_nodes(_key: int, matrix: Matrix2) -> int:
    return 8 + sum((value.bit_length() + 63) // 64 for value in matrix.entries)


class Pow5CFSource:
    """An authenticated, query-owned source of successive decimal ×5 words.

    The root is LSD-first, in the order required by decimal multiplication.
    Rows expose only MSD-first digit and continuant projections.
    """

    def __init__(self, ledger: ResourceLedger, *, shared_cache: bool = True) -> None:
        if type(ledger) is not ResourceLedger or type(shared_cache) is not bool:
            raise TypeError("CF source requires a ledger and a Boolean cache policy")
        self.ledger = ledger
        self.shared_cache = shared_cache
        self._closed = False
        self._epoch: int = 0
        self._exponent: int = 0
        self._root: int = 0
        prefix = f"mahler-cf-source-{ledger.owner_count}"
        self._scratch_owner = ledger.register(prefix + "-scratch", "observer-scratch")
        matrix_owner = ledger.register(prefix + "-continuants", "cf-word-memo")
        self._arena = LedgerSLPArena(ledger, prefix, "mahler-cf")
        with cleanup_on_error(self._arena.dispose):
            self._matrices: OwnedMemo[int, Matrix2] = OwnedMemo(
                ledger, matrix_owner, node_cost=_matrix_nodes
            )
            with cleanup_on_error(self._matrices.dispose):
                self._root = self._arena.terminal(1)

    def __enter__(self) -> Self:
        self._require_open()
        return self

    def __exit__(
        self,
        _exc_type: type[BaseException] | None,
        _exc: BaseException | None,
        _traceback: TracebackType | None,
    ) -> None:
        self.close()

    def _require_open(self) -> None:
        if self._closed:
            raise RuntimeError("continued-fraction source is closed")

    def close(self) -> None:
        self._closed = True
        cleanup_all((self._matrices.dispose, self._arena.dispose))

    def next_row(self) -> Pow5CFRow:
        """Publish the next row; failed retirement revokes the source."""
        self._require_open()
        if self._exponent >= _MAX_EXPONENT:
            raise StopIteration("power-of-five source exponent exceeds 4096")
        start = len(self._arena.nodes)
        with cleanup_on_error(lambda: self._arena.rollback_unpublished_suffix(start)):
            root, carry = self._pointed_successor(self._root)
            if carry:
                root = self._arena.concat(root, self._arena.terminal(carry))
            if symbol_at(self._arena, root, self._arena.nodes[root].length - 1) == 0:
                raise ArithmeticError("×5 source retained a leading zero")
            next_exponent = self._exponent + 1
            row = Pow5CFRow(
                self,
                self._epoch + 1,
                next_exponent,
                root,
                self._arena.node_id_generation,
                self._arena.nodes[root],
            )
        self._root = root
        self._exponent = next_exponent
        self._epoch += 1
        if len(self._arena.nodes) > 1024:
            with cleanup_on_error(self.close):
                self._compact_current_root()
                row = Pow5CFRow(
                    self,
                    self._epoch,
                    next_exponent,
                    self._root,
                    self._arena.node_id_generation,
                    self._arena.nodes[self._root],
                )
        return row

    def _compact_current_root(self) -> None:
        """Move the live grammar into a fresh owner and retire obsolete history."""
        old_arena = self._arena
        old_matrices = self._matrices
        prefix = f"mahler-cf-source-{self.ledger.owner_count}"
        arena = LedgerSLPArena(self.ledger, prefix, "mahler-cf")
        with cleanup_on_error(arena.dispose):
            matrix_owner = self.ledger.register(prefix + "-continuants", "cf-word-memo")
            matrices: OwnedMemo[int, Matrix2] = OwnedMemo(
                self.ledger, matrix_owner, node_cost=_matrix_nodes
            )
            with cleanup_on_error(matrices.dispose):
                with LedgerReservation(self.ledger, self._scratch_owner) as scratch:
                    results = fold_slp_dag(
                        old_arena,
                        self._root,
                        empty_value=arena.empty_id,
                        terminal_value=arena.terminal,
                        concatenate=arena.concat,
                        repeat=arena.repeat,
                        on_schedule=lambda _: scratch.reserve(nodes=3),
                        on_unschedule=lambda _: scratch.release(nodes=3),
                        on_evaluate=lambda _: scratch.reserve(nodes=3),
                    )
                    root = results[self._root]
                # No row can be used during this synchronous switch. A failed
                # retirement revokes the source rather than publishing a root.
                try:
                    cleanup_all((old_matrices.dispose, old_arena.dispose))
                except BaseException:
                    self._closed = True
                    raise
                self._arena = arena
                self._matrices = matrices
                self._root = root

    def _pointed_successor(self, root: int) -> tuple[int, int]:
        """Compile only the demanded incoming carry of each reached node."""
        arena = self._arena
        values: dict[tuple[int, int], tuple[int, int]] = {}
        pending: list[tuple[int, int, bool]] = []
        with LedgerReservation(self.ledger, self._scratch_owner) as scratch:

            def push(node_id: int, inlet: int, joined: bool) -> None:
                scratch.reserve(nodes=3)
                pending.append((node_id, inlet, joined))

            def exit_for(node_id: int, inlet: int) -> int:
                size = arena.nodes[node_id].length
                return inlet if size == 0 else symbol_at(arena, node_id, size - 1) // 2

            push(root, 0, False)
            while pending:
                node_id, inlet, joined = pending.pop()
                scratch.release(nodes=3)
                key = (node_id, inlet)
                if key in values:
                    continue
                node = arena.nodes[node_id]
                if node.kind == "EMPTY":
                    result = (arena.empty_id, inlet)
                elif node.kind == "TERM":
                    if not 0 <= node.symbol <= 9:
                        raise ValueError("decimal source contains an invalid digit")
                    carry, digit = divmod(5 * node.symbol + inlet, 10)
                    result = (arena.terminal(digit), carry)
                elif node.kind in ("CONCAT", "REPEAT"):
                    child = node.left if node.kind == "CONCAT" else node.child
                    right = node.right if node.kind == "CONCAT" else node.child
                    next_inlet = exit_for(child, inlet)
                    first = (child, inlet)
                    second = (right, next_inlet)
                    if not joined:
                        push(node_id, inlet, True)
                        if node.kind == "CONCAT" or node.count > 1:
                            push(right, next_inlet, False)
                        push(child, inlet, False)
                        continue
                    output, carry = values[first]
                    if node.kind == "CONCAT":
                        rest, carry = values[second]
                        output = arena.concat(output, rest)
                    elif node.count > 1:
                        rest, carry = values[second]
                        output = arena.concat(
                            output, arena.repeat(rest, node.count - 1)
                        )
                    result = (output, carry)
                else:
                    raise ValueError("unknown decimal source node")
                scratch.reserve(nodes=4)
                values[key] = result
            return values[(root, 0)]

    def authenticate_row(
        self, epoch: int, exponent: int, root: int, generation: int, node: object
    ) -> None:
        """Authenticate the selected source occurrence and arena generation."""
        self._require_open()
        if (
            epoch != self._epoch
            or exponent != self._exponent
            or root != self._root
            or generation != self._arena.node_id_generation
            or not 0 <= root < len(self._arena.nodes)
            or self._arena.nodes[root] is not node
        ):
            raise ValueError("continued-fraction row is stale or foreign")

    def checked_width(
        self, epoch: int, exponent: int, root: int, generation: int, node: object
    ) -> int:
        self.authenticate_row(epoch, exponent, root, generation, node)
        return self._arena.nodes[root].length

    def checked_digit(
        self,
        epoch: int,
        exponent: int,
        root: int,
        generation: int,
        node: object,
        offset: int,
    ) -> int:
        self.authenticate_row(epoch, exponent, root, generation, node)
        return symbol_at(self._arena, root, offset)

    def checked_segment(
        self,
        epoch: int,
        exponent: int,
        root: int,
        generation: int,
        node: object,
        begin: int,
        end: int,
        reserve_bits: Callable[[int], None],
    ) -> Matrix2:
        self.authenticate_row(epoch, exponent, root, generation, node)
        arena = self._arena
        return fold_slp_interval(
            arena,
            root,
            begin,
            end,
            identity=Matrix2.identity(),
            length=lambda node_id: arena.nodes[node_id].length,
            full_value=lambda node_id, _reverse: self._source_matrix(
                node_id, reserve_bits
            ),
            compose=lambda first, second: first.multiply(second),
            repeat=lambda value, count: value.power(count),
            reverse=True,
        )

    def _source_matrix(
        self, node_id: int, reserve_bits: Callable[[int], None]
    ) -> Matrix2:
        """Compile each reached source node once with its exact ordering."""
        pending = [(node_id, False)]
        temporary: dict[int, Matrix2] = {}
        temporary_bits = 0
        while pending:
            current, joined = pending.pop()
            cached = self._matrices.get(current) if self.shared_cache else None
            if cached is None:
                cached = temporary.get(current)
            if cached is not None:
                continue
            node = self._arena.nodes[current]
            reserve_bits(temporary_bits + 32 * (node.length + 8 * len(pending) + 128))
            if node.kind == "TERM":
                if not 0 <= node.symbol <= 9:
                    raise ValueError("decimal source contains an invalid digit")
                value = Matrix2.digit(node.symbol + 1)
            elif node.kind == "EMPTY":
                value = Matrix2.identity()
            elif not joined:
                pending.append((current, True))
                if node.kind == "CONCAT":
                    pending.append((node.right, False))
                    pending.append((node.left, False))
                elif node.kind == "REPEAT":
                    pending.append((node.child, False))
                else:
                    raise ValueError("unknown decimal source node")
                continue
            else:

                def get(child: int) -> Matrix2:
                    result = self._matrices.get(child) if self.shared_cache else None
                    if result is None:
                        result = temporary[child]
                    return result

                if node.kind == "CONCAT":
                    # Physical words are stored LSD-first.
                    value = get(node.right).multiply(get(node.left))
                elif node.kind == "REPEAT":
                    value = get(node.child).power(node.count)
                else:
                    raise ValueError("unknown decimal source node")
            if self.shared_cache:
                self._matrices[current] = value
            else:
                temporary_bits += 8 * (
                    sum(entry.bit_length() for entry in value.entries) + 256
                )
                reserve_bits(temporary_bits + 32 * (node.length + 128))
                temporary[current] = value
        result = self._matrices.get(node_id) if self.shared_cache else None
        return temporary[node_id] if result is None else result


@dataclass(frozen=True, slots=True)
class Pow5CFRow:
    """One row issued by a live source at its current generation."""

    _source: Pow5CFSource
    _epoch: int
    _exponent: int
    _root: int
    _generation: int
    _node: object

    def require_current(self) -> None:
        self._source.authenticate_row(
            self._epoch, self._exponent, self._root, self._generation, self._node
        )

    @property
    def exponent(self) -> int:
        self.require_current()
        return self._exponent

    @property
    def width(self) -> int:
        self.require_current()
        return self._source.checked_width(
            self._epoch, self._exponent, self._root, self._generation, self._node
        )

    def digit_at(self, index: int) -> int:
        self.require_current()
        if type(index) is not int or not 0 <= index < self.width:
            raise ValueError("decimal digit index is outside its source row")
        return self._source.checked_digit(
            self._epoch,
            self._exponent,
            self._root,
            self._generation,
            self._node,
            self.width - 1 - index,
        )

    def segment(self, start: int, length: int) -> Matrix2:
        """Read an MSD-first interval as one ordered exact continuant."""
        self.require_current()
        if (
            type(start) is not int
            or type(length) is not int
            or length < 1
            or not 0 <= start <= self.width - length
        ):
            raise ValueError("continued-fraction interval is outside its source row")
        if length == 1 and start + length != self.width:
            return Matrix2.digit(self.digit_at(start) + 1)
        source = self._source
        scratch = RunArithmeticWorkspace.for_ledger(source.ledger, "mahler-cf-segment")
        with scratch.scope():
            scratch.require_bits(32 * (length * 4 + self.width * 4 + 128))
            # The bounded suffix clock shares only a source-authenticated cut.
            if length <= 4 and start + length == self.width and self.exponent >= length:
                from number_compiler.sequences.antihydra.mahler_cf_low_period import (
                    low_suffix_response,
                )

                return low_suffix_response(
                    self.exponent, length, reserve_bits=scratch.require_bits
                )
            return source.checked_segment(
                self._epoch,
                self._exponent,
                self._root,
                self._generation,
                self._node,
                self.width - start - length,
                self.width - start,
                scratch.require_bits,
            )
