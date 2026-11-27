"""All-inlet decimal multiplication actions over a ledger-owned SLP."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_on_error


@dataclass(frozen=True, slots=True)
class _ActionRows:
    """Unpublished rows valid within a single compilation."""

    exits: tuple[int, ...]
    outputs: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _ResetWord:
    """A zero-inlet first digit, common suffix, and constant carry exit."""

    first: int
    tail: int
    outgoing: int


@dataclass(frozen=True, slots=True)
class DecimalSLPAction:
    """Arena-qualified source and emitted words for one compilation."""

    _arena: LedgerSLPArena
    _source_root: int
    _source_node: object
    _rows: _ActionRows
    _output_nodes: tuple[object, ...]

    def resolve(self, arena: LedgerSLPArena, inlet: int) -> tuple[int, int]:
        """Resolve one row after authenticating its source and output nodes."""
        if arena is not self._arena:
            raise ValueError("decimal action belongs to another arena")
        arena.empty()
        if arena.node_storage_poisoned:
            raise ValueError("decimal action is stale after arena mutation")
        if type(inlet) is not int or not 0 <= inlet < len(self._rows.exits):
            raise ValueError("incoming carry is outside the action alphabet")
        if (
            not 0 <= self._source_root < len(arena.nodes)
            or arena.nodes[self._source_root] is not self._source_node
        ):
            raise ValueError("decimal action is stale after source reclamation")
        root = self._rows.outputs[inlet]
        if (
            not 0 <= root < len(arena.nodes)
            or arena.nodes[root] is not self._output_nodes[inlet]
        ):
            raise ValueError("decimal action is stale after output reclamation")
        return root, self._rows.exits[inlet]


def multiply_decimal_slp(
    arena: LedgerSLPArena,
    root: int,
    multiplier: int,
    ledger: ResourceLedger,
    scratch_owner: int,
    *,
    max_power_bits: int = 4096,
) -> DecimalSLPAction:
    """Compile a decimal digit word in multiplication order for every inlet.

    Output roots belong to the supplied arena. A failure rolls its newly
    interned suffix back before returning control to the publisher.
    """
    if type(multiplier) is not int or multiplier not in (2, 5):
        raise ValueError("decimal multiplier must be 2 or 5")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("invalid decimal SLP root")
    if arena.ledger is not ledger:
        raise ValueError("decimal action requires the arena's ledger")
    if type(max_power_bits) is not int or max_power_bits < 1:
        raise ValueError("decimal action power budget must be positive")
    identity = _ResetWord(-1, arena.empty_id, 0)

    def word(value: _ResetWord, inlet: int) -> int:
        if value.first < 0:
            return arena.empty_id
        return arena.concat(arena.terminal(value.first + inlet), value.tail)

    def then(first: _ResetWord, second: _ResetWord) -> _ResetWord:
        if first.first < 0:
            return second
        if second.first < 0:
            return first
        return _ResetWord(
            first.first,
            arena.concat(first.tail, word(second, first.outgoing)),
            second.outgoing,
        )

    def atom(digit: int) -> _ResetWord:
        if type(digit) is not int or not 0 <= digit < 10:
            raise ValueError("decimal SLP contains a nondecimal digit")
        carry, first = divmod(multiplier * digit, 10)
        return _ResetWord(first, arena.empty_id, carry)

    def repeat(value: _ResetWord, count: int) -> _ResetWord:
        if count.bit_length() > max_power_bits:
            raise ValueError("decimal SLP repetition exceeds its power budget")
        if not count or value.first < 0:
            return identity
        if count == 1:
            return value
        steady = word(value, value.outgoing)
        return _ResetWord(
            value.first,
            arena.concat(value.tail, arena.repeat(steady, count - 1)),
            value.outgoing,
        )

    # One reset action is retained per node. Inlet variants are issued only
    # at the root, while the common suffix belongs to the ledgered arena.
    start = len(arena.nodes)
    with (
        cleanup_on_error(lambda: arena.rollback_unpublished_suffix(start)),
        ledger.reservation(scratch_owner, nodes=8 * (start + 1)),
    ):
        rows = fold_slp_dag(
            arena,
            root,
            empty_value=identity,
            terminal_value=atom,
            concatenate=then,
            repeat=repeat,
        )
        value = rows[root]
        result = _ActionRows(
            tuple(range(multiplier))
            if value.first < 0
            else (value.outgoing,) * multiplier,
            tuple(word(value, inlet) for inlet in range(multiplier)),
        )
        return DecimalSLPAction(
            arena,
            root,
            arena.nodes[root],
            result,
            tuple(arena.nodes[output] for output in result.outputs),
        )
