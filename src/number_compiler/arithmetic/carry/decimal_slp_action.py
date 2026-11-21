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
class DecimalSLPAction:
    """Arena-qualified emitted words and carry exits for one compilation."""

    _arena: LedgerSLPArena
    _generation: int
    _rows: _ActionRows
    _output_nodes: tuple[object, ...]

    def resolve(self, arena: LedgerSLPArena, inlet: int) -> tuple[int, int]:
        """Resolve one row after checking its arena, generation and node."""
        if arena is not self._arena:
            raise ValueError("decimal action belongs to another arena")
        arena.empty()
        if arena.node_id_generation != self._generation:
            raise ValueError("decimal action is stale after arena mutation")
        if type(inlet) is not int or not 0 <= inlet < len(self._rows.exits):
            raise ValueError("incoming carry is outside the action alphabet")
        root = self._rows.outputs[inlet]
        if (
            not 0 <= root < len(arena.nodes)
            or arena.nodes[root] is not self._output_nodes[inlet]
        ):
            raise ValueError("decimal action output no longer belongs to its arena")
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
    identity = _ActionRows(tuple(range(multiplier)), (arena.empty_id,) * multiplier)

    def then(first: _ActionRows, second: _ActionRows) -> _ActionRows:
        return _ActionRows(
            tuple(second.exits[first.exits[c]] for c in range(multiplier)),
            tuple(
                arena.concat(first.outputs[c], second.outputs[first.exits[c]])
                for c in range(multiplier)
            ),
        )

    def atom(digit: int) -> _ActionRows:
        if type(digit) is not int or not 0 <= digit < 10:
            raise ValueError("decimal SLP contains a nondecimal digit")
        rows = tuple(divmod(multiplier * digit + c, 10) for c in range(multiplier))
        return _ActionRows(
            tuple(carry for carry, _ in rows),
            tuple(arena.terminal(output) for _, output in rows),
        )

    def repeat(value: _ActionRows, count: int) -> _ActionRows:
        if count.bit_length() > max_power_bits:
            raise ValueError("decimal SLP repetition exceeds its power budget")
        if not count or value == identity:
            return identity
        # For 2 and 5, each decimal column chooses the outgoing carry from
        # its digit alone. After the first nonempty tile every inlet enters
        # the same steady tile. Retain its emitted word as one repeat node.
        steady = value.exits[0]
        if any(exit_carry != steady for exit_carry in value.exits):
            raise AssertionError(
                "nonempty reflected multiplication tile kept its inlet"
            )
        repeats = arena.repeat(value.outputs[steady], count - 1)
        return _ActionRows(
            value.exits,
            tuple(arena.concat(first, repeats) for first in value.outputs),
        )

    # The temporary result map has one bounded all-inlet row per arena node.
    # Repeated-word outputs are stored in the independently ledgered arena.
    start = len(arena.nodes)
    with (
        cleanup_on_error(lambda: arena.rollback_unpublished_suffix(start)),
        ledger.reservation(scratch_owner, nodes=4 * multiplier * (start + 1)),
    ):
        rows = fold_slp_dag(
            arena,
            root,
            empty_value=identity,
            terminal_value=atom,
            concatenate=then,
            repeat=repeat,
        )
        result = rows[root]
        return DecimalSLPAction(
            arena,
            arena.node_id_generation,
            result,
            tuple(arena.nodes[output] for output in result.outputs),
        )
