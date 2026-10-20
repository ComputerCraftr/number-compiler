"""Two-input Q19 carry-normalization port fold for exact modular endpoints.

A reverse/add pair word has palindromic coefficients s_i in 0..18 and the
physical successor is the decimal normalization of sum(s_i*10**i).
This fold evaluates both incoming carry values on an interned CONCAT/REPEAT
SLP, including numeric forward and reversed emissions.  A repeated run is
handled by exponentiation by squaring, not by enumerating its symbols.

The output of this module is *only* a numerical projection of an already
source-authenticated Q19 occurrence.  It cannot certify a future temporal
return or a shortcut across unvisited generations.
"""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )


@dataclass(frozen=True, slots=True)
class DecimalPairNumericPort:
    """One carry-Mealy block with both possible incoming carry values.

    ``forward`` weights emitted digits LSD-first; ``reversed`` weights them in
    reverse spatial order. Both coefficients are residues modulo ``modulus``.
    """

    length: int
    forward: tuple[int, int]
    reversed: tuple[int, int]
    outgoing: tuple[int, int]
    modulus: int

    @classmethod
    def identity(cls, modulus: int) -> DecimalPairNumericPort:
        return cls(0, (0, 0), (0, 0), (0, 1), modulus)

    @classmethod
    def atom(cls, symbol: int, modulus: int) -> DecimalPairNumericPort:
        if type(symbol) is not int or not 0 <= symbol <= 18:
            raise ValueError("Q19 digit pair must lie in 0..18")
        outgoing: tuple[int, int] = (int(symbol >= 10), int(symbol >= 9))
        digits: tuple[int, int] = (
            symbol - 10 * outgoing[0],
            symbol + 1 - 10 * outgoing[1],
        )
        return cls(1, digits, digits, outgoing, modulus)

    def then(
        self,
        high: DecimalPairNumericPort,
        *,
        ledger: ResourceLedger | None = None,
    ) -> DecimalPairNumericPort:
        """Append a higher-position block to a lower-position block."""
        if type(high) is not DecimalPairNumericPort or high.modulus != self.modulus:
            raise ValueError("Q19 numeric ports must use the same residue ring")
        m = self.modulus
        low_shift = pow(10, self.length, m)
        high_shift = pow(10, high.length, m)
        out = (
            high.outgoing[self.outgoing[0]],
            high.outgoing[self.outgoing[1]],
        )
        forward = (
            (self.forward[0] + low_shift * high.forward[self.outgoing[0]]) % m,
            (self.forward[1] + low_shift * high.forward[self.outgoing[1]]) % m,
        )
        reversed_values = (
            (high_shift * self.reversed[0] + high.reversed[self.outgoing[0]]) % m,
            (high_shift * self.reversed[1] + high.reversed[self.outgoing[1]]) % m,
        )
        if ledger is not None:
            ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_COMPOSITIONS)
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OPERAND_BITS,
                self.length.bit_length()
                + high.length.bit_length()
                + m.bit_length()
                + sum(
                    value.bit_length()
                    for value in (
                        *self.forward,
                        *self.reversed,
                        *self.outgoing,
                        *high.forward,
                        *high.reversed,
                        *high.outgoing,
                    )
                ),
            )
        return DecimalPairNumericPort(
            self.length + high.length, forward, reversed_values, out, m
        )

    def repeat(
        self, count: int, *, ledger: ResourceLedger | None = None
    ) -> DecimalPairNumericPort:
        if type(count) is not int or count < 0:
            raise ValueError("Q19 numeric repeat count must be nonnegative")
        result = self.identity(self.modulus)
        power = self
        while count:
            if count & 1:
                result = result.then(power, ledger=ledger)
            count >>= 1
            if count:
                power = power.then(power, ledger=ledger)
        return result


@dataclass(frozen=True, slots=True)
class PairWordNumericSummary:
    """Forward/reversed pair SLP and its last-symbol-punctured reverse."""

    forward: DecimalPairNumericPort
    backward: DecimalPairNumericPort
    prefix_forward: DecimalPairNumericPort
    prefix_backward: DecimalPairNumericPort

    @property
    def length(self) -> int:
        return self.forward.length


@contextmanager
def _numeric_fold_workspace(
    ledger: ResourceLedger, workspace_owner: int, node_bound: int
) -> Generator[
    tuple[dict[int, PairWordNumericSummary], list[tuple[int, bool]]], None, None
]:
    """Reserve temporary fold maps and clear them on success or failure."""
    with ledger.reservation(
        workspace_owner,
        entries=4 * (node_bound + 1),
        nodes=8 * (node_bound + 1),
    ):
        memo: dict[int, PairWordNumericSummary] = {}
        tasks: list[tuple[int, bool]] = []
        try:
            yield memo, tasks
        finally:
            tasks.clear()
            memo.clear()


def fold_pair_slp(
    arena: SLPArena,
    root: int,
    *,
    modulus: int,
    ledger: ResourceLedger,
    workspace_owner: int,
) -> PairWordNumericSummary:
    """Fold Q19 symbols in one nonrecursive DAG pass, ignoring parity tags."""
    if type(modulus) is not int or modulus < 2:
        raise ValueError("modulus must be a positive integer >=2")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("Q19 pair SLP root is invalid")
    if type(ledger) is not ResourceLedger:
        raise TypeError("Q19 numeric fold requires its execution ledger")
    node_bound = len(arena.nodes)
    zero = DecimalPairNumericPort.identity(modulus)
    identity = PairWordNumericSummary(zero, zero, zero, zero)
    with _numeric_fold_workspace(ledger, workspace_owner, node_bound) as (
        memo,
        tasks,
    ):
        tasks.append((root, False))
        while tasks:
            node_id, ready = tasks.pop()
            if node_id in memo:
                continue
            ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_NODE_VISITS)
            node = arena.nodes[node_id]
            if not ready:
                tasks.append((node_id, True))
                if node.kind == "CONCAT":
                    if node.right not in memo:
                        tasks.append((node.right, False))
                    if node.left not in memo:
                        tasks.append((node.left, False))
                elif node.kind == "REPEAT" and node.child not in memo:
                    tasks.append((node.child, False))
                continue
            if node.kind == "EMPTY":
                value = identity
            elif node.kind == "TERM":
                if 0 <= node.symbol <= 18:
                    atom = DecimalPairNumericPort.atom(node.symbol, modulus)
                    ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OPERAND_BITS,
                        node.symbol.bit_length() + modulus.bit_length(),
                    )
                    value = PairWordNumericSummary(atom, atom, zero, zero)
                else:
                    if node.symbol not in (19, 20, 21):
                        raise ValueError("Q19 SLP contains an unknown marker")
                    value = identity
            elif node.kind == "CONCAT":
                left, right = memo[node.left], memo[node.right]
                forward = left.forward.then(right.forward, ledger=ledger)
                backward = right.backward.then(left.backward, ledger=ledger)
                if right.length:
                    prefix_forward = left.forward.then(
                        right.prefix_forward, ledger=ledger
                    )
                    prefix_backward = right.prefix_backward.then(
                        left.backward, ledger=ledger
                    )
                else:
                    prefix_forward, prefix_backward = (
                        left.prefix_forward,
                        left.prefix_backward,
                    )
                value = PairWordNumericSummary(
                    forward, backward, prefix_forward, prefix_backward
                )
            elif node.kind == "REPEAT":
                child = memo[node.child]
                count = node.count
                if count < 1:
                    raise ValueError("Q19 repeated SLP must have positive count")
                forward = child.forward.repeat(count, ledger=ledger)
                backward = child.backward.repeat(count, ledger=ledger)
                if child.length:
                    prefix_forward = child.forward.repeat(
                        count - 1, ledger=ledger
                    ).then(child.prefix_forward, ledger=ledger)
                    prefix_backward = child.prefix_backward.then(
                        child.backward.repeat(count - 1, ledger=ledger),
                        ledger=ledger,
                    )
                else:
                    prefix_forward = prefix_backward = zero
                value = PairWordNumericSummary(
                    forward, backward, prefix_forward, prefix_backward
                )
            else:
                raise ValueError("unrecognized Q19 SLP node type")
            memo[node_id] = value
        result = memo[root]
        ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OUTPUT_FIELDS, 16)
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OUTPUT_BITS,
            sum(
                number.bit_length()
                for summary in (
                    result.forward,
                    result.backward,
                    result.prefix_forward,
                    result.prefix_backward,
                )
                for number in (
                    summary.length,
                    *summary.forward,
                    *summary.reversed,
                    *summary.outgoing,
                    summary.modulus,
                )
            ),
        )
        return result


@dataclass(frozen=True, slots=True)
class ReversePairNumericProjection:
    """Physical Q19 successor and reversal modulo a declared modulus."""

    modulus: int
    output_width: int
    target_mod: int
    reverse_target_mod: int
    pair_carry_out: int
    q19_root: int
    temporal_steps: int


def project_q19_numeric(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    *,
    modulus: int,
) -> ReversePairNumericProjection:
    """Read an authenticated Q19 action without enumerating its output digits."""
    owner.validate(occurrence)
    if type(modulus) is not int or modulus < 2:
        raise ValueError("Q19 numeric modulus must be an integer >=2")
    # The immutable arena's encoded half contains the whole pair field's
    # unique coefficients; the physical mirrored half is reconstructed as an
    # action of the *reversed* half port (not an expanded digit string).
    from number_compiler.arithmetic.automata.slp_walks import symbol_at

    parity = symbol_at(owner.arena, occurrence.root, 0) - 19
    if parity not in (0, 1):
        raise ValueError("Q19 encoded half has an invalid center parity")
    half = fold_pair_slp(
        owner.arena,
        occurrence.root,
        modulus=modulus,
        ledger=owner.ledger,
        workspace_owner=owner.scratch_owner,
    )
    with owner.ledger.reservation(owner.scratch_owner, entries=32, nodes=32):
        full = half.forward.then(
            half.prefix_backward if parity else half.backward,
            ledger=owner.ledger,
        )
        if full.length != occurrence.pair_width:
            raise AssertionError("numeric port fold disagrees with Q19 pair width")
        growth = full.outgoing[0]
        if growth != occurrence.output_width - occurrence.pair_width:
            raise AssertionError("Q19 port fold and authenticated growth disagree")
        target = (full.forward[0] + growth * pow(10, full.length, modulus)) % modulus
        reverse = (growth + pow(10, growth, modulus) * full.reversed[0]) % modulus
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_MODULAR_PROJECTIONS)
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OUTPUT_FIELDS, 7)
    owner.ledger.bump(
        _reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_OUTPUT_BITS,
        sum(
            number.bit_length()
            for number in (
                modulus,
                occurrence.output_width,
                target,
                reverse,
                growth,
                occurrence.root,
                occurrence.temporal_steps,
            )
        ),
    )
    return ReversePairNumericProjection(
        modulus,
        occurrence.output_width,
        target,
        reverse,
        growth,
        occurrence.root,
        occurrence.temporal_steps,
    )


__all__ = [
    "DecimalPairNumericPort",
    "PairWordNumericSummary",
    "ReversePairNumericProjection",
    "fold_pair_slp",
    "project_q19_numeric",
]
