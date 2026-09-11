"""Read-only proof of retained contextual residual successor bindings."""

from __future__ import annotations

from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunction,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.semantic_composition_payload import _agreement
from number_compiler.sequences.reverse_add.active_output import PAIR
from number_compiler.sequences.reverse_add.contextual_residual import (
    ReverseContextualResidualArena,
)


def _atoms(bits: BitFunctionArena) -> dict[int, FactoredFunction]:
    """Read the existing primitive constants; never publish proof functions."""
    found = {}
    for record in bits.nodes:
        if record.signature.inputs or record.signature.output != PAIR:
            continue
        valid = bits.functions.resolve(record.valid).terminal
        if valid is None or valid.kind != "atom" or valid.value != 1:
            continue
        value = 0
        for bit, root in enumerate(record.bits):
            terminal = bits.functions.resolve(root).terminal
            if (
                terminal is None
                or terminal.kind != "atom"
                or terminal.value not in (0, 1)
            ):
                break
            value |= terminal.value << bit
        else:
            if value < 19:
                found[value] = record
    return found


def audit_reverse_residuals(
    ledger: object, roots: tuple[object, ...]
) -> set[tuple[int, int]]:
    invalid: set[tuple[int, int]] = set()
    if not isinstance(ledger, ResourceLedger):
        return invalid
    containers = dict(ledger.iter_containers())
    for arena in roots:
        if type(arena) is not ReverseContextualResidualArena:
            continue
        memo = arena._successors
        if (
            arena.ledger is not ledger
            or arena.bits.ledger is not ledger
            or memo.ledger is not ledger
            or containers.get(memo.owner) is not memo._data
        ):
            invalid.add((memo.owner, id(memo)))
            continue
        atoms = _atoms(arena.bits)
        covered: dict[
            tuple[FactoredFunctionID, FactoredFunctionID, FinitePort], set[int]
        ] = {}
        for key, result in memo.items():
            try:
                if type(key) is not tuple or len(key) != 4:
                    raise ValueError("invalid residual successor key")
                before, after, source, residual = key
                if type(source) is not FinitePort or source.cardinality != 19:
                    raise ValueError("invalid residual source")
                source.__post_init__()
                a, b, old, new = (
                    arena.bits.resolve(f) for f in (before, after, residual, result)
                )
                inputs = tuple(p for p in a.signature.inputs if p != source)
                if (
                    source not in a.signature.inputs
                    or a.signature.inputs != b.signature.inputs
                    or a.valid != b.valid
                    or old.signature.inputs != inputs
                    or new.signature.inputs != inputs
                    or old.signature.output != a.signature.output
                    or new.signature.output != b.signature.output
                    or len(atoms) != 19
                ):
                    raise ValueError("residual transport has inconsistent domains")
                matches = set()
                for value, atom in atoms.items():
                    replacement = {source.variable: atom}
                    if _agreement(arena.bits.functions, a, replacement, old):
                        if not _agreement(arena.bits.functions, b, replacement, new):
                            raise ValueError("residual successor does not commute")
                        matches.add(value)
                if not matches:
                    raise ValueError("residual is not a source cofactor")
                covered.setdefault((before, after, source), set()).update(matches)
            except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                invalid.add((memo.owner, id(result)))
        if any(len(values) != 19 for values in covered.values()):
            invalid.add((memo.owner, id(memo._data)))
    return invalid
