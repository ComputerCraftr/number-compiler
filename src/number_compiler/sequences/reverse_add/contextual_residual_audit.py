"""Family-owned retained-shape audit for contextual residual successors."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunction,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.resources.semantic_composition_payload import agreement
from number_compiler.sequences.reverse_add.active_output import PAIR
from number_compiler.sequences.reverse_add.contextual_residual import (
    ReverseContextualResidualArena,
)


def _atoms(bits: BitFunctionArena) -> dict[int, FactoredFunction]:
    """Read existing primitive constants without publishing proof functions."""
    found: dict[int, FactoredFunction] = {}
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


def audit_reverse_contextual_residual(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate one exact arena and return only direct successor-store members."""
    if (
        type(ledger) is not ResourceLedger
        or type(root) is not ReverseContextualResidualArena
    ):
        raise TypeError("contextual residual audit requires its exact ledger and arena")
    snapshot: OwnedMemoAuditSnapshot[
        tuple[FactoredFunctionID, FactoredFunctionID, FinitePort, FactoredFunctionID],
        FactoredFunctionID,
    ] = root.successor_audit_snapshot()
    owner = snapshot.owner
    if (
        root.ledger is not ledger
        or root.bits.ledger is not ledger
        or snapshot.ledger is not ledger
        or root.successor_audit_container is not snapshot.container
    ):
        return PayloadAuditContribution(invalid=(PayloadAuditEntry(owner, root),))

    atoms = _atoms(root.bits)
    covered: dict[
        tuple[FactoredFunctionID, FactoredFunctionID, FinitePort], set[int]
    ] = {}
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    for key, result in snapshot.payload_view.items():
        try:
            if not is_exact_object_tuple(key) or len(key) != 4:
                raise ValueError("invalid residual successor key")
            before, after, source, residual = key
            if (
                type(before) is not FactoredFunctionID
                or type(after) is not FactoredFunctionID
                or type(residual) is not FactoredFunctionID
                or type(result) is not FactoredFunctionID
            ):
                raise ValueError("invalid residual function identity")
            if type(source) is not FinitePort or source.cardinality != 19:
                raise ValueError("invalid residual source")
            source.__post_init__()
            a, b, old, new = (
                root.bits.resolve(function)
                for function in (before, after, residual, result)
            )
            inputs = tuple(port for port in a.signature.inputs if port != source)
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
            matches: set[int] = set()
            for value, atom in atoms.items():
                replacement = {source.variable: atom}
                if agreement(root.bits.functions, a, replacement, old):
                    if not agreement(root.bits.functions, b, replacement, new):
                        raise ValueError("residual successor does not commute")
                    matches.add(value)
            if not matches:
                raise ValueError("residual is not a source cofactor")
            covered.setdefault((before, after, source), set()).update(matches)
        except (TypeError, ValueError, AttributeError, KeyError, IndexError):
            invalid.append(PayloadAuditEntry(owner, result))
        else:
            approved.extend(
                (PayloadAuditEntry(owner, key), PayloadAuditEntry(owner, result))
            )
    if any(len(values) != 19 for values in covered.values()):
        invalid.append(PayloadAuditEntry(owner, snapshot.container))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["audit_reverse_contextual_residual"]
