"""Small helpers shared by retained-payload audits."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import fields, is_dataclass
from typing import cast

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items

ProofPayloadAuditor = Callable[[ResourceLedger], set[tuple[int, int]]]

_PROOF_GEOMETRY_FIELDS: dict[type[object], frozenset[str]] = {}
_PROOF_OPAQUE_TYPES: set[type[object]] = set()
_PROOF_PAYLOAD_AUDITORS: list[ProofPayloadAuditor] = []


def register_proof_geometry_fields(
    definitions: Mapping[type[object], frozenset[str]],
) -> None:
    """Register geometry-only fields when proof tooling is explicitly loaded.

    The resource layer deliberately does not import proof executors.  A proof
    module that is used by a caller registers its concrete record types here,
    preserving payload-audit precision without making ordinary production
    metric collection load the quarantined implementation.
    """
    _PROOF_GEOMETRY_FIELDS.update(definitions)


def proof_geometry_fields() -> dict[type[object], frozenset[str]]:
    """Return a copy of the proof record policies registered in this process."""
    return dict(_PROOF_GEOMETRY_FIELDS)


def register_proof_opaque_types(*definitions: type[object]) -> None:
    """Register bounded scalar proof records that have no traversable payload."""
    _PROOF_OPAQUE_TYPES.update(definitions)


def proof_opaque_types() -> tuple[type[object], ...]:
    """Return bounded proof scalar types registered in this process."""
    return tuple(_PROOF_OPAQUE_TYPES)


def register_proof_payload_auditor(auditor: ProofPayloadAuditor) -> None:
    """Register an independent audit owned by explicitly loaded proof code."""
    if auditor not in _PROOF_PAYLOAD_AUDITORS:
        _PROOF_PAYLOAD_AUDITORS.append(auditor)


def audit_registered_proof_payloads(ledger: ResourceLedger) -> set[tuple[int, int]]:
    """Run only auditors already registered by explicitly imported proof code."""
    invalid: set[tuple[int, int]] = set()
    for auditor in tuple(_PROOF_PAYLOAD_AUDITORS):
        invalid.update(auditor(ledger))
    return invalid


def proof_objects(root: object) -> set[int]:
    """Find quarantined oracle objects even behind source-role declarations."""
    found: set[int] = set()
    seen: set[int] = set()
    pending = [root]
    while pending:
        value = pending.pop()
        identity = id(value)
        if identity in seen:
            continue
        seen.add(identity)
        if type(value).__module__.startswith("devtools.verification."):
            found.add(identity)
        elif isinstance(value, Mapping):
            mapping = cast(Mapping[object, object], value)
            pending.extend(
                item for pair in audit_mapping_items(mapping) for item in pair
            )
        elif isinstance(value, (Sequence, set, frozenset)) and not isinstance(
            value, (str, bytes)
        ):
            pending.extend(cast(Iterable[object], value))
        elif is_dataclass(value) and not isinstance(value, type):
            pending.extend(
                cast(object, getattr(value, item.name)) for item in fields(value)
            )
    return found


__all__ = [
    "audit_registered_proof_payloads",
    "proof_geometry_fields",
    "proof_objects",
    "proof_opaque_types",
    "register_proof_geometry_fields",
    "register_proof_opaque_types",
    "register_proof_payload_auditor",
]
