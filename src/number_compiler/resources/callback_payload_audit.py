"""Detect exact future payloads hidden behind retained execution callbacks."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import fields, is_dataclass
from functools import partial
from types import FunctionType, MethodType, ModuleType

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan, DyadicTile
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items

_PAYLOAD_NAMES = frozenset(
    {
        "digits",
        "tail",
        "slab",
        "cut",
        "h_rows",
        "carry_rows",
        "carry_tape",
        "carry_outputs",
        "coefficient_tape",
        "coefficients",
        "future",
        "future_word",
        "whole_word",
        "output_span",
        "target_span",
        "normalized_tail",
        "packed_history",
        "affine_b",
        "b_program",
        "complete_b",
        "offset_ports",
        "tile_ports",
    }
)


def _payload_name(name: str) -> bool:
    normalized = name.lower().strip("_")
    if any(
        part in normalized
        for part in (
            "future_behavior",
            "future_profile",
            "future_class",
            "future_certificate",
            "future_admission",
            "future_snapshot",
            "future_work",
        )
    ):
        return False
    return normalized in _PAYLOAD_NAMES or any(
        part in _PAYLOAD_NAMES for part in normalized.split("_")
    )


def audit_callback_future_payloads(
    ledger: ResourceLedger,
) -> frozenset[tuple[int, int]]:
    """Return callback-reachable exact future objects outside source authority.

    Source geometry may legitimately retain its original span.  Therefore an
    exact tile is rejected here only when the closure/attribute path explicitly
    identifies it as a future digit, tail, slab, carry, coefficient, or target
    payload. Registered container contents are audited by the main inventory.
    """
    violations: set[tuple[int, int]] = set()
    seen: set[tuple[int, bool, bool]] = set()
    dataclass_fields: dict[type[object], tuple[tuple[str, bool], ...]] = {}
    non_dataclasses: set[type[object]] = set()
    registered = {id(value): owner for owner, value in ledger.iter_containers()}
    roles = {item.owner: item.role for item in ledger.inventory()}
    certified_future_roles = frozenset(
        {
            "future_behavior_profile",
            "future_behavior_profile_interner",
            "future_behavior_class",
            "future_behavior_class_interner",
            "future_behavior_certificate",
            "future_behavior_admission",
            "future_behavior_publication_snapshot",
            "future_behavior_workspace",
        }
    )
    pending = [(root, False, False) for root in ledger.iter_execution_roots()]
    while pending:
        value, callback_scope, suspicious = pending.pop()
        marker = id(value), callback_scope, suspicious
        if marker in seen:
            continue
        seen.add(marker)
        # A callback may use its owning ledger for work accounting.  The
        # ledger's registered containers are audited independently through
        # their declared owners; traversing back through the ledger here
        # incorrectly reclassifies immutable source digits as callback-owned
        # future payloads.
        if value is ledger:
            continue
        registered_owner = registered.get(id(value))
        if registered_owner is not None and (
            not suspicious or roles.get(registered_owner) in certified_future_roles
        ):
            # Store contents are validated by the owner-aware payload pass.
            # A callback reference does not change that ownership. Suspiciously
            # named captures still cross the boundary so they cannot disguise
            # a future payload in an otherwise valid store.
            continue
        if suspicious and type(value) is int:
            # Coordinates and exponents are allowed metadata, but callbacks
            # must not retain a value named as a complete future word/tail or
            # affine B payload.  The semantic name supplies the distinction;
            # accepting a small value here would make the invariant depend on
            # the particular query rather than the representation.
            violations.add((-1, id(value)))
            continue
        if value is None or isinstance(
            value, (str, bytes, int, float, bool, type, ModuleType)
        ):
            continue
        if isinstance(value, ExactSource):
            continue
        if isinstance(value, (DyadicSpan, DyadicTile)):
            if suspicious:
                violations.add((-1, id(value)))
            continue
        if isinstance(value, partial):
            pending.extend(
                (
                    (value.func, True, suspicious),
                    (value.args, True, suspicious),
                    (value.keywords, True, suspicious),
                )
            )
            continue
        if isinstance(value, MethodType):
            pending.extend(
                ((value.__self__, True, suspicious), (value.__func__, True, suspicious))
            )
            continue
        if isinstance(value, FunctionType):
            names = value.__code__.co_freevars
            for name, cell in zip(names, value.__closure__ or (), strict=True):
                try:
                    child = cell.cell_contents
                except ValueError:
                    continue
                pending.append((child, True, suspicious or _payload_name(name)))
            pending.append((value.__defaults__, True, suspicious))
            pending.append((value.__kwdefaults__, True, suspicious))
            continue
        if suspicious and (
            isinstance(value, Mapping)
            and value
            and all(type(item) is int for item in value.values())
            or isinstance(value, (Sequence, set, frozenset))
            and value
            and all(type(item) is int for item in value)
        ):
            violations.add((-1, id(value)))
        if isinstance(value, Mapping):
            pending.extend(
                (child, callback_scope, suspicious)
                for pair in audit_mapping_items(value)
                for child in pair
            )
            continue
        if isinstance(value, (Sequence, set, frozenset)):
            pending.extend((child, callback_scope, suspicious) for child in value)
            continue
        value_type = type(value)
        layout = dataclass_fields.get(value_type)
        if layout is None and value_type not in non_dataclasses:
            try:
                if not is_dataclass(value):
                    raise TypeError
                layout = tuple(
                    (field.name, _payload_name(field.name)) for field in fields(value)
                )
            except TypeError:
                non_dataclasses.add(value_type)
            else:
                dataclass_fields[value_type] = layout
        if layout is not None:
            pending.extend(
                (
                    getattr(value, name),
                    callback_scope,
                    suspicious or callback_scope and named_payload,
                )
                for name, named_payload in layout
            )
            continue
        try:
            attributes = vars(value)
        except TypeError:
            attributes = {}
        pending.extend(
            (
                child,
                callback_scope,
                suspicious or callback_scope and _payload_name(name),
            )
            for name, child in attributes.items()
            if child is not ledger
        )
    return frozenset(violations)


__all__ = ["audit_callback_future_payloads"]
