"""Charged semantic-domain registry for the shared recursive image arena."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherLocalInterfaceArena,
    )

# Both owners validate allocated signatures and complete local interfaces.
# The sum type preserves their distinct records without coercing higher ports
# into the finite Diamond representation.
FieldInterfaceArena: TypeAlias = "DiamondQuotientArena | HigherLocalInterfaceArena"


@dataclass(frozen=True, slots=True)
class FieldImageDomain:
    action_owner: ArenaToken
    action_kind: str
    action_validate: Callable[[FieldCellActionID], object]
    action_authority: object | None
    interfaces: FieldInterfaceArena
    signature_kind: str
    output_owner: ArenaToken
    output_kind: str
    output_validate: Callable[[CoordinateOutputMorphismID], object]
    signature_for: Callable[[FieldCellActionID, FieldGeometryID], PortSignatureID]
    signature_authority: object | None


@dataclass(frozen=True, slots=True)
class FieldImageDomainKey:
    role: str
    owner: ArenaToken
    kind: str


@dataclass(frozen=True, slots=True)
class FieldImageInterfaceAuthority:
    arena: FieldInterfaceArena
    signature_kind: str


@dataclass(frozen=True, slots=True)
class FieldImageOutputAuthority:
    owner: ArenaToken
    kind: str
    validate: Callable[[CoordinateOutputMorphismID], object]
    authority: object | None


FieldImageDomainEntry: TypeAlias = (
    FieldImageDomain | FieldImageInterfaceAuthority | FieldImageOutputAuthority
)


def validate_field_image_authorities(
    ledger: ResourceLedger,
    action_authority: object,
    action_validate: Callable[[FieldCellActionID], object],
    output_authority: object,
    output_validate: Callable[[CoordinateOutputMorphismID], object],
    signature_authority: object,
    signature_for: Callable[[FieldCellActionID, FieldGeometryID], PortSignatureID],
) -> None:
    """Require bound validators backed by actual index-owned arena stores."""
    roots = tuple(ledger.iter_execution_roots())
    containers = tuple(value for _, value in ledger.iter_containers())
    for authority, validator, role in (
        (action_authority, action_validate, "action"),
        (output_authority, output_validate, "output"),
        (signature_authority, signature_for, "signature"),
    ):
        if (
            not any(root is authority for root in roots)
            or getattr(authority, "ledger", None) is not ledger
        ):
            raise ValueError(f"field image {role} authority is not an index arena")
        if getattr(validator, "__self__", None) is not authority:
            raise TypeError(f"field image {role} validator is not authority-bound")
        if role != "signature" and not any(
            value is container
            for value in vars(authority).values()
            for container in containers
        ):
            raise ValueError(
                f"field image {role} authority owns no registered arena store"
            )


def register_field_image_domain(
    ledger: ResourceLedger,
    owner: int,
    domains: MutableMapping[FieldImageDomainKey, FieldImageDomainEntry],
    interfaces: FieldInterfaceArena,
    *,
    action_owner: ArenaToken,
    action_kind: str,
    action_validate: Callable[[FieldCellActionID], object],
    output_owner: ArenaToken,
    output_kind: str,
    output_validate: Callable[[CoordinateOutputMorphismID], object],
    signature_kind: str,
    signature_for: Callable[[FieldCellActionID, FieldGeometryID], PortSignatureID],
    action_authority: object | None,
    output_authority: object | None,
    signature_authority: object | None,
) -> None:
    """Validate, reserve, and atomically add one exact semantic domain."""
    if interfaces.ledger is not ledger:
        raise ValueError("field image domains require one index ledger")
    if type(action_owner) is not ArenaToken or type(output_owner) is not ArenaToken:
        raise TypeError("field image domains require exact arena owners")
    if any(
        type(value) is not str or not value
        for value in (action_kind, output_kind, signature_kind)
    ):
        raise ValueError("field image domains require nonempty semantic sorts")
    if not all(
        callable(item)
        for item in (
            action_validate,
            output_validate,
            signature_for,
        )
    ):
        raise TypeError("field image domains require allocated validators")
    action_key = FieldImageDomainKey("action", action_owner, action_kind)
    if action_key in domains:
        raise ValueError("field action sort is already registered")
    if any(
        item is None
        for item in (
            action_authority,
            output_authority,
            signature_authority,
        )
    ):
        raise ValueError("field image domains require owning authorities")
    assert action_authority is not None
    assert output_authority is not None
    assert signature_authority is not None
    validate_field_image_authorities(
        ledger,
        action_authority,
        action_validate,
        output_authority,
        output_validate,
        signature_authority,
        signature_for,
    )
    interface_key = FieldImageDomainKey(
        "interface",
        interfaces.owner,
        interfaces.interface_kind,
    )
    output_key = FieldImageDomainKey("output", output_owner, output_kind)
    interface_authority = FieldImageInterfaceAuthority(interfaces, signature_kind)
    existing_interface = domains.get(interface_key)
    if existing_interface is not None and existing_interface != interface_authority:
        raise ValueError("local interface sort has another image authority")
    output_record = FieldImageOutputAuthority(
        output_owner,
        output_kind,
        output_validate,
        output_authority,
    )
    existing_output = domains.get(output_key)
    if existing_output is not None and (
        type(existing_output) is not FieldImageOutputAuthority
        or existing_output.authority is not output_authority
        or getattr(existing_output.validate, "__self__", None)
        is not getattr(output_validate, "__self__", None)
        or getattr(existing_output.validate, "__func__", existing_output.validate)
        is not getattr(output_validate, "__func__", output_validate)
    ):
        raise ValueError("coordinate output sort has another image authority")
    domain = FieldImageDomain(
        action_owner,
        action_kind,
        action_validate,
        action_authority,
        interfaces,
        signature_kind,
        output_owner,
        output_kind,
        output_validate,
        signature_for,
        signature_authority,
    )
    additions: list[tuple[FieldImageDomainKey, FieldImageDomainEntry]] = [
        (action_key, domain)
    ]
    if existing_interface is None:
        additions.append((interface_key, interface_authority))
    if existing_output is None:
        additions.append((output_key, output_record))
    ledger.reserve(owner, entries=len(additions))
    for key, value in additions:
        domains[key] = value


__all__ = [
    "FieldImageDomain",
    "FieldImageDomainEntry",
    "FieldImageDomainKey",
    "FieldImageInterfaceAuthority",
    "FieldImageOutputAuthority",
    "FieldInterfaceArena",
    "register_field_image_domain",
]
