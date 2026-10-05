"""Bounded, issued authority records for reverse radial semantic IDs."""

from __future__ import annotations

from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID

SemanticIdentityMemoRecord: TypeAlias = tuple[
    FieldCellActionID,
    int,
    tuple[int, int],
    SemanticIdentity,
    str,
    tuple[object, ...],
]


def build_radial_identity(
    radial: PowerTwoCyclotomicRadialQuotient,
) -> SemanticIdentity:
    if type(radial) is not PowerTwoCyclotomicRadialQuotient:
        raise TypeError("reverse radial identity requires an exact quotient")
    if type(radial.no_growth) is not int or type(radial.growth) is not int:
        raise TypeError("reverse radial identity coordinates require exact integers")
    return SemanticIdentity(
        "reverse-centered-radial-action-v1",
        (
            "reverse-centered-radial-action-v1",
            f"no-growth:{radial.no_growth}",
            f"growth:{radial.growth}",
        ),
    )


def valid_radial_memo(
    reference: FieldCellActionID,
    action_identity: int,
    radial: PowerTwoCyclotomicRadialQuotient,
    record: object,
    issued_record: object,
    owner: ArenaToken,
    kind: str,
    size: int,
) -> bool:
    """Validate a warm record against immutable issued-object authority."""
    if record is not issued_record or type(record) is not tuple or len(record) != 6:
        return False
    source, action_seal, radial_seal, identity, digest, behavior = record
    if (
        type(source) is not FieldCellActionID
        or type(action_seal) is not int
        or type(radial_seal) is not tuple
        or len(radial_seal) != 2
        or type(radial_seal[0]) is not int
        or type(radial_seal[1]) is not int
        or type(identity) is not SemanticIdentity
        or type(digest) is not str
        or type(behavior) is not tuple
    ):
        return False
    try:
        source.validate(owner, kind, size=size)
    except (TypeError, ValueError):
        return False
    return (
        source == reference
        and action_seal == action_identity
        and radial_seal == (radial.no_growth, radial.growth)
        and identity.digest == digest
        and identity.behavior is behavior
        and len(behavior) == 3
        and behavior[0] == "reverse-centered-radial-action-v1"
        and type(behavior[1]) is str
        and behavior[1].startswith("no-growth:")
        and type(behavior[2]) is str
        and behavior[2].startswith("growth:")
    )


__all__ = ["SemanticIdentityMemoRecord", "build_radial_identity", "valid_radial_memo"]
