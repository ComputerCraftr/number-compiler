"""Bounded, issued authority records for reverse radial semantic IDs."""

from __future__ import annotations

from typing import TypeAlias

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityDomain,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.sequences.reverse_add.semantic_tags import (
    REVERSE_CENTERED_RADIAL_ACTION_TAG,
    REVERSE_RADIAL_MULTIPLIER_COMPONENT_TAG,
)

RadialIdentityKey: TypeAlias = tuple[str, int, int, int, tuple[int, ...] | None]
RadialIdentitySeal: TypeAlias = tuple[int, int, RadialIdentityKey, str]
SemanticIdentityMemoRecord: TypeAlias = tuple[
    FieldCellActionID,
    int,
    RadialIdentitySeal,
    SemanticIdentity,
    str,
    tuple[object, ...],
]


def build_radial_identity(
    radial: PowerTwoCyclotomicRadialQuotient,
) -> SemanticIdentity:
    if type(radial) is not PowerTwoCyclotomicRadialQuotient:
        raise TypeError("reverse radial identity requires an exact quotient")
    radial.__post_init__()
    key = radial.canonical_key
    if type(key) is not tuple:
        raise TypeError("reverse radial quotient needs a canonical multiplier key")
    component = SemanticIdentity(
        SemanticIdentityDomain.ANONYMOUS,
        (REVERSE_RADIAL_MULTIPLIER_COMPONENT_TAG, key),
    )
    return SemanticIdentity(
        SemanticIdentityDomain.REVERSE_CENTERED_RADIAL_ACTION,
        (
            REVERSE_CENTERED_RADIAL_ACTION_TAG,
            component,
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
    if (
        record is not issued_record
        or not is_exact_object_tuple(record)
        or len(record) != 6
    ):
        return False
    source, action_seal, radial_seal, identity, digest, behavior = record
    if (
        type(source) is not FieldCellActionID
        or type(action_seal) is not int
        or not is_exact_object_tuple(radial_seal)
        or len(radial_seal) != 4
        or type(radial_seal[0]) is not int
        or type(radial_seal[1]) is not int
        or not is_exact_object_tuple(radial_seal[2])
        or type(radial_seal[3]) is not str
        or type(identity) is not SemanticIdentity
        or type(digest) is not str
        or not is_exact_object_tuple(behavior)
    ):
        return False
    try:
        source.validate(owner, kind, size=size)
    except (TypeError, ValueError):
        return False
    if type(radial) is not PowerTwoCyclotomicRadialQuotient:
        return False
    try:
        radial.__post_init__()
    except (TypeError, ValueError):
        return False
    return (
        source == reference
        and action_seal == action_identity
        and radial_seal[:3] == (radial.no_growth, radial.growth, radial.canonical_key)
        and identity.digest == digest
        and identity.behavior is behavior
        and len(behavior) == 2
        and behavior[0] == REVERSE_CENTERED_RADIAL_ACTION_TAG
        and type(behavior[1]) is SemanticIdentity
        and behavior[1].behavior
        == (REVERSE_RADIAL_MULTIPLIER_COMPONENT_TAG, radial.canonical_key)
        and behavior[1].digest == radial_seal[3]
    )


__all__ = [
    "RadialIdentityKey",
    "RadialIdentitySeal",
    "SemanticIdentityMemoRecord",
    "build_radial_identity",
    "valid_radial_memo",
]
