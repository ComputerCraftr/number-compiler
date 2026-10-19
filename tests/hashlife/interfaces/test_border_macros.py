from dataclasses import dataclass

import pytest

from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.hashlife.interfaces.border_macros import (
    BorderMacroIdentity,
    BorderMacroKind,
    BorderMacroPhase,
    BorderSourceCursor,
    BorderTemporalSpan,
    BorderTemporalUnit,
    BorderWireValue,
    canonical_cycle_rotation,
    require_exact_border_join,
    require_exact_temporal_port_join,
)
from tests.support.assertions import assert_mutation_rejected


@dataclass(frozen=True, slots=True)
class _InterfaceSignature:
    family: FamilyId
    state: tuple[int, int]

    def wire_value(self) -> BorderWireValue:
        return self.state


@dataclass(slots=True)
class _MutableInterfaceSignature:
    family: FamilyId
    state: list[int]

    def wire_value(self) -> BorderWireValue:
        return tuple(self.state)


def _phase(
    owner: object,
    root_in: str,
    root_out: str,
    tick: int,
    phase: int,
    *,
    family: FamilyId = FamilyId.REVERSE_ADD,
) -> BorderMacroPhase:
    identity = BorderMacroIdentity(
        family,
        BorderMacroKind.PATH,
        _InterfaceSignature(family, (1, 7)),
    )
    return BorderMacroPhase(
        identity,
        phase,
        BorderSourceCursor(family, owner, root_in, tick, 1, phase % 4),
        BorderSourceCursor(family, owner, root_out, tick + 1, 1, (phase + 2) % 4),
        (9, 8),
        (1, 7),
        3,
        4,
        (77, 77),
        (22, 121),
    )


def _temporal_span(
    owner: object,
    *,
    family: FamilyId = FamilyId.FERMAT,
    unit: BorderTemporalUnit = BorderTemporalUnit.PHYSICAL_TICKS,
    radix: int = 10,
    position: int = 1,
    offset: int = 0,
    steps: int = 2,
    duration_limit: int = 8,
    clock_horizon: int = 8,
    source_residue: int = 13,
    endpoint_residue: int = 17,
) -> BorderTemporalSpan:
    return BorderTemporalSpan(
        family,
        owner,
        unit,
        radix,
        position,
        offset,
        steps,
        duration_limit,
        clock_horizon,
        source_residue,
        endpoint_residue,
    )


def test_structural_identity_has_no_catalogue_ordinal_and_phase_is_explicit() -> None:
    owner = object()
    first = _phase(owner, "root-a", "root-b", 10, 0)
    second = _phase(owner, "root-b", "root-c", 11, 2)

    assert first.identity == second.identity
    assert first.phase == 0
    assert second.phase == 2
    require_exact_border_join(first, second)


@pytest.mark.parametrize("family", tuple(FamilyId))
def test_shared_metadata_accepts_family_owned_signatures(family: FamilyId) -> None:
    """Metadata has no family whitelist and grants no execution capability."""
    signature = _InterfaceSignature(family, (1, 7))
    identity = BorderMacroIdentity(family, BorderMacroKind.PATH, signature)
    assert identity.checked_signature() is signature
    assert identity.packet()["family"] == family.value


def test_equal_state_labels_do_not_join_different_completed_children() -> None:
    owner = object()
    first = _phase(owner, "root-a", "root-b", 10, 0)
    unrelated = _phase(owner, "root-copy-of-b", "root-c", 11, 2)

    with pytest.raises(ValueError, match="exact completed child"):
        require_exact_border_join(first, unrelated)


def test_macro_identity_requires_typed_family_signature() -> None:
    identity = BorderMacroIdentity(
        FamilyId.REVERSE_ADD,
        BorderMacroKind.PATH,
        _InterfaceSignature(FamilyId.REVERSE_ADD, (1, 7)),
    )

    def valid_identity(value: object) -> bool:
        if type(value) is not BorderMacroIdentity:
            return False
        try:
            value.__post_init__()
        except (TypeError, ValueError):
            return False
        return True

    assert_mutation_rejected(
        identity,
        "signature",
        ([1, 7],),
        valid_identity,
    )

    with pytest.raises(ValueError, match="another family"):
        BorderMacroIdentity(
            FamilyId.REVERSE_ADD,
            BorderMacroKind.PATH,
            _InterfaceSignature(FamilyId.DOUBLE_REVERSE, (1, 7)),
        )

    forged = BorderMacroIdentity(
        FamilyId.REVERSE_ADD,
        BorderMacroKind.PATH,
        _InterfaceSignature(FamilyId.REVERSE_ADD, (1, 7)),
    )
    for untyped_family in ("reverse-add", True):
        object.__setattr__(forged, "family", untyped_family)
        with pytest.raises(TypeError, match="typed owner-law identifier"):
            forged.__post_init__()
    object.__setattr__(forged, "family", FamilyId.REVERSE_ADD)

    owner = object()
    reverse = _phase(owner, "a", "b", 0, 0)
    double = _phase(
        owner,
        "b",
        "c",
        1,
        1,
        family=FamilyId.DOUBLE_REVERSE,
    )
    with pytest.raises(ValueError, match="exact completed child"):
        require_exact_border_join(reverse, double)


def test_macro_identity_rejects_mutable_protocol_signatures() -> None:
    with pytest.raises(TypeError, match="immutable typed record"):
        BorderMacroIdentity(
            FamilyId.REVERSE_ADD,
            BorderMacroKind.PATH,
            _MutableInterfaceSignature(FamilyId.REVERSE_ADD, [1, 7]),
        )


def test_guarded_cycle_ordering_is_total_for_mixed_wire_value_kinds() -> None:
    canonical, offset = canonical_cycle_rotation(
        (1, None), guard_key=lambda value: value
    )

    assert canonical == (None, 1)
    assert offset == 1

    nested, nested_offset = canonical_cycle_rotation(
        (("port", (1, 2)), ("port", (None, 3))),
        guard_key=lambda value: value,
    )
    assert nested == (("port", (None, 3)), ("port", (1, 2)))
    assert nested_offset == 1


def test_macro_identity_packet_and_hash_use_frozen_wire_snapshot() -> None:
    signature = _InterfaceSignature(FamilyId.REVERSE_ADD, (1, 7))
    identity = BorderMacroIdentity(
        FamilyId.REVERSE_ADD, BorderMacroKind.PATH, signature
    )
    packet = identity.packet()
    identity_hash = hash(identity)

    object.__setattr__(signature, "state", (7, 1))
    assert identity.packet() == packet
    assert hash(identity) == identity_hash
    with pytest.raises(ValueError, match="changed after identity creation"):
        identity.checked_signature()

    object.__setattr__(signature, "state", (1, 7))
    assert identity.checked_signature() is signature

    forged = _InterfaceSignature(FamilyId.REVERSE_ADD, (7, 1))
    object.__setattr__(identity, "signature", forged)
    with pytest.raises(ValueError, match="changed after identity creation"):
        identity.__post_init__()
    assert identity.packet() == packet
    object.__setattr__(identity, "signature", signature)


def test_two_tick_phase_can_carry_two_owner_certified_width_births() -> None:
    owner = object()
    identity = BorderMacroIdentity(
        FamilyId.DOUBLE_REVERSE,
        BorderMacroKind.EDGE,
        _InterfaceSignature(FamilyId.DOUBLE_REVERSE, (1, 7)),
    )
    phase = BorderMacroPhase(
        identity,
        0,
        BorderSourceCursor(FamilyId.DOUBLE_REVERSE, owner, 12, 64, 2, 0),
        BorderSourceCursor(FamilyId.DOUBLE_REVERSE, owner, 29, 66, 2, 2),
        (1, 7),
        (9, 8),
        5,
        7,
        (11, 11),
        (22, 121),
        physical_span=2,
    )
    assert phase.width_out - phase.width_in == 2


def test_temporal_port_join_requires_exact_owner_unit_and_coordinate_domain() -> None:
    owner = object()
    first = _temporal_span(owner, offset=0, steps=2, endpoint_residue=17)
    adjacent = _temporal_span(
        owner, offset=2, steps=3, source_residue=17, endpoint_residue=19
    )
    require_exact_temporal_port_join(first, adjacent)

    foreign_owner = _temporal_span(
        object(), offset=2, steps=3, source_residue=17, endpoint_residue=19
    )
    with pytest.raises(ValueError, match="owner or domain"):
        require_exact_temporal_port_join(first, foreign_owner)

    other_unit = _temporal_span(
        owner,
        unit=BorderTemporalUnit.TRACE_SQUARING_STEPS,
        offset=2,
        steps=3,
        source_residue=17,
        endpoint_residue=19,
    )
    with pytest.raises(ValueError, match="owner or domain"):
        require_exact_temporal_port_join(first, other_unit)

    other_radix = _temporal_span(
        owner,
        radix=5,
        offset=2,
        steps=3,
        source_residue=17,
        endpoint_residue=19,
    )
    with pytest.raises(ValueError, match="owner or domain"):
        require_exact_temporal_port_join(first, other_radix)

    other_position = _temporal_span(
        owner,
        position=2,
        offset=2,
        steps=3,
        source_residue=17,
        endpoint_residue=19,
    )
    with pytest.raises(ValueError, match="owner or domain"):
        require_exact_temporal_port_join(first, other_position)


def test_temporal_port_join_checks_family_seam_and_duration() -> None:
    owner = object()
    first = _temporal_span(owner, offset=0, steps=2, endpoint_residue=17)
    mismatched_family = _temporal_span(
        owner,
        family=FamilyId.MERSENNE,
        offset=2,
        steps=3,
        source_residue=17,
        endpoint_residue=19,
    )
    with pytest.raises(ValueError, match="owner or domain"):
        require_exact_temporal_port_join(first, mismatched_family)

    false_seam = _temporal_span(
        owner, offset=2, steps=3, source_residue=18, endpoint_residue=19
    )
    with pytest.raises(ValueError, match="endpoint seam"):
        require_exact_temporal_port_join(first, false_seam)

    first_short_limit = _temporal_span(
        owner,
        offset=0,
        steps=2,
        duration_limit=4,
        endpoint_residue=17,
    )
    too_long = _temporal_span(
        owner,
        offset=2,
        steps=3,
        duration_limit=4,
        source_residue=17,
        endpoint_residue=19,
    )
    with pytest.raises(ValueError, match="duration limit"):
        require_exact_temporal_port_join(first_short_limit, too_long)

    with pytest.raises(ValueError, match="duration bound"):
        _temporal_span(
            owner,
            offset=7,
            steps=2,
            clock_horizon=8,
            source_residue=17,
            endpoint_residue=19,
        )


def test_temporal_span_keeps_coordinates_as_bounded_producer_metadata() -> None:
    owner = object()
    span = _temporal_span(
        owner,
        position=100_000,
        source_residue=0,
        endpoint_residue=1,
    )
    assert span.position == 100_000

    with pytest.raises(ValueError):
        _temporal_span(owner, radix=True)
    with pytest.raises(ValueError):
        _temporal_span(owner, position=True)
    with pytest.raises(ValueError):
        _temporal_span(owner, source_residue=True)
    with pytest.raises(ValueError):
        _temporal_span(owner, endpoint_residue=-1)
