import pytest

from number_compiler.hashlife.interfaces.border_macros import (
    BorderFamilyId,
    BorderMacroIdentity,
    BorderMacroKind,
    BorderMacroPhase,
    BorderSourceCursor,
    require_exact_border_join,
)


def _phase(
    owner: object,
    root_in: str,
    root_out: str,
    tick: int,
    phase: int,
    *,
    family: BorderFamilyId = BorderFamilyId.REVERSE_ADD,
) -> BorderMacroPhase:
    identity = BorderMacroIdentity(family, BorderMacroKind.PATH, ((1, 7), (9, 8)))
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


def test_structural_identity_has_no_catalogue_ordinal_and_phase_is_explicit() -> None:
    owner = object()
    first = _phase(owner, "root-a", "root-b", 10, 0)
    second = _phase(owner, "root-b", "root-c", 11, 2)

    assert first.identity == second.identity
    assert first.phase == 0
    assert second.phase == 2
    require_exact_border_join(first, second)


def test_equal_state_labels_do_not_join_different_completed_children() -> None:
    owner = object()
    first = _phase(owner, "root-a", "root-b", 10, 0)
    unrelated = _phase(owner, "root-copy-of-b", "root-c", 11, 2)

    with pytest.raises(ValueError, match="exact completed child"):
        require_exact_border_join(first, unrelated)


def test_macro_identity_is_family_typed_and_rejects_mutable_signatures() -> None:
    with pytest.raises(TypeError, match="immutable typed values"):
        BorderMacroIdentity(
            BorderFamilyId.REVERSE_ADD,
            BorderMacroKind.PATH,
            ([1, 7],),
        )

    owner = object()
    reverse = _phase(owner, "a", "b", 0, 0)
    double = _phase(
        owner,
        "b",
        "c",
        1,
        1,
        family=BorderFamilyId.TWO_REVERSE_TEN,
    )
    with pytest.raises(ValueError, match="exact completed child"):
        require_exact_border_join(reverse, double)


def test_two_tick_phase_can_carry_two_owner_certified_width_births() -> None:
    owner = object()
    identity = BorderMacroIdentity(
        BorderFamilyId.TWO_REVERSE_TEN,
        BorderMacroKind.EDGE,
        ((1, 7), (9, 8)),
    )
    phase = BorderMacroPhase(
        identity,
        0,
        BorderSourceCursor(BorderFamilyId.TWO_REVERSE_TEN, owner, 12, 64, 2, 0),
        BorderSourceCursor(BorderFamilyId.TWO_REVERSE_TEN, owner, 29, 66, 2, 2),
        (1, 7),
        (9, 8),
        5,
        7,
        (11, 11),
        (22, 121),
        physical_span=2,
    )
    assert phase.width_out - phase.width_in == 2
