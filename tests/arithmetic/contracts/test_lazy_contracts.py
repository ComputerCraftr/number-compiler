"""Lazy references cannot be confused across arenas or with explicit endpoints."""

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    CarryBit,
    ExactEndpoint,
    ExactSource,
    FrameTransform,
    LazyFieldRef,
    LoweringCapability,
    MaterializedEndpoint,
    TransferSummaryID,
    WordLimb,
)


def test_equal_local_ids_do_not_alias_between_arenas() -> None:
    first, second = ArenaToken("same-label"), ArenaToken("same-label")
    a, b = ArenaHandle(first, "program", 0), ArenaHandle(second, "program", 0)
    assert a != b and len({a, b}) == 2
    assert a.validate(first, "program") is a
    with pytest.raises(ValueError):
        a.validate(second, "program")
    with pytest.raises(ValueError):
        a.validate(first, "summary")
    with pytest.raises(ValueError):
        ArenaHandle(first, "program", -1)


def test_source_alphabet_is_explicit_and_future_geometry_has_no_payload() -> None:
    source = ExactSource((18, 4), 10, orbit="reverse-pair", alphabet_size=19)
    assert source.base == 10 and source.digits == (18, 4)
    with pytest.raises(ValueError):
        ExactSource((18,), 10)
    owner = ArenaToken()
    future = LazyFieldRef(
        ArenaHandle(owner, "source", 0),
        ActionProgramID(owner, "program", 1),
        FrameTransform(10**100, True),
        10**200,
    )
    assert not hasattr(future, "digits") and not hasattr(future, "span")
    assert future.frame.shift == 10**100


def test_exact_endpoint_requires_same_arena_lowering_capability() -> None:
    owner = ArenaToken()
    future = LazyFieldRef(
        ArenaHandle(owner, "source", 0), ActionProgramID(owner, "program", 1)
    )
    with pytest.raises(ValueError):
        ExactEndpoint(future, (1, 2), 10, LoweringCapability(ArenaToken()))
    output = ExactEndpoint(future, (1, 2), 10, LoweringCapability(owner))
    assert output.digits == (1, 2)
    assert isinstance(output, MaterializedEndpoint)


def test_action_and_transfer_handles_are_runtime_distinct() -> None:
    owner = ArenaToken()
    action = ActionProgramID(owner, "program", 0)
    summary = TransferSummaryID(owner, "program", 0)
    assert cast(ArenaHandle, action) != summary
    assert not isinstance(summary, ActionProgramID)
    with pytest.raises(TypeError):
        LazyFieldRef(ArenaHandle(owner, "source", 0), cast("ActionProgramID", summary))
    with pytest.raises(ValueError):
        LazyFieldRef(ArenaHandle(ArenaToken(), "source", 0), action)
    with pytest.raises(ValueError):
        action.validate(owner, "program", size=0)


def test_local_payload_bounds_are_enforced() -> None:
    assert WordLimb((1 << 64) - 1).bits == 64
    assert CarryBit(1).value == 1
    for value, bits in ((1 << 64, 64), (0, 65), (-1, 64)):
        with pytest.raises(ValueError):
            WordLimb(value, bits)
    with pytest.raises(ValueError):
        CarryBit(2)


@pytest.mark.parametrize("identifier", [True, 1.0, "1"])
def test_handle_ids_do_not_admit_other_values_equal_to_integers(
    identifier: bool | float | str,
) -> None:
    with pytest.raises(TypeError, match="local ID an integer"):
        ActionProgramID(ArenaToken(), "program", cast("int", identifier))


def test_arena_token_subclasses_cannot_spoof_owner_identity() -> None:
    class TokenAlias(ArenaToken):
        pass

    alias = TokenAlias("same-label")
    with pytest.raises(TypeError, match="arena owner"):
        ArenaHandle(alias, "program", 0)
    valid = ArenaHandle(ArenaToken("same-label"), "program", 0)
    with pytest.raises(ValueError, match="validation domain"):
        valid.validate(alias, "program")


@pytest.mark.parametrize("label", [True, 1, 1.0, None])
def test_arena_token_label_rejects_scalar_aliases(
    label: None | bool | float,
) -> None:
    with pytest.raises(TypeError, match="label"):
        ArenaToken(cast("str", label))


def test_lazy_and_endpoint_boundaries_revalidate_integer_identity() -> None:
    owner = ArenaToken()
    source = ArenaHandle(owner, "source", 0)
    forged = ActionProgramID(owner, "program", 0)
    object.__setattr__(forged, "local_id", True)
    with pytest.raises(TypeError, match="local ID an integer"):
        LazyFieldRef(source, forged)
    with pytest.raises(ValueError, match="negative field extent"):
        LazyFieldRef(source, ActionProgramID(owner, "program", 0), extent=True)

    field = LazyFieldRef(source, ActionProgramID(owner, "program", 0))
    capability = LoweringCapability(owner)
    with pytest.raises(TypeError, match="exact integers"):
        MaterializedEndpoint(field, (True,), 2, capability)
    with pytest.raises(TypeError, match="exact integers"):
        MaterializedEndpoint(field, (1,), True, capability)


def test_lazy_source_and_lowering_purpose_reject_python_alias_sorts() -> None:
    owner = ArenaToken()

    class SourceHandleAlias(ArenaHandle):
        pass

    with pytest.raises(TypeError, match="exact source"):
        LazyFieldRef(
            SourceHandleAlias(owner, "source", 0),
            ActionProgramID(owner, "program", 0),
        )
    with pytest.raises(ValueError, match="purpose"):
        LoweringCapability(owner, cast("str", True))
