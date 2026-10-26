"""The powered local codec exposes bounded semantics, never exact tiles."""

from collections.abc import Callable
from dataclasses import fields
from typing import cast

import pytest

from devtools.experiments.reverse_add.powered_local_codec import (
    PoweredLocalCodec,
    PoweredLocalEffect,
)
from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.local_action_codec import (
    compose_finite_lookup_maps,
    publish_source_binding,
    validate_finite_lookup_map,
    validate_local_handle,
    validate_mirror_transform,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.reverse_add.powered_local_codec import (
    ReversePoweredLocalCodec,
)
from tests.support.reverse_field_action import source_cells


def test_powered_local_effect_accepts_only_exact_runtime_handle_sorts() -> None:
    interface = LocalInterfaceID(ArenaToken("interface"), "local-interface", 0)
    output = CoordinateOutputMorphismID(
        ArenaToken("output"),
        "coordinate-output-morphism",
        0,
    )
    effect = PoweredLocalEffect(interface, output)
    assert tuple(field.name for field in fields(effect)) == ("interface", "output")
    with pytest.raises(TypeError, match="local-interface"):
        PoweredLocalEffect(
            cast(
                LocalInterfaceID,
                TransferSummaryID(
                    ArenaToken("proof"),
                    "transfer-summary",
                    0,
                ),
            ),
            output,
        )


def test_codec_contract_has_no_exact_tile_or_proof_state_surface() -> None:
    names = {
        name
        for name, value in vars(PoweredLocalCodec).items()
        if not name.startswith("_") and callable(value)
    }
    assert names == {
        "validate_action",
        "leaf_interface",
        "compose_spatial",
        "compose_temporal",
        "transformed",
        "observe_output",
    }
    assert not any("tile" in name or "state" in name for name in names)


def test_shared_local_handle_validation_preserves_owner_sort_and_range() -> None:
    owner = ArenaToken("local-action")
    reference = TransferSummaryID(owner, "local-action", 0)

    assert (
        validate_local_handle(
            reference, TransferSummaryID, owner, "local-action", size=1
        )
        is reference
    )
    with pytest.raises(ValueError, match="different arena"):
        validate_local_handle(
            reference,
            TransferSummaryID,
            ArenaToken("foreign-local-action"),
            "local-action",
            size=1,
        )
    with pytest.raises(ValueError, match="different arena or node kind"):
        validate_local_handle(reference, TransferSummaryID, owner, "other", size=1)
    with pytest.raises(ValueError, match="allocated range"):
        validate_local_handle(
            TransferSummaryID(owner, "local-action", 1),
            TransferSummaryID,
            owner,
            "local-action",
            size=1,
        )
    with pytest.raises(TypeError, match="TransferSummaryID"):
        validate_local_handle(
            ActionProgramID(owner, "local-action", 0),
            TransferSummaryID,
            owner,
            "local-action",
            size=1,
        )


def test_finite_lookup_composition_is_ordered_and_validated_at_admission() -> None:
    validate_finite_lookup_map((1, 1, 0))
    validate_finite_lookup_map((2, 0, 1))
    before = (1, 1, 0)
    after = (2, 0, 1)

    assert compose_finite_lookup_maps(before, after) == (0, 0, 2)
    assert compose_finite_lookup_maps(after, before) == (0, 1, 1)
    with pytest.raises(TypeError, match="immutable tuples"):
        validate_finite_lookup_map([0, 1, 2])
    with pytest.raises(ValueError, match="leaves its state domain"):
        validate_finite_lookup_map((0, 3, 1))
    with pytest.raises(ValueError, match="nonempty state domain"):
        validate_finite_lookup_map(())
    with pytest.raises(ValueError, match="wrong state-domain size"):
        validate_finite_lookup_map((0, 1), expected_size=3)


def test_local_codecs_share_only_the_mirror_subgroup() -> None:
    assert validate_mirror_transform(ActionTransform.IDENTITY, message="bad") is (
        ActionTransform.IDENTITY
    )
    assert validate_mirror_transform(ActionTransform.MIRROR, message="bad") is (
        ActionTransform.MIRROR
    )
    with pytest.raises(ValueError, match="bad"):
        validate_mirror_transform(ActionTransform.CONJUGATE, message="bad")
    with pytest.raises(ValueError, match="bad"):
        validate_mirror_transform(1, message="bad")


def test_reverse_codec_rejects_mutated_transform_before_composition_cache_hit() -> None:
    ledger, sources, root = source_cells((1, 2))
    codec = ReversePoweredLocalCodec(10, sources, ledger=ledger)
    action = codec.source_action(root)
    right = codec.leaf(3)
    codec.compose(action, right)

    object.__setattr__(action, "transform", ActionTransform.CONJUGATE)
    with pytest.raises(ValueError, match="malformed reverse local action transform"):
        codec.resolve(action)
    with pytest.raises(ValueError, match="malformed reverse local action transform"):
        codec.compose(action, right)


def test_source_binding_publication_rolls_back_inserted_value_on_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("source-bindings", "source_binding")
    store: LedgerDict[int, str] = ledger.make_dict(owner)
    ledger.register_container(owner, store, payloads=store.items)
    original_setitem: Callable[[LedgerDict[int, str], int, str], None] = LedgerDict[
        int, str
    ].__setitem__

    def insert_then_fail(target: LedgerDict[int, str], key: int, value: str) -> None:
        original_setitem(target, key, value)
        raise RuntimeError("injected source publication failure")

    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_fail)
    with pytest.raises(RuntimeError, match="injected source publication failure"):
        publish_source_binding(ledger, owner, store, 17, "action")

    assert len(store) == 0
    assert ledger.account_status(owner).entries == 0
    assert ledger.entries == 0
