"""The powered local codec exposes bounded semantics, never exact tiles."""

from dataclasses import fields
from typing import cast

import pytest

from devtools.experiments.reverse_add.powered_local_codec import (
    PoweredLocalCodec,
    PoweredLocalEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
)


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
