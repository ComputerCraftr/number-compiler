"""Admitted homogeneous cell alphabets need no temporal-spine replay."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.tile_action_algebra import PrimitiveTileAction


def test_mixed_deep_action_checks_endpoint_alphabet_without_temporal_walk(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, primitive, _scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.compose(
        adapter.power(primitive, 128), adapter.admit(DigitNormalizeBlockEffect(3))
    )
    with _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source:
        original = adapter._action
        seen = []

        def resolve(
            current: FieldCellActionID,
        ) -> PrimitiveTileAction:
            seen.append(current)
            return original(current)

        monkeypatch.setattr(adapter, "_action", resolve)
        adapter.validate_input(action, source.tile)
        adapter.validate_output(action, source.tile)
        assert seen == [action, action]
