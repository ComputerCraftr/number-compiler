"""Read-only family-effect audit capabilities from admitted runtime owners."""

from collections.abc import Callable, Iterable
from typing import cast

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.tile_execution_adapter import FamilyTileHooks


class FamilyEffectPayloadAudit:
    def __init__(self, roots: Iterable[object]) -> None:
        self.effect_types: set[type[BlockEffect]] = set()
        self.compatibility_types: set[type[object]] = set()
        self._validators: dict[type[object], Callable[[BlockEffect], None]] = {}
        self._checks: dict[int, tuple[object, bool]] = {}
        for root in roots:
            if type(root) not in (DiamondRuntime, LazyCompiler):
                continue
            assert isinstance(root, (DiamondRuntime, LazyCompiler))
            hooks = root.family_hooks
            if type(hooks) is not FamilyTileHooks:
                continue
            self.effect_types.add(hooks.effect_type)
            kind, validator = (
                hooks.compatibility_type,
                hooks.validate_compatibility_effect,
            )
            if kind is not None and validator is not None:
                self.compatibility_types.add(kind)
                self._validators[kind] = validator

    def valid_compatibility(self, value: object) -> bool:
        validator = self._validators.get(type(value))
        if validator is None:
            return False
        cached = self._checks.get(id(value))
        if cached is not None and cached[0] is value:
            return cached[1]
        try:
            validator(cast(BlockEffect, value))
        except (TypeError, ValueError):
            valid = False
        else:
            valid = True
        self._checks[id(value)] = (value, valid)
        return valid
