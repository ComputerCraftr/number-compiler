"""Index-owned frozen observations of bounded primitive higher kernels.

The higher evaluator often reaches the same primitive transition through many
different temporal derivations.  These tables canonicalize that bounded local
law before evaluating a recursive state.  They contain kernel ordinals only;
they never contain source coordinates, future symbols, or composed states.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherActionSchema,
    )


class HigherPrimitiveTables:
    """Memoize complete bounded primitive calls across point observations."""

    def __init__(self, schema: HigherActionSchema, ledger: ResourceLedger) -> None:
        self.schema, self.ledger = schema, ledger
        ledger.register_execution_root(self)
        prefix = f"higher-primitive-tables-{len(ledger.inventory())}"
        self._step_owner = ledger.register(
            prefix + "-steps",
            "higher_primitive_kernel_table",
        )
        self._emit_owner = ledger.register(
            prefix + "-outputs",
            "higher_primitive_kernel_table",
        )
        self._interface_owner = ledger.register(
            prefix + "-interfaces",
            "higher_primitive_kernel_table",
        )
        self._interfaces: MutableMapping[FieldCellActionID, tuple[int, int, int]] = (
            ledger.make_dict(self._interface_owner)
        )
        ledger.register_container(
            self._interface_owner,
            self._interfaces,
            payloads=self._interfaces.items,
        )
        self._steps: MutableMapping[tuple[FieldCellActionID, int, int, int], int] = (
            ledger.make_dict(self._step_owner)
        )
        self._outputs: MutableMapping[tuple[FieldCellActionID, int, int, int], int] = (
            ledger.make_dict(self._emit_owner)
        )
        ledger.register_container(
            self._step_owner,
            self._steps,
            payloads=self._steps.items,
        )
        ledger.register_container(
            self._emit_owner,
            self._outputs,
            payloads=self._outputs.items,
        )

    def _primitive_interface(
        self,
        action: FieldCellActionID,
    ) -> tuple[int, int, int]:
        self.schema.validate_action(action)
        found = self._interfaces.get(action)
        if found is not None:
            return found
        if self.schema.kind(action) != "primitive":
            raise ValueError("primitive table action must be a primitive kernel")
        left = self.schema.state_count(action, 0)
        right = self.schema.state_count(action, 1)
        _base, blank = self.schema.alphabet(action)
        if any(type(value) is not int or value < 1 for value in (left, right)):
            raise ValueError("primitive table has an invalid state interface")
        if type(blank) is not int or blank < 0:
            raise ValueError("primitive table has an invalid alphabet")
        return left, right, blank

    def _reserve_result(
        self,
        action: FieldCellActionID,
        interface: tuple[int, int, int],
        owner: int,
    ) -> None:
        """Publish immutable admission only with a successfully checked result."""
        missing = action not in self._interfaces
        self.ledger.reserve_many(
            ((owner, 1, 0), (self._interface_owner, int(missing), 0)),
        )
        if missing:
            self._interfaces[action] = interface

    @staticmethod
    def _ordinal(value: int, bound: int, role: str) -> None:
        if type(value) is not int:
            raise TypeError(f"primitive {role} must be an exact integer")
        if not 0 <= value < bound:
            raise ValueError(f"primitive {role} is outside its bounded interface")

    def step(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int:
        left, right, blank = self._primitive_interface(action)
        if type(side) is not int:
            raise TypeError("primitive side must be an exact integer")
        if side not in (0, 1):
            raise ValueError("primitive side must be zero or one")
        self._ordinal(state, left if side == 0 else right, "state")
        self._ordinal(symbol, blank + 1, "symbol")
        key = action, side, state, symbol
        found = self._steps.get(key)
        if found is not None:
            self.ledger.bump("higher_primitive_step_hits")
            return found
        result = self.schema.step(action, side, state, symbol)
        self._ordinal(result, left if side == 0 else right, "transition result")
        self._reserve_result(action, (left, right, blank), self._step_owner)
        self._steps[key] = result
        self.ledger.bump("higher_primitive_step_publications")
        return result

    def emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        left_count, right_count, blank = self._primitive_interface(action)
        self._ordinal(left, left_count, "left state")
        self._ordinal(symbol, blank + 1, "symbol")
        self._ordinal(right, right_count, "right state")
        key = action, left, symbol, right
        found = self._outputs.get(key)
        if found is not None:
            self.ledger.bump("higher_primitive_output_hits")
            return found
        result = self.schema.emit(action, left, symbol, right)
        self._ordinal(result, blank + 1, "output result")
        self._reserve_result(action, (left_count, right_count, blank), self._emit_owner)
        self._outputs[key] = result
        self.ledger.bump("higher_primitive_output_publications")
        return result


__all__ = ["HigherPrimitiveTables"]
