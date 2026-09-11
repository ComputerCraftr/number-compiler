"""Primitive reverse/add laws behind recursively typed temporal actions."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.field_action import ReverseFieldActionArena


@dataclass(frozen=True, slots=True)
class _PrimitiveCodec:
    effect: BlockEffect
    domains: tuple[tuple[BoundaryState, ...], tuple[BoundaryState, ...]]


class ReverseHigherActionSchema:
    """Interpret a field-action DAG without loading a powered proof machine."""

    def __init__(
        self,
        actions: ReverseFieldActionArena,
        primitive: FieldCellActionID,
        terminal: FieldCellActionID,
    ) -> None:
        self.actions = actions
        self.ledger: ResourceLedger = actions.ledger
        self.identity = actions.identity
        self.primitive = primitive
        self.terminal = terminal
        self._codecs = (
            (
                primitive,
                self._codec(BaseBlockEffect(actions.resolve(primitive).base)),
            ),
            (
                terminal,
                self._codec(DigitNormalizeBlockEffect(actions.resolve(terminal).base)),
            ),
        )

    @staticmethod
    def _codec(effect: BlockEffect) -> _PrimitiveCodec:
        domains: list[tuple[BoundaryState, ...]] = []
        for side in (BoundarySide.LEFT, BoundarySide.RIGHT):
            domain = effect.boundary_universe(side)
            if domain is None:
                raise ValueError("reverse primitive has no finite boundary universe")
            values = tuple(domain)
            domains.append(values)
        return _PrimitiveCodec(effect, (domains[0], domains[1]))

    def validate_action(self, action: FieldCellActionID) -> None:
        self.actions.validate_action(action)

    def children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        self.validate_action(action)
        return self.actions.action_children(action)

    def kind(
        self,
        action: FieldCellActionID,
    ) -> Literal["identity", "primitive", "compose"]:
        self.validate_action(action)
        if action == self.identity:
            return "identity"
        if any(candidate == action for candidate, _codec in self._codecs):
            return "primitive"
        if self.children(action) is not None:
            return "compose"
        raise ValueError("reverse action has no executable construction witness")

    def alphabet(self, action: FieldCellActionID) -> tuple[int, int]:
        self.validate_action(action)
        base = self.actions.resolve(action).base
        return base, 2 * base - 1

    @staticmethod
    def _side(side: int) -> BoundarySide:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("reverse higher boundary side must be zero or one")
        return BoundarySide(side)

    def _primitive(self, action: FieldCellActionID) -> _PrimitiveCodec:
        self.validate_action(action)
        for candidate, codec in self._codecs:
            if candidate == action:
                return codec
        raise ValueError("reverse higher operation requires a primitive action")

    def state_count(self, action: FieldCellActionID, side: int) -> int:
        direction = self._side(side)
        if self.kind(action) == "identity":
            return 1
        return len(self._primitive(action).domains[int(direction)])

    def initial(self, action: FieldCellActionID, side: int) -> int:
        direction = self._side(side)
        if self.kind(action) == "identity":
            return 0
        primitive = self._primitive(action)
        return primitive.domains[int(direction)].index(
            primitive.effect.initial(direction)
        )

    def step(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int:
        direction = self._side(side)
        if self.kind(action) == "identity":
            if state != 0:
                raise ValueError("reverse identity has one boundary state")
            return 0
        primitive = self._primitive(action)
        self.ledger.bump("primitive_transition_evaluations")
        self.ledger.bump("nonlinear_branch_evaluations")
        domain = primitive.domains[int(direction)]
        if type(state) is not int or not 0 <= state < len(domain):
            raise ValueError("reverse primitive state is outside its domain")
        _base, blank = self.alphabet(action)
        if type(symbol) is not int or not 0 <= symbol <= blank:
            raise ValueError("reverse primitive symbol is outside its alphabet")
        target = primitive.effect.advance(direction, domain[state], symbol)
        return domain.index(target)

    def emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        if self.kind(action) == "identity":
            return symbol
        primitive = self._primitive(action)
        self.ledger.bump("primitive_output_evaluations")
        left_domain, right_domain = primitive.domains
        if (
            type(left) is not int
            or not 0 <= left < len(left_domain)
            or type(right) is not int
            or not 0 <= right < len(right_domain)
        ):
            raise ValueError("reverse primitive output boundary is outside its domain")
        return int(
            primitive.effect.emit(left_domain[left], symbol, right_domain[right])
        )


__all__ = ["ReverseHigherActionSchema"]
