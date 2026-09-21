"""Primitive reverse/add laws behind recursively typed temporal actions."""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass
from typing import Literal

from devtools.experiments.reverse_add.field_action import ReverseFieldActionArena
from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger


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
        prefix = f"reverse-higher-schema-{len(self.ledger.inventory())}"
        self._children_owner = self.ledger.register(
            prefix + "-children", "reverse_action_children"
        )
        self._children: MutableMapping[
            FieldCellActionID,
            tuple[FieldCellActionID, FieldCellActionID],
        ] = self.ledger.make_dict(self._children_owner)
        self.ledger.register_container(
            self._children_owner,
            self._children,
            payloads=self._children.items,
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
        if type(action) is not FieldCellActionID:
            raise TypeError("expected a reverse field-action ID")
        self.actions.validate_action(action)

    def validate_action_readonly(self, action: FieldCellActionID) -> None:
        """Validate authority without changing the execution cache.

        Payload audits call this path while traversing higher semantic sorts.
        Their read-only snapshots must not publish cache entries or consume a
        caller's execution budget.
        """
        if type(action) is not FieldCellActionID:
            raise TypeError("expected a reverse field-action ID")
        self.actions.validate_action(action)

    def children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        self.validate_action(action)
        return self._children_after_validation(action)

    def _children_after_validation(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        """Resolve one immutable construction edge after authority checking.

        Operation machines repeatedly ask for the same balanced action edges.
        The field-action arena is append-only, so an edge already obtained
        from its validating accessor is immutable.  Keeping this cache on the
        index ledger avoids repeated witness-store probes without creating a
        second action or successor authority.
        """
        if action == self.identity or any(
            candidate == action for candidate, _codec in self._codecs
        ):
            return None
        if action in self._children:
            return self._children[action]
        result = self.actions.action_children(action)
        if result is None:
            return None
        self.ledger.reserve(self._children_owner, entries=1)
        self._children[action] = result
        self.ledger.bump("reverse_higher_schema_children_publications")
        return result

    def kind(
        self,
        action: FieldCellActionID,
    ) -> Literal["identity", "primitive", "compose"]:
        self.validate_action(action)
        if action == self.identity:
            return "identity"
        if any(candidate == action for candidate, _codec in self._codecs):
            return "primitive"
        # Classification is an admission check used by the primitive tables.
        # It must not publish execution metadata for a rejected composed input.
        # Execution paths call ``children`` explicitly, which is the point at
        # which retaining the immutable construction edge becomes chargeable.
        children = self._children.get(action)
        if children is not None or self.actions.action_children(action) is not None:
            return "compose"
        raise ValueError("reverse action has no executable construction witness")

    def alphabet(self, action: FieldCellActionID) -> tuple[int, int]:
        base = self.actions.resolve(action).base
        return base, 2 * base - 1

    @staticmethod
    def _side(side: int) -> BoundarySide:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("reverse higher boundary side must be zero or one")
        return BoundarySide(side)

    def _primitive_after_validation(self, action: FieldCellActionID) -> _PrimitiveCodec:
        for candidate, codec in self._codecs:
            if candidate == action:
                return codec
        raise ValueError("reverse higher operation requires a primitive action")

    def state_count(self, action: FieldCellActionID, side: int) -> int:
        direction = self._side(side)
        kind = self.kind(action)
        if kind == "identity":
            return 1
        return len(self._primitive_after_validation(action).domains[int(direction)])

    def initial(self, action: FieldCellActionID, side: int) -> int:
        direction = self._side(side)
        kind = self.kind(action)
        if kind == "identity":
            return 0
        primitive = self._primitive_after_validation(action)
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
        kind = self.kind(action)
        if kind == "identity":
            if state != 0:
                raise ValueError("reverse identity has one boundary state")
            return 0
        primitive = self._primitive_after_validation(action)
        self.ledger.bump("primitive_transition_evaluations")
        self.ledger.bump("nonlinear_branch_evaluations")
        domain = primitive.domains[int(direction)]
        if type(state) is not int or not 0 <= state < len(domain):
            raise ValueError("reverse primitive state is outside its domain")
        blank = 2 * primitive.effect.base - 1
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
        kind = self.kind(action)
        if kind == "identity":
            return symbol
        primitive = self._primitive_after_validation(action)
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
