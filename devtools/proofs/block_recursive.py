"""Canonical recursive occurrence carrier for higher composed block effects.

Higher temporal composition must not enumerate the complete boundary universe
of its first child and must not retain the already-scanned source boundary as a
second temporal state representation.  One canonical object therefore owns
both pieces that used to be duplicated between ``_RecursiveBoundaryState`` and
``_RecursiveResidualAction``:

* ``anchor`` -- the canonical first-child boundary *after* this occurrence;
* ``previous`` + ``tile`` -- the hash-consed dyadic spatial action forest.

For a non-constant node, ``previous.anchor`` is exactly the first-child anchor
before ``tile``.  Thus there is no independent ``anchor_before`` field and no
second wrapper interner.  Adjacent equal-size tiles are joined eagerly, so the
carrier is a canonical binary forest rather than an append-only history chain.
Absolute source length is occurrence geometry and is deliberately absent.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    _CONTEXT_IDS,
    BlockEffect,
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile


@dataclass(frozen=True, slots=True)
class _ProviderLayer:
    """One source-parametric image layer over an original spatial tile.

    ``left`` and ``right`` are the complete provider boundary states surrounding
    the tile.  The layer therefore names an image action, not its emitted word.
    No future symbol or future exact tile is retained here.
    """

    effect: BlockEffect
    left: BoundaryState
    right: BoundaryState


class _RecursiveResidualAction:
    """One canonical recursive spatial occurrence/action node.

    The object is also the boundary state returned by the composed effect.  This
    removes the former one-for-one ``_RecursiveBoundaryState`` wrapper.  The
    transition cache lives here because transitions are properties of this exact
    canonical occurrence, not of a second semantic state space.
    """

    __slots__ = (
        "node_id",
        "side",
        "previous",
        "tile",
        "reversed",
        "anchor",
        "layers",
        "transition_symbol",
        "transition_result",
        "transition_more",
    )
    __hash__ = object.__hash__

    def __init__(
        self,
        side: BoundarySide,
        previous: _RecursiveResidualAction | None,
        tile: DyadicTile | None,
        anchor: BoundaryState,
        layers: tuple[_ProviderLayer, ...] = (),
        *,
        reversed: bool = False,
    ) -> None:
        self.node_id = next(_CONTEXT_IDS)
        self.side = side
        self.previous = previous
        self.tile = tile
        self.reversed = reversed
        self.anchor = anchor
        self.layers = layers
        self.transition_symbol = -1
        self.transition_result: object | None = None
        self.transition_more: dict[int, object] | None = None

    @property
    def is_constant(self) -> bool:
        return self.previous is None

    @property
    def residual(self) -> _RecursiveResidualAction:
        """Compatibility view: the canonical boundary state *is* its residual."""
        return self


# Compatibility name for type checks and downstream API code.  This is an alias,
# not another class/object space; source audits assert the two names are identical.
_RecursiveBoundaryState = _RecursiveResidualAction


__all__ = ["_ProviderLayer", "_RecursiveBoundaryState", "_RecursiveResidualAction"]
