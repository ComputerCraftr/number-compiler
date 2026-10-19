"""Exact normalized-tail forcing morphism for proof and diagnostics only."""

from __future__ import annotations

from dataclasses import dataclass

from devtools.verification.collatz_semantic_action import (
    CollatzBlockAction,
    CollatzBlockActionArena,
)
from number_compiler.arithmetic.contracts.successor_congruence import (
    ExactTargetCacheIdentity,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicSpan,
    DyadicTile,
    align_span,
    first_symbol,
)
from number_compiler.sequences.collatz.frame import CollatzFixedPointPadicFrame


@dataclass(frozen=True, slots=True)
class CollatzForcingClass:
    """Source-independent extensional operator class."""

    class_id: int
    fixed_ones: bool
    local_shift: int
    block_action: CollatzBlockAction | None

    def __post_init__(self) -> None:
        if type(self.class_id) is not int or self.class_id < 0:
            raise ValueError(
                "Collatz forcing class ID must be a nonnegative exact integer"
            )
        if type(self.fixed_ones) is not bool:
            raise TypeError("Collatz fixed-frame flag must be Boolean")
        if type(self.local_shift) is not int:
            raise TypeError("Collatz local shift must be an exact integer")
        if self.local_shift not in (0, 1):
            raise ValueError(self.local_shift)
        if self.fixed_ones != (self.block_action is None):
            raise ValueError((self.fixed_ones, self.block_action))
        if self.fixed_ones and self.local_shift:
            raise ValueError("fixed all-ones class cannot have a local shift")
        if (
            self.block_action is not None
            and self.block_action.local_shift != self.local_shift
        ):
            raise ValueError((self.local_shift, self.block_action))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        if self.fixed_ones:
            return ("collatz-forcing-action", "fixed-ones")
        action = self.block_action
        if action is None:
            raise AssertionError(self)
        return ("collatz-forcing-action", action.canonical_key)


@dataclass(frozen=True, slots=True)
class CollatzForcingOccurrence:
    """Normalized accelerated-Collatz occurrence.

    The removable radix-4 ``1**q`` frame is *not state*.  ``q`` contributes an
    additive valuation cocycle to the physical-time/event weight, but the exact
    normalized successor depends only on the aligned tail plus the bounded
    local action sector.  This occurrence therefore stores no ``frame_depth``
    and no duplicated ``valuation`` scalar.

    The exact tail remains arena-owned *spatial payload*.  Temporal identity is
    the bounded 3-adic fixed-frame quotient plus the source-independent block
    action.  Exact target identity is the canonical normalized spatial tail.
    """

    forcing: CollatzForcingClass
    spatial_key: tuple[DyadicTile, ...] | None
    residue3: int
    residue3_precision: int = 8
    occurrence_id: int = 0

    def __post_init__(self) -> None:
        if type(self.residue3) is not int or type(self.residue3_precision) is not int:
            raise TypeError("Collatz residue payload requires exact integers")
        if type(self.occurrence_id) is not int or self.occurrence_id < 0:
            raise ValueError(
                "Collatz occurrence ID must be a nonnegative exact integer"
            )
        if not 0 < self.residue3_precision <= 40:
            raise ValueError("Collatz residue precision must fit one 64-bit limb")
        if self.forcing.fixed_ones != (self.spatial_key is None):
            raise ValueError((self.forcing, self.spatial_key))
        modulus = 3**self.residue3_precision
        if not 0 <= self.residue3 < modulus:
            raise ValueError((self.residue3, modulus))

    @property
    def padic_frame(self) -> CollatzFixedPointPadicFrame:
        return CollatzFixedPointPadicFrame(
            self.residue3_precision,
            self.residue3,
            self.forcing.local_shift,
        )

    @property
    def temporal_key(self) -> tuple[object, ...]:
        return (
            "collatz-temporal-quotient",
            self.forcing.canonical_key,
            self.padic_frame.canonical_key,
        )

    @property
    def occurrence_key(self) -> tuple[object, ...]:
        if self.spatial_key is None:
            return ("collatz-forcing-occurrence", "fixed-ones")
        return (
            "collatz-forcing-occurrence",
            tuple(tile.node_id for tile in self.spatial_key),
        )

    @property
    def cache_identity(self) -> ExactTargetCacheIdentity:
        return ExactTargetCacheIdentity(
            self.temporal_key,
            self.occurrence_key,
            False,
        )


@dataclass(frozen=True, slots=True)
class CollatzForcingMorphismMetrics:
    requests: int
    source_hits: int
    source_entries: int
    forcing_classes: int
    frame_aliases: int
    action_aliases: int
    normalized_occurrences: int = 0


class CollatzForcingMorphismArena:
    """Strip gauge, intern extensional action, retain exact tail as payload."""

    __slots__ = (
        "_classes",
        "_occurrences",
        "_payloads",
        "_residue_summaries",
        "_sources",
        "action_aliases",
        "actions",
        "frame_aliases",
        "requests",
        "source_hits",
    )

    def __init__(self, actions: object) -> None:
        if not isinstance(actions, CollatzBlockActionArena):
            raise TypeError(type(actions))
        self.actions = actions
        self._sources: dict[tuple[object, ...], CollatzForcingOccurrence] = {}
        self._classes: dict[tuple[object, ...], CollatzForcingClass] = {}
        self._occurrences: dict[tuple[object, ...], CollatzForcingOccurrence] = {}
        self._payloads: dict[int, DyadicSpan | None] = {}
        self._residue_summaries: dict[tuple[int, int], tuple[int, int]] = {}
        self.requests = 0
        self.source_hits = 0
        self.frame_aliases = 0
        self.action_aliases = 0

    def _class_for_tail(self, tail: DyadicSpan | None) -> CollatzForcingClass:
        if tail is None:
            semantic_key: tuple[object, ...] = ("collatz-forcing-action", "fixed-ones")
            found = self._classes.get(semantic_key)
            if found is not None:
                return found
            out = CollatzForcingClass(len(self._classes), True, 0, None)
            self._classes[semantic_key] = out
            return out

        local_shift = int(first_symbol(tail.chunks[0].tile) == 3)
        action = self.actions.intern(tail, local_shift)
        semantic_key = ("collatz-forcing-action", action.canonical_key)
        found = self._classes.get(semantic_key)
        if found is not None:
            self.action_aliases += 1
            return found
        out = CollatzForcingClass(
            len(self._classes),
            False,
            local_shift,
            action,
        )
        self._classes[semantic_key] = out
        return out

    def _residue3(self, tail: DyadicSpan | None, precision: int = 8) -> int:
        if type(precision) is not int:
            raise TypeError("Collatz residue precision must be an exact integer")
        if not 0 < precision <= 40:
            raise ValueError("Collatz residue precision must fit one 64-bit limb")
        if tail is not None and type(tail) is not DyadicSpan:
            raise TypeError("Collatz tail must be an exact dyadic span")
        modulus = 3**precision
        if tail is None:
            return 1
        stack = [(chunk.tile, False) for chunk in tail.chunks]
        while stack:
            tile, ready = stack.pop()
            key = (tile.node_id, precision)
            if key in self._residue_summaries:
                continue
            if tile.level == 0:
                if tile.symbol is None:
                    raise AssertionError(tile)
                out = (tile.symbol % modulus, 4 % modulus)
            else:
                if tile.left is None or tile.right is None:
                    raise AssertionError(tile)
                if not ready:
                    stack.extend(
                        ((tile, True), (tile.right, False), (tile.left, False))
                    )
                    continue
                left, left_place = self._residue_summaries[
                    (tile.left.node_id, precision)
                ]
                right, right_place = self._residue_summaries[
                    (tile.right.node_id, precision)
                ]
                out = (
                    (left + left_place * right) % modulus,
                    (left_place * right_place) % modulus,
                )
            self._residue_summaries[key] = out
        result, place = 0, 1
        for chunk in tail.chunks:
            residue, next_place = self._residue_summaries[
                (chunk.tile.node_id, precision)
            ]
            result = (result + place * residue) % modulus
            place = (place * next_place) % modulus
        return result

    def tail_span(self, occurrence: CollatzForcingOccurrence) -> DyadicSpan | None:
        if type(occurrence) is not CollatzForcingOccurrence:
            raise TypeError("expected a Collatz forcing occurrence")
        spatial_ids = (
            None
            if occurrence.spatial_key is None
            else tuple(tile.node_id for tile in occurrence.spatial_key)
        )
        key = (
            occurrence.forcing.class_id,
            spatial_ids,
            occurrence.residue3,
            occurrence.residue3_precision,
        )
        if self._occurrences.get(key) is not occurrence:
            raise ValueError("occurrence does not belong to this forcing arena")
        try:
            return self._payloads[occurrence.occurrence_id]
        except KeyError as exc:
            raise ValueError(
                "occurrence does not belong to this forcing arena"
            ) from exc

    def retained_payload_spans(self) -> tuple[DyadicSpan, ...]:
        """Exact normalized tails retained as spatial payload, never temporal IDs."""
        return tuple(span for span in self._payloads.values() if span is not None)

    def intern(
        self,
        source_key: tuple[object, ...],
        *,
        frame_depth: int,
        tail: DyadicSpan | None,
    ) -> CollatzForcingOccurrence:
        if type(source_key) is not tuple:
            raise TypeError("Collatz source key must be an immutable tuple")
        if type(frame_depth) is not int:
            raise TypeError("Collatz frame depth must be an exact integer")
        if frame_depth < 0:
            raise ValueError(frame_depth)
        if tail is not None and type(tail) is not DyadicSpan:
            raise TypeError("Collatz tail must be an exact dyadic span")
        self.requests += 1
        found = self._sources.get(source_key)
        if found is not None:
            self.source_hits += 1
            return found

        tail = None if tail is None else align_span(tail, 0)
        forcing = self._class_for_tail(tail)
        valuation = 2 * frame_depth + forcing.local_shift
        if valuation <= 0:
            raise ValueError((frame_depth, forcing.local_shift))
        spatial_key = (
            None if tail is None else tuple(chunk.tile for chunk in tail.chunks)
        )
        residue3 = self._residue3(tail)
        occurrence_key = (
            forcing.class_id,
            None if tail is None else tail.tile_ids,
            residue3,
            8,
        )
        occurrence = self._occurrences.get(occurrence_key)
        if occurrence is None:
            occurrence = CollatzForcingOccurrence(
                forcing,
                spatial_key,
                residue3,
                8,
                len(self._occurrences) + 1,
            )
            self._occurrences[occurrence_key] = occurrence
            self._payloads[occurrence.occurrence_id] = tail
        else:
            # A different low 1**q frame reached the same normalized exact
            # occurrence.  q is a transition weight, not another state ID.
            self.frame_aliases += 1
        self._sources[source_key] = occurrence
        return occurrence

    def metrics(self) -> CollatzForcingMorphismMetrics:
        return CollatzForcingMorphismMetrics(
            self.requests,
            self.source_hits,
            len(self._sources),
            len(self._classes),
            self.frame_aliases,
            self.action_aliases,
            len(self._occurrences),
        )


__all__ = [
    "CollatzForcingClass",
    "CollatzForcingMorphismArena",
    "CollatzForcingMorphismMetrics",
    "CollatzForcingOccurrence",
]
