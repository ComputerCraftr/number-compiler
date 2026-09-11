"""Proof-only exact reverse/add history morphism and operator-phase identities.

The decimal H-row carry slab is a proof/bootstrap certificate.  The exact
history theorem reconstructs the current symmetric pair field, but that exact
field is *occurrence data*, not the HashLife/operator identity.

For one successor the causal machine has the exact affine form

    S' = A_g S + E.

Only the linear phase ``A_g`` is source-independent.  The forcing offset ``E``
is derived from the already-computed forward carry row and remains exact
occurrence data.  ``ReverseAddForcingClass`` therefore interns only ``A_g``;
the accompanying ``ReverseAddAffineAction`` and pair payload remain on the
occurrence.  Different occurrences can share the linear operator class while
still producing different exact and semantic successors.

This separation is intentionally stricter than the old v0.59.5 quotient:

* history provenance is absent from both class and occurrence identity;
* absolute origin is absent (spans are aligned to zero);
* exact pair content is absent from ``ReverseAddForcingClass``;
* exact pair content remains in ``ReverseAddForcingOccurrence`` because the
  operator is not, by itself, a successor-complete state quotient.

The smaller LOW/ID/HIGH reset behavior remains a derived observer only.  It is
useful for spatial action composition but is not allowed to authorize temporal
state aliasing.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.proofs import require_exact_oracle
from devtools.proofs.reverse_action import reconstruct_slab_span
from devtools.proofs.semantic_action import ReverseAddAffineAction
from devtools.proofs.temporal_quotient import ReverseAddCarryCutState
from number_compiler.arithmetic.carry.event_memory import event_memory_horizon
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.successor_congruence import (
    ExactTargetCacheIdentity,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicSpan,
    align_span,
    iter_symbols,
)


@dataclass(frozen=True, slots=True)
class ReverseAddForcingClass:
    """Source-independent linear reverse/add operator phase.

    The exact forcing offset ``E`` is occurrence data.  Only ``A_g`` is a
    reusable operator independent of the pair/carry payload.
    """

    class_id: int
    base: int
    growth: int

    def __post_init__(self) -> None:
        require_exact_oracle()
        if self.base < 2 or self.growth not in (0, 1):
            raise ValueError((self.base, self.growth))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return ("reverse-add-linear-operator", self.base, self.growth)


@dataclass(frozen=True, slots=True)
class ReverseAddForcingOccurrence:
    """Exact spatial occurrence under one bounded temporal forcing class.

    The pair tape is arena-owned spatial payload.  The temporal object stores a
    canonical spatial handle only so exact target caches remain sound; it does
    not retain an absolute length or a second copy of the pair field.
    """

    forcing: ReverseAddForcingClass
    action: ReverseAddAffineAction
    spatial_key: tuple[int, ...]
    occurrence_id: int
    owner: ArenaToken

    def __post_init__(self) -> None:
        require_exact_oracle()
        if (
            self.action.base != self.forcing.base
            or self.action.growth != self.forcing.growth
        ):
            raise ValueError((self.action, self.forcing))
        if not self.spatial_key:
            raise ValueError("reverse/add occurrence requires spatial payload")

    @property
    def base(self) -> int:
        require_exact_oracle()
        return self.forcing.base

    @property
    def temporal_key(self) -> tuple[object, ...]:
        # Carry reset positions are a spatial action observer and may scale
        # with tape width.  They are deliberately excluded from temporal
        # identity; the bounded temporal operator class is the forcing phase.
        require_exact_oracle()
        return ("reverse-add-temporal-forcing", self.forcing.canonical_key)

    @property
    def occurrence_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return ("reverse-add-forcing-occurrence", self.base, self.spatial_key)

    @property
    def cache_identity(self) -> ExactTargetCacheIdentity:
        require_exact_oracle()
        return ExactTargetCacheIdentity(
            self.temporal_key,
            self.occurrence_key,
            False,
        )


@dataclass(frozen=True, slots=True)
class ReverseAddForcingMorphismMetrics:
    requests: int
    source_hits: int
    source_entries: int
    forcing_classes: int
    forcing_occurrences: int
    history_aliases: int
    action_aliases: int
    carry_behavior_classes: int
    carry_behavior_aliases: int

    def __post_init__(self) -> None:
        require_exact_oracle()


class ReverseAddForcingMorphismArena:
    """Map H-row certificates to exact occurrences of shared linear phases.

    The caller supplies the affine action because the single physical carry
    scan is owned by ``ReverseAddCausalSpacetimeEngine``.  This arena never
    reimplements a carry scan and therefore cannot create a second causal
    owner.
    """

    __slots__ = (
        "_classes",
        "_owner",
        "_occurrences",
        "_payloads",
        "_sources",
        "action_aliases",
        "base",
        "history_aliases",
        "requests",
        "source_hits",
    )

    def __init__(self, base: int = 10) -> None:
        require_exact_oracle()
        base = int(base)
        if base < 2:
            raise ValueError(base)
        self.base = base
        self._owner = ArenaToken("reverse-forcing")
        self._sources: dict[tuple[object, ...], ReverseAddForcingOccurrence] = {}
        self._classes: dict[tuple[object, ...], ReverseAddForcingClass] = {}
        self._occurrences: dict[tuple[object, ...], ReverseAddForcingOccurrence] = {}
        self._payloads: dict[int, DyadicSpan] = {}
        self.requests = 0
        self.source_hits = 0
        self.history_aliases = 0
        self.action_aliases = 0

    def source_key(self, carries: tuple[DyadicSpan, ...]) -> tuple[object, ...]:
        require_exact_oracle()
        if len(carries) != event_memory_horizon(self.base):
            raise ValueError((len(carries), event_memory_horizon(self.base)))
        return ReverseAddCarryCutState.from_rows(
            carries,
            base=self.base,
        ).canonical_key

    def _class_for_action(
        self,
        action: ReverseAddAffineAction,
    ) -> tuple[ReverseAddForcingClass, bool]:
        require_exact_oracle()
        if action.base != self.base:
            raise ValueError((action.base, self.base))
        semantic_key = (
            "reverse-add-linear-operator",
            self.base,
            int(action.growth),
        )
        found = self._classes.get(semantic_key)
        if found is not None:
            return found, True
        out = ReverseAddForcingClass(
            len(self._classes),
            self.base,
            int(action.growth),
        )
        self._classes[semantic_key] = out
        return out, False

    def pair_span(self, occurrence: ReverseAddForcingOccurrence) -> DyadicSpan:
        require_exact_oracle()
        self.validate_occurrence(occurrence)
        try:
            return self._payloads[occurrence.occurrence_id]
        except KeyError as exc:
            raise ValueError(
                "occurrence does not belong to this forcing arena"
            ) from exc

    def validate_occurrence(self, occurrence: ReverseAddForcingOccurrence) -> None:
        """Reject foreign handles before any integer-key cache is consulted."""
        require_exact_oracle()
        if occurrence.owner is not self._owner:
            raise ValueError("foreign reverse/add forcing occurrence")

    def pair_values(self, occurrence: ReverseAddForcingOccurrence) -> tuple[int, ...]:
        require_exact_oracle()
        return tuple(map(int, iter_symbols(self.pair_span(occurrence))))

    def retained_payload_spans(self) -> tuple[DyadicSpan, ...]:
        """Exact spatial payloads retained by occurrence interning."""
        require_exact_oracle()
        return tuple(self._payloads.values())

    def intern_pair_span(
        self,
        pair_span: DyadicSpan,
        *,
        action: ReverseAddAffineAction,
    ) -> ReverseAddForcingOccurrence:
        """Intern exact spatial payload under its shared bounded temporal phase.

        No full pair tuple or reset-position list is materialized here.  Those
        were derived spatial observers that duplicated information already held
        by the dyadic payload and were never valid temporal cache identity.
        """
        require_exact_oracle()
        if pair_span.length <= 0:
            raise ValueError(pair_span.length)
        pair_span = align_span(pair_span, 0)

        forcing, class_existed = self._class_for_action(action)
        occurrence_key = (
            "reverse-add-forcing-occurrence",
            self.base,
            pair_span.tile_ids,
        )
        existing = self._occurrences.get(occurrence_key)
        if existing is not None:
            # An exact occurrence must never acquire a different semantic
            # linear phase or exact forcing action; either would reveal broken
            # canonicalization.
            if existing.forcing.canonical_key != forcing.canonical_key:
                raise AssertionError((existing.forcing, forcing))
            if existing.action.canonical_key != action.canonical_key:
                raise AssertionError((existing.action, action))
            return existing

        if class_existed:
            # A different exact payload has the same source-independent linear
            # operator phase.  Its exact forcing offset may still differ.
            self.action_aliases += 1

        out = ReverseAddForcingOccurrence(
            forcing,
            action,
            pair_span.tile_ids,
            len(self._occurrences),
            self._owner,
        )
        self._occurrences[occurrence_key] = out
        self._payloads[out.occurrence_id] = pair_span
        return out

    def intern(
        self,
        carries: tuple[DyadicSpan, ...],
        *,
        action: ReverseAddAffineAction,
    ) -> ReverseAddForcingOccurrence:
        """Apply the exact H-row morphism and intern its operator occurrence."""
        require_exact_oracle()
        self.requests += 1
        source_key = self.source_key(carries)
        found = self._sources.get(source_key)
        if found is not None:
            self.source_hits += 1
            if found.action.canonical_key != action.canonical_key:
                raise AssertionError("history source changed exact forcing action")
            return found

        pair_span = reconstruct_slab_span(carries, self.base)
        occurrence_key = (
            "reverse-add-forcing-occurrence",
            self.base,
            pair_span.tile_ids,
        )
        existed = occurrence_key in self._occurrences
        occurrence = self.intern_pair_span(pair_span, action=action)
        if existed:
            # Distinct proof histories collapsed to the same exact occurrence.
            self.history_aliases += 1
        self._sources[source_key] = occurrence
        return occurrence

    def metrics(self) -> ReverseAddForcingMorphismMetrics:
        require_exact_oracle()
        return ReverseAddForcingMorphismMetrics(
            self.requests,
            self.source_hits,
            len(self._sources),
            len(self._classes),
            len(self._occurrences),
            self.history_aliases,
            self.action_aliases,
            0,  # retired eager carry-reset observer
            0,
        )


__all__ = [
    "ReverseAddForcingClass",
    "ReverseAddForcingMorphismArena",
    "ReverseAddForcingMorphismMetrics",
    "ReverseAddForcingOccurrence",
]
