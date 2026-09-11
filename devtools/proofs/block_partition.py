"""Finite-domain partition residual machinery for composed block effects.

This mixin owns the exact one-coordinate MTDD/partition quotient.  It is split
from :mod:`_block_composed` so the generic composition runtime does not also
carry ~450 lines of finite-domain behavioral refinement.
"""

from __future__ import annotations

from typing import Callable, Protocol, cast

from number_compiler.arithmetic.contracts.block_effect import (
    _CONTEXT_IDS,
    BlockContextBudget,
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _state_key,
)
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect


class _PartitionBoundaryState:
    """Canonical reduced one-coordinate decision function.

    ``partition`` is a disjoint exact cover of the complete opposite boundary
    domain.  Each entry is ``(second_state, argument_mask)``.  The masks are
    arbitrary-width Python integers, so transition updates are performed as
    set preimages/intersections rather than by enumerating argument cells.

    Two instances with the same anchor and normalized partition denote exactly
    the same continuation function and are hash-consed to one identity.  This is
    the one-variable specialization of the package's reduced MTDD semantics.
    """

    __slots__ = (
        "node_id",
        "side",
        "anchor",
        "partition",
        "transition_symbol",
        "transition_result",
        "transition_more",
        "lookup_arg",
        "lookup_result",
    )
    __hash__ = object.__hash__

    def __init__(
        self,
        side: BoundarySide,
        anchor: BoundaryState,
        partition: tuple[tuple[BoundaryState, int], ...],
    ) -> None:
        self.node_id = next(_CONTEXT_IDS)
        self.side = side
        self.anchor = anchor
        self.partition = partition
        self.transition_symbol = -1
        self.transition_result: object | None = None
        self.transition_more: dict[int, object] | None = None
        self.lookup_arg = -1
        self.lookup_result: BoundaryState | None = None

    def canonical_cache_state(self) -> _PartitionBoundaryState:
        """Partition identities are final at interning time."""
        return self

    def value_at(self, index: int) -> BoundaryState:
        if self.lookup_arg == index:
            result = self.lookup_result
            if result is None:
                raise AssertionError("partition lookup cache lost result")
            return result
        bit = 1 << int(index)
        for result, mask in self.partition:
            if mask & bit:
                self.lookup_arg = int(index)
                self.lookup_result = result
                return result
        raise AssertionError(("partition does not cover argument", index))


class _ComparableStateKey(Protocol):
    def __lt__(self, other: object, /) -> bool: ...


class PartitionCompositionMixin:
    _partition_domain_liftable: bool
    _partition_domains: tuple[
        tuple[BoundaryState, ...] | None, tuple[BoundaryState, ...] | None
    ]
    _partition_domain_index: tuple[dict[object, int] | None, dict[object, int] | None]
    _partition_intern: tuple[
        dict[tuple[object, tuple[tuple[object, int], ...]], _PartitionBoundaryState]
        | None,
        dict[tuple[object, tuple[tuple[object, int], ...]], _PartitionBoundaryState]
        | None,
    ]
    _partition_intern_hits: int
    _partition_intern_misses: int
    _partition_preimage_maps: tuple[
        dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]
    ]
    _partition_preimage_cache: tuple[
        dict[tuple[int, int], int], dict[tuple[int, int], int]
    ]
    _partition_preimage_hits: int
    _partition_preimage_misses: int
    _partition_emit_masks: tuple[
        dict[tuple[object, int], tuple[int, ...]],
        dict[tuple[object, int], tuple[int, ...]],
    ]
    _states: list[int]
    _blank_saturation_hits: list[int]
    _partition_enabled: tuple[bool, bool]
    _partition_full_masks: tuple[int, int]

    @property
    def blank(self) -> int:
        raise NotImplementedError

    @property
    def first(self) -> BlockEffect:
        raise NotImplementedError

    @property
    def second(self) -> BlockEffect:
        raise NotImplementedError

    budget: BlockContextBudget
    _emit_child_uncached: Callable[
        [BlockEffect, BoundaryState, int, BoundaryState], int
    ]

    @staticmethod
    def _canonical_child_state(
        effect: object,
        side: BoundarySide,
        state: BoundaryState,
    ) -> BoundaryState:
        """Return the child's final canonical state before it enters a parent key."""
        if isinstance(state, _PartitionBoundaryState):
            method = getattr(effect, "_canonical_partition_state", None)
            if method is not None:
                return method(side, state)
        return state

    @staticmethod
    def _normalize_partition(
        partition: tuple[tuple[BoundaryState, int], ...]
        | list[tuple[BoundaryState, int]],
        full_mask: int,
    ) -> tuple[tuple[BoundaryState, int], ...]:
        merged: dict[object, tuple[BoundaryState, int]] = {}
        coverage = 0
        for result, raw_mask in partition:
            mask = int(raw_mask) & int(full_mask)
            if not mask:
                continue
            if coverage & mask:
                raise AssertionError("overlapping continuation partition")
            coverage |= mask
            key = _state_key(result)
            old = merged.get(key)
            if old is None:
                merged[key] = (result, mask)
            else:
                merged[key] = (old[0], old[1] | mask)
        if coverage != full_mask:
            raise AssertionError(
                ("incomplete continuation partition", coverage, full_mask)
            )
        values = list(merged.values())
        try:
            values.sort(key=lambda item: cast(_ComparableStateKey, _state_key(item[0])))
        except TypeError:
            values.sort(key=lambda item: repr(_state_key(item[0])))
        return tuple(values)

    def _intern_partition_state(
        self,
        side: BoundarySide,
        anchor: BoundaryState,
        partition: tuple[tuple[BoundaryState, int], ...]
        | list[tuple[BoundaryState, int]],
    ) -> _PartitionBoundaryState:
        index = int(side)
        pool = self._partition_intern[index]
        if pool is None:
            raise AssertionError(
                "partition residual interner is not enabled for this side"
            )
        anchor = self._canonical_child_state(self.first, side, anchor)
        partition = [
            (self._canonical_child_state(self.second, side, result), mask)
            for result, mask in partition
        ]
        normalized = self._normalize_partition(
            partition, self._partition_full_masks[index]
        )
        semantic = tuple((_state_key(result), mask) for result, mask in normalized)
        key = (_state_key(anchor), semantic)
        found = pool.get(key)
        if found is not None:
            self._partition_intern_hits += 1
            return self._canonical_partition_state(side, found)
        out = _PartitionBoundaryState(side, anchor, normalized)
        pool[key] = out
        self._partition_intern_misses += 1
        self.budget.consume_node()
        self._states[index] += 1
        from number_compiler.arithmetic.automata.guard import record_residual_metrics

        record_residual_metrics(states=1)
        # Exact partition identity is final at interning time.  Do not install a
        # later behavioral alias after parent recursive actions may already have
        # retained this object: post-hoc representatives were a direct source of
        # noncanonical parent IDs and late HashLife hits.
        return out

    def _canonical_partition_state(
        self, side: BoundarySide, state: _PartitionBoundaryState
    ) -> _PartitionBoundaryState:
        """Return the stable exact extensional partition identity."""
        if state.side is not side:
            raise ValueError((state.side, side))
        return state

    def _partition_preimages(self, side: BoundarySide, symbol: int) -> tuple[int, ...]:
        index = int(side)
        cache = self._partition_preimage_maps[index]
        found = cache.get(int(symbol))
        if found is not None:
            return found
        domain = self._partition_domains[index]
        domain_index = self._partition_domain_index[index]
        if domain is None or domain_index is None:
            raise AssertionError("missing partition domain")
        opposite = (
            BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
        )
        masks = [0] * len(domain)
        if isinstance(self.first, FiniteBlockEffect):
            table = (
                self.first.right_transitions
                if opposite is BoundarySide.RIGHT
                else self.first.left_transitions
            )
            alphabet = self.first.alphabet_size
            for source_index, argument in enumerate(domain):
                target_index = int(
                    table[int(cast(int, argument)) * alphabet + int(symbol)]
                )
                masks[target_index] |= 1 << source_index
        else:
            for source_index, argument in enumerate(domain):
                target = self.first.advance(opposite, argument, symbol)
                indexed_target = domain_index.get(_state_key(target))
                if indexed_target is None:
                    raise AssertionError(
                        (
                            "partition transition escaped complete domain",
                            side,
                            symbol,
                            target,
                        )
                    )
                masks[indexed_target] |= 1 << source_index
        out = tuple(masks)
        cache[int(symbol)] = out
        return out

    def _partition_preimage_mask(
        self, side: BoundarySide, symbol: int, target_mask: int
    ) -> int:
        index = int(side)
        cache = self._partition_preimage_cache[index]
        key = (int(symbol), int(target_mask))
        found = cache.get(key)
        if found is not None:
            self._partition_preimage_hits += 1
            return found
        preimages = self._partition_preimages(side, symbol)
        x = int(target_mask)
        out = 0
        while x:
            bit = x & -x
            out |= preimages[bit.bit_length() - 1]
            x ^= bit
        cache[key] = out
        self._partition_preimage_misses += 1
        return out

    def _partition_output_masks(
        self, side: BoundarySide, anchor: BoundaryState, symbol: int
    ) -> tuple[int, ...]:
        index = int(side)
        # A composed child owns the canonical output relation over its own
        # boundary universe.  Reuse that reduced selector row directly instead
        # of rebuilding it in the parent by scalar Cartesian probes.
        if not isinstance(self.first, FiniteBlockEffect):
            row_method = getattr(
                self.first, "_output_masks_over_boundary_universe", None
            )
            if row_method is not None:
                row = row_method(side, anchor, int(symbol))
                if row is not None:
                    return cast(tuple[int, ...], row)
        cache = self._partition_emit_masks[index]
        key = (_state_key(anchor), int(symbol))
        found = cache.get(key)
        if found is not None:
            return found
        domain = self._partition_domains[index]
        if domain is None:
            raise AssertionError("missing partition domain")
        masks = [0] * (self.blank + 1)
        if isinstance(self.first, FiniteBlockEffect):
            alphabet = self.first.alphabet_size
            right_count = self.first.right_count
            outputs = self.first.outputs
            if side is BoundarySide.LEFT:
                offset = (int(cast(int, anchor)) * alphabet + int(symbol)) * right_count
                for argument_index in range(len(domain)):
                    masks[outputs[offset + argument_index]] |= 1 << argument_index
            else:
                anchor_i = int(cast(int, anchor))
                for argument_index in range(len(domain)):
                    offset = (
                        argument_index * alphabet + int(symbol)
                    ) * right_count + anchor_i
                    masks[outputs[offset]] |= 1 << argument_index
        else:
            for argument_index, argument in enumerate(domain):
                if side is BoundarySide.LEFT:
                    first_symbol = self._emit_child_uncached(
                        self.first, anchor, symbol, argument
                    )
                else:
                    first_symbol = self._emit_child_uncached(
                        self.first, argument, symbol, anchor
                    )
                masks[int(first_symbol)] |= 1 << argument_index
        out = tuple(masks)
        cache[key] = out
        return out

    def _advance_partition(
        self, side: BoundarySide, state: _PartitionBoundaryState, symbol: int
    ) -> _PartitionBoundaryState:
        index = int(side)
        next_anchor = self._canonical_child_state(
            self.first, side, self.first.advance(side, state.anchor, symbol)
        )
        selectors = self._partition_output_masks(side, state.anchor, symbol)
        merged: dict[object, tuple[BoundaryState, int]] = {}
        for old_value, target_mask in state.partition:
            source_mask = self._partition_preimage_mask(side, symbol, target_mask)
            if not source_mask:
                continue
            for first_symbol, selector in enumerate(selectors):
                mask = source_mask & selector
                if not mask:
                    continue
                if isinstance(self.second, FiniteBlockEffect):
                    table = (
                        self.second.left_transitions
                        if side is BoundarySide.LEFT
                        else self.second.right_transitions
                    )
                    result: BoundaryState = int(
                        table[
                            int(cast(int, old_value)) * self.second.alphabet_size
                            + first_symbol
                        ]
                    )
                else:
                    result = self.second.advance(side, old_value, first_symbol)
                result = self._canonical_child_state(self.second, side, result)
                result_key = _state_key(result)
                old = merged.get(result_key)
                if old is None:
                    merged[result_key] = (result, mask)
                else:
                    merged[result_key] = (old[0], old[1] | mask)
        out = self._intern_partition_state(side, next_anchor, list(merged.values()))
        if out is state and symbol == self.blank:
            self._blank_saturation_hits[index] += 1
        return out


__all__ = ["PartitionCompositionMixin", "_PartitionBoundaryState"]
