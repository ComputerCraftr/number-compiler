from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from devtools.proofs.block_partition import _PartitionBoundaryState
from devtools.proofs.block_recursive import (
    _RecursiveBoundaryState,
    _RecursiveResidualAction,
)
from devtools.proofs.block_spacetime_runtime import SpacetimeRuntimeMixin
from number_compiler.arithmetic.contracts.block_effect import (
    _CONTEXT_IDS,
    BlockContextBudget,
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _cache_state_key,
    _state_key,
)
from number_compiler.arithmetic.fields.dyadic_tile import leaf

if TYPE_CHECKING:
    from devtools.proofs.block_composed import ComposedBlockEffect


class _FunctionalBoundaryState:
    """Canonical extensional boundary residual.

    ``image[j]`` is the exact second-effect boundary state obtained when this
    residual is evaluated at the j-th state of the complete opposite boundary
    universe of the first effect.  Equality is therefore function equality on
    the complete finite domain, not update-history equality.
    """

    __slots__ = (
        "anchor",
        "image",
        "node_id",
        "side",
        "transition_more",
        "transition_result",
        "transition_symbol",
    )
    __hash__ = object.__hash__

    def __init__(
        self,
        side: BoundarySide,
        anchor: BoundaryState,
        image: tuple[BoundaryState, ...],
    ) -> None:
        self.node_id = next(_CONTEXT_IDS)
        self.side = side
        self.anchor = anchor
        self.image = image
        self.transition_symbol = -1
        self.transition_result: object | None = None
        self.transition_more: dict[int, object] | None = None


class ComposedRuntimeMixin(SpacetimeRuntimeMixin):
    """Execution/cache methods for a composed block effect.

    Split from construction/canonicalization so the operator definition does
    not regrow into a single oversized implementation module.
    """

    _functional_domains: tuple[
        tuple[BoundaryState, ...] | None, tuple[BoundaryState, ...] | None
    ]
    _functional_domain_index: tuple[dict[object, int] | None, dict[object, int] | None]
    _functional_intern: tuple[
        dict[tuple[object, tuple[object, ...]], _FunctionalBoundaryState] | None,
        dict[tuple[object, tuple[object, ...]], _FunctionalBoundaryState] | None,
    ]
    _functional_intern_hits: int
    _functional_intern_misses: int
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
    _symbolic_output_rows: tuple[
        dict[tuple[object, int], tuple[int, ...]],
        dict[tuple[object, int], tuple[int, ...]],
    ]
    _boundary_anchor_masks: list[dict[object, tuple[BoundaryState, int]] | None]
    _boundary_value_masks: tuple[
        dict[int, dict[object, tuple[BoundaryState, int]]],
        dict[int, dict[object, tuple[BoundaryState, int]]],
    ]
    _symbolic_output_row_hits: int
    _symbolic_output_row_misses: int
    _symbolic_output_group_evals: int
    _boundary_value_index_builds: int
    _boundary_universe: list[tuple[BoundaryState, ...] | None]
    _recursive_residual_intern: tuple[
        dict[tuple[object, ...], _RecursiveResidualAction] | None,
        dict[tuple[object, ...], _RecursiveResidualAction] | None,
    ]
    _states: list[int]
    _recursive_residual_intern_hits: int
    _recursive_residual_intern_misses: int
    _recursive_value_cache_hits: int
    _recursive_value_cache_misses: int
    _recursive_value_cache: dict[tuple[object, object], BoundaryState]
    _macro_output_hits: int
    _macro_output_misses: int
    _macro_tile_advance_hits: int
    _macro_tile_advance_misses: int
    _macro_boundary_advance_hits: int
    _macro_boundary_advance_misses: int
    _macro_tile_output_hits: int
    _macro_tile_output_misses: int
    _macro_boundary_output_hits: int
    _macro_boundary_output_misses: int
    _macro_tile_advance_cache: dict[tuple[object, ...], BoundaryState]
    _macro_tile_output_cache: dict[tuple[object, ...], object]
    _transition_entries: list[int]
    _map_eval_hits: int
    _map_eval_misses: int
    _blank_saturation_hits: list[int]

    @property
    def supports_predecessor_trace(self) -> bool:
        raise NotImplementedError

    _output_slots: dict[tuple[object, int, object], int] | None
    _output_cache_hits: int
    _output_cache_misses: int
    _output_uncached_probes: int
    _sparse_emit_delegations: int
    _sparse_emit_admission_bits: int
    _sparse_emit_first_seen: int
    _sparse_emit_admissions: int

    @property
    def blank_left_tail(self) -> int:
        raise NotImplementedError

    @property
    def blank_right_tail(self) -> int:
        raise NotImplementedError

    _functional_enabled: tuple[bool, bool]
    _partition_enabled: tuple[bool, bool]
    _partition_full_masks: tuple[int, int]
    _recursive_constant: tuple[
        _RecursiveBoundaryState | None, _RecursiveBoundaryState | None
    ]

    @property
    def blank(self) -> int:
        raise NotImplementedError

    @property
    def base(self) -> int:
        raise NotImplementedError

    @property
    def first(self) -> BlockEffect:
        raise NotImplementedError

    @property
    def second(self) -> BlockEffect:
        raise NotImplementedError

    budget: BlockContextBudget
    boundary_universe: Callable[[BoundarySide], tuple[BoundaryState, ...] | None]
    _intern_functional_state: Callable[
        [BoundarySide, BoundaryState, tuple[BoundaryState, ...]],
        _FunctionalBoundaryState,
    ]
    _canonical_partition_state: Callable[
        [BoundarySide, _PartitionBoundaryState], _PartitionBoundaryState
    ]
    _advance_partition: Callable[
        [BoundarySide, _PartitionBoundaryState, int], _PartitionBoundaryState
    ]

    def advance_uniform(
        self,
        side: BoundarySide,
        state: BoundaryState,
        symbol: int,
        count: int,
    ) -> BoundaryState:
        """Advance one counted uniform spatial tile without cell expansion.

        The uniform region is represented as canonical dyadic geometry and
        absorbed as one boundary macrocell; no counted execution word exists.
        """
        count = int(count)
        if count <= 0:
            return state
        from number_compiler.arithmetic.fields.dyadic_tile import uniform_span

        out = state
        # Geometry is decomposed into canonical aligned dyadic tiles and each
        # tile goes straight to the single effect-owned HashLife action cache.
        # Do not wrap this forest in a second SpacetimeBoundary state carrier.
        for chunk in uniform_span(0, count, int(symbol)).chunks:
            out = self._advance_effect_tile_macro(
                cast(BlockEffect, self), side, out, chunk.tile
            )
        return out

    @staticmethod
    def _transition_get(
        state: _FunctionalBoundaryState
        | _PartitionBoundaryState
        | _RecursiveBoundaryState,
        symbol: int,
    ) -> object | None:
        if state.transition_symbol == symbol:
            return state.transition_result
        more = state.transition_more
        return None if more is None else more.get(symbol)

    def _transition_put(
        self,
        state: _FunctionalBoundaryState
        | _PartitionBoundaryState
        | _RecursiveBoundaryState,
        symbol: int,
        result: object,
    ) -> None:
        index = int(state.side)
        if state.transition_symbol < 0:
            state.transition_symbol = symbol
            state.transition_result = result
            self._transition_entries[index] += 1
            return
        if state.transition_symbol == symbol:
            state.transition_result = result
            return
        more = state.transition_more
        if more is None:
            more = {}
            state.transition_more = more
        if symbol not in more:
            self._transition_entries[index] += 1
        more[symbol] = result

    def advance(
        self, side: BoundarySide, state: BoundaryState, symbol: int
    ) -> BoundaryState:
        assert isinstance(
            state,
            (
                _FunctionalBoundaryState,
                _PartitionBoundaryState,
                _RecursiveBoundaryState,
            ),
        ), type(state)
        if state.side is not side:
            raise ValueError((state.side, side))
        if isinstance(state, _PartitionBoundaryState):
            state = self._canonical_partition_state(side, state)
        found = self._transition_get(state, symbol)
        if found is not None:
            if isinstance(found, _PartitionBoundaryState):
                return self._canonical_partition_state(side, found)
            return found

        if self._partition_enabled[int(side)]:
            if not isinstance(state, _PartitionBoundaryState):
                raise AssertionError(type(state))
            out: BoundaryState = self._canonical_partition_state(
                side, self._advance_partition(side, state, symbol)
            )
            self._transition_put(state, symbol, out)
            return out

        if self._functional_enabled[int(side)]:
            if not isinstance(state, _FunctionalBoundaryState):
                raise AssertionError(type(state))
            domains = self._functional_domains
            indices = self._functional_domain_index
            index = int(side)
            opposite = (
                BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
            )
            domain = domains[index]
            domain_index = indices[index]
            if domain is None or domain_index is None:
                raise AssertionError("missing canonical functional domain")
            next_anchor = self._canonical_child_state(
                self.first, side, self.first.advance(side, state.anchor, symbol)
            )
            image: list[BoundaryState] = []
            for argument in domain:
                next_argument = self.first.advance(opposite, argument, symbol)
                previous_value = state.image[domain_index[_state_key(next_argument)]]
                if side is BoundarySide.LEFT:
                    first_symbol = self._emit_child_uncached(
                        self.first, state.anchor, symbol, argument
                    )
                else:
                    first_symbol = self._emit_child_uncached(
                        self.first, argument, symbol, state.anchor
                    )
                image.append(
                    self._canonical_child_state(
                        self.second,
                        side,
                        self.second.advance(side, previous_value, first_symbol),
                    )
                )
            out = self._intern_functional_state(side, next_anchor, tuple(image))
            if out is state and symbol == self.blank:
                self._blank_saturation_hits[index] += 1
            self._transition_put(state, symbol, out)
            return out

        if self._recursive_enabled[int(side)]:
            if not isinstance(state, _RecursiveBoundaryState):
                raise AssertionError(type(state))
            out = self._advance_effect_tile_macro(
                cast(BlockEffect, self), side, state, leaf(int(symbol))
            )
            if out is state and symbol == self.blank:
                self._blank_saturation_hits[int(side)] += 1
            self._transition_put(state, symbol, out)
            return out
            if out is state and symbol == self.blank:
                self._blank_saturation_hits[int(side)] += 1
            self._transition_put(state, symbol, out)
            return out

        raise AssertionError(("no active boundary carrier", side, type(state)))

    def predecessor(
        self, side: BoundarySide, state: BoundaryState
    ) -> BoundaryState | None:
        assert isinstance(
            state,
            (
                _FunctionalBoundaryState,
                _PartitionBoundaryState,
                _RecursiveBoundaryState,
            ),
        ), type(state)
        if state.side is not side:
            raise ValueError((state.side, side))
        return None

    def _state_anchor(self, side: BoundarySide, state: BoundaryState) -> BoundaryState:
        assert isinstance(
            state,
            (
                _FunctionalBoundaryState,
                _PartitionBoundaryState,
                _RecursiveBoundaryState,
            ),
        ), (side, type(state))
        return state.anchor

    def _residual_value_for_argument(
        self,
        side: BoundarySide,
        state: BoundaryState,
        argument: BoundaryState,
    ) -> BoundaryState:
        """Evaluate one canonical finite residual coordinate without scalar emit."""
        index = int(side)
        if self._partition_enabled[index]:
            if not isinstance(state, _PartitionBoundaryState):
                raise AssertionError(type(state))
            domain_index = self._partition_domain_index[index]
            if domain_index is None:
                raise AssertionError("missing partition domain index")
            return state.value_at(domain_index[_state_key(argument)])
        if self._functional_enabled[index]:
            if not isinstance(state, _FunctionalBoundaryState):
                raise AssertionError(type(state))
            domain_index = self._functional_domain_index[index]
            if domain_index is None:
                raise AssertionError("missing functional domain index")
            return state.image[domain_index[_state_key(argument)]]
        if self._recursive_enabled[index]:
            if not isinstance(state, _RecursiveBoundaryState):
                raise AssertionError(type(state))
            return self._eval_recursive_residual(side, state.residual, argument)
        raise AssertionError("residual value requested from unsupported carrier")

    def _boundary_anchor_groups(
        self,
        side: BoundarySide,
    ) -> dict[object, tuple[BoundaryState, int]] | None:
        """Group one complete boundary universe by first-child anchor as bitsets."""
        index = int(side)
        cached = self._boundary_anchor_masks[index]
        if cached is not None:
            return cached
        domain = self.boundary_universe(side)
        if domain is None:
            return None
        grouped = cast(
            dict[object, tuple[BoundaryState, int]],
            cast("ComposedBlockEffect", self)._owned_dict(
                "block_boundary_anchor_group"
            ),
        )
        for i, state in enumerate(domain):
            anchor = self._state_anchor(side, state)
            key = _state_key(anchor)
            prior = grouped.get(key)
            bit = 1 << i
            if prior is None:
                grouped[key] = (anchor, bit)
            else:
                grouped[key] = (prior[0], prior[1] | bit)
        self._boundary_anchor_masks[index] = grouped
        return grouped

    def _boundary_value_groups(
        self,
        side: BoundarySide,
        argument: BoundaryState,
    ) -> dict[object, tuple[BoundaryState, int]] | None:
        """Group a complete boundary universe by one residual lookup coordinate."""
        index = int(side)
        if self._partition_enabled[index]:
            domain_index = self._partition_domain_index[index]
        elif self._functional_enabled[index]:
            domain_index = self._functional_domain_index[index]
        else:
            return None
        if domain_index is None:
            return None
        coordinate = domain_index.get(_state_key(argument))
        if coordinate is None:
            raise AssertionError(
                (side, argument, "argument outside finite residual domain")
            )
        cache = self._boundary_value_masks[index]
        found = cache.get(coordinate)
        if found is not None:
            return found
        domain = self.boundary_universe(side)
        if domain is None:
            return None
        grouped = cast(
            dict[object, tuple[BoundaryState, int]],
            cast("ComposedBlockEffect", self)._owned_dict("block_boundary_value_group"),
        )
        for i, state in enumerate(domain):
            if isinstance(state, _PartitionBoundaryState):
                value = state.value_at(coordinate)
            elif isinstance(state, _FunctionalBoundaryState):
                value = state.image[coordinate]
            else:
                assert False, type(state)
            value = self._canonical_child_state(self.second, side, value)
            key = _state_key(value)
            prior = grouped.get(key)
            bit = 1 << i
            if prior is None:
                grouped[key] = (value, bit)
            else:
                grouped[key] = (prior[0], prior[1] | bit)
        cache[coordinate] = grouped
        self._boundary_value_index_builds += 1
        return grouped

    def _output_masks_over_boundary_universe(
        self,
        side: BoundarySide,
        anchor: BoundaryState,
        symbol: int,
    ) -> tuple[int, ...] | None:
        """Canonical output row over every reachable opposite boundary state.

        Composition is performed on selector masks.  The varying boundary
        universe is first partitioned by first-child anchor and by the single
        residual coordinate read by ``emit``.  When the second child also owns a
        symbolic row, that row is *lifted* through the residual-value partition;
        no Cartesian scalar output calls are needed at that layer.
        """
        index = int(side)
        opposite = (
            BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
        )
        domain = self.boundary_universe(opposite)
        if domain is None:
            return None
        if isinstance(anchor, _PartitionBoundaryState):
            anchor = self._canonical_partition_state(side, anchor)
        key = (_state_key(anchor), int(symbol))
        cached = self._symbolic_output_rows[index].get(key)
        if cached is not None:
            self._symbolic_output_row_hits += 1
            return cached
        self._symbolic_output_row_misses += 1

        anchor_groups = self._boundary_anchor_groups(opposite)
        if anchor_groups is None:
            return None
        first_anchor = self._state_anchor(side, anchor)
        symbol = int(symbol)
        if side is BoundarySide.LEFT:
            fixed_argument = self.first.advance(BoundarySide.LEFT, first_anchor, symbol)
        else:
            fixed_argument = self.first.advance(
                BoundarySide.RIGHT, first_anchor, symbol
            )
        value_groups = self._boundary_value_groups(opposite, fixed_argument)
        if value_groups is None:
            return None

        second_row_method = getattr(
            self.second, "_output_masks_over_boundary_universe", None
        )
        second_index: dict[object, int] | None = None
        if second_row_method is not None:
            second_domain = self.second.boundary_universe(opposite)
            if second_domain is not None:
                second_index = {
                    _state_key(state): i for i, state in enumerate(second_domain)
                }
        # For this fixed residual coordinate, lifting the same child selector row
        # through ``value_groups`` is reusable across every first-anchor group.
        lifted_cache: dict[tuple[int, ...], tuple[int, ...]] = {}

        def lifted_second_row(
            second_fixed: BoundaryState,
            first_symbol: int,
        ) -> tuple[int, ...] | None:
            if second_row_method is None or second_index is None:
                return None
            row = second_row_method(side, second_fixed, int(first_symbol))
            if row is None:
                return None
            found = lifted_cache.get(row)
            if found is not None:
                return found
            lifted = [0] * len(row)
            for value, value_mask in value_groups.values():
                coordinate = second_index.get(_state_key(value))
                if coordinate is None:
                    raise AssertionError(
                        ("second residual escaped boundary universe", value)
                    )
                bit = 1 << coordinate
                matched = False
                for out_symbol, selector in enumerate(row):
                    if selector & bit:
                        lifted[out_symbol] |= value_mask
                        matched = True
                        break
                if not matched:
                    raise AssertionError(("incomplete child symbolic row", value, row))
            out = tuple(lifted)
            lifted_cache[row] = out
            return out

        # If the first child itself owns a complete symbolic output row, use
        # that row as the selector for the varying first-child anchor.  The old
        # code called ``_emit_child_uncached(first, ...)`` once per anchor group.
        # At the Collatz T^8 partition lift that meant hundreds of T^2 scalar
        # compiler probes even though T^2 had already compiled the exact row.
        # Besides wasting work, those probes polluted the compiler-vs-runtime
        # cache accounting.
        first_row_method = getattr(
            self.first, "_output_masks_over_boundary_universe", None
        )
        first_row: tuple[int, ...] | None = None
        first_index: dict[object, int] | None = None
        if first_row_method is not None:
            first_domain = self.first.boundary_universe(opposite)
            if first_domain is not None:
                first_index = {
                    _state_key(state): i for i, state in enumerate(first_domain)
                }
                first_row = first_row_method(side, first_anchor, symbol)

        def first_output(varying_anchor: BoundaryState) -> int:
            if first_row is not None and first_index is not None:
                coordinate = first_index.get(_state_key(varying_anchor))
                if coordinate is None:
                    raise AssertionError(
                        ("first residual escaped boundary universe", varying_anchor)
                    )
                bit = 1 << coordinate
                for out_symbol, selector in enumerate(first_row):
                    if selector & bit:
                        return out_symbol
                raise AssertionError(
                    ("incomplete first-child symbolic row", varying_anchor, first_row)
                )
            if side is BoundarySide.LEFT:
                return self._emit_child_uncached(
                    self.first, first_anchor, symbol, varying_anchor
                )
            return self._emit_child_uncached(
                self.first, varying_anchor, symbol, first_anchor
            )

        masks = [0] * (self.blank + 1)
        for varying_anchor, anchor_mask in anchor_groups.values():
            first_symbol = first_output(varying_anchor)
            if side is BoundarySide.LEFT:
                moving_argument = self.first.advance(
                    BoundarySide.RIGHT, varying_anchor, symbol
                )
                second_fixed = self._residual_value_for_argument(
                    BoundarySide.LEFT, anchor, moving_argument
                )
            else:
                moving_argument = self.first.advance(
                    BoundarySide.LEFT, varying_anchor, symbol
                )
                second_fixed = self._residual_value_for_argument(
                    BoundarySide.RIGHT, anchor, moving_argument
                )

            lifted = lifted_second_row(second_fixed, first_symbol)
            if lifted is not None:
                for out_symbol, selector in enumerate(lifted):
                    subset = anchor_mask & selector
                    if subset:
                        masks[out_symbol] |= subset
                        self._symbolic_output_group_evals += 1
                continue

            # Lowest finite child has no symbolic-row API.  This fallback still
            # works on reduced value groups rather than individual domain states.
            for second_varying, value_mask in value_groups.values():
                subset = anchor_mask & value_mask
                if not subset:
                    continue
                if side is BoundarySide.LEFT:
                    out = self._emit_child_uncached(
                        self.second, second_fixed, first_symbol, second_varying
                    )
                else:
                    out = self._emit_child_uncached(
                        self.second, second_varying, first_symbol, second_fixed
                    )
                masks[int(out)] |= subset
                self._symbolic_output_group_evals += 1

        full = (1 << len(domain)) - 1
        coverage = 0
        for mask in masks:
            if coverage & mask:
                raise AssertionError("symbolic output row overlaps")
            coverage |= mask
        if coverage != full:
            raise AssertionError(
                ("incomplete symbolic output row", side, symbol, coverage, full)
            )
        output_row = tuple(masks)
        self._symbolic_output_rows[index][key] = output_row
        return output_row

    @staticmethod
    def _emit_child_uncached(
        effect: BlockEffect,
        left: BoundaryState,
        symbol: int,
        right: BoundaryState,
    ) -> int:
        """Evaluate a child output without populating its runtime scalar memo.

        Partition/functional compilation enumerates complete semantic rows.  Those
        probes are compiler work, not runtime requests, and retaining every probed
        ``(left,symbol,right)`` tuple caused the large late-hit Collatz caches.
        """
        method = getattr(effect, "_emit_uncached", None)
        if method is not None:
            return int(method(left, symbol, right))
        return int(effect.emit(left, symbol, right))

    def _canonical_emit_inputs(
        self,
        left: BoundaryState,
        right: BoundaryState,
    ) -> tuple[BoundaryState, BoundaryState]:
        carriers = (
            _FunctionalBoundaryState,
            _PartitionBoundaryState,
            _RecursiveBoundaryState,
        )
        assert isinstance(left, carriers), type(left)
        assert isinstance(right, carriers), type(right)
        if left.side is not BoundarySide.LEFT:
            raise ValueError((left.side, BoundarySide.LEFT))
        if right.side is not BoundarySide.RIGHT:
            raise ValueError((right.side, BoundarySide.RIGHT))
        if isinstance(left, _PartitionBoundaryState):
            left = self._canonical_partition_state(BoundarySide.LEFT, left)
        if isinstance(right, _PartitionBoundaryState):
            right = self._canonical_partition_state(BoundarySide.RIGHT, right)
        return left, right

    def _emit_compute(
        self,
        left: BoundaryState,
        symbol: int,
        right: BoundaryState,
        *,
        cache_children: bool,
    ) -> int:
        left_anchor = self._state_anchor(BoundarySide.LEFT, left)
        right_anchor = self._state_anchor(BoundarySide.RIGHT, right)
        if cache_children:
            first_symbol = self.first.emit(left_anchor, symbol, right_anchor)
        else:
            first_symbol = self._emit_child_uncached(
                self.first, left_anchor, symbol, right_anchor
            )
        left_argument = self.first.advance(BoundarySide.RIGHT, right_anchor, symbol)
        right_argument = self.first.advance(BoundarySide.LEFT, left_anchor, symbol)
        if self._partition_enabled[0]:
            if not isinstance(left, _PartitionBoundaryState):
                raise AssertionError(type(left))
            left_index = self._partition_domain_index[0]
            if left_index is None:
                raise AssertionError("missing canonical left partition index")
            second_left = left.value_at(left_index[_state_key(left_argument)])
        elif self._functional_enabled[0]:
            if not isinstance(left, _FunctionalBoundaryState):
                raise AssertionError(type(left))
            left_index = self._functional_domain_index[0]
            if left_index is None:
                raise AssertionError("missing canonical left functional index")
            second_left = left.image[left_index[_state_key(left_argument)]]
        elif self._recursive_enabled[0]:
            if not isinstance(left, _RecursiveBoundaryState):
                raise AssertionError(type(left))
            second_left = self._eval_recursive_residual(
                BoundarySide.LEFT, left.residual, left_argument
            )
        else:
            raise AssertionError(("no left boundary carrier", type(left)))
        if self._partition_enabled[1]:
            if not isinstance(right, _PartitionBoundaryState):
                raise AssertionError(type(right))
            right_index = self._partition_domain_index[1]
            if right_index is None:
                raise AssertionError("missing canonical right partition index")
            second_right = right.value_at(right_index[_state_key(right_argument)])
        elif self._functional_enabled[1]:
            if not isinstance(right, _FunctionalBoundaryState):
                raise AssertionError(type(right))
            right_index = self._functional_domain_index[1]
            if right_index is None:
                raise AssertionError("missing canonical right functional index")
            second_right = right.image[right_index[_state_key(right_argument)]]
        elif self._recursive_enabled[1]:
            if not isinstance(right, _RecursiveBoundaryState):
                raise AssertionError(type(right))
            second_right = self._eval_recursive_residual(
                BoundarySide.RIGHT, right.residual, right_argument
            )
        else:
            raise AssertionError(("no right boundary carrier", type(right)))
        if cache_children:
            return int(self.second.emit(second_left, first_symbol, second_right))
        return self._emit_child_uncached(
            self.second, second_left, first_symbol, second_right
        )

    def _emit_uncached(
        self,
        left: BoundaryState,
        symbol: int,
        right: BoundaryState,
    ) -> int:
        left, right = self._canonical_emit_inputs(left, right)
        self._output_uncached_probes += 1
        return self._emit_compute(left, int(symbol), right, cache_children=False)

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        left, right = self._canonical_emit_inputs(left, right)
        symbol = int(symbol)

        cache_key = (_cache_state_key(left), symbol, _cache_state_key(right))
        slots = self._output_slots
        cached = None if slots is None else slots.get(cache_key)
        if cached is not None:
            self._output_cache_hits += 1
            return cached
        self._output_cache_misses += 1

        result = self._emit_compute(left, symbol, right, cache_children=True)
        if slots is None:
            slots = cast(
                dict[tuple[object, int, object], int],
                cast("ComposedBlockEffect", self)._owned_dict("block_output_slots"),
            )
            self._output_slots = slots
        if cache_key not in slots:
            self.budget.consume_cache()
        slots[cache_key] = result
        return result

    def operator_nodes(self) -> int:
        # Count object owners, not construction IDs.  ``node_id`` is a diagnostic
        # namespace and must never be able to hide a duplicated operator owner in
        # the very metric used to audit canonical ownership.
        seen: set[int] = set()
        stack: list[BlockEffect] = [cast(BlockEffect, self)]
        while stack:
            node = stack.pop()
            ident = id(node)
            if ident in seen:
                continue
            seen.add(ident)
            if isinstance(node, ComposedRuntimeMixin):
                stack.extend((node.first, node.second))
        return len(seen)

    def runtime_stats(self) -> dict[str, int]:
        from devtools.proofs.block_runtime_stats import composed_runtime_stats

        return composed_runtime_stats(cast("ComposedBlockEffect", self))


__all__ = ["ComposedRuntimeMixin", "_FunctionalBoundaryState"]
