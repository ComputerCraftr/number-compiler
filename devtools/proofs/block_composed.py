from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from typing import TypeVar, cast

from devtools.proofs.block_partition import (
    PartitionCompositionMixin,
    _PartitionBoundaryState,
)
from devtools.proofs.block_recursive import (
    _RecursiveResidualAction,
)
from devtools.proofs.block_runtime import ComposedRuntimeMixin, _FunctionalBoundaryState
from number_compiler.arithmetic.contracts.block_definition import (
    BlockDefinition,
    CompatibilityCompositionRuntime,
    ComposedBlockDefinition,
)
from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BlockContextBudget,
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _effect_key,
    _state_key,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger

_K = TypeVar("_K")
_V = TypeVar("_V")
_T = TypeVar("_T")


class ComposedBlockEffect(
    CompatibilityCompositionRuntime,
    PartitionCompositionMixin,
    ComposedRuntimeMixin,
):
    """Explicit execution context for ``second(first(input))`` definitions.

    The public algebra has only ``initial(side)``, ``advance(side,...)`` and
    ``emit``.  Direction is data, not a duplicated class/API hierarchy.
    Composition substitutes the two-sided transducer equations directly; it
    never applies either child to an intermediate word.
    """

    __slots__ = (
        "_definition",
        "_first_context",
        "_second_context",
        "_node_id",
        "budget",
        "_partition_domain_liftable",
        "_initial",
        "_transition_entries",
        "_states",
        "_map_eval_hits",
        "_map_eval_misses",
        "_output_slots",
        "_output_cache_hits",
        "_output_cache_misses",
        "_output_uncached_probes",
        "_sparse_emit_delegations",
        "_sparse_emit_admission_bits",
        "_sparse_emit_first_seen",
        "_sparse_emit_admissions",
        "_blank_saturation_cap",
        "_blank_saturation_hits",
        "_functional_enabled",
        "_functional_domains",
        "_functional_domain_index",
        "_functional_intern",
        "_functional_intern_hits",
        "_functional_intern_misses",
        "_partition_enabled",
        "_partition_domains",
        "_partition_domain_index",
        "_partition_full_masks",
        "_partition_intern",
        "_partition_intern_hits",
        "_partition_intern_misses",
        "_partition_preimage_maps",
        "_partition_preimage_cache",
        "_partition_preimage_hits",
        "_partition_preimage_misses",
        "_partition_emit_masks",
        "_symbolic_output_rows",
        "_boundary_anchor_masks",
        "_boundary_value_masks",
        "_symbolic_output_row_hits",
        "_symbolic_output_row_misses",
        "_symbolic_output_group_evals",
        "_boundary_value_index_builds",
        "_boundary_universe",
        "_recursive_enabled",
        "_recursive_residual_intern",
        "_recursive_constant",
        "_recursive_value_cache",
        "_recursive_residual_intern_hits",
        "_recursive_residual_intern_misses",
        "_recursive_value_cache_hits",
        "_recursive_value_cache_misses",
        "_macro_tile_advance_cache",
        "_macro_tile_output_cache",
        "_macro_output_hits",
        "_macro_output_misses",
        "_macro_tile_advance_hits",
        "_macro_tile_advance_misses",
        "_macro_boundary_advance_hits",
        "_macro_boundary_advance_misses",
        "_macro_tile_output_hits",
        "_macro_tile_output_misses",
        "_macro_boundary_output_hits",
        "_macro_boundary_output_misses",
        "_provider_task_cache",
        "_provider_task_hits",
        "_provider_task_misses",
        "_ledger",
        "_owned_store_serial",
    )

    def __init__(
        self,
        first: BlockEffect,
        second: BlockEffect,
        *,
        budget: BlockContextBudget,
        _definition: ComposedBlockDefinition | None = None,
        _force_recursive: bool = False,
        _force_functional: bool = False,
        _ledger: ResourceLedger | None = None,
    ) -> None:
        if first.base != second.base or first.blank != second.blank:
            raise ValueError((first.base, second.base, first.blank, second.blank))
        definition = (
            ComposedBlockDefinition(first, second)
            if _definition is None
            else _definition
        )
        if _effect_key(first) != _effect_key(definition.first) or _effect_key(
            second
        ) != _effect_key(definition.second):
            raise ValueError("runtime children do not match the immutable composition")
        self._definition = definition
        self._first_context, self._second_context = first, second
        self._node_id = next(_OPERATOR_IDS)
        self.budget = budget
        self._ledger = _ledger
        self._owned_store_serial = 0
        # True only for a partition carrier whose domain came directly from a
        # complete extensional/function carrier.  A parent may consume this
        # capability once to build one higher exact partition bimachine.  The
        # resulting partition does not propagate the capability again, avoiding
        # the old eager-universe cliff without an exponent or state-count gate.
        self._partition_domain_liftable = False
        # Exact extensional canonicalization is installed at the bottom T^2
        # composition, where the complete first-effect domains are tiny and
        # fixed (base boundary automata).  Higher compositions consume these
        # canonical T^2 identities, but do not flatten a large child universe
        # into a giant vector merely to claim canonicalization.
        domains: list[tuple[BoundaryState, ...] | None] = [None, None]
        enabled = [False, False]
        if _force_recursive and _force_functional:
            raise ValueError("proof carrier cannot be both recursive and functional")
        if _force_functional:
            domains[0] = first.boundary_universe(BoundarySide.RIGHT)
            domains[1] = first.boundary_universe(BoundarySide.LEFT)
            if domains[0] is None or domains[1] is None:
                raise ValueError(
                    "forced proof function carrier requires finite child domains"
                )
            enabled = [True, True]
        elif (
            not _force_recursive
            and isinstance(first, BaseBlockEffect)
            and isinstance(second, BaseBlockEffect)
        ):
            domains[0] = first.boundary_universe(BoundarySide.RIGHT)
            domains[1] = first.boundary_universe(BoundarySide.LEFT)
            enabled = [True, True]
        elif (
            not _force_recursive
            and self.eager_boundary_quotient
            and not isinstance(first, ComposedRuntimeMixin)
        ):
            # The atom explicitly certifies a complete extensional boundary
            # quotient.  Consume that capability exactly; do not make carrier
            # selection depend on an arbitrary state-count cutoff.  Once the
            # first child is itself composed, the reduced partition/MTDD carrier
            # below is authoritative, so the extensional vector does not keep
            # propagating upward as a second state space.
            domains[0] = first.boundary_universe(BoundarySide.RIGHT)
            domains[1] = first.boundary_universe(BoundarySide.LEFT)
            if domains[0] is None or domains[1] is None:
                raise AssertionError("certified eager boundary quotient did not close")
            enabled = [True, True]

        self._functional_enabled = (enabled[0], enabled[1])
        self._functional_domains: tuple[
            tuple[BoundaryState, ...] | None, tuple[BoundaryState, ...] | None
        ] = (domains[0], domains[1])
        self._functional_domain_index: tuple[
            dict[object, int] | None, dict[object, int] | None
        ] = (
            None
            if domains[0] is None
            else {_state_key(q): i for i, q in enumerate(domains[0])},
            None
            if domains[1] is None
            else {_state_key(q): i for i, q in enumerate(domains[1])},
        )
        self._functional_intern: tuple[
            dict[tuple[object, tuple[object, ...]], _FunctionalBoundaryState] | None,
            dict[tuple[object, tuple[object, ...]], _FunctionalBoundaryState] | None,
        ] = ({} if enabled[0] else None, {} if enabled[1] else None)
        self._functional_intern_hits = 0
        self._functional_intern_misses = 0

        # When the first child is already a proved finite semantic quotient, its
        # opposite boundary domain has stable integer identities.  Represent the
        # continuation as an exact partition of that finite domain.  Transition
        # updates use bitset preimages and output-selector intersections, which
        # is the reduced one-coordinate MTDD operation specialized to this
        # bimachine composition.  No argument-cell vector is materialized.
        partition_domains: list[tuple[BoundaryState, ...] | None] = [None, None]
        partition_enabled = [False, False]
        if not _force_recursive and isinstance(first, FiniteBlockEffect):
            partition_domains[0] = first.boundary_universe(BoundarySide.RIGHT)
            partition_domains[1] = first.boundary_universe(BoundarySide.LEFT)
            partition_enabled = [True, True]
        elif (
            False
            and isinstance(first, ComposedRuntimeMixin)
            and bool(getattr(first, "eager_boundary_quotient", False))
            and all(first._functional_enabled)
            and not any(first._partition_enabled)
            and not any(first._recursive_enabled)
        ):
            # First exact symbolic lift: the child is an extensional function
            # carrier over the source family's certified finite atom domain.
            partition_domains[0] = first.boundary_universe(BoundarySide.RIGHT)
            partition_domains[1] = first.boundary_universe(BoundarySide.LEFT)
            partition_enabled = [True, True]
            self._partition_domain_liftable = True
        elif (
            isinstance(first, ComposedRuntimeMixin)
            and bool(getattr(first, "_partition_domain_liftable", False))
            and all(first._partition_enabled)
            and not any(first._recursive_enabled)
        ):
            # Second exact symbolic lift: consume the child capability once.
            # Physical Collatz T^4 closes at 50/90 boundary states, so T^8 can
            # stay in the exact partition bimachine instead of manufacturing
            # thousands of recursive prefix occurrences.  This resulting T^8
            # carrier deliberately does not advertise another lift; higher
            # powers use the recursive quadtree rather than enumerating T^8.
            partition_domains[0] = first.boundary_universe(BoundarySide.RIGHT)
            partition_domains[1] = first.boundary_universe(BoundarySide.LEFT)
            if partition_domains[0] is None or partition_domains[1] is None:
                raise AssertionError("liftable partition child did not close")
            partition_enabled = [True, True]
        # IMPORTANT: once ``first`` is a partition or recursive composed effect,
        # do not enumerate its reachable boundary universe.  That was the eager-
        # universe barrier that made higher powers either compile millions of
        # states or manufacture a second raw boundary-history carrier behind
        # exponent/state-count cutoffs.
        self._partition_enabled = (partition_enabled[0], partition_enabled[1])
        self._partition_domains: tuple[
            tuple[BoundaryState, ...] | None, tuple[BoundaryState, ...] | None
        ] = (partition_domains[0], partition_domains[1])
        self._partition_domain_index: tuple[
            dict[object, int] | None, dict[object, int] | None
        ] = (
            None
            if partition_domains[0] is None
            else {_state_key(q): i for i, q in enumerate(partition_domains[0])},
            None
            if partition_domains[1] is None
            else {_state_key(q): i for i, q in enumerate(partition_domains[1])},
        )
        self._partition_full_masks = (
            0 if partition_domains[0] is None else (1 << len(partition_domains[0])) - 1,
            0 if partition_domains[1] is None else (1 << len(partition_domains[1])) - 1,
        )
        self._partition_intern: tuple[
            dict[tuple[object, tuple[tuple[object, int], ...]], _PartitionBoundaryState]
            | None,
            dict[tuple[object, tuple[tuple[object, int], ...]], _PartitionBoundaryState]
            | None,
        ] = ({} if partition_enabled[0] else None, {} if partition_enabled[1] else None)
        self._partition_intern_hits = 0
        self._partition_intern_misses = 0
        # For each side/symbol, target-index -> bitset of source arguments whose
        # first-child transition lands on that target.
        self._partition_preimage_maps: tuple[
            dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]
        ] = ({}, {})
        self._partition_preimage_cache: tuple[
            dict[tuple[int, int], int], dict[tuple[int, int], int]
        ] = ({}, {})
        self._partition_preimage_hits = 0
        self._partition_preimage_misses = 0
        # (anchor semantic key, symbol) -> exact first-output selector masks.
        self._partition_emit_masks: tuple[
            dict[tuple[object, int], tuple[int, ...]],
            dict[tuple[object, int], tuple[int, ...]],
        ] = ({}, {})
        # Canonical child-owned output rows over the complete reachable opposite
        # boundary universe.  Parent partition compilation consumes these rows
        # directly instead of probing one scalar (left,symbol,right) tuple per
        # argument.  The inverse indexes are algebraic structure, not runtime
        # projection memoization.
        self._symbolic_output_rows: tuple[
            dict[tuple[object, int], tuple[int, ...]],
            dict[tuple[object, int], tuple[int, ...]],
        ] = ({}, {})
        self._boundary_anchor_masks: list[
            dict[object, tuple[BoundaryState, int]] | None
        ] = [None, None]
        self._boundary_value_masks: tuple[
            dict[int, dict[object, tuple[BoundaryState, int]]],
            dict[int, dict[object, tuple[BoundaryState, int]]],
        ] = ({}, {})
        self._symbolic_output_row_hits = 0
        self._symbolic_output_row_misses = 0
        self._symbolic_output_group_evals = 0
        self._boundary_value_index_builds = 0

        self._boundary_universe: list[tuple[BoundaryState, ...] | None] = [None, None]

        # Higher composed effects use one exact recursive residual carrier.  It
        # stores algebraic child actions, not a materialized child-state universe
        # and not the already-scanned source boundary.
        recursive_enabled = [
            not partition_enabled[i] and not enabled[i] for i in (0, 1)
        ]
        self._recursive_enabled = (recursive_enabled[0], recursive_enabled[1])
        # The former boundary-state interner duplicated every recursive action
        # with a second wrapper object.  It is deleted; the residual action
        # itself is now the canonical boundary state.
        self._recursive_residual_intern: tuple[
            dict[tuple[object, ...], _RecursiveResidualAction] | None,
            dict[tuple[object, ...], _RecursiveResidualAction] | None,
        ] = ({} if recursive_enabled[0] else None, {} if recursive_enabled[1] else None)
        constants: list[_RecursiveResidualAction | None] = [None, None]
        self._states = [0, 0]
        self._recursive_residual_intern_hits = 0
        self._recursive_residual_intern_misses = 0
        self._recursive_value_cache_hits = 0
        self._recursive_value_cache_misses = 0
        self._recursive_value_cache: dict[tuple[object, object], BoundaryState] = {}
        for side_1 in (BoundarySide.LEFT, BoundarySide.RIGHT):
            if recursive_enabled[int(side_1)]:
                constants[int(side_1)] = _RecursiveResidualAction(
                    side_1,
                    None,
                    None,
                    self._canonical_child_state(first, side_1, first.initial(side_1)),
                )
                self.budget.consume_node()
                self._states[int(side_1)] += 1
                from number_compiler.arithmetic.automata.guard import (
                    record_residual_metrics,
                )

                record_residual_metrics(states=1)
        self._recursive_constant = (constants[0], constants[1])

        # Legacy sparse-root counters remain in the public metrics so old callers
        # can verify they are zero.  Production higher-power temporal state no
        # longer enters this interner.
        self._macro_output_hits = 0
        self._macro_output_misses = 0
        self._macro_tile_advance_hits = 0
        self._macro_tile_advance_misses = 0
        self._macro_boundary_advance_hits = 0
        self._macro_boundary_advance_misses = 0
        self._macro_tile_output_hits = 0
        self._macro_tile_output_misses = 0
        self._macro_boundary_output_hits = 0
        self._macro_boundary_output_misses = 0
        self._macro_tile_advance_cache: dict[tuple[object, ...], BoundaryState] = {}
        self._macro_tile_output_cache: dict[tuple[object, ...], object] = {}
        self._provider_task_cache: dict[tuple[object, ...], BoundaryState] = {}
        self._provider_task_hits = 0
        self._provider_task_misses = 0
        initial: list[BoundaryState] = []
        for side_2 in (BoundarySide.LEFT, BoundarySide.RIGHT):
            index = int(side_2)
            domain = domains[index]
            partition_domain = partition_domains[index]
            if partition_enabled[index]:
                if partition_domain is None:
                    raise AssertionError("enabled partition residual without domain")
                initial.append(
                    self._intern_partition_state(
                        side_2,
                        first.initial(side_2),
                        ((second.initial(side_2), self._partition_full_masks[index]),),
                    )
                )
            elif enabled[index]:
                if domain is None:
                    raise AssertionError("enabled canonical residual without domain")
                image = tuple(second.initial(side_2) for _ in domain)
                initial.append(
                    self._intern_functional_state(side_2, first.initial(side_2), image)
                )
            else:
                constant = self._recursive_constant[index]
                if constant is None:
                    raise AssertionError("missing recursive residual constant")
                initial.append(
                    self._intern_recursive_state(
                        side_2, first.initial(side_2), constant
                    )
                )
        self._initial = (initial[0], initial[1])
        self._transition_entries = [0, 0]
        self._map_eval_hits = 0
        self._map_eval_misses = 0

        # Generic blank-composition theorem.  Once the first effect's local
        # boundary is fixed, the induced residual map is absorbed after the
        # opposite first-tail plus the matching second-tail.
        saturation: tuple[int, int] | None = None
        if first.stable_blank_output and second.stable_blank_output:
            saturation = (
                first.blank_right_tail + second.blank_left_tail,
                first.blank_left_tail + second.blank_right_tail,
            )
        self._blank_saturation_cap = (0, 0) if saturation is None else saturation
        self._blank_saturation_hits = [0, 0]
        # Projection-only exact semantic memo.  Entries are keyed by canonical
        # boundary-state identities and are governed by BlockContextBudget; no
        # direct-mapped collision may evict a proved reusable result.  Formula
        # construction allocates no output-cache entries.
        self._output_slots: dict[tuple[object, int, object], int] | None = None
        self._output_cache_hits = 0
        self._output_cache_misses = 0
        self._output_uncached_probes = 0
        # These legacy admission counters remain for metric compatibility.  The
        # production recursive carrier no longer emits raw-history scalar keys,
        # so they should remain zero in higher-power projection.
        self._sparse_emit_delegations = 0
        self._sparse_emit_admission_bits = 0
        self._sparse_emit_first_seen = 0
        self._sparse_emit_admissions = 0
        if self._ledger is not None:
            self._adopt_runtime_stores()

    def _owned_dict(
        self,
        role: str,
        values: Mapping[_K, _V] | None = None,
    ) -> MutableMapping[_K, _V]:
        ledger = self._ledger
        if ledger is None:
            return {} if values is None else dict(values)
        serial = self._owned_store_serial
        self._owned_store_serial += 1
        owner = ledger.register(
            f"block-runtime-{self._node_id}-{serial}-{role}",
            role,
        )
        result: OwnedMemo[_K, _V] = OwnedMemo(ledger, owner)
        if values:
            result.update(values)
        return result

    def _owned_list(self, role: str, values: list[_T]) -> MutableSequence[_T]:
        ledger = self._ledger
        if ledger is None:
            return list(values)
        serial = self._owned_store_serial
        self._owned_store_serial += 1
        owner = ledger.register(
            f"block-runtime-{self._node_id}-{serial}-{role}",
            role,
        )
        result: MutableSequence[_T] = ledger.make_list(
            owner,
            nodes_per_entry=0,
            append_only=False,
        )
        ledger.reserve(owner, entries=len(values))
        result.extend(values)
        return result

    def _adopt_runtime_stores(self) -> None:
        """Move every mutable execution store under the active index ledger."""
        self._functional_domain_index = cast(
            tuple[dict[object, int] | None, dict[object, int] | None],
            tuple(
                None
                if item is None
                else self._owned_dict("block_function_domain", item)
                for item in self._functional_domain_index
            ),
        )
        self._functional_intern = cast(
            tuple[
                dict[tuple[object, tuple[object, ...]], _FunctionalBoundaryState]
                | None,
                dict[tuple[object, tuple[object, ...]], _FunctionalBoundaryState]
                | None,
            ],
            tuple(
                None
                if item is None
                else self._owned_dict("block_function_interner", item)
                for item in self._functional_intern
            ),
        )
        self._partition_domain_index = cast(
            tuple[dict[object, int] | None, dict[object, int] | None],
            tuple(
                None
                if item is None
                else self._owned_dict("block_partition_domain", item)
                for item in self._partition_domain_index
            ),
        )
        self._partition_intern = cast(
            tuple[
                dict[
                    tuple[object, tuple[tuple[object, int], ...]],
                    _PartitionBoundaryState,
                ]
                | None,
                dict[
                    tuple[object, tuple[tuple[object, int], ...]],
                    _PartitionBoundaryState,
                ]
                | None,
            ],
            tuple(
                None
                if item is None
                else self._owned_dict("block_partition_interner", item)
                for item in self._partition_intern
            ),
        )
        for name_1 in (
            "_partition_preimage_maps",
            "_partition_preimage_cache",
            "_partition_emit_masks",
            "_symbolic_output_rows",
            "_boundary_value_masks",
            "_recursive_residual_intern",
        ):
            pair = getattr(self, name_1)
            setattr(
                self,
                name_1,
                tuple(
                    None
                    if item is None
                    else self._owned_dict("block_" + name_1[1:], item)
                    for item in pair
                ),
            )
        for name_2 in (
            "_recursive_value_cache",
            "_macro_tile_advance_cache",
            "_macro_tile_output_cache",
            "_provider_task_cache",
        ):
            setattr(
                self,
                name_2,
                self._owned_dict("block_" + name_2[1:], getattr(self, name_2)),
            )
        for name_3 in (
            "_boundary_anchor_masks",
            "_boundary_universe",
            "_states",
            "_transition_entries",
            "_blank_saturation_hits",
        ):
            setattr(
                self,
                name_3,
                self._owned_list("block_" + name_3[1:], getattr(self, name_3)),
            )

    @property
    def definition(self) -> ComposedBlockDefinition:
        return self._definition

    @property
    def node_id(self) -> int:
        return self._node_id

    @property
    def first(self) -> BlockEffect:
        return self._first_context

    @property
    def second(self) -> BlockEffect:
        return self._second_context

    @property
    def base(self) -> int:
        return self.definition.base

    @property
    def blank(self) -> int:
        return self.definition.blank

    @property
    def exponent(self) -> int:
        return self.definition.exponent

    @property
    def blank_left_tail(self) -> int:
        return self.definition.blank_left_tail

    @property
    def blank_right_tail(self) -> int:
        return self.definition.blank_right_tail

    @property
    def stable_blank_output(self) -> bool:
        return self.definition.stable_blank_output

    @property
    def supports_predecessor_trace(self) -> bool:
        return self.definition.supports_predecessor_trace

    @property
    def eager_boundary_quotient(self) -> bool:
        return self.definition.eager_boundary_quotient

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return self.definition.canonical_key

    @classmethod
    def from_definition(
        cls, definition: ComposedBlockDefinition, *, budget: BlockContextBudget
    ) -> ComposedBlockEffect:
        """Create independent runtime owners for every node of an immutable DAG."""
        if type(definition) is not ComposedBlockDefinition:
            raise TypeError("expected an immutable composition definition")
        built: dict[int, BlockEffect] = {}
        stack: list[tuple[BlockDefinition, bool]] = [(definition, False)]
        while stack:
            node, ready = stack.pop()
            if id(node) in built:
                continue
            if isinstance(node, ComposedBlockDefinition):
                if not ready:
                    stack.extend(
                        ((node, True), (node.second, False), (node.first, False))
                    )
                    continue
                result: BlockEffect = cls(
                    built[id(node.first)],
                    built[id(node.second)],
                    budget=budget,
                    _definition=node,
                )
            else:
                # Only sealed immutable primitives can occur in a definition.
                result = cast(BlockEffect, node)
            built[id(node)] = result
        return cast(ComposedBlockEffect, built[id(definition)])

    def _intern_functional_state(
        self,
        side: BoundarySide,
        anchor: BoundaryState,
        image: tuple[BoundaryState, ...],
    ) -> _FunctionalBoundaryState:
        pools = self._functional_intern
        anchor = self._canonical_child_state(self.first, side, anchor)
        image = tuple(self._canonical_child_state(self.second, side, q) for q in image)
        key = (_state_key(anchor), tuple(_state_key(q) for q in image))
        pool = pools[int(side)]
        if pool is None:
            raise AssertionError(
                "functional residual interner is not enabled for this side"
            )
        found = pool.get(key)
        if found is not None:
            self._functional_intern_hits += 1
            return found
        out = _FunctionalBoundaryState(side, anchor, image)
        pool[key] = out
        self._functional_intern_misses += 1
        self.budget.consume_node()
        self._states[int(side)] += 1
        from number_compiler.arithmetic.automata.guard import record_residual_metrics

        record_residual_metrics(states=1)
        return out

    def initial(self, side: BoundarySide) -> BoundaryState:
        return self._initial[int(side)]

    def boundary_universe(
        self, side: BoundarySide, *, max_states: int | None = None
    ) -> tuple[BoundaryState, ...] | None:
        """Return the complete reachable canonical boundary universe when small.

        The result is exact.  If ``max_states`` is crossed, ``None`` is returned
        and the caller must retain the path representation; partial enumeration
        is never used as evidence of function equality.
        """
        index = int(side)
        if not self._functional_enabled[index] and not self._partition_enabled[index]:
            return None
        cached = self._boundary_universe[index]
        if cached is not None:
            return cached if max_states is None or len(cached) <= max_states else None
        from collections import deque

        start = self.initial(side)
        if isinstance(start, _PartitionBoundaryState):
            start = self._canonical_partition_state(side, start)
        states: list[BoundaryState] = [start]
        seen: set[object] = {_state_key(start)}
        todo = deque([start])
        while todo:
            state = todo.popleft()
            for symbol in range(self.blank + 1):
                nxt = self.advance(side, state, symbol)
                if isinstance(nxt, _PartitionBoundaryState):
                    nxt = self._canonical_partition_state(side, nxt)
                semantic = _state_key(nxt)
                if semantic not in seen:
                    seen.add(semantic)
                    states.append(nxt)
                    if max_states is not None and len(states) > max_states:
                        return None
                    todo.append(nxt)
        out = tuple(states)
        self._boundary_universe[index] = out
        return out


__all__ = ["ComposedBlockEffect"]
