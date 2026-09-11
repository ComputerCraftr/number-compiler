"""Source-independent physical-Collatz block powering.

The physical map

    C(n) = 3*n+1  (n odd)
           n/2    (n even)

is a finite two-sided digit transducer on an LSD-first binary tape:

* odd ``3*n+1`` uses a finite LSD->MSD state containing the previous input bit
  and one carry bit;
* even ``n/2`` is a one-cell structural right-context lookup;
* the first input bit selects the phase and that phase is propagated in the
  left boundary state;
* blank padding is a third alphabet symbol and is never part of semantic digit
  content.

Consequently the atom is source-independent and can be squared by the same
canonical compiler algebra used by reverse/add.  No parity itinerary or
whole-state successor chain is discovered while constructing ``C**n``.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, Iterator

from number_compiler.arithmetic.contracts.block_effect import (
    _OPERATOR_IDS,
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_power_types import BlockPower
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.temporal_family import _issue_certificate
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    value_from_lsd_digits,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_unindexed_metrics
from number_compiler.resources.metric_records import (
    HashLifeBehaviorMetrics,
    LedgerMetrics,
)
from number_compiler.resources.powered_metrics import project_powered_metrics

if TYPE_CHECKING:
    from number_compiler.projection.lazy_radix import RadixProjection


# Left boundary states.  START means no active source digit has been consumed.
_START = 0
_EVEN = 1


# Odd states encode (previous_bit, carry) in states 2..5.
def _odd_state(previous: int, carry: int) -> int:
    previous = require_integer(previous, "previous Collatz bit", 0, 1)
    carry = require_integer(carry, "Collatz carry", 0, 1)
    if previous not in (0, 1) or carry not in (0, 1):
        raise ValueError((previous, carry))
    return 2 + (previous << 1) + carry


def _odd_parts(state: int) -> tuple[int, int]:
    state = require_integer(state, "Collatz odd state", 2, 5)
    if not 2 <= state <= 5:
        raise ValueError(state)
    value = state - 2
    return (value >> 1) & 1, value & 1


@dataclass(frozen=True, slots=True)
class CollatzPhysicalBlockMetrics(LedgerMetrics):
    seed: int
    steps: int
    operator_nodes: int
    compose_operations: int
    syntax_depth_bound: int
    descriptor_bits: int
    point_queries: int
    retained_execution_nodes: int
    canonical_program_word_roots: int
    left_boundary_residuals: int
    right_boundary_residuals: int
    direct_powered_point_queries: int
    temporal_leaf_applications: int
    canonical_spacetime_macrocell_roots: int = 0
    spacetime_tile_output_entries: int = 0
    spacetime_tile_output_max_level: int = 0
    spacetime_temporal_absorption_max: int = 0
    high_level_tile_hits: int = 0
    high_level_tile_misses: int = 0
    retained_cache_entries: int = 0
    raw_spacetime_boundary_cache_entries: int = 0
    retained_cache_accounting_delta: int = 0
    spacetime_macro_cache_hits: int = 0
    spacetime_macro_cache_misses: int = 0
    spacetime_macro_cache_entries: int = 0
    spacetime_tile_advance_cache_hits: int = 0
    spacetime_tile_advance_cache_misses: int = 0
    spacetime_tile_advance_cache_entries: int = 0
    spacetime_tile_output_cache_hits: int = 0
    spacetime_tile_output_cache_misses: int = 0
    spacetime_boundary_advance_cache_hits: int = 0
    spacetime_boundary_advance_cache_misses: int = 0
    spacetime_boundary_advance_cache_entries: int = 0
    spacetime_reverse_boundary_advance_cache_hits: int = 0
    spacetime_reverse_boundary_advance_cache_misses: int = 0
    spacetime_reverse_boundary_advance_cache_entries: int = 0
    spacetime_boundary_output_cache_hits: int = 0
    spacetime_boundary_output_cache_misses: int = 0
    spacetime_boundary_output_cache_entries: int = 0
    spacetime_sparse_transition_cache_hits: int = 0
    spacetime_sparse_transition_cache_misses: int = 0
    spacetime_sparse_transition_cache_entries: int = 0
    scalar_emit_cache_hits: int = 0
    scalar_emit_cache_misses: int = 0
    scalar_emit_cache_entries: int = 0
    scalar_emit_compiler_probes: int = 0
    canonical_tile_arena_nodes: int = 0
    canonical_tile_intern_hits: int = 0
    canonical_tile_intern_misses: int = 0
    canonical_tile_mirror_hits: int = 0
    canonical_tile_mirror_misses: int = 0
    total_hashlife_retained_entries: int = 0
    canonical_function_left_states: int = 0
    canonical_function_right_states: int = 0
    canonical_partition_left_states: int = 0
    canonical_partition_right_states: int = 0
    canonical_recursive_left_states: int = 0
    canonical_recursive_right_states: int = 0
    recursive_action_left_nodes: int = 0
    recursive_action_right_nodes: int = 0
    recursive_state_intern_hits: int = 0
    recursive_state_intern_misses: int = 0
    recursive_action_intern_hits: int = 0
    recursive_action_intern_misses: int = 0
    recursive_value_cache_hits: int = 0
    recursive_value_cache_misses: int = 0
    recursive_value_cache_entries: int = 0
    partition_preimage_cache_hits: int = 0
    partition_preimage_cache_misses: int = 0
    symbolic_output_row_cache_hits: int = 0
    symbolic_output_row_cache_misses: int = 0
    symbolic_output_row_cache_entries: int = 0
    symbolic_output_group_evals: int = 0
    boundary_value_index_builds: int = 0
    functional_carrier_layers_left: int = 0
    functional_carrier_layers_right: int = 0
    partition_carrier_layers_left: int = 0
    partition_carrier_layers_right: int = 0
    recursive_carrier_layers_left: int = 0
    recursive_carrier_layers_right: int = 0
    first_recursive_exponent_left: int = 0
    first_recursive_exponent_right: int = 0
    sparse_carrier_layers_left: int = 0
    sparse_carrier_layers_right: int = 0
    first_sparse_exponent_left: int = 0
    first_sparse_exponent_right: int = 0
    max_partition_domain_left: int = 0
    max_partition_domain_right: int = 0
    mixed_finite_carrier_layers: int = 0
    compiler_retained_execution_nodes: int = 0
    query_retained_execution_nodes: int = 0
    compiler_retained_cache_entries: int = 0
    query_retained_cache_entries: int = 0
    budgeted_cache_entries: int = 0
    leaf_effect_cache_entries: int = 0
    source_index_cache_entries: int = 0
    finite_action_cache_entries: int = 0
    canonical_tile_arena_nodes_global: int = 0
    canonical_tile_arena_nodes_index_build: int = 0
    canonical_tile_arena_nodes_query: int = 0
    canonical_tile_intern_hits_index_build: int = 0
    canonical_tile_intern_misses_index_build: int = 0
    canonical_tile_mirror_hits_index_build: int = 0
    canonical_tile_mirror_misses_index_build: int = 0
    canonical_tile_intern_hits_query: int = 0
    canonical_tile_intern_misses_query: int = 0
    canonical_tile_mirror_hits_query: int = 0
    canonical_tile_mirror_misses_query: int = 0
    canonical_tile_node_id_collisions: int = 0
    canonical_tile_invalid_intern_entries: int = 0
    canonical_tile_mirror_involution_violations: int = 0
    operator_node_id_collisions: int = 0
    semantic_effect_duplicate_owners: int = 0
    compiler_recursive_state_intern_hits: int = 0
    compiler_recursive_state_intern_misses: int = 0
    compiler_recursive_action_intern_hits: int = 0
    compiler_recursive_action_intern_misses: int = 0
    compiler_recursive_value_cache_hits: int = 0
    compiler_recursive_value_cache_misses: int = 0
    compiler_recursive_value_cache_entries: int = 0
    compiler_partition_preimage_cache_hits: int = 0
    compiler_partition_preimage_cache_misses: int = 0
    compiler_partition_preimage_cache_entries: int = 0
    compiler_symbolic_output_row_cache_hits: int = 0
    compiler_symbolic_output_row_cache_misses: int = 0
    compiler_symbolic_output_row_cache_entries: int = 0
    compiler_symbolic_output_group_evals: int = 0
    spacetime_tile_advance_repeated_cold_misses: int = 0
    spacetime_tile_output_repeated_cold_misses: int = 0
    scalar_emit_repeated_cold_misses: int = 0
    recursive_value_repeated_cold_misses: int = 0
    algebraic_memo_cache_entries: int = 0
    compiler_algebraic_memo_cache_entries: int = 0
    query_algebraic_memo_cache_entries: int = 0
    partition_preimage_cache_entries: int = 0
    partition_preimage_map_cache_entries: int = 0
    partition_emit_mask_cache_entries: int = 0
    boundary_anchor_mask_cache_entries: int = 0
    boundary_value_mask_cache_entries: int = 0
    compiler_partition_preimage_map_cache_entries: int = 0
    compiler_partition_emit_mask_cache_entries: int = 0
    compiler_boundary_anchor_mask_cache_entries: int = 0
    compiler_boundary_value_mask_cache_entries: int = 0
    bounded_application_enabled: int = 0
    bounded_application_temporal_state_classes: int = 0
    bounded_application_temporal_action_classes: int = 0
    bounded_application_exact_spatial_occurrences: int = 0
    bounded_application_symbolic_action_nodes: int = 0
    bounded_application_jump_entries: int = 0
    bounded_application_primitive_step_evaluations: int = 0
    bounded_application_action_compositions: int = 0
    bounded_application_action_applications: int = 0
    bounded_application_nonlinear_branch_evaluations: int = 0
    bounded_application_exact_endpoint_entries: int = 0
    bounded_application_query_requests: int = 0
    bounded_application_quotient_builds: int = 0
    bounded_application_residual_physical_steps: int = 0
    bounded_application_retained_entries: int = 0


class CollatzPhysicalBlockEffect:
    """One exact physical Collatz step on a padded LSD-first binary tape."""

    __slots__ = (
        "_sealed",
        "base",
        "blank",
        "exponent",
        "node_id",
        "blank_left_tail",
        "blank_right_tail",
        "stable_blank_output",
        "supports_predecessor_trace",
        "eager_boundary_quotient",
    )

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("kernel definitions are immutable")
        object.__setattr__(self, name, value)

    def __delattr__(self, name: str) -> None:
        raise AttributeError("immutable definition attributes cannot be deleted")

    def __init__(self) -> None:
        self.base = 2
        self.blank = 2
        self.exponent = 1
        self.node_id = next(_OPERATOR_IDS)
        # An odd multiplication settles after at most two blank cells; an even
        # shift needs only the immediately higher source symbol.
        self.blank_left_tail = 2
        self.blank_right_tail = 1
        self.stable_blank_output = True
        self.supports_predecessor_trace = False
        # The complete atom carrier is only 6 left states x 3 right states.
        # This opt-in lets composed powers retain exact extensional normalized
        # action tables instead of falling back to provenance words.
        self.eager_boundary_quotient = True
        self._sealed = True

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-physical-block", 1)

    def initial(self, side: BoundarySide) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        return _START if side is BoundarySide.LEFT else self.blank

    def boundary_universe(
        self,
        side: BoundarySide,
        *,
        max_states: int | None = None,
    ) -> tuple[int, ...] | None:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        states = tuple(range(6)) if side is BoundarySide.LEFT else (0, 1, self.blank)
        if max_states is not None:
            max_states = require_integer(max_states, "maximum boundary states", 0)
        if max_states is not None and len(states) > max_states:
            return None
        return states

    def advance(self, side: BoundarySide, state: BoundaryState, symbol: int) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("Collatz boundary side must be an exact enum value")
        state = require_integer(state, "Collatz boundary state")
        symbol = require_integer(symbol, "Collatz source symbol")
        if symbol not in (0, 1, self.blank):
            raise ValueError(symbol)
        if side is BoundarySide.RIGHT:
            # After scanning a suffix from high to low, the right state is the
            # symbol immediately above the current position.
            return symbol

        if state == _START:
            if symbol == self.blank:
                return _START
            if symbol == 0:
                return _EVEN
            # x0=1 selects odd mode.  At the first cell, 1 + 0 + 0 + 1 = 2,
            # so the carry after the cell is one and previous input is one.
            return _odd_state(1, 1)
        if state == _EVEN:
            return _EVEN
        previous, carry = _odd_parts(state)
        current = 0 if symbol == self.blank else symbol
        total = current + previous + carry
        return _odd_state(current, total >> 1)

    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int:
        left = require_integer(left, "Collatz left boundary")
        symbol = require_integer(symbol, "Collatz source symbol")
        right = require_integer(right, "Collatz right boundary")
        if symbol not in (0, 1, self.blank) or right not in (0, 1, self.blank):
            raise ValueError((symbol, right))

        consumes_right, local = self.output_consumer(left, symbol)
        return right if consumes_right else local

    def output_consumer(self, left: int, symbol: int) -> tuple[bool, int]:
        """Return the geometry-selected right view and left-local output.

        ``True`` means the even shift consumes the adjacent higher symbol.
        The other branch is already an exact output of the odd carry state.
        """
        left = require_integer(left, "Collatz left boundary")
        symbol = require_integer(symbol, "Collatz source symbol")
        if symbol not in (0, 1, self.blank):
            raise ValueError(symbol)

        # The first digit itself chooses the global Collatz branch.
        if left == _START:
            if symbol == self.blank:
                return False, self.blank
            if symbol == 0:
                return True, 0
            # Odd first cell includes +1.
            return False, (symbol + 1) & 1

        if left == _EVEN:
            # Binary division by two: output_i = input_(i+1).  A blank next
            # symbol means this and every higher output position is blank.
            return True, 0

        previous, carry = _odd_parts(left)
        current = 0 if symbol == self.blank else symbol
        total = current + previous + carry
        if symbol == self.blank and total == 0:
            return False, self.blank
        return False, total & 1

    def predecessor(self, side: BoundarySide, state: BoundaryState) -> None:
        return None

    def operator_nodes(self) -> int:
        return 1

    def runtime_stats(self) -> dict[str, int]:
        return {
            "operator_nodes": 1,
            "retained_execution_nodes": 0,
            "canonical_program_word_roots": 0,
            "left_boundary_residuals": 0,
            "right_boundary_residuals": 0,
            "residual_cache_hits": 0,
            "residual_cache_misses": 0,
            "output_cache_hits": 0,
            "output_cache_misses": 0,
            "output_cache_slots": 0,
            "output_cache_occupied": 0,
            "left_transition_entries": 0,
            "right_transition_entries": 0,
            "finite_kernel_left_states": 0,
            "finite_kernel_right_states": 0,
            "finite_kernel_storage_bytes": 0,
            "leaf_effect_transition_cache_entries": 0,
            "leaf_effect_output_cache_entries": 0,
            "leaf_effect_cache_entries": 0,
        }


def power_collatz_physical_effect(
    steps: int,
    *,
    max_context_nodes: int | None = None,
    max_cache_entries: int | None = None,
) -> BlockPower:
    """Compile ``physical_collatz**steps`` by source-independent squaring."""
    steps = require_integer(steps, "Collatz physical steps", 0)
    compiler = LazyCompiler(ResourceLedger(max_context_nodes, max_cache_entries))
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    return compile_collatz_physical_power(compiler, steps)


class PoweredCollatzTerm:
    """Exact physical Collatz nth state using only the powered block fast path."""

    __slots__ = (
        "__weakref__",
        "seed",
        "steps",
        "seed_digits",
        "_source_construction",
        "power",
        "effect",
        "compose_operations",
        "syntax_depth_bound",
        "_index",
        "_radix_projections",
        "_ledger",
        "_compiler",
        "_max_context_nodes",
        "_max_cache_entries",
        "_active_width",
        "_microblocks",
    )

    def __init__(
        self,
        seed: int,
        steps: int,
        *,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
    ) -> None:
        seed = require_integer(seed, "seed", 1)
        steps = require_integer(steps, "steps", 0)
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self.seed = seed
        self.steps = steps
        self.seed_digits = tuple(map(int, digits_lsd(seed, 2)))
        self._source_construction = OriginalSourceConstruction(
            ExactSource(
                self.seed_digits, 2, blank=2, extent=self.maximum_width, alphabet_size=2
            ),
        )
        self._ledger.register_execution_root(self)
        self._compiler = LazyCompiler(self._ledger)
        self._max_context_nodes = max_context_nodes
        self._max_cache_entries = max_cache_entries
        self._index: HashLifeBlockIndex | None = None
        radix_owner = self._ledger.register(
            "radix-applications", "application_index", "INDEX_OWNED"
        )
        self._radix_projections: MutableMapping[int, RadixProjection] = (
            self._ledger.make_dict(radix_owner)
        )
        self._active_width: int | None = None
        from number_compiler.projection.microblock_cache import MicroblockCache

        self._microblocks = MicroblockCache(
            self._ledger,
            self._compiler.token,
            self._compiler.resolve,
        )
        if steps == 0:
            self.power = None
            self.effect = None
            self.compose_operations = 0
            self.syntax_depth_bound = 0
            return
        from number_compiler.sequences.collatz.compilation import (
            compile_collatz_physical_power,
        )

        power = compile_collatz_physical_power(self._compiler, steps)
        if power.root is None:
            raise AssertionError("positive Collatz exponent without powered effect")
        self.power = power
        self.effect = power.root
        self.compose_operations = power.compose_operations
        self.syntax_depth_bound = power.syntax_depth

    @property
    def maximum_width(self) -> int:
        # For every two physical ticks, ``y + 2 <= 3 * (x + 2) / 2`` whether
        # the first tick is odd or even.  Also ``(3/2)**32 < 2**19``.  The
        # resulting rational exponent bound is exact integer metadata: it
        # avoids both materializing ``3**pairs`` and allocating the much looser
        # half-step padding that used to dominate cold point observations.
        pairs, remainder = divmod(self.steps, 2)
        pair_growth = (19 * pairs + 31) // 32
        paired_bound = min(
            len(self.seed_digits) + pairs,
            (self.seed + 2).bit_length() + pair_growth,
        )
        return paired_bound + 2 * remainder + 2

    @property
    def operator_nodes(self) -> int:
        # Compilation already froze this structural count in ``BlockPower``.
        # Re-walking the live effect here can populate canonical composition
        # interners after a metrics snapshot, making reporting mutate the very
        # counters it reports.
        return 0 if self.power is None else int(self.power.operator_nodes)

    @property
    def descriptor_bits(self) -> int:
        return bit_width(self.seed) + bit_width(self.steps) + 2

    def _point_index(self) -> HashLifeBlockIndex:
        if self.steps == 0 or self.effect is None:
            raise ValueError("step zero is a literal seed")
        found = self._index
        if found is None:
            found = HashLifeBlockIndex(
                self.effect,
                self.seed_digits,
                logical_length=self.maximum_width,
                source_construction=self._source_construction,
                certificate=_issue_certificate(
                    self.effect, "collatz", self.steps, ledger=self._ledger
                ),
                max_tile_nodes=self._max_context_nodes,
                max_cache_entries=self._max_cache_entries,
                ledger=self._ledger,
                compiler=self._compiler,
                microblocks=self._microblocks,
            )
            self._index = found
        return found

    @source_reads_only
    def _point_symbol(self, position: int) -> int:
        """Observe a binary cell, preserving the kernel's explicit blank symbol."""
        position = require_integer(position, "digit coordinate")
        if not 0 <= position < self.maximum_width:
            raise IndexError(position)
        if self.steps == 0:
            if position >= len(self.seed_digits):
                return 2
            return int(self.seed_digits[position])
        value = self._point_index().direct_powered_point(position)
        if value not in (0, 1, 2):
            raise AssertionError(value)
        return int(value)

    @source_reads_only
    def digit(self, position: int) -> int:
        value = self._point_symbol(position)
        if value == 2:
            raise IndexError(position)
        return value

    @source_reads_only
    def width(self) -> int:
        if self.steps == 0:
            return len(self.seed_digits)
        found = self._active_width
        if found is None:
            found = self._point_index().direct_active_width()
            self._active_width = found
        return found

    @property
    def estimated_bit_length(self) -> int:
        return self.width()

    def iter_digits(self) -> Iterator[int]:
        if self.steps == 0:
            yield from self.seed_digits
            return
        yield from self._point_index().iter_direct_active()

    def digits(self) -> tuple[int, ...]:
        return tuple(map(int, self.iter_digits()))

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        width = self.width()
        if width > max_bits:
            raise ValueError((width, max_bits))
        return value_from_lsd_digits(self.iter_digits(), 2)

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        """Return the seed/function/application HashLife description split.

        This metric does not materialize the output word.  For positive powers it
        reports the compact source-independent jump function separately from the
        seed-specific causal state/action description created by point queries.
        """
        return self._point_index().behavior_metrics()

    def metrics(self) -> CollatzPhysicalBlockMetrics:
        if self._index is None:
            point = collect_unindexed_metrics(self._ledger)
        else:
            point = self._index.metrics()
        return project_powered_metrics(
            CollatzPhysicalBlockMetrics,
            point,
            seed=self.seed,
            steps=self.steps,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
        )


__all__ = [
    "CollatzPhysicalBlockEffect",
    "CollatzPhysicalBlockMetrics",
    "power_collatz_physical_effect",
    "PoweredCollatzTerm",
]
