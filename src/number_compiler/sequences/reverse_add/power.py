"""Compact binary-powered reverse/add term descriptors and random access.

The immutable temporal operator descriptor is constructed by binary
composition, so construction retains ``O(log n)`` syntax.  Production digit,
width, and materialization queries use that source-independent powered operator
directly through :class:`HashLifeBlockIndex`.  The retired whole-field and
forcing-occurrence temporal lifts are reference/oracle machinery only and are
not reachable from this descriptor.

The public index uses recursive field images and output-complete interfaces.
Runtime metrics include semantic observation work and query retention; compiler
node counts alone do not establish HashLife execution scaling.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import ceil, log2
from typing import Iterator
from number_compiler.arithmetic.polynomials.twisted_observer import TwistedCylinderProjection

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
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
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_unindexed_metrics
from number_compiler.resources.metric_records import (
    HashLifeBehaviorMetrics,
    LedgerMetrics,
)
from number_compiler.resources.powered_metrics import project_powered_metrics
from number_compiler.sequences.reverse_add.compilation import compile_reverse_pair_power


def pair_field_from_integer(value: int, base: int) -> tuple[int, ...]:
    value = require_integer(value, "seed", 0)
    base = require_integer(base, "base", 2)
    digits = digits_lsd(value, base)
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


@dataclass(frozen=True, slots=True)
class ReverseAddPowerMetrics(LedgerMetrics):
    seed: int
    base: int
    generation: int
    operator_nodes: int
    compose_operations: int
    syntax_depth_bound: int
    descriptor_bits: int
    point_queries: int
    run_action_cache_entries: int
    retained_execution_nodes: int
    canonical_program_word_roots: int
    left_boundary_residuals: int
    right_boundary_residuals: int
    hashlife_section_cache_entries: int = 0
    hashlife_section_cache_hits: int = 0
    hashlife_tile_roots: int = 0
    hashlife_leaf_cache_entries: int = 0
    hashlife_leaf_cache_hits: int = 0
    hashlife_boundary_cache_entries: int = 0
    hashlife_boundary_cache_hits: int = 0
    hashlife_forest_chunks: int = 0
    hashlife_max_level: int = 0
    hashlife_temporal_leaf_applications: int = 0
    hashlife_high_level_tile_hits: int = 0
    hashlife_finite_action_unique: int = 0
    hashlife_finite_action_alias_hits: int = 0
    hashlife_finite_action_tile_hits: int = 0
    hashlife_finite_action_retained_entries: int = 0
    hashlife_finite_action_mirror_alias_hits: int = 0
    hashlife_finite_action_conjugate_alias_hits: int = 0
    hashlife_peak_live_tile_roots: int = 0
    hashlife_tile_observations: int = 0
    hashlife_direct_powered_point_queries: int = 0
    spacetime_primitive_field_steps: int = 0
    spacetime_primitive_slab_steps: int = 0
    spacetime_slab_jump_entries: int = 0
    spacetime_jump_entries: int = 0
    spacetime_affine_apply_entries: int = 0
    spacetime_carry_projection_entries: int = 0
    spacetime_carry_projection_hits: int = 0
    spacetime_carry_unique_actions: int = 0
    spacetime_carry_action_alias_hits: int = 0
    spacetime_carry_mirror_alias_hits: int = 0
    spacetime_carry_conjugate_alias_hits: int = 0
    spacetime_domain_canonical_refs: int = 0
    spacetime_finite_cell_alphabet: int = 0
    spacetime_carry_direction: str = "lsd-to-msd"
    spacetime_terminal_projection_entries: int = 0
    spacetime_forcing_classes: int = 0
    spacetime_forcing_history_aliases: int = 0
    spacetime_forcing_source_hits: int = 0
    spacetime_forcing_carry_behavior_classes: int = 0
    spacetime_forcing_carry_behavior_aliases: int = 0
    spacetime_primitive_forcing_steps: int = 0
    spacetime_forcing_jump_entries: int = 0
    spacetime_forcing_occurrences: int = 0
    spacetime_forcing_action_aliases: int = 0
    spacetime_forcing_successor_conflicts: int = 0
    spacetime_forcing_exact_target_conflicts: int = 0
    canonical_spacetime_macrocell_roots: int = 0
    spacetime_tile_output_entries: int = 0
    spacetime_tile_output_max_level: int = 0
    spacetime_temporal_absorption_max: int = 0
    hashlife_high_level_tile_misses: int = 0
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

    @property
    def hashlife_cache_entries(self) -> int:
        return self.resource_ledger_entries

    @property
    def execution_state_nodes(self) -> int:
        return self.resource_ledger_nodes


class ReverseAddPoweredTerm:
    """Exact source-specialized ``reverse_add(seed)[generation]`` descriptor."""

    __slots__ = (
        "__weakref__",
        "seed",
        "base",
        "generation",
        "seed_digits",
        "seed_pair",
        "_source_construction",
        "pair_power",
        "effect",
        "_index",
        "_ledger",
        "_compiler",
        "compose_operations",
        "syntax_depth_bound",
        "_hashlife_max_tile_nodes",
        "_hashlife_max_cache_entries",
        "_active_width",
    )

    def __init__(
        self,
        seed: int,
        generation: int,
        *,
        base: int = 10,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
    ) -> None:
        seed = require_integer(seed, "seed", 0)
        generation = require_integer(generation, "generation", 0)
        base = require_integer(base, "base", 2)
        self.seed = seed
        self.base = base
        self.generation = generation
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._ledger.register_execution_root(self)
        self._compiler = LazyCompiler(self._ledger)
        self._hashlife_max_tile_nodes = max_context_nodes
        self._hashlife_max_cache_entries = max_cache_entries
        self.seed_digits = tuple(map(int, digits_lsd(seed, base)))
        self.seed_pair = pair_field_from_integer(seed, base)
        self._source_construction = OriginalSourceConstruction(
            ExactSource(
                self.seed_pair,
                base,
                blank=2 * base - 1,
                extent=self.maximum_width,
                alphabet_size=2 * base - 1,
            ),
        )
        self._index: HashLifeBlockIndex | None = None
        self._active_width: int | None = None

        if generation == 0:
            self.pair_power = None
            self.effect: BlockEffect | None = None
            self.compose_operations = 0
            self.syntax_depth_bound = 0
            return

        terminal = self._compiler.atom(DigitNormalizeBlockEffect(base))
        if generation == 1:
            self.pair_power = None
            self.effect = terminal
            self.compose_operations = 0
            self.syntax_depth_bound = 1
            return

        power = compile_reverse_pair_power(self._compiler, base, generation - 1)
        if power.root is None:
            raise AssertionError("positive pair exponent without powered effect")
        effect = self._compiler.compose(power.root, terminal)
        self.pair_power = power
        self.effect = effect
        # Geometry is carried by ``maximum_width`` only.  The HashLife spatial
        # carrier represents the blank exterior as aligned dyadic tiles rather
        # than interning a generation-sized padding run.
        self.compose_operations = power.compose_operations + 1
        self.syntax_depth_bound = power.syntax_depth + 1

    @property
    def operator_nodes(self) -> int:
        if self.effect is None:
            return 0
        return int(self.effect.operator_nodes())

    @property
    def descriptor_bits(self) -> int:
        # The operator DAG is a deterministic function of these parameters; this
        # is the irreducible external descriptor, not an accounting dodge for
        # in-memory operator nodes (reported separately above).
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 3
        )

    @property
    def maximum_width(self) -> int:
        return len(self.seed_digits) + self.generation

    def _point_index(self) -> HashLifeBlockIndex:
        if self.generation == 0 or self.effect is None:
            raise ValueError("generation zero is a literal seed, not a powered block")
        found = self._index
        if found is None:
            found = HashLifeBlockIndex(
                self.effect,
                self.seed_pair,
                logical_length=self.maximum_width,
                source_construction=self._source_construction,
                certificate=_issue_certificate(
                    self.effect, "reverse-add", self.generation - 1, ledger=self._ledger
                ),
                max_tile_nodes=self._hashlife_max_tile_nodes,
                max_cache_entries=self._hashlife_max_cache_entries,
                ledger=self._ledger,
                compiler=self._compiler,
            )
            self._index = found
        return found

    @source_reads_only
    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        if self.generation == 0:
            if position >= len(self.seed_digits):
                raise IndexError(position)
            return self.seed_digits[position]
        if position >= self.maximum_width:
            raise IndexError(position)
        value = self._point_index().direct_powered_point(position)
        if value == int(self.effect.blank):  # type: ignore[union-attr]
            raise IndexError(position)
        if not 0 <= value < self.base:
            raise AssertionError((value, self.base, self.generation, position))
        return value

    def direct_powered_digit(self, position: int) -> int:
        """Backward-compatible alias for the production direct powered path."""
        return self.digit(position)

    @source_reads_only
    def width(self) -> int:
        if self.generation == 0:
            return len(self.seed_digits)
        found = self._active_width
        if found is None:
            found = self._point_index().direct_active_width()
            self._active_width = found
        return found

    @property
    def estimated_bit_length(self) -> int:
        width = self.width()
        if self.base == 2:
            return width
        return max(1, ceil(width * log2(self.base)))

    def iter_digits(self) -> Iterator[int]:
        if self.generation == 0:
            yield from self.seed_digits
            return
        for value in self._point_index().iter_direct_active():
            if not 0 <= value < self.base:
                raise AssertionError((value, self.base))
            yield int(value)

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())

    def is_palindrome(self) -> bool:
        """Demand mirror equality, stopping at the first certified mismatch.

        The outer three comparisons cover the observed growth safety tube for
        196. Surviving those comparisons requires the full exact consumer;
        no finite observation is promoted to an all-future ray certificate.
        """
        from number_compiler.sequences.reverse_add.palindrome import mirror_palindrome

        return mirror_palindrome(self.width(), self.digit)

    def mirror_obstruction(self, *, first_width: int = 1) -> TwistedCylinderProjection | None:
        """Demand a cyclic/negacyclic certificate for this powered target."""
        from number_compiler.arithmetic.polynomials.twisted_observer import first_mirror_obstruction

        if self.generation == 0:
            return first_mirror_obstruction(self.width(), self.digit, first_width=first_width)
        return self._point_index().direct_mirror_obstruction(first_width=first_width)

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        if self.estimated_bit_length > max_bits:
            raise ValueError((self.estimated_bit_length, max_bits))
        return value_from_lsd_digits(self.iter_digits(), self.base)

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        """Return the seed/function/application HashLife description split.

        This metric does not materialize the output word.  For positive powers it
        reports the compact source-independent jump function separately from the
        seed-specific causal state/action description created by point queries.
        """
        return self._point_index().behavior_metrics()

    def metrics(self) -> ReverseAddPowerMetrics:
        if self._index is None:
            point = collect_unindexed_metrics(self._ledger)
        else:
            point = self._index.metrics()
        return project_powered_metrics(
            ReverseAddPowerMetrics,
            point,
            seed=self.seed,
            base=self.base,
            generation=self.generation,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
            spacetime_carry_direction="lsd-to-msd",
        )


__all__ = [
    "pair_field_from_integer",
    "ReverseAddPowerMetrics",
    "ReverseAddPoweredTerm",
]
