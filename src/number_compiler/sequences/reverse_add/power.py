"""Reverse/add queries owned by the shared source-bound tile scheduler.

The causal boundary evaluator is no longer a production fallback. Identity,
one-step, fused two-step and guarded no-growth consumers use the original source.
General temporal pullback remains open; compact syntax is not execution.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, replace
from math import ceil, log2
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    value_from_lsd_digits,
)
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.output_stream_metrics import (
    closing_output_stream,
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.resources.owned_memo import OwnedMemo
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.palindrome import (
    mirror_obstruction_from_output,
    mirror_palindrome_from_output,
)

if TYPE_CHECKING:
    from number_compiler.resources.hashlife_behavior_metrics import (
        HashLifeBehaviorMetrics,
    )
    from number_compiler.resources.reverse_power_metrics import ReverseAddPowerMetrics
    from number_compiler.sequences.reverse_add.boundary_window import (
        ReverseBoundaryWindowObservation,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )
    from number_compiler.sequences.reverse_add.temporal_accumulator99 import (
        PoweredAccumulator99,
    )
    from number_compiler.sequences.reverse_add.temporal_laurent_accumulator import (
        SourceBoundLaurentResult,
    )
    from number_compiler.sequences.reverse_add.temporal_matrix import (
        ReverseInnovationBank,
        SkewMoment,
        SourceBoundMoment,
    )
    from number_compiler.sequences.reverse_add.temporal_residue99 import (
        ReverseAddResidue99,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        CertifiedReverseAddSeedMorphism,
    )


_LAURENT_CACHE_ENTRY_NODES = 40
_ACCUMULATOR99_CACHE_ENTRY_NODES = 40


@dataclass(frozen=True, slots=True)
class _TermBoundAccumulator99CacheEntry:
    source_binding: tuple[int, int, int]
    term_token: object
    base_result: PoweredAccumulator99
    base_snapshot: tuple[object, ...]
    enriched_result: PoweredAccumulator99 | None
    enriched_snapshot: tuple[object, ...] | None


@dataclass(frozen=True, slots=True)
class _TermBoundLaurentCacheEntry:
    """Observation payload bound to its exact term owner and source action."""

    source_binding: tuple[int, int, int]
    term_token: object
    result: SourceBoundLaurentResult
    result_snapshot: tuple[int, ...]


def _accumulator99_snapshot(result: PoweredAccumulator99) -> tuple[object, ...]:
    from .temporal_accumulator99 import (
        AccumulatorMooreState99,
        PoweredAccumulator99,
        RankOneAccumulatorAction99,
    )

    if type(result) is not PoweredAccumulator99:
        raise TypeError("mod-99 cache result has a foreign type")
    state = result.state
    if type(state) is not AccumulatorMooreState99:
        raise TypeError("mod-99 cache state has a foreign type")
    phase = require_integer(state.phase, "accumulator phase", 0, 1)
    state_a = require_integer(state.a, "first accumulator residue", 0, 98)
    state_b = require_integer(state.b, "second accumulator residue", 0, 98)
    AccumulatorMooreState99.__post_init__(state)

    action = result.action
    if type(action) is not RankOneAccumulatorAction99:
        raise TypeError("mod-99 cache action has a foreign type")
    multiplier = require_integer(action.multiplier, "rank-one multiplier", 0, 98)
    coupling = require_integer(action.coupling, "rank-one coupling", 0, 98)
    RankOneAccumulatorAction99.__post_init__(action)

    source_reverse = result.source_reverse_mod99
    if source_reverse is not None:
        source_reverse = require_integer(
            source_reverse, "source reverse residue", 0, 98
        )
    source_certified = result.source_certified
    if type(source_certified) is not bool or not source_certified:
        raise ValueError("mod-99 cache result lost source certification")
    absorbed = result.absorbed_mod11
    if type(absorbed) is not bool:
        raise TypeError("mod-99 absorbed flag must be Boolean")
    complete_integer_certified = result.complete_integer_certified
    if type(complete_integer_certified) is not bool:
        raise TypeError("mod-99 integer certificate flag must be Boolean")

    return (
        require_integer(result.generation, "accumulator generation", 0),
        require_integer(result.bootstrap_generation, "bootstrap generation", 0),
        phase,
        state_a,
        state_b,
        require_integer(result.integer_mod99, "integer residue", 0, 98),
        require_integer(result.reverse_mod99, "reverse residue", 0, 98),
        absorbed,
        require_integer(result.even_blocks_powered, "powered even blocks", 0),
        multiplier,
        coupling,
        require_integer(result.source_mod99, "source residue", 0, 98),
        require_integer(result.generation_mod99, "generation residue", 0, 98),
        source_certified,
        complete_integer_certified,
        source_reverse,
    )


def pair_field_from_integer(value: int, base: int) -> tuple[int, ...]:
    """Original-source encoding retained for independent kernel consumers."""
    value = require_integer(value, "seed", 0)
    base = require_integer(base, "base", 2)
    return pair_field_from_digits(digits_lsd(value, base))


def pair_field_from_digits(digits: tuple[int, ...]) -> tuple[int, ...]:
    if type(digits) is not tuple or not digits:
        raise ValueError("reverse pair source requires original digits")
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


class ReverseAddPoweredTerm:
    """Lazy source/action request; no successor or boundary replay backend."""

    __slots__ = (
        "__weakref__",
        "_binding",
        "_boundary_observer",
        "_boundary_observer_identity",
        "_ledger",
        "_accumulator99_cache",
        "_accumulator99_cache_identity",
        "_accumulator99_cache_owner",
        "_accumulator99_cache_token",
        "_laurent_cache",
        "_laurent_cache_identity",
        "_laurent_cache_owner",
        "_laurent_cache_token",
        "_laurent_scratch_owner",
        "_center11_scratch_owner",
        "_mirror_output_scratch",
        "_source_construction",
        "_workspace",
        "_workspace_identity",
        "base",
        "generation",
        "seed",
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
        self.seed = require_integer(seed, "seed", 0)
        self.generation = require_integer(generation, "generation", 0)
        self.base = require_integer(base, "base", 2)
        self._binding = (self.seed, self.generation, self.base)
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._accumulator99_cache: (
            OwnedMemo[None, _TermBoundAccumulator99CacheEntry] | None
        ) = None
        self._accumulator99_cache_identity: (
            OwnedMemo[None, _TermBoundAccumulator99CacheEntry] | None
        ) = None
        self._accumulator99_cache_owner: int | None = None
        self._accumulator99_cache_token = object()
        self._laurent_cache: OwnedMemo[None, _TermBoundLaurentCacheEntry] | None = None
        self._laurent_cache_identity: (
            OwnedMemo[None, _TermBoundLaurentCacheEntry] | None
        ) = None
        self._laurent_cache_owner: int | None = None
        self._laurent_cache_token = object()
        self._laurent_scratch_owner: int | None = None
        self._center11_scratch_owner: int | None = None
        self._boundary_observer: object | None = None
        self._boundary_observer_identity: object | None = None
        initialize_output_stream_metrics(self._ledger, "reverse_output_stream")
        self._mirror_output_scratch: LedgerList[int] | None = None
        self._workspace: ReverseSourceImageWorkspace | None = None
        self._workspace_identity: ReverseSourceImageWorkspace | None = None
        self._source_construction: OriginalSourceConstruction | None = None
        self._ledger.register_execution_root(self)

    def validate_source_binding(self) -> None:
        """Reject rebinding before any source-dependent observation or construction."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")

    def completed_q19_occurrence(
        self,
    ) -> tuple[ReversePairQ19OutputOwner, ReversePairOutputOccurrence, bool, int]:
        """Demand the authenticated endpoint through its existing workspace owner."""
        return self.source_workspace().completed_q19_occurrence()

    def source_workspace(self) -> ReverseSourceImageWorkspace:
        from number_compiler.sequences.reverse_add.source_images import (
            ReverseSourceImageWorkspace,
        )

        self.validate_source_binding()
        found = self._workspace
        if found is None:
            found = ReverseSourceImageWorkspace(
                self._ledger,
                self.seed,
                self.generation,
                base=self.base,
                source_construction=self._source_construction,
            )
            self._workspace = found
            self._workspace_identity = found
        elif found is not self._workspace_identity or found.ledger is not self._ledger:
            raise ValueError("reverse/add term workspace binding changed")
        return found

    def prepare_recursive_source_authority(self) -> None:
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base == 10:
            return
        from number_compiler.sequences.reverse_add.source_images import (
            MAX_COMPLETED_CHILD_FALLBACK_STEPS,
        )

        if not 3 <= self.generation <= MAX_COMPLETED_CHILD_FALLBACK_STEPS:
            return
        if self._source_construction is not None:
            return
        pair = pair_field_from_integer(self.seed, self.base)
        blank = 2 * self.base - 1
        required = max(1, len(pair) + self.generation)
        extent = 1 << ((required - 1).bit_length())
        self._source_construction = OriginalSourceConstruction(
            ExactSource(
                pair,
                self.base,
                "reverse-add-pair",
                blank,
                extent,
                2 * self.base,
            )
        )
        self._ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_PAIR_AUTHORITY_SYMBOLS, len(pair)
        )

    @property
    def operator_nodes(self) -> int:
        return 0 if self._workspace is None else self._workspace.operator_nodes

    @property
    def resource_ledger(self) -> ResourceLedger:
        return self._ledger

    @property
    def published_workspace(self) -> ReverseSourceImageWorkspace | None:
        """Return the source image only when a demand has already published it."""
        return self._workspace

    @property
    def compose_operations(self) -> int:
        return 0 if self._workspace is None else self._workspace.compose_operations

    @property
    def syntax_depth_bound(self) -> int:
        return 0 if self._workspace is None else self._workspace.syntax_depth_bound

    @property
    def descriptor_bits(self) -> int:
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 3
        )

    @property
    def maximum_width(self) -> int:
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        workspace = self._workspace
        if workspace is not None:
            if (
                workspace is not self._workspace_identity
                or workspace.ledger is not self._ledger
            ):
                raise ValueError("reverse/add term workspace binding changed")
            completed = workspace.completed_width_if_cached()
            if completed is not None:
                return completed
        return len(digits_lsd(self.seed, self.base)) + self.generation

    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        self.prepare_recursive_source_authority()
        return self._digit_source_only(position)

    @source_reads_only
    def _digit_source_only(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        return self.source_workspace().digit(position)

    def direct_powered_digit(self, position: int) -> int:
        """Compatibility alias; does not select another execution path."""
        return self.digit(position)

    def width(self) -> int:
        self.prepare_recursive_source_authority()
        return self._width_source_only()

    @source_reads_only
    def _width_source_only(self) -> int:
        return self.source_workspace().width()

    @property
    def estimated_bit_length(self) -> int:
        width = self.width()
        return width if self.base == 2 else max(1, ceil(width * log2(self.base)))

    def _measured_output_digits(self) -> Iterator[int]:
        def source() -> Iterator[int]:
            self.prepare_recursive_source_authority()
            yield from self.source_workspace().iter_digits()

        return measured_output_stream(self._ledger, "reverse_output_stream", source)

    def iter_digits(self) -> Iterator[int]:
        return self._measured_output_digits()

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())

    def is_palindrome(self) -> bool:
        width = self.width()
        if width == 1:
            return True
        with closing_output_stream(self._measured_output_digits()) as digits:
            return mirror_palindrome_from_output(
                width,
                digits,
                ledger=self._ledger,
                scratch=self._output_mirror_scratch(),
            )

    def _output_mirror_scratch(self) -> LedgerList[int]:
        scratch: LedgerList[int] | None = self._mirror_output_scratch
        if scratch is None:
            owner = self._ledger.register(
                "reverse-output-mirror-scratch", "explicit_lowering"
            )
            scratch = self._ledger.make_list(
                owner, nodes_per_entry=2, append_only=False
            )
            self._mirror_output_scratch = scratch
        return scratch

    def mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        first_width = require_integer(first_width, "first sheet width", 1)
        width = self.width()
        scratch = self._output_mirror_scratch()
        with closing_output_stream(self._measured_output_digits()) as digits:
            return mirror_obstruction_from_output(
                width,
                digits,
                ledger=self._ledger,
                scratch=scratch,
                first_width=first_width,
            )

    def temporal_spatial_bank_morphism(
        self, start: int, count: int, *, period: int = 2
    ) -> ReverseAddSpatialBankMorphism:
        """Publish a source-issued protected spatial bank without an integer."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("spatial bank morphism requires decimal reversal")
        return self.source_workspace().certified_spatial_bank_morphism(
            start, count, period=period
        )

    def temporal_ring_bank(
        self, start: int = 0, count: int = 8
    ) -> ReverseAddTemporalRingBank:
        """Finite source-certified GT/EQ/LT, F5 and carry/borrow ring output."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        return self.source_workspace().certified_temporal_ring_bank(start, count)

    def temporal_seed_orbit_morphism(
        self, steps: int, *, start: int = 1
    ) -> CertifiedReverseAddSeedMorphism:
        """Exact pointed Q19 temporal source-root action with joined ring ports.

        This uses bounded real Q19 T2/T4 transitions, not an unproved
        fast dyadic Q19 cone, or a hypothetical repeated inlet word.
        """
        from .temporal_seed_morphism import certified_reverse_add_seed_morphism

        return certified_reverse_add_seed_morphism(self, steps, start=start)

    def temporal_seed_orbit_morphism_power_of_two(
        self, exponent: int, *, start: int = 1
    ) -> CertifiedReverseAddSeedMorphism:
        """Repeatedly square an actual source-root action, not an input word."""
        exponent = require_integer(exponent, "temporal exponent", 0)
        if exponent > 24:
            raise ValueError("no unrestricted fast dyadic Q19 operator is certified")
        result = self.temporal_seed_orbit_morphism(1, start=start)
        for _ in range(exponent):
            result = result.square()
        return result

    def temporal_accumulator99(
        self, *, include_source_reverse: bool = False
    ) -> PoweredAccumulator99:
        """Power the complete mod-99 alternating accumulator Moore quotient.

        No Q19 occurrence, carry-word forecast, or width trajectory is created.
        This authority is strictly modular, not an exact endpoint publisher.
        """
        self.validate_source_binding()
        if self.base != 10:
            raise ValueError("temporal accumulator99 is decimal-only")
        if type(include_source_reverse) is not bool:
            raise TypeError("source reverse demand must be Boolean")
        from .temporal_accumulator99 import (
            PoweredAccumulator99,
            from_seed_guarded,
            source_reverse_mod99_guarded,
        )

        cache = self._accumulator99_cache
        if cache is None and (
            self._accumulator99_cache_identity is not None
            or self._accumulator99_cache_owner is not None
        ):
            raise ValueError("mod-99 cache owner was detached from its term")
        if cache is not None:
            if (
                cache is not self._accumulator99_cache_identity
                or cache.ledger is not self._ledger
                or cache.owner != self._accumulator99_cache_owner
            ):
                raise ValueError("mod-99 cache lost its term-ledger authority")
            if cache.audit_snapshot().disposed:
                self._accumulator99_cache = None
                self._accumulator99_cache_identity = None
                self._accumulator99_cache_owner = None
                self._accumulator99_cache_token = object()
                cache = None
            elif None in cache:
                entry = cache[None]
                if type(entry) is not _TermBoundAccumulator99CacheEntry:
                    raise TypeError("mod-99 cache contains a foreign entry")
                base_result = entry.base_result
                enriched_result = entry.enriched_result
                if (
                    entry.term_token is not self._accumulator99_cache_token
                    or entry.source_binding != self._binding
                    or type(base_result) is not PoweredAccumulator99
                    or base_result.source_reverse_mod99 is not None
                    or _accumulator99_snapshot(base_result) != entry.base_snapshot
                    or (enriched_result is None) != (entry.enriched_snapshot is None)
                ):
                    raise ValueError("mod-99 cache lost its source-bound result")
                if enriched_result is not None and (
                    type(enriched_result) is not PoweredAccumulator99
                    or enriched_result.source_reverse_mod99 is None
                    or _accumulator99_snapshot(enriched_result)
                    != entry.enriched_snapshot
                ):
                    raise ValueError("mod-99 cache lost its enriched result")
                if not include_source_reverse:
                    return base_result
                if enriched_result is not None:
                    return enriched_result
                source_reverse = (
                    base_result.reverse_mod99
                    if self.generation == 0
                    else source_reverse_mod99_guarded(self.seed, ledger=self._ledger)
                )
                self.validate_source_binding()
                enriched_result = replace(
                    base_result,
                    source_reverse_mod99=source_reverse,
                )
                cache[None] = _TermBoundAccumulator99CacheEntry(
                    self._binding,
                    self._accumulator99_cache_token,
                    base_result,
                    entry.base_snapshot,
                    enriched_result,
                    _accumulator99_snapshot(enriched_result),
                )
                return enriched_result

        computed = from_seed_guarded(
            self.seed,
            self.generation,
            ledger=self._ledger,
            include_source_reverse=include_source_reverse,
        )
        self.validate_source_binding()
        if include_source_reverse:
            if computed.source_reverse_mod99 is None:
                raise AssertionError("source-reverse demand returned no coordinate")
            computed_enriched: PoweredAccumulator99 | None = computed
            base_result = replace(computed, source_reverse_mod99=None)
        else:
            if computed.source_reverse_mod99 is not None:
                raise AssertionError("base accumulator eagerly exposed source reverse")
            base_result = computed
            computed_enriched = None
        requested_result = computed_enriched if include_source_reverse else base_result
        if requested_result is None:
            raise AssertionError("mod-99 demand lost its requested projection")
        memo = cache
        created = memo is None
        owner = self._accumulator99_cache_owner
        if memo is None:
            owner = self._ledger.register(
                f"reverse-accumulator99-cache-{self._ledger.owner_count}",
                "query_memo",
                scope=ResourceScope.INDEX_OWNED,
            )
            try:
                memo = OwnedMemo[None, _TermBoundAccumulator99CacheEntry](
                    self._ledger,
                    owner,
                    nodes_per_entry=_ACCUMULATOR99_CACHE_ENTRY_NODES,
                    evictable=True,
                )
            except BaseException as construction_error:
                try:
                    self._ledger.retire_unpublished_owner(owner)
                except BaseException as cleanup_error:
                    raise cleanup_error from construction_error
                raise
        try:
            memo[None] = _TermBoundAccumulator99CacheEntry(
                self._binding,
                self._accumulator99_cache_token,
                base_result,
                _accumulator99_snapshot(base_result),
                computed_enriched,
                None
                if computed_enriched is None
                else _accumulator99_snapshot(computed_enriched),
            )
        except BlockContextBudgetExceeded as publication_error:
            try:
                if created:
                    memo.dispose()
            except BaseException as cleanup_error:
                raise cleanup_error from publication_error
            return requested_result
        except BaseException as publication_error:
            try:
                if created:
                    memo.dispose()
            except BaseException as cleanup_error:
                raise cleanup_error from publication_error
            raise
        if created:
            if owner is None:
                raise AssertionError("mod-99 cache publication lost its owner")
            self._accumulator99_cache = memo
            self._accumulator99_cache_identity = memo
            self._accumulator99_cache_owner = owner
        return requested_result

    def temporal_laurent_accumulator(self) -> SourceBoundLaurentResult:
        """Observe a bounded exact Laurent/carry run owned by this term.

        This is a finite source observation, not a Q19 issuer or future-period
        certificate. Its persistent result lives in this term's ledger-owned
        memo; all digit and run construction is charged to a temporary ledger
        reservation before seed expansion.
        """
        self.validate_source_binding()
        if self.base != 10:
            raise ValueError("temporal Laurent action is decimal-only")
        from .temporal_laurent_accumulator import (
            MAX_FINITE_LAURENT_TICKS,
            SourceBoundLaurentResult,
            source_bound_laurent_projection,
        )

        if self.seed != 0 and self.generation > MAX_FINITE_LAURENT_TICKS:
            limit = MAX_FINITE_LAURENT_TICKS
            raise ValueError(
                f"source-bound Laurent supports at most {limit} physical ticks; "
                "no unbounded carry-driver period is certified"
            )

        cache = self._laurent_cache
        if cache is None and (
            self._laurent_cache_identity is not None
            or self._laurent_cache_owner is not None
        ):
            raise ValueError("Laurent cache owner was detached from its term")
        if cache is not None:
            if (
                cache is not self._laurent_cache_identity
                or cache.ledger is not self._ledger
                or cache.owner != self._laurent_cache_owner
            ):
                raise ValueError("Laurent cache lost its term-ledger authority")
            if cache.audit_snapshot().disposed:
                self._laurent_cache = None
                self._laurent_cache_identity = None
                self._laurent_cache_owner = None
                self._laurent_cache_token = object()
                cache = None
            elif None in cache:
                entry = cache[None]
                if type(entry) is not _TermBoundLaurentCacheEntry:
                    raise TypeError("Laurent cache contains a foreign entry")
                if (
                    entry.term_token is not self._laurent_cache_token
                    or entry.source_binding != self._binding
                ):
                    raise ValueError("Laurent cache entry has a foreign source binding")
                result = entry.result
                if type(result) is not SourceBoundLaurentResult:
                    raise TypeError("Laurent cache entry contains a foreign result")
                if (
                    type(result.generation) is not int
                    or result.generation != self.generation
                ):
                    raise ValueError("Laurent cache payload has a stale generation")
                if result.cache_snapshot() != entry.result_snapshot:
                    raise ValueError("Laurent cache result changed after publication")
                self._ledger.bump(_reverse_add_keys.REVERSE_LAURENT_CACHE_HITS)
                return result

        self._ledger.bump(_reverse_add_keys.REVERSE_LAURENT_CACHE_MISSES)
        scratch_owner = self._laurent_scratch_owner
        if scratch_owner is None:
            scratch_owner = self._ledger.register(
                f"reverse-laurent-source-work-{self._ledger.owner_count}",
                "temporary_work",
                scope=ResourceScope.INDEX_OWNED,
            )
            self._laurent_scratch_owner = scratch_owner
        result = source_bound_laurent_projection(
            self.seed,
            self.generation,
            ledger=self._ledger,
            scratch_owner=scratch_owner,
        )
        if (self.seed, self.generation, self.base) != self._binding:
            self._ledger.bump(_reverse_add_keys.REVERSE_LAURENT_FAILED_WORK)
            raise ValueError("Laurent source binding changed during construction")

        cache_owner = None if cache is None else cache.owner
        memo = cache
        try:
            if memo is None:
                cache_owner = self._ledger.register(
                    f"reverse-laurent-result-cache-{self._ledger.owner_count}",
                    "query_memo",
                    scope=ResourceScope.INDEX_OWNED,
                )
                memo = OwnedMemo[None, _TermBoundLaurentCacheEntry](
                    self._ledger,
                    cache_owner,
                    nodes_per_entry=_LAURENT_CACHE_ENTRY_NODES,
                    evictable=True,
                )
            memo[None] = _TermBoundLaurentCacheEntry(
                source_binding=self._binding,
                term_token=self._laurent_cache_token,
                result=result,
                result_snapshot=result.cache_snapshot(),
            )
        except BaseException as publication_error:
            self._ledger.bump(
                _reverse_add_keys.REVERSE_LAURENT_CACHE_PUBLICATION_FAILURES
            )
            try:
                if memo is not None and memo is not cache:
                    memo.dispose()
                elif cache_owner is not None and cache is None:
                    self._ledger.retire_unpublished_owner(cache_owner)
            except BaseException as cleanup_error:
                raise cleanup_error from publication_error
            if isinstance(publication_error, BlockContextBudgetExceeded):
                return result
            raise
        if cache_owner is None:
            raise AssertionError("Laurent cache publication lost its owner")
        if cache is None:
            self._laurent_cache = memo
            self._laurent_cache_identity = memo
            self._laurent_cache_owner = cache_owner
        return result

    def temporal_mirrored_diagonal(
        self, *, max_steps: int | None = None
    ) -> dict[str, object]:
        """Observe a bounded source interval with reserved, exception-safe scratch.

        The packet grants no future repetition authority.
        """
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("mirrored diagonal is decimal-only")
        from .temporal_mirrored_diagonal import (
            MAX_MIRRORED_TICKS,
            center11_interval_packet,
            center11_scratch_nodes,
        )
        from .temporal_port_quotient import (
            decimal_width_upper_bound,
        )

        if max_steps is not None and type(max_steps) is not int:
            raise ValueError("mirrored diagonal exceeds its finite source interval")
        if max_steps is None:
            max_steps = MAX_MIRRORED_TICKS
        if (
            not 1 <= max_steps <= MAX_MIRRORED_TICKS
            or not 1 <= self.generation <= max_steps
        ):
            raise ValueError("mirrored diagonal exceeds its finite source interval")
        max_width = decimal_width_upper_bound(self.seed) + self.generation
        scratch_nodes = center11_scratch_nodes(max_width)
        scratch_owner = self._center11_scratch_owner
        if scratch_owner is None:
            scratch_owner = self._ledger.register(
                "reverse-center11-term-scratch",
                "temporary_work",
                scope=ResourceScope.INDEX_OWNED,
            )
            self._center11_scratch_owner = scratch_owner

        def tick_started(_width: int) -> None:
            self._ledger.bump(_reverse_add_keys.REVERSE_CENTER11_SOURCE_TICKS)

        def coefficient_visits(count: int) -> None:
            self._ledger.bump(
                _reverse_add_keys.REVERSE_CENTER11_COEFFICIENT_VISITS, count
            )

        try:
            with self._ledger.reservation(scratch_owner, nodes=scratch_nodes):
                packet = center11_interval_packet(
                    self.seed,
                    self.generation,
                    max_steps=max_steps,
                    on_tick_start=tick_started,
                    on_coefficient_visits=coefficient_visits,
                )
            if (self.seed, self.generation, self.base) != self._binding:
                raise ValueError("reverse/add term changed during mirrored observation")
        except BaseException as error:
            try:
                self._ledger.bump(_reverse_add_keys.REVERSE_CENTER11_FAILED_WORK)
            except BaseException as accounting_error:
                raise accounting_error from error
            raise
        return packet

    def temporal_residue99(self) -> ReverseAddResidue99:
        """Predict mod-99 without initializing the Q19 source workspace."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("temporal residue99 is decimal-only")
        from .temporal_residue99 import from_seed

        return from_seed(self.seed, self.generation)

    def temporal_matrix(self, *, max_bits: int = 16384) -> SourceBoundMoment:
        """Project the authenticated endpoint into its exact skew matrix."""
        from number_compiler.sequences.reverse_add.temporal_matrix import (
            source_bound_temporal_matrix,
        )

        return source_bound_temporal_matrix(self, max_bits=max_bits)

    def temporal_moments(self, *, modulus: int) -> SkewMoment:
        """Project modular U,V through the exact modulus-specific source owner."""
        from number_compiler.sequences.reverse_add.temporal_matrix import (
            source_bound_modular_moments,
        )

        return source_bound_modular_moments(self, modulus=modulus)

    def temporal_stencil(
        self, *, max_bits: int = 16384, max_digits: int = 8192
    ) -> ReverseInnovationBank:
        """Observe the exact endpoint's bounded five-band/borrow stencil.

        Width and bit caps are checked before endpoint digit expansion. The
        returned future borrow stencil is diagnostic source law; it does not
        authorize skipping future full-root transitions.
        """
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("temporal stencil is decimal-only")
        max_digits = require_integer(max_digits, "stencil digit budget", 1)
        if self.maximum_width > max_digits:
            raise ValueError("reverse/add stencil exceeds its digit budget")
        action = self.temporal_matrix(max_bits=max_bits)
        from number_compiler.sequences.reverse_add.temporal_matrix import (
            ReverseInnovationBank,
        )

        width = max(1, self.maximum_width)
        workspace_owner = self._ledger.register(
            f"reverse-temporal-stencil-work-{self._ledger.owner_count}",
            "temporary_work",
            scope=ResourceScope.INDEX_OWNED,
        )
        try:
            with self._ledger.reservation(
                workspace_owner,
                entries=16 * width + 64,
                nodes=16 * width + 64,
            ):
                return ReverseInnovationBank.observe(
                    action.target,
                    max_digits=max_digits,
                    ledger=self._ledger,
                )
        finally:
            self._ledger.mark_disposed(workspace_owner)

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        estimate = self.estimated_bit_length
        if estimate > max_bits:
            raise ValueError((estimate, max_bits))
        return value_from_lsd_digits(self.iter_digits(), self.base)

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        from number_compiler.sequences.reverse_add.behavior_metrics import (
            reverse_behavior_metrics,
        )

        return reverse_behavior_metrics(self)

    def observe_boundary_macro(
        self,
        *,
        max_states: int = 4096,
        max_compositions: int = 50_000,
        max_relation_entries: int = 8192,
        max_relation_states: int = 32_768,
    ) -> ReverseBoundaryWindowObservation:
        """Return a conservative decimal edge observation for this term.

        The result contains no complete endpoint. Its finite relation cache is
        owned by this term's resource ledger and shared across K=2,4,8 demands.
        """
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("boundary macro observation is decimal-only")
        from number_compiler.sequences.reverse_add.boundary_window import (
            ReverseBoundaryWindowObserver,
        )

        observer = self._boundary_observer
        if observer is None:
            observer = ReverseBoundaryWindowObserver(
                self.seed,
                self.generation,
                self._ledger,
                source_workspace=self.source_workspace(),
                max_states=max_states,
                max_compositions=max_compositions,
                max_relation_entries=max_relation_entries,
                max_relation_states=max_relation_states,
            )
            self._boundary_observer = observer
            self._boundary_observer_identity = observer
        elif (
            type(observer) is not ReverseBoundaryWindowObserver
            or observer is not self._boundary_observer_identity
            or observer.ledger is not self._ledger
            or observer.relations.ledger is not self._ledger
            or observer.binding != self._binding
            or observer.max_states != max_states
            or observer.max_compositions != max_compositions
            or observer.max_relation_entries != max_relation_entries
            or observer.max_relation_states != max_relation_states
        ):
            raise ValueError("boundary observer binding or budget changed")
        return observer.observe(
            seed=self.seed, generation=self.generation, base=self.base
        )

    def metrics(self) -> ReverseAddPowerMetrics:
        from number_compiler.resources.metric_collection import (
            collect_unindexed_metrics,
        )
        from number_compiler.resources.powered_metrics import project_powered_metrics
        from number_compiler.resources.reverse_power_metrics import (
            ReverseAddPowerMetrics,
        )

        return project_powered_metrics(
            ReverseAddPowerMetrics,
            collect_unindexed_metrics(self._ledger),
            seed=self.seed,
            base=self.base,
            generation=self.generation,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
            spacetime_carry_direction="lsd-to-msd",
        )


__all__ = ["ReverseAddPoweredTerm", "pair_field_from_integer"]
