"""Canonical nth-term projection/materialization API for all supported families."""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Callable, Hashable, Iterator
from dataclasses import dataclass
from math import ceil, log2
from typing import TYPE_CHECKING, TypeVar

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.api.elementary_payloads import (
    FermatTermPayload,
    MersenneTermPayload,
    ScalarTermPayload,
)
from number_compiler.api.observation_types import FamilyId
from number_compiler.api.query_types import TermQuery
from number_compiler.api.reverse_payloads import (
    DoubleReverseTermPayload,
    PoweredReverseAddTermPayload,
)
from number_compiler.api.symbolic_terms import SymbolicExpression, initialize_projected
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.arithmetic.fields.symbolic_extent import (
    Extent,
)
from number_compiler.arithmetic.formula.formula import FormulaRoot
from number_compiler.resources.metric_keys import api as _api_metrics
from number_compiler.resources.metric_keys import shared as _shared_metrics
from number_compiler.resources.output_stream_metrics import measured_output_stream

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.state_reduction import (
        ReverseAddGrowthState,
    )
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm, Run
    from number_compiler.sequences.collatz.block_power import (
        CollatzPhysicalBlockMetrics,
        PoweredCollatzTerm,
    )
    from number_compiler.sequences.collatz.character import (
        CollatzGrowthCharacter,
        CollatzRadialCharacter,
    )


NumberFamily = FamilyId

_PoweredOwner = TypeVar("_PoweredOwner")


@dataclass(frozen=True, slots=True)
class ProjectionMetrics:
    family: NumberFamily
    index: int
    construction_steps: int
    projection_work: int
    descriptor_nodes: int
    descriptor_bits: int
    width: Extent | None
    raw_squarings: int = 0
    prime_block_compilations: int = 0
    prime_max_block_length: int = 0
    prime_dag_states: int = 0
    prime_cache_hits: int = 0
    prime_factor_stages: int = 0
    prime_discovery_queries: int = 0
    prime_peak_pending_frames: int = 0
    prime_retained_entries: int = 0
    prime_arithmetic_bit_work: int = 0
    prime_parent_gap_positions_materialized: int = 0
    shared_cache_hits: int = 0
    shared_cache_misses: int = 0
    shared_cache_entries: int = 0
    shared_cache_bytes: int = 0
    shared_cache_evictions: int = 0
    shared_cache_bypasses: int = 0
    shared_cache_publications: int = 0
    prime_admission_work: int = 0
    prime_request_allocations: int = 0
    prime_scheduler_work: int = 0
    prime_scheduler_peak_entries: int = 0
    prime_scheduler_counters: tuple[tuple[str, int], ...] = ()


@dataclass(frozen=True, slots=True)
class FormulaTermPayload:
    root: FormulaRoot
    radix: int

    def __post_init__(self) -> None:
        if type(self.root) is not FormulaRoot:
            raise TypeError("formula payload requires a canonical formula root")
        require_integer(self.radix, "formula radix", 2)

    @property
    def estimated_bit_length(self) -> int:
        if self.radix == 2:
            return self.root.width
        return max(1, ceil(self.root.width * log2(self.radix)))

    def digits(self) -> tuple[int, ...]:
        from number_compiler.hashlife.execution.evaluator import materialize_values

        return tuple(map(int, materialize_values(self.root)))

    def iter_digits(self, *, reverse: bool = False) -> Iterator[int]:
        from number_compiler.hashlife.execution.evaluator import iter_values

        if type(reverse) is not bool:
            raise TypeError("reverse must be a Boolean")
        return (int(value) for value in iter_values(self.root, reverse=reverse))

    @source_reads_only
    def digit(self, index: int) -> int:
        from number_compiler.hashlife.execution.evaluator import value_at

        index = require_integer(index, "digit coordinate")
        if not 0 <= index < self.root.width:
            raise IndexError(index)
        return int(value_at(self.root, index))

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        if self.estimated_bit_length > max_bits:
            raise ValueError((self.estimated_bit_length, max_bits))
        return value_from_lsd_digits(self.iter_digits(), self.radix)


@dataclass(frozen=True, slots=True)
class PoweredCollatzTermPayload:
    term: PoweredCollatzTerm
    radix: int

    def __post_init__(self) -> None:
        from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

        if type(self.term) is not PoweredCollatzTerm:
            raise TypeError("powered Collatz payload requires its exact term type")
        require_integer(self.radix, "Collatz payload radix", 2)

    @property
    def estimated_bit_length(self) -> int:
        # Construction must remain independent of endpoint execution.  The
        # physical Collatz map can grow by at most two binary digits per tick,
        # so this is a conservative symbolic cap rather than an eager width
        # projection.
        return self.term.maximum_width

    def materialize(self, *, max_bits: int) -> int:
        return self.term.materialize(max_bits=max_bits)

    def digits(self) -> tuple[int, ...]:
        if self.radix == 2:
            return self.term.digits()
        return tuple(self._forward_digits())

    def iter_digits(self, *, reverse: bool = False) -> Iterator[int]:
        if type(reverse) is not bool:
            raise TypeError("reverse must be a Boolean")
        if reverse:
            return iter(reversed(tuple(self._forward_digits())))
        return self._forward_digits()

    def _forward_digits(self) -> Iterator[int]:
        if self.radix == 2:
            return self.term.iter_digits()

        def projected() -> Iterator[int]:
            # Explicit full-output lowering happens once, on first demand.
            # It must not become one source-image reconstruction per digit.
            ledger = self.term._ledger
            ledger.bump(_api_metrics.COLLATZ_RADIX_CONVERSION_REQUESTS)
            try:
                value = self.materialize(max_bits=self.term.maximum_width)
                ledger.bump(
                    _api_metrics.COLLATZ_RADIX_CONVERSION_OPERAND_BITS,
                    value.bit_length(),
                )
                digits = digits_lsd(value, self.radix)
            except BaseException:
                ledger.bump(_api_metrics.COLLATZ_RADIX_CONVERSION_FAILURES)
                raise
            for digit in digits:
                ledger.bump(_api_metrics.COLLATZ_RADIX_CONVERSION_EMITTED_DIGITS)
                yield int(digit)

        return measured_output_stream(
            self.term._ledger, "collatz_output_stream", projected
        )

    @source_reads_only
    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if index < 0:
            raise IndexError(index)
        if self.radix == 2:
            return self.term.digit(index)
        from number_compiler.projection.lazy_radix import collatz_radix_digit

        return collatz_radix_digit(self.term, self.radix, index)

    def power_metrics(self) -> CollatzPhysicalBlockMetrics:
        return self.term.metrics()


@dataclass(frozen=True, slots=True)
class AntihydraTermPayload:
    """Lazy total arithmetic image of the pinned blank-tape source."""

    term: AntihydraArithmeticTerm

    def __post_init__(self) -> None:
        from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

        if type(self.term) is not AntihydraArithmeticTerm:
            raise TypeError("Antihydra payload requires its exact arithmetic owner")

    @property
    def estimated_bit_length(self) -> int:
        # Each source return maps h to h+floor(h/2), increasing bit width by
        # at most one. This bound rejects impossible output budgets without
        # forcing the lazy arithmetic image.
        return 4 + self.term.requested

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        value = self.term.value()
        if value.bit_length() > max_bits:
            raise ValueError((value.bit_length(), max_bits))
        return value

    def digits(self) -> tuple[int, ...]:
        ledger = self.term.ledger
        ledger.bump(_api_metrics.ANTIHYDRA_OUTPUT_STREAM_REQUESTS)
        ledger.bump(_shared_metrics.ANTIHYDRA_DIGIT_CONVERSION_REQUESTS)
        try:
            value = self.term.value()
            ledger.bump(
                _shared_metrics.ANTIHYDRA_DIGIT_CONVERSION_OPERAND_BITS,
                value.bit_length(),
            )
            digits = digits_lsd(value, 2)
        except BaseException:
            ledger.bump(_api_metrics.ANTIHYDRA_OUTPUT_STREAM_FAILURES)
            ledger.bump(_shared_metrics.ANTIHYDRA_DIGIT_CONVERSION_FAILURES)
            raise
        ledger.bump(_api_metrics.ANTIHYDRA_OUTPUT_STREAM_EMITTED_DIGITS, len(digits))
        ledger.bump(
            _shared_metrics.ANTIHYDRA_DIGIT_CONVERSION_EMITTED_DIGITS, len(digits)
        )
        return digits

    @source_reads_only
    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        return self.term.digit(index)

    def info(self) -> dict[str, object]:
        result = self.term.result()
        return {
            "requested_returns": result.requested,
            "completed_arithmetic_returns": result.returns,
            "h": result.h,
            "ledger": result.balance,
            "minimum_ledger": result.minimum,
            "first_failure_index": result.first_failure_index,
            "source_binding": result.source_binding,
            "total_arithmetic": True,
            "physical_roof_evaluated": self.term._physical is not None,
        }

    def physical_run(self) -> Run:
        return self.term.physical_run()

    def power_metrics(self) -> dict[str, object]:
        return self.term.metrics()


TermPayload = (
    PoweredReverseAddTermPayload
    | DoubleReverseTermPayload
    | PoweredCollatzTermPayload
    | AntihydraTermPayload
    | CommaTermPayload
    | FormulaTermPayload
    | FermatTermPayload
    | MersenneTermPayload
    | ScalarTermPayload
)


@dataclass(frozen=True, slots=True, init=False)
class ProjectedNumberTerm:
    family: NumberFamily
    index: int
    parameter: int | None
    source_radix: int | None
    _symbolic: SymbolicExpression
    payload: TermPayload
    metrics: ProjectionMetrics

    def __init__(
        self,
        family: NumberFamily,
        index: int,
        parameter: int | None,
        source_radix: int | None,
        symbolic: str | SymbolicExpression,
        payload: TermPayload,
        metrics: ProjectionMetrics,
    ) -> None:
        initialize_projected(
            self, family, index, parameter, source_radix, symbolic, payload, metrics
        )

    @property
    def symbolic(self) -> str:
        return self._symbolic.render()

    @property
    def estimated_bit_length(self) -> Extent:
        return self.payload.estimated_bit_length

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        return self.payload.materialize(
            max_bits=require_integer(max_bits, "output bit cap", 0)
        )

    def source_digits(self) -> tuple[int, ...] | None:
        if isinstance(
            self.payload,
            (
                FormulaTermPayload,
                PoweredReverseAddTermPayload,
                DoubleReverseTermPayload,
                PoweredCollatzTermPayload,
                AntihydraTermPayload,
                CommaTermPayload,
            ),
        ):
            return self.payload.digits()
        return None

    def digit(self, index: int) -> int:
        """Evaluate one source-radix digit without materializing the word."""
        if isinstance(self.payload, DoubleReverseTermPayload):
            return self.payload.digit(index)
        if isinstance(self.payload, PoweredReverseAddTermPayload):
            index = require_integer(index, "digit coordinate")
            if index < 0:
                raise IndexError(index)
            self.payload.term._prepare_recursive_source_authority()
        return self._digit_source_only(index)

    @source_reads_only
    def _digit_source_only(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if isinstance(self.payload, PoweredReverseAddTermPayload):
            return self.payload.digit(index)
        if isinstance(
            self.payload,
            (
                PoweredCollatzTermPayload,
                AntihydraTermPayload,
                CommaTermPayload,
                FormulaTermPayload,
                FermatTermPayload,
                MersenneTermPayload,
            ),
        ):
            return self.payload.digit(index)
        raise TypeError(f"{self.family} term has no source-radix digit projection")


class NumberCompiler:
    """Project and materialize exact nth terms without family-specific frontends.

    A367620 uses one-based OEIS indices. Other iteration indices are zero-based.
    ``prime`` means the zero-based prime at or above
    ``start``.  ``mersenne`` uses the conventional exponent parameter, so term
    index ``p`` is ``2**p-1`` and requires ``p>=1``.

    A bounded cache keeps the complete execution owner for recently requested
    powered terms. Repeated observations share that owner's cumulative metrics
    and HashLife results. Different sources and powers retain separate ledgers;
    Collatz radix views share their existing binary term owner. Set
    ``max_cached_terms=0`` for independent cold requests.
    Like the underlying mutable execution owners, this compiler is intended
    for serial use. The limit bounds cached terms, not the size of their DAGs.
    """

    def __init__(
        self,
        *,
        max_cached_terms: int = 8,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
        shared_cache: bool = True,
    ) -> None:
        if type(shared_cache) is not bool:
            raise TypeError("shared_cache must be a bool")
        self._shared_cache = shared_cache
        self._max_cached_terms = require_integer(
            max_cached_terms, "powered term cache capacity", 0
        )
        self._max_context_nodes = (
            None
            if max_context_nodes is None
            else require_integer(max_context_nodes, "context node budget", 0)
        )
        self._max_cache_entries = (
            None
            if max_cache_entries is None
            else require_integer(max_cache_entries, "cache entry budget", 0)
        )
        self._powered_terms: OrderedDict[Hashable, object] = OrderedDict()
        self._powered_hits = self._powered_misses = self._powered_evictions = 0

    def powered_cache_info(self) -> dict[str, int]:
        """Report API-owner reuse separately from each term's runtime ledger."""
        return {
            "capacity": self._max_cached_terms,
            "retained_terms": len(self._powered_terms),
            "hits": self._powered_hits,
            "misses": self._powered_misses,
            "evictions": self._powered_evictions,
        }

    def clear_powered_cache(self) -> None:
        """Release API references; already returned terms remain usable."""
        self._powered_terms.clear()

    @staticmethod
    def clear_shared_cache() -> None:
        """Clear process summaries and invalidate outstanding cache leases."""
        from number_compiler.resources.process_cache import clear_process_cache

        clear_process_cache()

    def _powered_term(
        self,
        key: Hashable,
        expected_type: type[_PoweredOwner],
        create: Callable[[], _PoweredOwner],
        is_valid: Callable[[_PoweredOwner], bool],
    ) -> _PoweredOwner:
        """Reuse one family-admitted owner without knowing family semantics.

        Projection adapters own keys, construction, and source/budget checks.
        This shared boundary only enforces exact owner type, validity, and LRU
        retention; it never reconstructs or interprets a family action.
        """
        found = self._powered_terms.get(key)
        if found is not None:
            if type(found) is expected_type and is_valid(found):
                self._powered_terms.move_to_end(key)
                self._powered_hits += 1
                return found
            del self._powered_terms[key]
            self._powered_evictions += 1

        self._powered_misses += 1
        term = create()
        if type(term) is not expected_type:
            raise TypeError("powered owner factory returned a foreign owner")
        if self._max_cached_terms:
            if len(self._powered_terms) == self._max_cached_terms:
                self._powered_terms.popitem(last=False)
                self._powered_evictions += 1
            self._powered_terms[key] = term
        return term

    def project(self, query: TermQuery) -> ProjectedNumberTerm:
        """Project one already-validated, family-specific execution query."""
        from number_compiler.api.family_registry import resolve_projection_adapter

        adapter = resolve_projection_adapter(query)
        return adapter(self, query)

    def project_digit(self, query: TermQuery, coordinate: int) -> int:
        """Demand one digit from a typed query without a parameter bag."""
        digit_index = require_integer(coordinate, "digit coordinate")
        if digit_index < 0:
            raise IndexError(digit_index)
        return self.project(query).digit(digit_index)

    def project_reverse_add_growth_state(
        self,
        seed: int,
        *,
        base: int = 10,
    ) -> ReverseAddGrowthState:
        """Project the reverse-add radial boundary order and sign only.

        This is the 196-style lazy forcing coordinate: ``boundary_offset`` is
        the z-adic radial order of the first non-neutral pair coefficient and
        ``relation`` is its -1/0/+1 unit phase.  No carry field, successor
        formula, or output digit word is constructed.
        """
        from number_compiler.arithmetic.functions.state_reduction import (
            ReverseAddGrowthState,
        )

        value = require_integer(seed, "seed", 0)
        base = require_integer(base, "base", 2)
        digits = digits_lsd(value, base)
        pair = tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))
        return ReverseAddGrowthState.from_pair(pair, base=base)

    def project_reverse_add_boundary_phase(self, seed: int, *, base: int = 10) -> int:
        """Project only the reverse-add boundary sign, without carry state."""
        return self.project_reverse_add_growth_state(seed, base=base).relation

    def project_reverse_add_growth(self, seed: int, *, base: int = 10) -> int:
        """Return the next reverse-add length-growth bit from boundary phase only."""
        return self.project_reverse_add_growth_state(seed, base=base).growth

    def project_collatz_growth(self, seed: int) -> CollatzGrowthCharacter:
        """Project only the next accelerated growth bit from ``chi_4(seed)``.

        This deliberately bypasses orbit construction and exact valuation/root
        germ acquisition.
        """
        from number_compiler.sequences.collatz.character import (
            collatz_growth_character_value,
        )

        return collatz_growth_character_value(require_integer(seed, "seed", 1))

    def project_collatz_radial_character(
        self,
        seed: int,
        order: int,
    ) -> CollatzRadialCharacter:
        """Project the cyclic radial phase needed by an order-``m`` observer.

        No Collatz successor, parity word, or root-germ state is constructed.
        For compressed radix-four sources use ``collatz_radial_character_word``
        directly so the full valuation coordinate need not be retained.
        """
        from number_compiler.sequences.collatz.character import (
            collatz_radial_character_value,
        )

        return collatz_radial_character_value(
            require_integer(seed, "seed", 1), require_integer(order, "order", 0)
        )

    def nth(self, query: TermQuery, *, max_bits: int = 1_000_000) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        projected = self.project(query)
        if (
            isinstance(projected.payload, AntihydraTermPayload)
            and projected.payload.estimated_bit_length > max_bits
        ):
            raise ValueError((projected.payload.estimated_bit_length, max_bits))
        return projected.materialize(max_bits=max_bits)


__all__ = [
    "AntihydraTermPayload",
    "CommaTermPayload",
    "DoubleReverseTermPayload",
    "FermatTermPayload",
    "FormulaTermPayload",
    "MersenneTermPayload",
    "NumberCompiler",
    "NumberFamily",
    "PoweredCollatzTermPayload",
    "PoweredReverseAddTermPayload",
    "ProjectedNumberTerm",
    "ProjectionMetrics",
    "ScalarTermPayload",
    "TermPayload",
]
