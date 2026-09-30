"""Canonical nth-term projection/materialization API for all supported families."""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Iterator
from dataclasses import dataclass
from math import ceil, log2
from typing import TYPE_CHECKING, Literal

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.api.symbolic_terms import SymbolicExpression, initialize_projected
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    value_from_lsd_digits,
)
from number_compiler.arithmetic.fields.symbolic_extent import (
    Extent,
    ReverseAddBitExtent,
    ReverseAddExtent,
)
from number_compiler.arithmetic.formula.formula import FormulaRoot
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)

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
    from number_compiler.sequences.comma.power import CommaTerm
    from number_compiler.sequences.reverse_add.power import (
        ReverseAddPoweredTerm,
        ReverseAddPowerMetrics,
    )


NumberFamily = Literal[
    "reverse-add", "collatz", "antihydra", "prime", "fermat", "mersenne", "a367620"
]


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
class PoweredReverseAddTermPayload:
    term: ReverseAddPoweredTerm

    def __post_init__(self) -> None:
        from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

        if type(self.term) is not ReverseAddPoweredTerm:
            raise TypeError("powered reverse payload requires its exact term type")

    @property
    def estimated_bit_length(self) -> Extent:
        # Keep the exact bit cap lazy for the same reason as the exact radix
        # width: construction itself must not execute the endpoint transducer.
        return ReverseAddBitExtent(self.term.seed, self.term.base, self.term.generation)

    def digits(self) -> tuple[int, ...]:
        return self.term.digits()

    def iter_digits(self, *, reverse: bool = False) -> Iterator[int]:
        if type(reverse) is not bool:
            raise TypeError("reverse must be a Boolean")
        if not reverse:
            return self.term.iter_digits()
        # Text emission is already linear in the digit count.  Reversing the
        # final stream here does not pollute pre-print construction/projection.
        return iter(reversed(self.term.digits()))

    @source_reads_only
    def digit(self, index: int) -> int:
        return self.term.digit(index)

    def materialize(self, *, max_bits: int) -> int:
        return self.term.materialize(max_bits=max_bits)

    def power_metrics(self) -> ReverseAddPowerMetrics:
        return self.term.metrics()


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
        return tuple(
            map(
                int,
                digits_lsd(
                    self.materialize(max_bits=self.term.maximum_width), self.radix
                ),
            )
        )

    def iter_digits(self, *, reverse: bool = False) -> Iterator[int]:
        if type(reverse) is not bool:
            raise TypeError("reverse must be a Boolean")
        if reverse:
            return iter(reversed(self.digits()))
        if self.radix == 2:
            return self.term.iter_digits()

        def projected() -> Iterator[int]:
            # Explicit full-output lowering happens once, on first demand.
            # It must not become one source-image reconstruction per digit.
            value = self.materialize(max_bits=self.term.maximum_width)
            yield from map(int, digits_lsd(value, self.radix))

        return projected()

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
        value = self.term.value()
        return digits_lsd(value, 2)

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


@dataclass(frozen=True, slots=True)
class FermatTermPayload:
    spec: FermatNumberSpec

    @property
    def estimated_bit_length(self) -> Extent:
        return self.spec.bit_length_extent

    @source_reads_only
    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if index < 0 or not self.spec.bit_length_extent.contains_index(index):
            raise IndexError(index)
        return int(index == 0 or self.spec.exponent_extent == index)

    def materialize(self, *, max_bits: int) -> int:
        return self.spec.materialize(max_bits=max_bits)


@dataclass(frozen=True, slots=True)
class MersenneTermPayload:
    spec: MersenneNumberSpec

    @property
    def estimated_bit_length(self) -> int:
        return self.spec.bit_length

    @source_reads_only
    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate")
        if not 0 <= index < self.spec.bit_length:
            raise IndexError(index)
        return 1

    def materialize(self, *, max_bits: int) -> int:
        return self.spec.materialize(max_bits=max_bits)


@dataclass(frozen=True, slots=True)
class ScalarTermPayload:
    value: int

    def __post_init__(self) -> None:
        require_integer(self.value, "scalar term", 0)

    @property
    def estimated_bit_length(self) -> int:
        return max(1, int(self.value).bit_length())

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        if self.estimated_bit_length > max_bits:
            raise ValueError((self.estimated_bit_length, max_bits))
        return int(self.value)


TermPayload = (
    PoweredReverseAddTermPayload
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
                PoweredCollatzTermPayload,
                AntihydraTermPayload,
                CommaTermPayload,
            ),
        ):
            return self.payload.digits()
        return None

    @source_reads_only
    def digit(self, index: int) -> int:
        """Evaluate one source-radix digit without materializing the word."""
        if isinstance(
            self.payload,
            (
                PoweredReverseAddTermPayload,
                PoweredCollatzTermPayload,
                AntihydraTermPayload,
                CommaTermPayload,
                FormulaTermPayload,
                FermatTermPayload,
                MersenneTermPayload,
            ),
        ):
            return self.payload.digit(require_integer(index, "digit coordinate"))
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
        self._powered_terms: OrderedDict[
            tuple[str, int, int, int],
            ReverseAddPoweredTerm
            | PoweredCollatzTerm
            | AntihydraArithmeticTerm
            | CommaTerm,
        ] = OrderedDict()
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
        self, family: str, source: int, generation: int, base: int
    ) -> (
        ReverseAddPoweredTerm | PoweredCollatzTerm | AntihydraArithmeticTerm | CommaTerm
    ):
        certificate_version = ""
        if family == "reverse-add":
            from number_compiler.sequences.reverse_add.power import (
                ReverseAddPoweredTerm,
            )
        elif family == "collatz":
            from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
        elif family == "antihydra":
            from number_compiler.sequences.antihydra.runtime import (
                AntihydraArithmeticTerm,
            )
        elif family == "a367620":
            from number_compiler.sequences.comma.certificates import CERTIFICATE_ID
            from number_compiler.sequences.comma.power import CommaTerm

            certificate_version = CERTIFICATE_ID
        else:
            raise ValueError("unsupported powered family")
        key = (
            family if not certificate_version else f"{family}:{certificate_version}",
            source,
            generation,
            base,
        )
        found = self._powered_terms.get(key)
        if found is not None:
            # A caller can retain a term after eviction, but changing its public
            # source parameters must not poison a later canonical request.
            if family == "reverse-add" and isinstance(found, ReverseAddPoweredTerm):
                valid = (found.seed, found.generation, found.base) == (
                    source,
                    generation,
                    base,
                )
            elif family == "collatz" and isinstance(found, PoweredCollatzTerm):
                valid = (found.seed, found.steps) == (source, generation)
            elif family == "antihydra" and isinstance(found, AntihydraArithmeticTerm):
                valid = (
                    found.requested,
                    found.max_steps,
                    found.max_state_bits,
                ) == (generation, source, base)
            elif family == "a367620" and isinstance(found, CommaTerm):
                valid = found.certificate_version == certificate_version and (
                    found.index,
                    found.max_states,
                    found.max_work,
                ) == (
                    generation,
                    source,
                    base,
                )
            else:
                valid = False
            if not valid:
                del self._powered_terms[key]
                self._powered_evictions += 1
                found = None
        if found is not None:
            self._powered_terms.move_to_end(key)
            self._powered_hits += 1
            return found
        self._powered_misses += 1
        term: (
            ReverseAddPoweredTerm
            | PoweredCollatzTerm
            | AntihydraArithmeticTerm
            | CommaTerm
        )
        if family == "reverse-add":
            term = ReverseAddPoweredTerm(
                source,
                generation,
                base=base,
                max_context_nodes=self._max_context_nodes,
                max_cache_entries=self._max_cache_entries,
            )
        elif family == "collatz":
            term = PoweredCollatzTerm(
                source,
                generation,
                shared_cache=self._shared_cache,
                max_context_nodes=self._max_context_nodes,
                max_cache_entries=self._max_cache_entries,
            )
        elif family == "antihydra":
            term = AntihydraArithmeticTerm(
                generation,
                shared_cache=self._shared_cache,
                max_steps=source,
                max_state_bits=base,
                max_cache_entries=(
                    8192 if self._max_cache_entries is None else self._max_cache_entries
                ),
            )
        elif family == "a367620":
            term = CommaTerm(
                generation,
                max_states=source,
                max_work=base,
                certificate_version=certificate_version,
                shared_cache=self._shared_cache,
                max_context_nodes=self._max_context_nodes,
                max_cache_entries=self._max_cache_entries,
            )
        else:
            raise ValueError("unsupported powered family")
        if self._max_cached_terms:
            if len(self._powered_terms) == self._max_cached_terms:
                self._powered_terms.popitem(last=False)
                self._powered_evictions += 1
            self._powered_terms[key] = term
        return term

    def project_nth(
        self,
        family: str,
        index: int,
        *,
        seed: int | None = None,
        base: int = 10,
        radix: int = 2,
        start: int = 2,
        max_steps: int = 4096,
        max_state_bits: int = 4096,
        max_comma_states: int = 131_072,
        max_comma_work: int = 1_000_000,
        max_prime_states: int = 131_072,
        max_prime_work: int = 1_000_000,
        max_prime_stages: int = 4096,
    ) -> ProjectedNumberTerm:
        if type(family) is not str:
            raise TypeError("family must be a string")
        name = family.lower().replace("_", "-")
        if name in {"196", "reverse196"}:
            name = "reverse-add"
            seed = 196 if seed is None else seed
            base = 10 if base is None else base
        if name == "primes":
            name = "prime"
        if name not in {
            "a367620",
            "reverse-add",
            "collatz",
            "antihydra",
            "prime",
            "fermat",
            "mersenne",
        }:
            raise ValueError(f"unsupported family: {family}")
        n = require_integer(index, "term index", 0)

        if name == "a367620":
            from number_compiler.sequences.comma.power import CommaTerm

            require_integer(n, "A367620 index", 1)
            states = require_integer(max_comma_states, "comma state budget", 1)
            work = require_integer(max_comma_work, "comma work budget", 1)
            if seed is not None or base != 10 or radix != 2 or start != 2:
                raise ValueError("A367620 uses its fixed decimal source and indexing")
            comma = self._powered_term(name, states, n, work)
            assert isinstance(comma, CommaTerm)
            return ProjectedNumberTerm(
                "a367620",
                n,
                20,
                10,
                SymbolicExpression("a367620", n),
                CommaTermPayload(comma),
                ProjectionMetrics(
                    "a367620",
                    n,
                    0,
                    0,
                    1,
                    n.bit_length() + 5,
                    None,
                ),
            )

        if name == "reverse-add":
            from number_compiler.sequences.reverse_add.power import (
                ReverseAddPoweredTerm,
            )

            if seed is None:
                raise ValueError("reverse-add requires seed")
            b = require_integer(base, "base", 2)
            source = require_integer(seed, "seed", 0)
            reverse_powered = self._powered_term("reverse-add", source, n, b)
            if not isinstance(reverse_powered, ReverseAddPoweredTerm):
                raise AssertionError("reverse-add cache contains another family")
            payload: TermPayload = PoweredReverseAddTermPayload(reverse_powered)
            # Width is an exact lazy observer.  Forcing it here would turn the
            # compact nth-term construction back into endpoint execution.
            width = ReverseAddExtent(source, b, n)
            node_bits = bit_width(max(1, reverse_powered.operator_nodes))
            desc_bits = (
                reverse_powered.descriptor_bits
                + reverse_powered.operator_nodes * max(1, node_bits + 2)
            )
            return ProjectedNumberTerm(
                "reverse-add",
                n,
                source,
                b,
                SymbolicExpression("reverse-add", n, source, b),
                payload,
                ProjectionMetrics(
                    "reverse-add",
                    n,
                    reverse_powered.compose_operations,
                    0,
                    max(1, reverse_powered.operator_nodes),
                    desc_bits,
                    width,
                ),
            )

        if name == "collatz":
            from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

            if seed is None:
                raise ValueError("collatz requires seed")
            r = require_integer(radix, "radix", 2)
            if not (r in (2, 3) or (r >= 6 and r % 6 == 0)):
                raise ValueError("Collatz radix must be 2, 3, or divisible by 6")
            seed = require_integer(seed, "seed", 1)
            powered = self._powered_term("collatz", seed, n, 2)
            if not isinstance(powered, PoweredCollatzTerm):
                raise AssertionError("Collatz cache contains another family")
            payload = PoweredCollatzTermPayload(powered, r)
            node_bits = bit_width(max(1, powered.operator_nodes))
            desc_bits = powered.descriptor_bits + powered.operator_nodes * max(
                1, node_bits + 2
            )
            return ProjectedNumberTerm(
                "collatz",
                n,
                seed,
                r,
                SymbolicExpression("collatz", n, seed),
                payload,
                ProjectionMetrics(
                    "collatz",
                    n,
                    powered.compose_operations,
                    0,
                    max(1, powered.operator_nodes),
                    desc_bits,
                    powered.maximum_width,
                ),
            )

        if name == "antihydra":
            from number_compiler.sequences.antihydra.runtime import (
                AntihydraArithmeticTerm,
            )

            if seed is not None:
                raise ValueError("Antihydra uses the pinned blank-tape source")
            steps = require_integer(max_steps, "macro return budget", 0)
            state_bits = require_integer(max_state_bits, "integer bit budget", 4)
            antihydra = self._powered_term("antihydra", steps, n, state_bits)
            if not isinstance(antihydra, AntihydraArithmeticTerm):
                raise AssertionError("Antihydra cache contains another family")
            payload = AntihydraTermPayload(antihydra)
            descriptor_bits = max(
                1, n.bit_length() + steps.bit_length() + state_bits.bit_length()
            )
            return ProjectedNumberTerm(
                "antihydra",
                n,
                None,
                2,
                SymbolicExpression("antihydra", n),
                payload,
                ProjectionMetrics("antihydra", n, 0, 0, 1, descriptor_bits, 4 + n),
            )

        if name == "prime":
            from number_compiler.sequences.prime.select import nth_prime_at_or_after

            start = require_integer(start, "prime start", 0)
            prime_states = require_integer(
                max_prime_states, "prime rank DAG state budget", 1
            )
            prime_work = require_integer(
                max_prime_work, "prime rank arithmetic work budget", 1
            )
            prime_stages = require_integer(
                max_prime_stages, "prime factor stage budget", 1
            )
            value, pm = nth_prime_at_or_after(
                start,
                n,
                max_states=prime_states,
                max_work=prime_work,
                max_stages=prime_stages,
                shared_cache=self._shared_cache,
            )
            payload = ScalarTermPayload(value)
            return ProjectedNumberTerm(
                "prime",
                n,
                start,
                None,
                SymbolicExpression("prime", n, start),
                payload,
                ProjectionMetrics(
                    "prime",
                    n,
                    pm.descent_rounds + pm.expansion_rounds,
                    pm.projection_work,
                    1,
                    max(1, value.bit_length()),
                    1,
                    prime_block_compilations=pm.block_compilations,
                    prime_max_block_length=pm.max_block_length,
                    prime_dag_states=pm.dag_states,
                    prime_cache_hits=pm.cache_hits,
                    prime_factor_stages=pm.factor_stages,
                    prime_discovery_queries=pm.discovery_queries,
                    prime_peak_pending_frames=pm.peak_pending_frames,
                    prime_retained_entries=pm.retained_entries,
                    prime_arithmetic_bit_work=pm.arithmetic_bit_work,
                    prime_parent_gap_positions_materialized=(
                        pm.parent_gap_positions_materialized
                    ),
                    shared_cache_hits=pm.shared_cache_hits,
                    shared_cache_misses=pm.shared_cache_misses,
                    shared_cache_entries=pm.shared_cache_entries,
                    shared_cache_bytes=pm.shared_cache_bytes,
                    shared_cache_evictions=pm.shared_cache_evictions,
                    shared_cache_bypasses=pm.shared_cache_bypasses,
                    shared_cache_publications=pm.shared_cache_publications,
                    prime_admission_work=pm.admission_work,
                    prime_request_allocations=pm.request_allocations,
                    prime_scheduler_work=pm.scheduler_work,
                    prime_scheduler_peak_entries=pm.scheduler_allocations,
                    prime_scheduler_counters=pm.scheduler_counters,
                ),
            )

        if name == "fermat":
            fermat_spec = FermatNumberSpec(n)
            payload = FermatTermPayload(fermat_spec)
            return ProjectedNumberTerm(
                "fermat",
                n,
                n,
                2,
                SymbolicExpression("fermat", n),
                payload,
                ProjectionMetrics(
                    "fermat",
                    n,
                    0,
                    0,
                    1,
                    fermat_spec.description_bits,
                    fermat_spec.bit_length_extent,
                    raw_squarings=0,
                ),
            )

        if n < 1:
            raise ValueError("Mersenne exponent/index must be >= 1")
        spec = MersenneNumberSpec(n)
        payload = MersenneTermPayload(spec)
        return ProjectedNumberTerm(
            "mersenne",
            n,
            n,
            2,
            SymbolicExpression("mersenne", n),
            payload,
            ProjectionMetrics(
                "mersenne",
                n,
                0,
                0,
                1,
                spec.description_bits,
                spec.bit_length,
                raw_squarings=0,
            ),
        )

    def project_digit(
        self,
        family: str,
        term_index: int,
        digit_index: int,
        **kwargs: int,
    ) -> int:
        """Validate a scalar request before creating its lazy term descriptor."""
        digit_index = require_integer(digit_index, "digit coordinate")
        if digit_index < 0:
            raise IndexError(digit_index)
        return self.project_nth(family, term_index, **kwargs).digit(digit_index)

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

    def nth(
        self, family: str, index: int, *, max_bits: int = 1_000_000, **kwargs: int
    ) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        projected = self.project_nth(family, index, **kwargs)
        if (
            isinstance(projected.payload, AntihydraTermPayload)
            and projected.payload.estimated_bit_length > max_bits
        ):
            raise ValueError((projected.payload.estimated_bit_length, max_bits))
        return projected.materialize(max_bits=max_bits)


__all__ = [
    "AntihydraTermPayload",
    "CommaTermPayload",
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
