"""Canonical nth-term projection/materialization API for all supported families."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from math import ceil, log2
from typing import Iterator, Literal

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
from number_compiler.arithmetic.functions.state_reduction import ReverseAddGrowthState
from number_compiler.hashlife.execution.evaluator import (
    iter_values,
    materialize_values,
    value_at,
)
from number_compiler.sequences.collatz.block_power import (
    CollatzPhysicalBlockMetrics,
    PoweredCollatzTerm,
)
from number_compiler.sequences.collatz.character import (
    CollatzGrowthCharacter,
    CollatzRadialCharacter,
    collatz_growth_character_value,
    collatz_radial_character_value,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)
from number_compiler.sequences.prime.select import nth_prime_at_or_after
from number_compiler.sequences.reverse_add.power import (
    ReverseAddPoweredTerm,
    ReverseAddPowerMetrics,
)

NumberFamily = Literal["reverse-add", "collatz", "prime", "fermat", "mersenne"]


@dataclass(frozen=True, slots=True)
class ProjectionMetrics:
    family: NumberFamily
    index: int
    construction_steps: int
    projection_work: int
    descriptor_nodes: int
    descriptor_bits: int
    width: Extent
    raw_squarings: int = 0
    prime_block_compilations: int = 0
    prime_max_block_length: int = 0


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
        return tuple(map(int, materialize_values(self.root)))

    def iter_digits(self, *, reverse: bool = False) -> Iterator[int]:
        if type(reverse) is not bool:
            raise TypeError("reverse must be a Boolean")
        return (int(value) for value in iter_values(self.root, reverse=reverse))

    @source_reads_only
    def digit(self, index: int) -> int:
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
        values = self.digits()
        return iter(reversed(values) if reverse else values)

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
    | FormulaTermPayload
    | FermatTermPayload
    | MersenneTermPayload
    | ScalarTermPayload
)


@dataclass(frozen=True, slots=True)
class ProjectedNumberTerm:
    family: NumberFamily
    index: int
    parameter: int | None
    source_radix: int | None
    symbolic: str
    payload: TermPayload
    metrics: ProjectionMetrics

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
                FormulaTermPayload,
                FermatTermPayload,
                MersenneTermPayload,
            ),
        ):
            return self.payload.digit(require_integer(index, "digit coordinate"))
        raise TypeError(f"{self.family} term has no source-radix digit projection")


class NumberCompiler:
    """Project and materialize exact nth terms without family-specific frontends.

    Indices are zero-based.  ``prime`` means the zero-based prime at or above
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

    def __init__(self, *, max_cached_terms: int = 8) -> None:
        self._max_cached_terms = require_integer(
            max_cached_terms, "powered term cache capacity", 0
        )
        self._powered_terms: OrderedDict[
            tuple[str, int, int, int], ReverseAddPoweredTerm | PoweredCollatzTerm
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

    def _powered_term(
        self, family: str, source: int, generation: int, base: int
    ) -> ReverseAddPoweredTerm | PoweredCollatzTerm:
        key = (family, source, generation, base)
        found = self._powered_terms.get(key)
        if found is not None:
            # A caller can retain a term after eviction, but changing its public
            # source parameters must not poison a later canonical request.
            valid = (
                (found.seed, found.generation, found.base) == (source, generation, base)
                if isinstance(found, ReverseAddPoweredTerm)
                else (found.seed, found.steps) == (source, generation)
            )
            if not valid:
                del self._powered_terms[key]
                self._powered_evictions += 1
                found = None
        if found is not None:
            self._powered_terms.move_to_end(key)
            self._powered_hits += 1
            return found
        self._powered_misses += 1
        term = (
            ReverseAddPoweredTerm(source, generation, base=base)
            if family == "reverse-add"
            else PoweredCollatzTerm(source, generation)
        )
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
        if name not in {"reverse-add", "collatz", "prime", "fermat", "mersenne"}:
            raise ValueError(f"unsupported family: {family}")
        n = require_integer(index, "term index", 0)

        if name == "reverse-add":
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
                f"reverse_add(seed={source},base={b})[{n}]",
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
                f"collatz(seed={seed})[{n}]",
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

        if name == "prime":
            start = require_integer(start, "prime start", 0)
            value, pm = nth_prime_at_or_after(start, n)
            payload = ScalarTermPayload(value)
            return ProjectedNumberTerm(
                "prime",
                n,
                start,
                None,
                f"prime_at_or_after(start={start})[{n}]",
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
                f"2^(2^{n})+1",
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
            f"2^{n}-1",
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
        return collatz_radial_character_value(
            require_integer(seed, "seed", 1), require_integer(order, "order", 0)
        )

    def nth(
        self, family: str, index: int, *, max_bits: int = 1_000_000, **kwargs: int
    ) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        return self.project_nth(family, index, **kwargs).materialize(max_bits=max_bits)


__all__ = [
    "NumberFamily",
    "ProjectionMetrics",
    "PoweredReverseAddTermPayload",
    "PoweredCollatzTermPayload",
    "FormulaTermPayload",
    "FermatTermPayload",
    "MersenneTermPayload",
    "ScalarTermPayload",
    "TermPayload",
    "ProjectedNumberTerm",
    "NumberCompiler",
]
